"""Pre-registration H, selection: the population, the C entry points, their sizes and the selected entry points
(PREREG_H_v1.md, "Population and selection"). No model call, no build, nothing of the data is executed.

    python3 -I -B h_select.py [--fetch] THEOREM_REPO UPSTREAMS_DIR OUT_TSV

THEOREM_REPO: theorem-labs/oss-verify-proofs checked out at the pinned commit (checked, as is the README's sha256).
UPSTREAMS_DIR: bare git repositories of the upstreams, one per (repository, commit), named by `upstream_dir`.
With --fetch, a missing upstream commit is first fetched (git, depth 1, by sha, no checkout; full fetch if the server
refuses a fetch by sha); without it the script makes no network access. The output depends only on the pinned commits.
Needs PyYAML (the system python3 has it; the veriforch venv does not).

Rules (the prereg's; the readings this script makes are spelled out):
- Population: the rows of the "What is proved" table of the README (60, asserted).
- Build record: proofs/<project>/<harness>/provenance/PROVENANCE.yaml.
- Harness files: harness.source.files of the build record; when that list is empty, harness.source.from.path.
- C entry point: every harness file ends in ".c", and the build record shows only objects compiled from C:
  (a) every source file that the record's licence components name (`files:`, the linked files) has the suffix .c
      (headers and included fragments .h .inc .def are not objects; .o/.a names are not sources); a C++ (.cc .cpp .cxx
      .c++ .C), assembly (.s .S .asm) or Objective-C (.m .mm) file makes the entry point not C;
  (b) the plain build links no C++ standard library (libc++.a, libc++abi.a).
  The toolchain's runtimes (the C library, compiler-rt, the sanitizer runtime, and libunwind and libc++, which ASan
  builds link for the sanitizer runtime) are not objects of the program and are not counted. A plain build that links
  libunwind.a is named in the reason.
- Size: physical lines (newline count, plus one for a non-empty last line without a newline) of the blobs at the
  recorded upstream commit whose path ends in ".c" or ".h" (case-sensitive): regular files only (no symlinks, no
  submodule contents), with no directory component named test, tests, fuzz, fuzzing, example, examples, doc, docs,
  bench, benchmark, benchmarks or contrib (exact name, any depth), and without the harness files when the harness
  comes from the upstream repository at that commit. Computed for every entry point whose harness files are all C.
- Selected: the C entry points of size <= 20,000; if more than 12, the 12 smallest (ties by entry point name, then
  project); cjson/cjson_read_fuzzer is added if it qualifies and is not among them. rank = processing order (ascending
  size, same ties).
Also writes OUT_TSV's stem + ".variants.tsv": each size under other readings (directory names case-insensitive; top-level
directories only; newline count only), the symlinked and submodule .c/.h paths left out, and whether the selection
under each reading equals the main one.
"""
from __future__ import annotations

import hashlib
import os
import re
import subprocess
import sys
from pathlib import Path

import yaml

THEOREM_COMMIT = "98e995d4daced70a0a4aa2c810854b88720735f1"
README_SHA256 = "58e191365e6993e596e88f9b832136bb106077935dd66088c6c5afca874706e2"
N_POPULATION = 60
MAX_LINES = 20000
MAX_SELECTED = 12
CJSON = ("cjson", "cjson_read_fuzzer")
EXCLUDED_DIRS = frozenset("test tests fuzz fuzzing example examples doc docs bench benchmark benchmarks contrib".split())

C_SUFFIXES = {"c"}
NON_OBJECT_SUFFIXES = {"h", "inc", "def", "o", "a"}
NON_C_SUFFIXES = {"cc": "C++", "cpp": "C++", "cxx": "C++", "c++": "C++", "C": "C++",
                  "s": "assembly", "S": "assembly", "asm": "assembly", "m": "Objective-C", "mm": "Objective-C++"}
CXX_STDLIB = ("libc++.a", "libc++abi.a")

GIT_ENV = dict(os.environ, GIT_TERMINAL_PROMPT="0", GIT_ASKPASS="/bin/false", GIT_CONFIG_NOSYSTEM="1")


def git(repo: Path, *args: str, check: bool = True, timeout: int = 600, binary: bool = False):
    p = subprocess.run(["git", "-C", str(repo), "-c", "pack.threads=1", "-c", "index.threads=1", *args],
                       capture_output=True, env=GIT_ENV, timeout=timeout, check=False)
    if check and p.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} in {repo}: rc {p.returncode}: {p.stderr.decode(errors='replace')}")
    return p if binary else subprocess.CompletedProcess(p.args, p.returncode, p.stdout.decode(errors="replace"),
                                                        p.stderr.decode(errors="replace"))


def norm_repo(url: str) -> str:
    u = url.strip().rstrip("/")
    u = re.sub(r"^https?://", "", u)
    return re.sub(r"\.git$", "", u).lower()


def upstream_dir(base: Path, url: str, commit: str) -> Path:
    return base / (re.sub(r"[^A-Za-z0-9._-]+", "_", norm_repo(url)) + "@" + commit[:12] + ".git")


def has_commit(repo: Path, commit: str) -> bool:
    return repo.is_dir() and git(repo, "cat-file", "-e", commit + "^{commit}", check=False).returncode == 0


def fetch(url: str, commit: str, dest: Path) -> None:
    if has_commit(dest, commit):
        return
    if not dest.exists():
        dest.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "init", "-q", "--bare", str(dest)], check=True, env=GIT_ENV)
    p = git(dest, "fetch", "-q", "--depth", "1", "--no-tags", url, commit, check=False, timeout=3600)
    if p.returncode != 0 or not has_commit(dest, commit):
        print(f"fetch by sha refused for {url} ({p.stderr.strip()[:200]}); fetching all branches and tags",
              file=sys.stderr)
        git(dest, "fetch", "-q", "--no-tags", url, "+refs/heads/*:refs/remotes/origin/*", "+refs/tags/*:refs/tags/*",
            timeout=3600)
    if not has_commit(dest, commit):
        raise RuntimeError(f"{url}: commit {commit} not found after fetch")


def readme_rows(theorem: Path) -> list[tuple[int, str, str, str, str]]:
    """(row, library, entry point, project, harness) for each row of the "What is proved" table."""
    text = (theorem / "README.md").read_bytes()
    if hashlib.sha256(text).hexdigest() != README_SHA256:
        raise SystemExit("README.md sha256 differs from the prereg's")
    lines = text.decode().splitlines()
    start = lines.index("## What is proved")
    rows = []
    for line in lines[start + 1:]:
        if line.startswith("## "):
            break
        m = re.fullmatch(r"\| ([^|]+?) \| \[([^\]]+)\]\(proofs/([^/]+)/([^/]+)/\) \| ([^|]+?) \|", line)
        if m:
            if m.group(2) != m.group(4):
                raise SystemExit(f"row link differs from its name: {line}")
            rows.append((len(rows) + 1, m.group(1), m.group(2), m.group(3), m.group(4)))
    if len(rows) != N_POPULATION:
        raise SystemExit(f"{len(rows)} rows in the README table, expected {N_POPULATION}")
    return rows


def source_tokens(text: str) -> list[tuple[str, str]]:
    """(file name, suffix) of each file-like token of a licence component's `files:` text."""
    out = []
    for m in re.finditer(r"(?<![A-Za-z0-9_./+-])([A-Za-z0-9_][A-Za-z0-9_./+-]*\.([A-Za-z][A-Za-z+]*))(?=[\s,;:()]|$)",
                         text):
        out.append((m.group(1), m.group(2)))
    return out


def classify(rec: dict) -> dict:
    """Languages of the harness and of the linked objects, by the build record."""
    src = rec["harness"]["source"]
    frm = src.get("from") or {}
    files = list(src.get("files") or [])
    hfiles = files if files else [frm.get("path", "")]
    harness_c = bool(hfiles) and all(f.endswith(".c") for f in hfiles)
    named = []
    for comp in rec.get("licence", {}).get("components", []):
        f = comp.get("files", "-")
        if isinstance(f, list):
            f = ", ".join(map(str, f))
        if f and f != "-":
            named.extend(source_tokens(str(f)))
    n_c = sorted({n for n, s in named if s in C_SUFFIXES})
    non_c = sorted({(n, NON_C_SUFFIXES[s]) for n, s in named if s in NON_C_SUFFIXES})
    plain = (rec.get("link_inputs", {}).get("plain", {}) or {}).get("inputs", {}) or {}
    cxx_std = [f"{k}({plain[k]})" for k in CXX_STDLIB if k in plain]
    unwind = f"libunwind.a({plain['libunwind.a']})" if "libunwind.a" in plain else ""
    linked = [f"named C sources: {len(n_c)}"]
    if non_c:
        linked.append("non-C sources: " + ", ".join(f"{n} ({lang})" for n, lang in non_c))
    if cxx_std:
        linked.append("plain build links " + ", ".join(cxx_std))
    if unwind:
        linked.append("plain build links " + unwind)
    objects_c = not non_c and not cxx_std
    if not harness_c:
        why = "harness " + ", ".join(f for f in hfiles if not f.endswith(".c")) + " is not C"
    elif non_c:
        why = "links objects compiled from " + ", ".join(f"{n} ({lang})" for n, lang in non_c)
    elif cxx_std:
        why = "plain build links the C++ standard library " + ", ".join(cxx_std)
    else:
        why = ""
    suffixes = sorted({f.rsplit(".", 1)[-1] for f in hfiles})
    lang = "C" if harness_c else "C++" if all(NON_C_SUFFIXES.get(s) == "C++" for s in suffixes) else (
        "other (" + ",".join(suffixes) + ")")
    return {"harness_files": hfiles, "harness_lang": lang, "linked": "; ".join(linked),
            "is_c": harness_c and objects_c, "not_c_why": why, "unwind": unwind, "frm": frm}


def blob_lines(data: bytes) -> tuple[int, int]:
    """(physical lines, newline count)."""
    n = data.count(b"\n")
    return n + (1 if data and not data.endswith(b"\n") else 0), n


def tree_sizes(repo: Path, commit: str, harness_paths: set[str]) -> dict:
    """Sizes of the .c/.h files at `commit` under the main reading and the variants."""
    ls = git(repo, "ls-tree", "-r", "-z", "--full-tree", commit, binary=True).stdout
    blobs, symlinks, gitlinks = [], [], []
    for ent in ls.split(b"\0"):
        if not ent:
            continue
        meta, path = ent.split(b"\t", 1)
        mode, typ, oid = meta.decode().split(" ")
        p = path.decode("utf-8", errors="surrogateescape")
        if mode == "160000":
            gitlinks.append(p)
            continue
        if not (p.endswith(".c") or p.endswith(".h")):
            continue
        if mode == "120000":
            symlinks.append(p)
            continue
        if typ == "blob" and mode in ("100644", "100755"):
            blobs.append((p, oid))
    # read every candidate blob once (git cat-file --batch, in tree order)
    req = b"".join(oid.encode() + b"\n" for _, oid in blobs)
    out = subprocess.run(["git", "-C", str(repo), "cat-file", "--batch"], input=req, capture_output=True,
                         env=GIT_ENV, timeout=1800, check=True).stdout
    pos, content = 0, {}
    for _, oid in blobs:
        nl = out.index(b"\n", pos)
        head = out[pos:nl].split(b" ")
        if head[0].decode() != oid or head[1] != b"blob":
            raise RuntimeError(f"cat-file: unexpected header {out[pos:nl]!r} for {oid}")
        size = int(head[2])
        content[oid] = out[nl + 1:nl + 1 + size]
        pos = nl + 1 + size + 1
    sizes = {"main": 0, "dirs_ci": 0, "dirs_top": 0, "newlines": 0}
    nfiles = 0
    for p, oid in blobs:
        if p in harness_paths:
            continue
        dirs = p.split("/")[:-1]
        phys, nls = blob_lines(content[oid])
        main_ok = not any(d in EXCLUDED_DIRS for d in dirs)
        if main_ok:
            sizes["main"] += phys
            sizes["newlines"] += nls
            nfiles += 1
        if not any(d.lower() in EXCLUDED_DIRS for d in dirs):
            sizes["dirs_ci"] += phys
        if not (dirs and dirs[0] in EXCLUDED_DIRS):
            sizes["dirs_top"] += phys
    return {"sizes": sizes, "files": nfiles, "symlinks": sorted(symlinks), "gitlinks": sorted(gitlinks)}


def select(entries: list[dict], key: str) -> list[tuple[str, str]]:
    """(project, harness) of the selected entry points in processing order, sizes read from size[key]."""
    q = [e for e in entries if e["is_c"] and e.get("size") and e["size"]["sizes"][key] <= MAX_LINES]
    q.sort(key=lambda e: (e["size"]["sizes"][key], e["entry_point"], e["project"]))
    sel = q[:MAX_SELECTED]
    if any((e["project"], e["harness"]) == CJSON for e in q) and not any(
            (e["project"], e["harness"]) == CJSON for e in sel):
        sel.append(next(e for e in q if (e["project"], e["harness"]) == CJSON))
    return [(e["project"], e["harness"]) for e in sel]


def tsv_field(v) -> str:
    return re.sub(r"[\t\r\n]+", " ", str(v))


def main(argv: list[str]) -> int:
    args = [a for a in argv[1:] if a != "--fetch"]
    do_fetch = "--fetch" in argv[1:]
    if len(args) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    theorem, updir, out = Path(args[0]).resolve(), Path(args[1]).resolve(), Path(args[2]).resolve()
    head = git(theorem, "rev-parse", "HEAD").stdout.strip()
    if head != THEOREM_COMMIT:
        raise SystemExit(f"{theorem} is at {head}, expected {THEOREM_COMMIT}")
    entries = []
    for row, library, ep, project, harness in readme_rows(theorem):
        rec = yaml.safe_load((theorem / "proofs" / project / harness / "provenance" / "PROVENANCE.yaml").read_text())
        ent = rec["entry_point"]
        if (ent["project"], ent["harness"]) != (project, harness):
            raise SystemExit(f"build record of {project}/{harness} names {ent['project']}/{ent['harness']}")
        up = rec["upstream"]
        e = {"row": row, "library": library, "entry_point": ep, "project": project, "harness": harness,
             "repo": up["repository"], "commit": up["commit"], **classify(rec)}
        if not re.fullmatch(r"[0-9a-f]{40}", e["commit"]):
            raise SystemExit(f"{project}/{harness}: upstream commit {e['commit']!r} is not a full sha")
        entries.append(e)
    # sizes: every entry point whose harness is C (one tree walk per upstream commit)
    trees: dict[tuple[str, str], dict] = {}
    for e in entries:
        if e["harness_lang"] != "C":
            continue
        frm = e["frm"]
        same = norm_repo(frm.get("repository", "")) == norm_repo(e["repo"]) and frm.get("commit") == e["commit"]
        hpaths = {frm["path"]} if same and frm.get("path") else set()
        key = (e["repo"], e["commit"], tuple(sorted(hpaths)))
        if key not in trees:
            d = upstream_dir(updir, e["repo"], e["commit"])
            if do_fetch:
                fetch(e["repo"], e["commit"], d)
            if not has_commit(d, e["commit"]):
                raise SystemExit(f"{d}: commit {e['commit']} missing (run with --fetch)")
            trees[key] = tree_sizes(d, e["commit"], hpaths)
        e["size"] = trees[key]
        e["harness_excluded"] = sorted(hpaths)
    main_sel = select(entries, "main")
    rank = {k: i + 1 for i, k in enumerate(main_sel)}
    cols = ["row", "library", "entry_point", "upstream_repository", "upstream_commit", "harness_path", "harness_lang",
            "linked_objects", "c_status", "lines", "selected", "rank", "reason"]
    lines_out = ["\t".join(cols)]
    n_q = sum(1 for e in entries if e["is_c"] and e.get("size") and e["size"]["sizes"]["main"] <= MAX_LINES)
    for e in entries:
        k = (e["project"], e["harness"])
        frm = e["frm"]
        hp = ", ".join(e["harness_files"]) if not frm.get("path") else frm["path"]
        if frm.get("repository") and norm_repo(frm["repository"]) != norm_repo(e["repo"]):
            hp += f" (in {frm['repository']} at {str(frm.get('commit', ''))[:12]})"
        n = e["size"]["sizes"]["main"] if e.get("size") else None
        if not e["is_c"]:
            reason = "not a C entry point: " + e["not_c_why"]
            if n is not None:
                reason += f" (size {n} for reference)"
        elif n > MAX_LINES:
            reason = f"C entry point; {n} lines > {MAX_LINES}"
        elif k in rank:
            reason = f"C entry point; {n} lines <= {MAX_LINES}; selected, rank {rank[k]} of {len(main_sel)}"
        else:
            reason = f"C entry point; {n} lines <= {MAX_LINES}; not among the {MAX_SELECTED} smallest of {n_q}"
        if e["is_c"] and e["unwind"]:
            reason += (f"; note: its plain build links {e['unwind']} (a toolchain runtime that Theorem lists as the"
                       " C++ runtime), not counted as an object of the program")
        lines_out.append("\t".join(tsv_field(v) for v in [
            e["row"], e["library"], e["entry_point"], e["repo"], e["commit"], hp, e["harness_lang"], e["linked"],
            "C" if e["is_c"] else "not C", n if n is not None else "-", "y" if k in rank else "n",
            rank.get(k, "-"), reason]))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines_out) + "\n")
    # variants: sizes under the other readings, and whether the selection changes
    vcols = ["row", "entry_point", "c_status", "files", "lines_main", "lines_dirs_case_insensitive",
             "lines_dirs_top_level_only", "lines_newline_count", "symlinked_ch_left_out", "submodules_left_out",
             "harness_files_left_out"]
    vlines = ["\t".join(vcols)]
    for e in entries:
        if not e.get("size"):
            continue
        s = e["size"]
        vlines.append("\t".join(tsv_field(v) for v in [
            e["row"], f"{e['project']}/{e['harness']}", "C" if e["is_c"] else "not C", s["files"],
            s["sizes"]["main"], s["sizes"]["dirs_ci"], s["sizes"]["dirs_top"], s["sizes"]["newlines"],
            ",".join(s["symlinks"]) or "-", ",".join(s["gitlinks"]) or "-", ",".join(e["harness_excluded"]) or "-"]))
    vlines.append("")
    vlines.append("# selection (processing order) under each reading")
    for key in ("main", "dirs_ci", "dirs_top", "newlines"):
        sel = select(entries, key)
        vlines.append(f"# {key}\t{'same as main' if sel == main_sel else 'DIFFERS'}\t"
                      + " ".join(f"{p}/{h}" for p, h in sel))
    vout = out.with_name(out.stem + ".variants.tsv")
    vout.write_text("\n".join(vlines) + "\n")
    print(f"{len(entries)} entry points; {sum(e['is_c'] for e in entries)} C; {n_q} C of size <= {MAX_LINES}; "
          f"{len(main_sel)} selected: " + " ".join(f"{p}/{h}" for p, h in main_sel))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
