"""Pre-registration H, part one inputs: the public seed corpus of each selected entry point (PREREG_H_v1.md, "Part one",
Inputs). Data only: no build script and no program of the data is run here.

    python3 -I -B h_corpus.py SELECTION_TSV OSSFUZZ_GIT UPSTREAMS_DIR OUT_DIR [--seeds PROJECT/HARNESS=DIR ...]

SELECTION_TSV: the table of h_select.py (its selected rows). OSSFUZZ_GIT: a git repository holding google/oss-fuzz at
bd2ce219. UPSTREAMS_DIR: the upstream repositories of h_select.py. OUT_DIR gets, per entry point with a corpus,
<project>__<harness>/inputs/ (the inputs, after the draw) and MANIFEST.tsv (name, bytes, sha256; sorted by name),
and CORPORA.tsv (one row per selected entry point: status, source, counts, manifest sha256).

The corpus is the one OSS-Fuzz at bd2ce219 packs (<harness>_seed_corpus.zip), else the corpus directory of the upstream
at the recorded commit, else "no public corpus". Each packing rule below is transcribed from the script that makes the
zip; the sha256 of that script is checked, so a different script stops this one. Files are taken from the upstream at
the commit Theorem's build record gives (OSS-Fuzz's Dockerfiles clone the upstream's head; the packing rule is
OSS-Fuzz's, the tree is the one Theorem built). An input's name is its file name (the zip member's last component).
More than 500 inputs: sorted by sha256("fv-paper-prereg-H-2026-10-25|<entry point>|<file name>"), the first 500 kept.

Generated corpora (cgif): OSS-Fuzz's build runs `meson test`, whose seed generators (tests/<name>.c linked with
fuzz/cgif_create_fuzz_seed.c or fuzz/cgif_rgb_create_fuzz_seed.c) write <name>.seed, and zips them. Running them is a
native run, so without --seeds the entry point is reported as pending, with the expected names (and the upstream's
own sha256 of each seed, from fuzz/seeds.sha256, where it has one) in <project>__<harness>/EXPECTED.tsv. With
--seeds PROJECT/HARNESS=DIR, the seeds are taken from DIR: the names must be the expected ones, and every seed with an
upstream sha256 must match it.
"""
from __future__ import annotations

import csv
import hashlib
import os
import re
import subprocess
import sys
from pathlib import Path

OSSFUZZ_COMMIT = "bd2ce21991a94a362b92fb1bf25f86d5a1a60842"
DRAW_SALT = "fv-paper-prereg-H-2026-10-25"
MAX_INPUTS = 500
GIT_ENV = dict(os.environ, GIT_TERMINAL_PROMPT="0", GIT_CONFIG_NOSYSTEM="1")

# sha256 of each script whose packing rule is transcribed below (checked before the rule is used)
SCRIPT_SHA256 = {
    ("oss-fuzz", "projects/cjson/build.sh"): "cacff2e7814c94b26a283de5d6f944085c29b6fd4033f99b19bb1ae8770e7192",
    ("oss-fuzz", "projects/yajl-ruby/build.sh"): "599f4d0473ccd616370a9f12707d05bdd02eb5d5e1ed37bbe577b85912f25669",
    ("oss-fuzz", "projects/bzip2/build.sh"): "e7979dbc21299b96c9453a4347e961d15b5a7909d2b89629e3b6542efb591cf2",
    ("oss-fuzz", "projects/cgif/build.sh"): "f5f9d837dda05b1e80c2ffa60c2d86438541b0a3db3b6becd480f757e7952d9e",
    ("upstream", "fuzzing/ossfuzz.sh"): "a832e5c52839fa54637b052d3cfd9f63da8deb66f3ea6890af3adf4ff6557927",
    ("upstream", "fuzz/meson.build"): "f364415d9e8632c9da5990a06852b086c970a4b24f8c740a5a09813e8267b65a",
    ("upstream", "tests/meson.build"): "6b624622fe2bcf943e51fbb51edffc678a11d51bdce07a5d8bbc7ab909365e5b",
    ("upstream", "fuzz/seeds.sha256"): "7d98c49ea5cb65995fd312391496b6ae1c31d1c58bb4ae1be518a0236606e434",
}


def git_bytes(repo: Path, *args: str) -> bytes:
    p = subprocess.run(["git", "-C", str(repo), *args], capture_output=True, env=GIT_ENV, timeout=600, check=False)
    if p.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} in {repo}: rc {p.returncode}: {p.stderr.decode(errors='replace')}")
    return p.stdout


def norm_repo(url: str) -> str:
    u = re.sub(r"^https?://", "", url.strip().rstrip("/"))
    return re.sub(r"\.git$", "", u).lower()


def upstream_dir(base: Path, url: str, commit: str) -> Path:
    return base / (re.sub(r"[^A-Za-z0-9._-]+", "_", norm_repo(url)) + "@" + commit[:12] + ".git")


class Src:
    """Files of one repository at one commit, read with git (nothing is checked out)."""

    def __init__(self, kind: str, repo: Path, commit: str):
        self.kind, self.repo, self.commit = kind, repo, commit
        if git_bytes(repo, "cat-file", "-t", commit).strip() != b"commit":
            raise SystemExit(f"{repo}: {commit} is not a commit")

    def read(self, path: str) -> bytes:
        return git_bytes(self.repo, "cat-file", "blob", f"{self.commit}:{path}")

    def script(self, path: str) -> str:
        """A packing script, after its sha256 check."""
        data = self.read(path)
        want = SCRIPT_SHA256[(self.kind, path)]
        got = hashlib.sha256(data).hexdigest()
        if got != want:
            raise SystemExit(f"{self.kind}:{path} sha256 {got}, transcribed rule is for {want}")
        return data.decode()

    def tree(self, prefix: str = "") -> list[tuple[str, str, str]]:
        """(mode, type, path) of every entry under prefix (recursive)."""
        out = git_bytes(self.repo, "ls-tree", "-r", "-t", "-z", "--full-tree", self.commit,
                        *([prefix] if prefix else []))
        ents = []
        for ent in out.split(b"\0"):
            if ent:
                meta, path = ent.split(b"\t", 1)
                mode, typ, _ = meta.decode().split(" ")
                ents.append((mode, typ, path.decode("utf-8", errors="surrogateescape")))
        return ents


def line(text: str, n: int) -> str:
    return text.splitlines()[n - 1]


def expect(cond: bool, what: str) -> None:
    if not cond:
        raise SystemExit(f"packing rule check failed: {what}")


# --- one function per entry point: returns {"status", "source", "inputs": {name: bytes}} or a pending/none record ---

def corpus_cjson(of: Src, up: Src, seeds: Path | None) -> dict:
    b = of.script("projects/cjson/build.sh")
    expect(line(b, 18).strip() == "$SRC/cjson/fuzzing/ossfuzz.sh", "cjson build.sh:18 calls fuzzing/ossfuzz.sh")
    s = up.script("fuzzing/ossfuzz.sh")
    expect(line(s, 15).strip() == 'find $SRC/cjson/fuzzing/inputs -name "*" | \\' and
           line(s, 16).strip() == "xargs zip $OUT/cjson_read_fuzzer_seed_corpus.zip",
           "cjson ossfuzz.sh:15-16 zip everything under fuzzing/inputs")
    inputs = {}
    for mode, typ, path in up.tree("fuzzing/inputs/"):
        if typ == "tree":
            continue  # find lists directories too; zip without -r stores a directory as an empty entry, not an input
        expect(typ == "blob" and mode in ("100644", "100755"), f"cjson {path} is a regular file")
        name = path.rsplit("/", 1)[-1]
        expect(name not in inputs, f"cjson file name {name} is unique")
        inputs[name] = up.read(path)
    return {"status": "corpus", "inputs": inputs,
            "source": f"OSS-Fuzz {OSSFUZZ_COMMIT[:8]} projects/cjson/build.sh:18 runs the upstream's fuzzing/ossfuzz.sh,"
                      f" whose lines 15-16 zip every file under fuzzing/inputs/; files from the upstream at"
                      f" {up.commit[:12]}"}


def corpus_yajl(of: Src, up: Src, seeds: Path | None) -> dict:
    b = of.script("projects/yajl-ruby/build.sh")
    m = re.fullmatch(r"echo '([^']*)' > \$WORK/seed\.json", line(b, 20))
    expect(m is not None, "yajl-ruby build.sh:20 writes $WORK/seed.json with echo '...'")
    expect(line(b, 21) == "zip -q $OUT/json_fuzzer_seed_corpus.zip $WORK/seed.json",
           "yajl-ruby build.sh:21 zips seed.json alone")
    expect(len(re.findall(r"seed_corpus", b)) == 1, "yajl-ruby build.sh makes one seed corpus")
    # bash's builtin echo (build.sh runs under bash, xpg_echo off) prints its argument unchanged plus a newline
    return {"status": "corpus", "inputs": {"seed.json": m.group(1).encode() + b"\n"},
            "source": f"OSS-Fuzz {OSSFUZZ_COMMIT[:8]} projects/yajl-ruby/build.sh:20-21: one seed, written by echo"
                      f" (text of line 20 plus a newline) and zipped as json_fuzzer_seed_corpus.zip"}


def corpus_bzip2_compress(of: Src, up: Src, seeds: Path | None) -> dict:
    b = of.script("projects/bzip2/build.sh")
    zips = set(re.findall(r"([A-Za-z0-9_]+_seed_corpus)\.zip", b))
    expect(zips == {"bzip2_decompress_target_seed_corpus"}, "bzip2 build.sh packs only the decompress target's seeds")
    dirs = [p for _, typ, p in up.tree() if typ == "tree"]
    expect(not dirs, "bzip2 upstream tree has no directory")
    return {"status": "no public corpus", "inputs": None,
            "source": f"OSS-Fuzz {OSSFUZZ_COMMIT[:8]} projects/bzip2/build.sh packs a seed corpus only for"
                      f" bzip2_decompress_target (lines 42-44); the upstream at {up.commit[:12]} has no directory at"
                      f" all, so no corpus directory"}


def cgif_expected(up: Src, which: str) -> tuple[list[str], dict[str, str]]:
    """Seed names of meson's tests_index / tests_rgb, and the upstream's sha256 of each seed it lists."""
    t = up.script("tests/meson.build")
    m = re.search(rf"^{which} = \[\n(.*?)^\]", t, re.S | re.M)
    expect(m is not None, f"cgif tests/meson.build defines {which}")
    names = re.findall(r"\{ 'name' : '([A-Za-z0-9_]+)',\s*'seed_should_fail' : (?:true|false)\s*\}", m.group(1))
    expect(len(names) == len(m.group(1).strip().splitlines()), f"cgif {which}: one name per line")
    sums = {}
    for ln in up.script("fuzz/seeds.sha256").splitlines():
        h, n = ln.split()
        sums[n] = h
    return [n + ".seed" for n in names], sums


def corpus_cgif(which: str, harness: str):
    def rule(of: Src, up: Src, seeds: Path | None) -> dict:
        b = of.script("projects/cgif/build.sh")
        expect(line(b, 23).strip() == "meson test -C build", "cgif build.sh:23 runs meson test")
        expect(f'cp "build/fuzz/{harness}_seed_corpus.zip" $OUT/.' in b, f"cgif build.sh copies {harness}'s zip")
        f = up.script("fuzz/meson.build")
        want = (f"test('create {'file fuzzer' if harness == 'cgif_file_fuzzer' else 'rgb fuzzer'} seed corpus zip"
                f" archive', zip, args : ['{harness}_seed_corpus.zip', "
                f"{'seeds_index' if which == 'tests_index' else 'seeds_rgb'}]")
        expect(want in f, f"cgif fuzz/meson.build zips {which}'s seeds as {harness}_seed_corpus.zip")
        names, sums = cgif_expected(up, which)
        src = (f"OSS-Fuzz {OSSFUZZ_COMMIT[:8]} projects/cgif/build.sh:23-27: `meson test` generates the seeds and"
               f" zips them (upstream fuzz/meson.build: one generator per {which} entry of tests/meson.build, run"
               f" to write <name>.seed; zip at lines 70-72); {len(names)} seeds, {sum(n in sums for n in names)} with"
               f" an upstream sha256 (fuzz/seeds.sha256)")
        if seeds is None:
            return {"status": "pending generation (native run of the seed generators)", "inputs": None,
                    "source": src, "expected": [(n, sums.get(n, "-")) for n in names]}
        got = sorted(p.name for p in seeds.iterdir() if p.is_file())
        expect(sorted(names) == got, f"generated seeds in {seeds} are exactly the {len(names)} expected names")
        inputs = {n: (seeds / n).read_bytes() for n in names}
        for n, data in inputs.items():
            if n in sums:
                expect(hashlib.sha256(data).hexdigest() == sums[n], f"seed {n} matches fuzz/seeds.sha256")
        return {"status": "corpus", "inputs": inputs, "source": src + f"; generated seeds from {seeds}",
                "expected": [(n, sums.get(n, "-")) for n in names]}
    return rule


RULES = {
    ("cjson", "cjson_read_fuzzer"): corpus_cjson,
    ("yajl-ruby", "json_fuzzer"): corpus_yajl,
    ("bzip2", "bzip2_compress_target"): corpus_bzip2_compress,
    ("cgif", "cgif_file_fuzzer"): corpus_cgif("tests_index", "cgif_file_fuzzer"),
    ("cgif", "cgif_rgb_fuzzer"): corpus_cgif("tests_rgb", "cgif_rgb_fuzzer"),
}


def draw(entry_point: str, names: list[str]) -> tuple[list[str], bool]:
    if len(names) <= MAX_INPUTS:
        return sorted(names), False
    key = {n: hashlib.sha256(f"{DRAW_SALT}|{entry_point}|{n}".encode()).hexdigest() for n in names}
    return sorted(sorted(names, key=lambda n: key[n])[:MAX_INPUTS]), True


def manifest_text(inputs: dict[str, bytes]) -> str:
    rows = ["name\tbytes\tsha256"]
    for n in sorted(inputs, key=lambda s: s.encode()):
        rows.append(f"{n}\t{len(inputs[n])}\t{hashlib.sha256(inputs[n]).hexdigest()}")
    return "\n".join(rows) + "\n"


def write_corpus(d: Path, inputs: dict[str, bytes]) -> str:
    """Write inputs/ and MANIFEST.tsv; an existing corpus must be identical. Returns the manifest's sha256."""
    man = manifest_text(inputs)
    mp = d / "MANIFEST.tsv"
    if mp.exists():
        if mp.read_text() != man:
            raise SystemExit(f"{d} holds a different corpus; not overwritten")
    (d / "inputs").mkdir(parents=True, exist_ok=True)
    for n, data in inputs.items():
        expect("/" not in n and n not in ("", ".", ".."), f"input name {n!r} is a plain file name")
        p = d / "inputs" / n
        if p.exists():
            if p.read_bytes() != data:
                raise SystemExit(f"{p} differs; not overwritten")
            continue
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(data)
    extra = sorted(set(p.name for p in (d / "inputs").iterdir()) - set(inputs))
    if extra:
        raise SystemExit(f"{d}/inputs holds files outside the corpus: {extra[:5]}")
    mp.write_text(man)
    return hashlib.sha256(man.encode()).hexdigest()


def main(argv: list[str]) -> int:
    seeds: dict[tuple[str, str], Path] = {}
    args = []
    it = iter(argv[1:])
    for a in it:
        if a == "--seeds":
            k, _, v = next(it).partition("=")
            p, _, h = k.partition("/")
            seeds[(p, h)] = Path(v).resolve()
        else:
            args.append(a)
    if len(args) != 4:
        print(__doc__, file=sys.stderr)
        return 2
    sel_tsv, ossfuzz, updir, out = (Path(a).resolve() for a in args)
    of = Src("oss-fuzz", ossfuzz, OSSFUZZ_COMMIT)
    with sel_tsv.open(newline="") as fh:
        rows = [r for r in csv.DictReader(fh, delimiter="\t") if r["selected"] == "y"]
    rows.sort(key=lambda r: int(r["rank"]))
    summary = ["\t".join(["rank", "entry_point", "project_harness", "status", "packed", "used", "drawn",
                          "manifest_sha256", "corpus_dir", "source"])]
    for r in rows:
        key = (r["library"], r["entry_point"])  # README library = proofs/<project> for every selected row
        if key not in RULES:
            raise SystemExit(f"no packing rule transcribed for {r['library']}/{r['entry_point']}")
        up = Src("upstream", upstream_dir(updir, r["upstream_repository"], r["upstream_commit"]), r["upstream_commit"])
        res = RULES[key](of, up, seeds.get(key))
        d = out / f"{key[0]}__{key[1]}"
        if res.get("expected"):
            d.mkdir(parents=True, exist_ok=True)
            (d / "EXPECTED.tsv").write_text("name\tupstream_sha256\n" + "".join(
                f"{n}\t{h}\n" for n, h in res["expected"]))
        if res["inputs"] is None:
            summary.append("\t".join([r["rank"], r["entry_point"], "/".join(key), res["status"],
                                      str(len(res.get("expected", []))) if res.get("expected") else "0", "-", "-",
                                      "-", "-", res["source"]]))
            continue
        used, drawn = draw(r["entry_point"], list(res["inputs"]))
        msha = write_corpus(d, {n: res["inputs"][n] for n in used})
        summary.append("\t".join([r["rank"], r["entry_point"], "/".join(key), res["status"], str(len(res["inputs"])),
                                  str(len(used)), "y" if drawn else "n", msha, str(d), res["source"]]))
    out.mkdir(parents=True, exist_ok=True)
    (out / "CORPORA.tsv").write_text("\n".join(summary) + "\n")
    print("\n".join(summary))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
