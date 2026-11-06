"""Make targets/thealgorithms_cpp(.toml) from the cirlean corpus copy: one variant per source file with
in-scope user functions (cirlean's coverage table), each file its own translation unit.
usage: python mk_thealgorithms.py [N_FILES] [NAME] [DIR_PREFIX,...]"""
import re
import shutil
import sys
from pathlib import Path

CORPUS = Path("/home/user/cirlean_work/corpus_real")
SRC = CORPUS / "dl_thealgorithms_fdcc29b" / "src"
DST = Path("/home/user/veriforch/targets/thealgorithms_cpp")   # shared source copy
LIBCXX = "/home/user/cirlean_work/dl_cir2c_eb2a332/cir2c-eb2a332/libcxx/include/c++/v1"
n = int(sys.argv[1]) if len(sys.argv) > 1 else 40
name = sys.argv[2] if len(sys.argv) > 2 else "thealgorithms_cpp"
prefixes = tuple(sys.argv[3].split(",")) if len(sys.argv) > 3 else ("",)

per_file = {}
for line in (CORPUS / "out_fdcc29b" / "inscope.tsv").read_text().splitlines():
    cols = line.split("\t")
    cir, fn = Path(cols[0]).stem, cols[1]
    if fn.startswith("std::") or "::{lambda" in fn:
        continue
    per_file.setdefault(cir, []).append(fn)
# map cir stem back to the source path (stem = path with non-alnum replaced by _)
srcs = {re.sub(r"[^A-Za-z0-9_]", "_", str(p.relative_to(SRC))[:-4]): p for p in SRC.rglob("*.cpp")}
chosen = [(stem, srcs[stem]) for stem in sorted(per_file)
          if stem in srcs and str(srcs[stem].relative_to(SRC)).startswith(prefixes)][:n]
for p in SRC.rglob("*"):
    if p.is_file() and p.suffix in (".cpp", ".hpp", ".h"):
        q = DST / p.relative_to(SRC)
        if not q.exists():
            q.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, q)
lines = ["# TheAlgorithms/C-Plus-Plus @ fdcc29b (copied from the cirlean coverage corpus); one TU per file.",
         f'name = "{name}"', 'lang = "cir"', f'root = "{DST}"', 'sources = []', 'entry = ["main"]', "",
         "[extra]", f'cxxflags = ["-nostdinc++", "-isystem", "{LIBCXX}", "-w"]', ""]
for stem, p in chosen:
    lines += ["[[variants]]", f'name = "{stem}"', f'sources = ["{p.relative_to(SRC)}"]', ""]
(DST.parent / f"{name}.toml").write_text("\n".join(lines))
print(len(chosen), "variants;", sum(len(per_file[s]) for s, _ in chosen), "in-scope user functions")
