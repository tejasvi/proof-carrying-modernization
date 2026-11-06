"""odo_mutate.py SRC DST OLD NEW : write DST = SRC with the one occurrence of OLD replaced by NEW
(planted faults of odotest_mutants.md, written into a copy; refuses unless OLD occurs exactly once,
and when DST is SRC)."""
import os
import sys

src, dst, old, new = sys.argv[1:5]
text = open(src).read()
n = text.count(old)
if n != 1:
    sys.exit(f"{old!r} occurs {n} times in {src}")
if os.path.exists(dst) and os.path.samefile(src, dst):
    sys.exit("DST is SRC")
open(dst, "w").write(text.replace(old, new))
print(f"{dst}: 1 line changed")
