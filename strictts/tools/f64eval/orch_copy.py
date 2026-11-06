"""Faithful copy of verif-orchestrator's run es-toolkit-tests (pin 91ea2f8): its generated module and its exact
test check files (read-only sources under ~/veriforch), into scratch/f64eval/orch2, with two variants: decide := false
(`_nd`) and the script replaced by `ts_eval` (`_eval`); `_orig` is unchanged.
Then: compile the module (tools/run.sh 0.2 590 lake env lean -R scratch/f64eval/orch2 -o
scratch/f64eval/orch2/Gen/v0_tests/Unit.olean scratch/f64eval/orch2/Gen/v0_tests/Unit.lean) and run
ORCH=orch2 tools/run.sh 0.3 590 tools/f64eval/orch_batch.sh eval OUT.txt [tests…] (one line per test)."""
import re, shutil
from pathlib import Path
SRC = Path.home() / "veriforch/runs/es-toolkit-tests/lean_v91ea2f8"
OUT = Path(__file__).resolve().parents[2] / "scratch/f64eval/orch2"
(OUT / "Gen/v0_tests").mkdir(parents=True, exist_ok=True)
shutil.copyfile(SRC / "Gen/v0_tests/Unit.lean", OUT / "Gen/v0_tests/Unit.lean")
n = 0
for f in sorted((SRC / "VO/v0/tests").glob("vo_test_*.lean")):
    t = f.stem
    s = f.read_text()
    (OUT / f"T_{t}_orig.lean").write_text(s)
    (OUT / f"T_{t}_nd.lean").write_text(s.replace("decide := true", "decide := false"))
    m = re.search(r"(theorem \S+ \(I : Impl\) :\n.*?:= by\n)(.*?)(\n\n#print axioms)", s, re.S)
    ev = s[:m.start(2)] + "  ts_eval" + s[m.end(2):]
    ev = ev.replace("import Gen.v0_tests.Unit", "import StrictTS.Proof.Eval\nimport Gen.v0_tests.Unit")
    (OUT / f"T_{t}_eval.lean").write_text(ev)
    n += 1
print(n, "tests")
