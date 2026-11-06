"""Self-tests of the orchestrator core (no Lean, no network). Run: scripts/vo-test"""
from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from veriforch.graph import bottom_up, reachable, sccs
from veriforch.lean import parse_messages
from veriforch.llm import LLMError, parse_json_answer
from veriforch.model import Contract, Unit
from veriforch.scheduler import hyp_binder, proof_key, vacuous


def test_sccs_order():
    # a -> b -> c, c -> b (cycle), d isolated: callees come first
    comps = sccs(["a", "b", "c", "d"], {"a": ["b"], "b": ["c"], "c": ["b"]})
    pos = {n: i for i, comp in enumerate(comps) for n in comp}
    assert sorted(comps, key=len)[-1] == ["b", "c"]
    assert pos["b"] < pos["a"] and pos["c"] < pos["a"]
    assert any(c == ["d"] for c in comps)


def test_bottom_up_ignores_unknown_callees():
    us = [Unit("f", "f", "fn_f", callees=["g", "printf"]), Unit("g", "g", "fn_g")]
    comps = bottom_up(us)
    assert comps.index(["g"]) < comps.index(["f"])
    assert reachable(us, ["f"]) == {"f", "g"}


def test_parse_messages_verdicts():
    proved = json.dumps({"severity": "information", "pos": {"line": 9, "column": 0},
                         "data": "'X.f_spec' depends on axioms: [propext, Classical.choice, Quot.sound]"})
    r = parse_messages(proved)
    assert r.status == "proved" and r.axioms == ["Classical.choice", "Quot.sound", "propext"]
    stuck = json.dumps({"severity": "error", "pos": {"line": 3, "column": 2}, "data": "unsolved goals\n⊢ False"})
    assert parse_messages(stuck).status == "stuck"
    err = json.dumps({"severity": "error", "pos": {"line": 1, "column": 0}, "data": "unknown identifier 'foo'"})
    assert parse_messages(err).status == "error"
    sorry = json.dumps({"severity": "warning", "pos": {"line": 1, "column": 0}, "data": "declaration uses 'sorry'"})
    assert parse_messages(sorry).status == "stuck"
    cheat = json.dumps({"severity": "information", "pos": {"line": 1, "column": 0},
                        "data": "'X.f' depends on axioms: [sorryAx]"})
    assert parse_messages(cheat).status == "stuck"


def test_json_answers():
    schema = {"type": "object", "properties": {"a": {"type": "string"}, "b": {"type": "array"}},
              "required": ["a", "b"]}
    assert parse_json_answer('```json\n{"a": "x", "b": []}\n```', schema) == {"a": "x", "b": []}
    assert parse_json_answer('Here: {"a": "x", "b": [1]} done', schema)["b"] == [1]
    for bad in ['{"a": "x"}', '{"a": 1, "b": []}', "no json"]:
        try:
            parse_json_answer(bad, schema)
        except LLMError:
            continue
        raise AssertionError(f"accepted {bad!r}")


def test_keys_and_hypotheses():
    k1 = proof_key("body", ["c2", "c1"], "pin", "api")
    assert k1 == proof_key("body", ["c1", "c2"], "pin", "api")       # order of callees irrelevant
    assert k1 != proof_key("body2", ["c1", "c2"], "pin", "api")
    c = Contract("g", "(x : Int) (hx : 0 ≤ x)", "Returns ctx fn_g.sym [.int x] m (fun _ _ => True)")
    assert hyp_binder("g", c) == "(h_g : ∀ (x : Int) (hx : 0 ≤ x), Returns ctx fn_g.sym [.int x] m (fun _ _ => True))"


def test_vacuity_guard():
    assert vacuous("(x : Int) (h : False)")
    assert vacuous("(n : Nat) (h : n < n)")
    assert not vacuous("(n : Nat) (h : n < 5) (m : Mem)")
    assert not vacuous("(b : Nat) (hb : b < m.next)")
    assert vacuous("(A B : Int) (n : Int) (s : Int → Int) (hs0 : s 0 = A)")       # trace-valued ghost
    assert not vacuous("(xs : List Int) (hstep : ∀ k : Int, 0 ≤ k → k < 5 → True)")


def test_compdb_flags():
    from veriforch.adapters.cir.compdb import entry_flags
    e = {"directory": "/w", "file": "src/a.c",
         "arguments": ["cc", "-DX=1", "-Iinc", "-c", "-O2", "-Wall", "src/a.c", "-o", "a.o", "-MD", "-MF", "a.d",
                       "-std=c11", "-isystem", "sys"]}
    f = entry_flags(e)
    assert "-DX=1" in f and "-std=c11" in f and "-I/w/inc" in f
    assert f[f.index("-isystem") + 1] == "/w/sys"
    assert not {"-c", "-O2", "-Wall", "-o", "a.o", "-MD", "-MF", "a.d", "src/a.c"} & set(f)


def test_modular_hypotheses_and_domains():
    from veriforch.adapters.cir.adapter import CirAdapter
    from veriforch.adapters.cir import equiv
    from veriforch.model import Contract
    from veriforch.scheduler import hyp_binder
    ad = CirAdapter()
    h = hyp_binder("g", Contract(unit="g", binders="(x : Int) (m : Mem)", statement="Returns ctx fn_g.sym [.int x] m P"))
    assert ad.modular_hyp_text(h, {"fn_g": "_Z1gi"}) == '(h_g : ∀ (x : Int) (m : Mem), Returns ctx "_Z1gi" [.int x] m P)'
    assert ad.modular_hyp_text("fn_other.sym fn_g.symx", {"fn_g": "g"}) == "fn_other.sym fn_g.symx"
    assert hyp_binder("k", Contract(unit="k", binders="", statement="Q")) == "(h_k : Q)"
    # the well-typed-call predicate of a pointer domain requires the pointer to exist at the call
    src = equiv.render("t", "(x0 : Ptr) (m : Mem) (hx0 : (∀ b p, x0 = Ptr.loc b p → b < m.next))", "[.ptr x0]", 1,
                       "G.a", "G.b", "fn_f", ["(∀ b p, x0 = Ptr.loc b p → b < m.next)"])
    assert "args = [.ptr x0] ∧ (∀ b p, x0 = Ptr.loc b p → b < m.next)" in src
    assert "obtain ⟨⟨x0, rfl, hwt0⟩, hsafe⟩" in src


if __name__ == "__main__":
    n = 0
    for name, fn in list(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
            n += 1
            print(f"ok {name}")
    print(f"{n} tests passed")
