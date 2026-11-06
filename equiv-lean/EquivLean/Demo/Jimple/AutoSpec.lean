import EquivLean.Demo.Gen.Jimple.SpecMapLines
import EquivLean.Bridge.Jimple.SpecAuto

/-!
# A Java method proved against its functional specification, no invariant written

`examples/java/spec_maplines/MapLines.java`: `run(Rec[] recs)` returns a `Result` whose
`ArrayList<String> displays` holds `"REC " + r.id + " " + r.name` for each record, in order, and
`rc = 0` (javac 17 + Soot 4.7.1, `Demo/Gen/Jimple/SpecMapLines.lean`).

The specification is a pure function of the records, `rs.map aLine`; the contract `aSpec a rs`
relates the array argument to the records (`Pairs (ARecAt σ) xs rs`) and the returned list to the
specification (`StrsAt σ' ys (rs.map aLine)`).  `a_sat` is one call `jspec_auto`: the loop
invariant at the head (statement 4) is generated, here

    ∃ i l ys m, fr.get 5 = some (.int i) ∧ 0 ≤ i.toInt ∧ i.toInt ≤ rs.length ∧
      fr.get 1 = some (.ref a) ∧ fr.get 2 = some (.ref l) ∧
      σ.heap l = some (.list .arrayList ys m) ∧ σ0.next ≤ l ∧
      Hide (StrsAt σ ys ((rs.take i.toInt.toNat).map aLine)) ∧ σ0.next ≤ σ.next ∧
      Hide (Grows σ0 σ) ∧ σ.initOf "MapLines$Result" = .done

(the index is Soot's local 5, the array local 1, the list local 2: found by running the method on
sampled inputs; the list's contents are the specification on the prefix).
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec

namespace EquivLean.Demo.AutoSpec

/-- A record as the specification sees it. -/
structure ARec where
  id : I64
  name : JStr

/-- The display line of a record. -/
def aLine (r : ARec) : JStr :=
  JStr.ofString "REC " ++ JStr.ofInt r.id.toInt ++ JStr.ofString " " ++ r.name

/-- `v` is a `MapLines$Rec` object holding `r`. -/
def ARecAt (σ : State) (v : Value) (r : ARec) : Prop :=
  ∃ x fs n, v = .ref x ∧ σ.heap x = some (.plain "MapLines$Rec" fs) ∧
    Fields.get fs ("MapLines$Rec", "id") = some (.long r.id) ∧
    Fields.get fs ("MapLines$Rec", "name") = some n ∧ StrAt σ n r.name

def aPre (a : Addr) (rs : List ARec) (args : List Value) (σ : State) : Prop :=
  args = [.ref a] ∧ (∃ et xs, σ.heap a = some (.array et xs) ∧ Pairs (ARecAt σ) xs rs) ∧
  rs.length < 2147483647 ∧ σ.initOf "MapLines$Result" = .done

def aPost (rs : List ARec) (r : Option Value) (σ' : State) : Prop :=
  ∃ res fs l k ys mods, r = some (.ref res) ∧ σ'.heap res = some (.plain "MapLines$Result" fs) ∧
    Fields.get fs ("MapLines$Result", "displays") = some (.ref l) ∧
    Fields.get fs ("MapLines$Result", "rc") = some (.int 0) ∧
    σ'.heap l = some (.list k ys mods) ∧ Spec.StrsAt σ' ys (rs.map aLine)

/-- The contract of `MapLines.run` for the records `rs` in the array at `a`. -/
def aSpec (a : Addr) (rs : List ARec) : Spec :=
  Spec.of (aPre a rs) (fun _ _ r σ' => aPost rs r σ')

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
/-- **Every terminating run of `MapLines.run` returns the specification's lines**; no loop
invariant written. -/
theorem a_sat (a : Addr) (rs : List ARec) :
    Sat Gen.SpecMapLines.prog Gen.SpecMapLines.MapLines.«run(MapLines$Rec[])».ref (aSpec a rs) := by
  jspec_auto

end EquivLean.Demo.AutoSpec

#print axioms EquivLean.Demo.AutoSpec.a_sat
