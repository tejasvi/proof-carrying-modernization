import EquivLean.Modernize.Cbact01c.JavaRunPadF

/-!
# CBACT01C → Java: the helper `cobdatft` (input and output type 2)

`cobdatft("2", inp, "2", out)`: characters 1-4, 6-7 and 9-10 of `inp`, then `out` from its
ninth character (`cobOut`). The call of `run` only. No loop.
-/

-- JimpleLean 2006Z took `ite_nat_ne` out of `jsimp`: these proofs decide address
-- (dis)equalities with it.
attribute [local jsimp high] Jimple.ite_nat_ne

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec

namespace EquivLean.Modernize.Cbact01c.Java

/-- What `cobdatft("2", i, "2", o)` returns. -/
def cobOut (i o : JStr) : JStr := i.take 4 ++ (i.take 7).drop 5 ++ (i.take 10).drop 8 ++ o.drop 8

theorem cobOut_length {i o : JStr} (hi : 10 ≤ i.length) (ho : 8 ≤ o.length) :
    (cobOut i o).length = o.length := by
  simp only [cobOut, List.length_append, List.length_take, List.length_drop]
  omega

theorem cobOut_fixStr_length (t o : JStr) (ho : 8 ≤ o.length) :
    (cobOut (fixStr t 20) o).length = o.length := by
  have h20 : (fixStr t 20).length = 20 := by
    have : ∀ n, (fixStr t n).length = n := by
      intro n; induction n with
      | zero => rfl
      | succ k ih => simp [fixStr, ih]
    exact this 20
  exact cobOut_length (by rw [h20]; decide) ho

abbrev cobdatftRef : MethodRef :=
  Gen.Cbact01c.«cobdatft(java.lang.String,java.lang.String,java.lang.String,java.lang.String)».ref

def cobdatftSpec : Spec := Spec.of
  (fun args σ => ∃ x1 x2 x3 x4 s2 s4, args = [.ref x1, .ref x2, .ref x3, .ref x4] ∧
     σ.heap x1 = some (.str (JStr.ofString "2")) ∧ σ.heap x2 = some (.str s2) ∧ 10 ≤ s2.length ∧
     σ.heap x3 = some (.str (JStr.ofString "2")) ∧ σ.heap x4 = some (.str s4) ∧ 8 ≤ s4.length)
  (fun args σ r σ' => ∀ x1 x2 x3 x4, args = [.ref x1, .ref x2, .ref x3, .ref x4] →
     ∃ x, r = some (.ref x) ∧
       σ'.heap x = some (.str (cobOut (argText σ (.ref x2)) (argText σ (.ref x4)))) ∧
       σ.next ≤ x ∧ Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cobdatft_vc : MethodVC Gen.prog (fun _ => none) 0 cobdatftRef cobdatftSpec [] 60 := by
  jverify [cobdatftSpec, cobOut, argText, Grows]

end EquivLean.Modernize.Cbact01c.Java

