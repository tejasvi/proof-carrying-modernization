import EquivLean.Modernize.Cbtrn03c.JavaW.Pad

/-!
# CBTRN03C → Java: contracts whose postconditions are functions of the entry state

A caller's symbolic execution uses a callee's postcondition without matching premises about the
entry state (after an allocation the entry state is not the caller's): the ghost values are
functions of the arguments and the entry state (`argText`), and the strings of the entry state
are still there (`StrMono`).  These contracts follow from the proved ones (`Sat.conseq`).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

/-- The rule of consequence for contracts. -/
theorem Sat.conseq {P : Program} {m : MethodRef} {S S' : Spec} (h : Sat P m S)
    (hpre : ∀ args σ, S'.pre args σ → S.pre args σ)
    (hpost : ∀ args σ o, S'.pre args σ → S.post args σ o → S'.post args σ o) : Sat P m S' :=
  fun args σ o hp hx => hpost args σ o hp (h args σ o (hpre args σ hp) hx)

theorem strMono_of_grows {σ σ' : State} (hg : Grows σ σ') :
    ∀ x s, σ.heap x = some (.str s) → σ'.heap x = some (.str s) :=
  fun x s hx => by rw [hg.2 x (State.lt_next_of_heap hx), hx]

/-! ### `pad` -/

def padSpecF : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (s : JStr) (n : I32), args = [.ref x, .int n] ∧
     σ.heap x = some (.str s) ∧ s.length < 2147483648 ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ (sv : Value) (n : I32), args = [sv, .int n] →
     ∃ y, r = some (.ref y) ∧ σ'.heap y = some (.str (fixJ (argText σ sv) n.toInt.toNat)) ∧
       σ.next ≤ y ∧ Grows σ σ' ∧ (∀ x s, σ.heap x = some (.str s) → σ'.heap x = some (.str s)) ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn03c" = σ.initOf "Cbtrn03c")

theorem pad_sat : Sat Gen.prog padRef padSpec := pad_vc.sat

theorem padF_sat : Sat Gen.prog padRef padSpecF := by
  refine Sat.conseq pad_sat (fun _ _ h => h) ?_
  intro args σ o hp ho
  obtain ⟨x, s, n, rfl, hx, -, -⟩ := hp
  cases o with
  | normal r σ' =>
    intro sv n' heq
    simp only [List.cons.injEq, Value.int.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨y, hr, hy, hfy, hg, hi, hs, ho⟩ := ho x s n rfl hx
    refine ⟨y, hr, ?_, hfy, hg, strMono_of_grows hg, hi, hs, ho⟩
    simp [argText, strOf, hx, hy]
  | exc e σ' => exact ho
  | wrong m => exact ho

def padSig : MethodSig :=
  ⟨"Cbtrn03c", .cls "java.lang.String", "pad", [.cls "java.lang.String", .prim .int]⟩

set_option maxHeartbeats 0 in
theorem padF_ok : ContractOK Gen.prog padSig padSpecF := by
  jcontract_ok [padF_sat]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.padF_ok
