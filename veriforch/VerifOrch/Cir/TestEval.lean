import CIR

/-!
# Test theorems "returns normally" by evaluation

cirlean's `cir_kernel` / `cir_native` prove `Returns ctx f args m (fun v _ => v = some (.int k))` by evaluating
the call. A `void` test, or a test whose outcome is not a return code, is stated as "returns normally":
`Returns ctx f [] m (fun _ _ => True)`. A failing check is undefined behaviour or an abort, so it never
returns normally. These lemmas bring that statement to the same Boolean evaluation:
* kernel-checked: `callReturnsK` with `decide +kernel`;
* by native evaluation: `callReturnsB` with `native_decide`, which also trusts Lean's compiler.
-/

namespace VerifOrch.Cir

open CIR

theorem returns_true_of_callReturnsB {ctx : Ctx} {sym : String} {args : List Val} {m : Mem}
    (h : CIR.callReturnsB ctx sym args m (fun _ => true) = true) :
    Returns ctx sym args m (fun _ _ => True) := by
  have h2 := CIR.returns_of_callReturnsB h
  unfold Returns Calls at h2 ⊢
  exact Res.holds_mono h2 (fun r _ => by
    rcases r with ⟨e, m'⟩
    cases e <;> simp_all)

theorem returns_true_of_callReturnsK {n : Nat} {ctx : Ctx} {sym : String} {args : List Val} {m : Mem}
    (h : CIR.callReturnsK n ctx sym args m (fun _ => true) = true) :
    Returns ctx sym args m (fun _ _ => True) :=
  returns_true_of_callReturnsB (CIR.callReturnsB_of_callReturnsK h)

end VerifOrch.Cir
