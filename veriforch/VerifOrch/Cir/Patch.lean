import CIR
import EquivLean.Bridge.Cir.Obs
import VerifOrch.Patch
import VerifOrch.Int

/-!
# Patch certificates for cirlean

`SafeRet ctx f args m`: the call runs without undefined behaviour and returns normally.
A patch of `fOld` (module `ctxOld`) into `fNew` (module `ctxNew`) is certified by

* `new_safe`: `SafeRet ctxNew fNew args m` (in fact its full contract) on every call of the
  contract, and
* `conservative`: equiv-lean's `EquivOn Bad ctxNew fNew ctxOld fOld` with
  `Bad := ill-typed call ∨ ¬ SafeRet ctxOld fOld`, i.e. on every well-typed call where the original
  is safe, the two versions have the same observable outcome (`Equiv (ObsEq m)`).

`changed_iff_unsafe_at` then says that on every call of the contract the outcome changed exactly
when the original was unsafe (`VerifOrch.changed_iff_unsafe_of_agree`).
-/

namespace VerifOrch.Cir

open CIR EquivLean EquivLean.Cir

/-- The call runs safely (no undefined behaviour, terminates) and returns normally. -/
def SafeRet (ctx : Ctx) (f : String) (args : List Val) (m : Mem) : Prop :=
  Returns ctx f args m (fun _ _ => True)

/-- Two runs agree: equiv-lean's equivalence with caller-visible outcomes (`ObsEq m`). -/
def Agree (ctxNew : Ctx) (fNew : String) (ctxOld : Ctx) (fOld : String) (args : List Val) (m : Mem) : Prop :=
  Equiv (ObsEq m) (evalCall ctxNew fNew args m) (evalCall ctxOld fOld args m)

theorem safeRet_of_returns {ctx : Ctx} {f : String} {args : List Val} {m : Mem}
    {post : Option Val → Mem → Prop} (h : Returns ctx f args m post) : SafeRet ctx f args m := by
  unfold SafeRet Returns Calls at *
  rw [Res.holds_ok_iff] at h ⊢
  obtain ⟨a, ha, hq⟩ := h
  refine ⟨a, ha, ?_⟩
  revert hq
  cases a.1 <;> simp

theorem safe_of_safeRet {ctx : Ctx} {f : String} {args : List Val} {m : Mem}
    (h : SafeRet ctx f args m) : Safe (evalCall ctx f args m) := by
  unfold SafeRet Returns Calls at h
  rw [Res.holds_ok_iff] at h
  obtain ⟨a, ha, -⟩ := h
  exact (safe_res _).2 ⟨a, ha⟩

/-- Agreement carries safety from the new run back to the original run. -/
theorem transfer {ctxNew ctxOld : Ctx} {fNew fOld : String} {args : List Val} {m : Mem}
    (hA : Agree ctxNew fNew ctxOld fOld args m) (hN : SafeRet ctxNew fNew args m) :
    SafeRet ctxOld fOld args m := by
  have hNs := safe_of_safeRet hN
  unfold SafeRet Returns Calls at hN ⊢
  rw [Res.holds_ok_iff] at hN ⊢
  obtain ⟨a, ha, hret⟩ := hN
  obtain ⟨hOs, hrun⟩ := hA.2 hNs
  obtain ⟨b, hb⟩ := (safe_res _).1 hOs
  obtain ⟨o, ho, hR⟩ := hrun b ((runs_res _ _).2 hb)
  have hoa : o = a := by rw [runs_res] at ho; rw [ha] at ho; cases ho; rfl
  subst hoa
  refine ⟨b, hb, ?_⟩
  have he : o.1 = b.1 := hR.1
  rw [← he]
  exact hret

/-- The bad set of a certificate: ill-typed calls (outside `WT`) and calls on which the original
is not safe. -/
def Bad (WT : List Val → Mem → Prop) (ctxOld : Ctx) (fOld : String) (args : List Val) (m : Mem) : Prop :=
  ¬ WT args m ∨ ¬ SafeRet ctxOld fOld args m

/-- The certificate at one call: if the new version is safe there and the call is well typed, the
outcome changed exactly when the original was unsafe. -/
theorem changed_iff_unsafe_at {WT : List Val → Mem → Prop} {ctxNew ctxOld : Ctx} {fNew fOld : String}
    {args : List Val} {m : Mem} (hwt : WT args m) (hnew : SafeRet ctxNew fNew args m)
    (conservative : EquivOn (Bad WT ctxOld fOld) ctxNew fNew ctxOld fOld) :
    (¬ Agree ctxNew fNew ctxOld fOld args m ↔ ¬ SafeRet ctxOld fOld args m) := by
  have := VerifOrch.changed_iff_unsafe_of_agree (X := Unit) (fun _ => True)
    (fun _ => SafeRet ctxOld fOld args m) (fun _ => SafeRet ctxNew fNew args m)
    (fun _ => Agree ctxNew fNew ctxOld fOld args m) (fun _ _ => hnew)
    (fun _ hs => conservative args m (by
      intro hb
      rcases hb with h | h
      · exact h hwt
      · exact h hs))
    (fun _ ha hn => transfer ha hn) () trivial
  exact this

/-- The certificate over a whole precondition `Pre` (which must imply well-typedness). -/
theorem changed_iff_unsafe {Pre WT : List Val → Mem → Prop} {ctxNew ctxOld : Ctx} {fNew fOld : String}
    (hwt : ∀ args m, Pre args m → WT args m)
    (new_safe : ∀ args m, Pre args m → SafeRet ctxNew fNew args m)
    (conservative : EquivOn (Bad WT ctxOld fOld) ctxNew fNew ctxOld fOld) :
    ∀ args m, Pre args m →
      (¬ Agree ctxNew fNew ctxOld fOld args m ↔ ¬ SafeRet ctxOld fOld args m) :=
  fun args m hp => changed_iff_unsafe_at (hwt args m hp) (new_safe args m hp) conservative

end VerifOrch.Cir
