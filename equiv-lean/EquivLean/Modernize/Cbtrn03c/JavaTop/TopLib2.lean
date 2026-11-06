import EquivLean.Modernize.Cbtrn03c.JavaTop.Pd
import EquivLean.Modernize.Cbtrn03c.JavaTop.Frames

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java, top layer: more simp helpers for the segments
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

open Lean Meta in
/-- `JStr.ofString "…"` on a literal as its explicit list of UTF-16 units (the string constants of
the displays against the model's lines). -/
dsimproc jstrLit (JStr.ofString _) := fun e => do
  let_expr JStr.ofString s := e | return .continue
  let .lit (.strVal str) := s.consumeMData | return .continue
  let elems := (JStr.ofString str).map fun (c : BitVec 16) =>
    mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 16) (mkNatLit c.toNat)
  return .done (← mkListLit (mkApp (mkConst ``BitVec) (mkNatLit 16)) elems)

/-- The text of EBCDIC bytes as the model's code points. -/
theorem jline_cps (bs : List UInt8) : jline (Model.cps bs) = cp037Str bs := by
  simp [cp037Str, cp037Unit, jline, Model.cps, cp037Code, List.map_map, Function.comp_def]

/-- `KeepsNonWs`, under another name: the frame premise `jFrameStep` unfolds when no hypothesis
states it (the entry segments). -/
def KeepsNonWsU (σ σ' : State) : Prop :=
  σ.next ≤ σ'.next ∧ StrMono σ σ' ∧
  (∀ x c fs, σ.heap x = some (.plain c fs) → c ≠ wsC → σ'.heap x = some (.plain c fs)) ∧
  (∀ x et xs, σ.heap x = some (.array et xs) → σ'.heap x = some (.array et xs))

theorem KeepsNonWs.of_u {σ σ' : State} (h : KeepsNonWsU σ σ') : KeepsNonWs σ σ' := h

attribute [jframe] KeepsNonWs.of_u

end EquivLean.Modernize.Cbtrn03c.Java.Top

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

set_option maxRecDepth 100000 in
theorem ebc_cp037_fin : ∀ n : Fin 256, Model.ebc (cp037Code (UInt8.ofNat n)) = UInt8.ofNat n := by
  decide +kernel

theorem ebc_cp037 (b : UInt8) : Model.ebc (cp037Code b) = b := by
  have h := ebc_cp037_fin ⟨b.toNat, b.toNat_lt⟩
  simpa using h

set_option maxRecDepth 100000 in
theorem cp037Code_lt_fin : ∀ n : Fin 256, cp037Code (UInt8.ofNat n) < 256 := by decide +kernel

theorem cp037Code_lt (b : UInt8) : cp037Code b < 256 := by
  have h := cp037Code_lt_fin ⟨b.toNat, b.toNat_lt⟩
  simpa using h

theorem cp037Unit_inj {a b : UInt8} (h : cp037Unit a = cp037Unit b) : a = b := by
  have ha := cp037Code_lt a
  have hb := cp037Code_lt b
  have e : cp037Code a = cp037Code b := by
    have := congrArg BitVec.toNat h
    simp only [cp037Unit, BitVec.toNat_ofNat] at this
    simp only [cp037Code] at ha hb ⊢
    omega
  rw [← ebc_cp037 a, ← ebc_cp037 b, e]

/-- Strings of EBCDIC bytes are equal exactly when the bytes are (CP037 is a bijection). -/
theorem cp037Str_inj (a b : List UInt8) : cp037Str a = cp037Str b ↔ a = b := by
  constructor
  · intro h
    unfold cp037Str at h
    induction a generalizing b with
    | nil => cases b with
      | nil => rfl
      | cons _ _ => simp at h
    | cons x xs ih => cases b with
      | nil => simp at h
      | cons y ys =>
        simp only [List.map_cons, List.cons.injEq] at h
        rw [cp037Unit_inj h.1, ih ys h.2]
  · rintro rfl; rfl

end EquivLean.Modernize.Cbtrn03c.Java.Top
