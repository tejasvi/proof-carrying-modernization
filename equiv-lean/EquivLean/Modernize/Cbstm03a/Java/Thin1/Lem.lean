import EquivLean.Modernize.Cbstm03a.Java.RunTerm

/-!
# CBSTM03A → Java, `run`'s thin VC: helper lemmas (namespace `…Java.Thin1`)

Record relations carried to a state that only grows; the `k`-th element of a `Forall2`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space heap_grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Thin1

theorem forall2_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} (h : Forall2 R xs ys) (i : Nat) (hi : i < xs.length),
      R xs[i] (ys[i]'(by rw [← Forall2.length_eq h]; exact hi))
  | [], [], .nil, _, hi => absurd hi (by simp)
  | _ :: _, _ :: _, .cons h _, 0, _ => h
  | _ :: _, _ :: _, .cons _ hs, i + 1, hi => forall2_getElem hs i (by simpa using hi)

theorem sfld_grows {σ σ' : State} (hg : Grows σ σ') {c : ClassName} {fs : List (FieldKey × Value)}
    {f : String} {s : JStr} (h : SFld σ c fs f s) : SFld σ' c fs f s := by
  obtain ⟨x, h1, h2, h3⟩ := h
  exact ⟨x, h1, heap_grows hg h2, h3⟩

theorem custAtN_grows {σ σ' : State} (hg : Grows σ σ') {v : Value} {t : CustR}
    (h : CustAtN σ v (some t)) : CustAtN σ' v (some t) := by
  simp only [CustAtN, CustAt] at h ⊢
  obtain ⟨x, hx, fs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := h
  exact ⟨x, hx, fs, heap_grows hg h0, h1, sfld_grows hg h2, sfld_grows hg h3, sfld_grows hg h4,
    sfld_grows hg h5, sfld_grows hg h6, sfld_grows hg h7, sfld_grows hg h8, sfld_grows hg h9,
    sfld_grows hg h10, sfld_grows hg h11, sfld_grows hg h12, h13, sfld_grows hg h14, sfld_grows hg h15,
    sfld_grows hg h16, sfld_grows hg h17, h18, sfld_grows hg h19⟩

theorem acctAtN_grows {σ σ' : State} (hg : Grows σ σ') {v : Value} {t : AcctR}
    (h : AcctAtN σ v (some t)) : AcctAtN σ' v (some t) := by
  simp only [AcctAtN, AcctAt] at h ⊢
  obtain ⟨x, hx, fs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨x, hx, fs, heap_grows hg h0, h1, sfld_grows hg h2, h3, h4, h5, sfld_grows hg h6, sfld_grows hg h7,
    sfld_grows hg h8, h9, h10, sfld_grows hg h11, sfld_grows hg h12, sfld_grows hg h13⟩

theorem getElem?_set_self_of_lt {α : Type} {l : List α} {i : Nat} {a : α} (h : i < l.length) :
    (l.set i a)[i]? = some a := by simp [h]

/-- `fixStr`, opaque to `jvc` (the thin paths never need the characters of a fixed text). -/
@[irreducible] def fixO (s : JStr) (n : Nat) : JStr := fixStr s n

theorem fixStr_hide (s : JStr) (n : Nat) : fixStr s n = fixO s n := by unfold fixO; rfl

theorem seqCode_00 {len : Nat} (h : 0 < len) : seqCode 0 0 len = JStr.ofString "00" := by
  simp [seqCode, h]

theorem seqStArr_00 {len : Nat} (h : 0 < len) : seqStArr 0 0 len = [.int 1, .int 0] := by
  simp [seqStArr, h]

theorem seqCode_10 : seqCode 0 0 0 = JStr.ofString "10" := by simp [seqCode]

theorem seqStArr_10 : seqStArr 0 0 0 = [.int 0, .int 1] := by simp [seqStArr]

theorem seqCode_eq_00 {i e : I32} {len : Nat} (he : e = 0) (hi : i.toInt < len) :
    seqCode i e len = JStr.ofString "00" := by
  simp [seqCode, he, hi]

theorem seqStArr_eq_00 {i e : I32} {len : Nat} (he : e = 0) (hi : i.toInt < len) :
    seqStArr i e len = [.int (i + 1), .int e] := by
  simp [seqStArr, he, hi]

theorem seqCode_eq_10 {i e : I32} {len : Nat} (he : e = 0) (hi : (len : Int) ≤ i.toInt) :
    seqCode i e len = JStr.ofString "10" := by
  simp [seqCode, he, Int.not_lt.mpr hi]

theorem seqStArr_eq_10 {i e : I32} {len : Nat} (he : e = 0) (hi : (len : Int) ≤ i.toInt) :
    seqStArr i e len = [.int i, .int 1] := by
  simp [seqStArr, he, Int.not_lt.mpr hi]

/-- `argText`, opaque to `jvc`. -/
@[irreducible] def argTextO (σ : State) (v : Value) : JStr := argText σ v

theorem argText_hide (σ : State) (v : Value) : argText σ v = argTextO σ v := by unfold argTextO; rfl

/-! The status literals as character lists (`decide` on `JStr.ofString` literals is slow). -/

theorem jstr_00 : JStr.ofString "00" = [BitVec.ofNat 16 48, BitVec.ofNat 16 48] := rfl
theorem jstr_04 : JStr.ofString "04" = [BitVec.ofNat 16 48, BitVec.ofNat 16 52] := rfl
theorem jstr_10 : JStr.ofString "10" = [BitVec.ofNat 16 49, BitVec.ofNat 16 48] := rfl

end EquivLean.Modernize.Cbstm03a.Java.Thin1
