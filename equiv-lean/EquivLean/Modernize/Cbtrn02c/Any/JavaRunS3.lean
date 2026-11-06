import EquivLean.Modernize.Cbtrn02c.Any.JavaRunO
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunS1
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunS2

/-!
# CBTRN02C → Java: the searches against the model's lookups

On arrays/lists of record objects holding the model's records, the Java searches find the index of
the model's lookup (`find?`): `firstIdx` of the Java key test equals `firstIdx` of the model's.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem findIdx?_congr {α β : Type} {p : α → Bool} {q : β → Bool} :
    ∀ {xs : List α} {ys : List β}, Forall2 (fun a b => p a = q b) xs ys →
      xs.findIdx? p = ys.findIdx? q
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    rw [List.findIdx?_cons, List.findIdx?_cons, h, findIdx?_congr hs]

theorem firstIdx_congr {α β : Type} {p : α → Bool} {q : β → Bool} {xs : List α} {ys : List β}
    (h : Forall2 (fun a b => p a = q b) xs ys) : firstIdx p xs = firstIdx q ys := by
  unfold firstIdx; rw [findIdx?_congr h]

theorem find?_of_firstIdx_neg {α : Type} {p : α → Bool} {l : List α} (h : firstIdx p l < 0) :
    l.find? p = none := by
  unfold firstIdx at h
  cases hf : l.findIdx? p with
  | some i => rw [hf] at h; simp at h; omega
  | none =>
    rw [List.find?_eq_none]
    intro x hx hpx
    rw [List.findIdx?_eq_none_iff] at hf
    exact absurd (hf x hx) (by simp [hpx])

theorem find?_of_firstIdx_nonneg {α : Type} {p : α → Bool} {l : List α} (h : 0 ≤ firstIdx p l) :
    ∃ (hi : (firstIdx p l).toNat < l.length), l.find? p = some l[(firstIdx p l).toNat] := by
  unfold firstIdx at h ⊢
  cases hf : l.findIdx? p with
  | none => rw [hf] at h; simp at h
  | some i =>
    simp only [Int.toNat_natCast]
    rw [List.findIdx?_eq_some_iff_getElem] at hf
    obtain ⟨hi, hpi, hlt⟩ := hf
    refine ⟨hi, ?_⟩
    rw [List.find?_eq_some_iff_getElem]
    exact ⟨hpi, i, hi, rfl, fun j hj => by simpa using hlt j hj⟩

theorem forall2_imp_right {α β : Type} {R S : α → β → Prop} {P : β → Prop}
    (hs : ∀ a b, R a b → P b → S a b) :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → (∀ b ∈ ys, P b) → Forall2 S xs ys
  | _, _, .nil, _ => .nil
  | _, _, .cons hr h, hp =>
    .cons (hs _ _ hr (hp _ List.mem_cons_self))
      (forall2_imp_right hs h (fun b hb => hp b (List.mem_cons_of_mem _ hb)))

/-- The text field of a cross-reference object. -/
theorem strField_xobj {σ : State} {v : Value} {x : List EquivLean.Cobol.Rec.FVal} (h : XObj σ v x) :
    strFieldOf σ xrefCardKey v = some (cp037Str (bAt x 0)) := by
  obtain ⟨a, fs, s0, s3, rfl, ha, g0, h0, -⟩ := h
  simp [strFieldOf, ha, g0, h0]

theorem beq_ofInt {n k : Int} (hn : n.natAbs < 10 ^ 18) (hk : k.natAbs < 10 ^ 18) :
    (some (BitVec.ofInt 64 n) == some (BitVec.ofInt 64 k)) = (n == k) := by
  by_cases h : n = k
  · subst h; simp
  · have : BitVec.ofInt 64 n ≠ BitVec.ofInt 64 k := fun e => h (ofInt_inj hn hk e)
    simp only [Option.some_beq_some]
    rw [beq_false_of_ne this, beq_false_of_ne h]

theorem beq_cp037 (b c : List UInt8) :
    (some (cp037Str b) == some (cp037Str c)) = (b == c) := by
  by_cases h : b = c
  · subst h; simp
  · have : cp037Str b ≠ cp037Str c := fun e => h (cp037Str_inj e)
    simp only [Option.some_beq_some]
    rw [beq_false_of_ne this, beq_false_of_ne h]

theorem longField_aobj {σ : State} {v : Value} {x : List EquivLean.Cobol.Rec.FVal} (h : AObj σ v x) :
    longFieldOf σ acctIdKey v = some (BitVec.ofInt 64 (nAt x 0)) := by
  obtain ⟨a, fs, _, _, _, _, _, _, _, rfl, ha, g0, -⟩ := h
  simp [longFieldOf, ha, g0]

theorem acct_first {σ : State} {xs : List Value} {accts : List (List EquivLean.Cobol.Rec.FVal)}
    (h : Forall2 (JRecAt AccountRecord "Cbtrn02c$AccountRecord" σ) xs accts)
    (hv : ∀ x ∈ accts, AccountRecord.Valid x) (id : Int) (hid : id.natAbs < 10 ^ 18) :
    firstIdx (fun v => longFieldOf σ acctIdKey v == some (BitVec.ofInt 64 id)) xs =
      firstIdx (fun a => Model.aId a == id) accts := by
  apply firstIdx_congr
  refine forall2_imp_right (P := AccountRecord.Valid) ?_ h hv
  intro v x hr hvx
  obtain ⟨hobj, n0, b1, n2, n3, n4, b5, b6, b7, n8, n9, b10, b11, b12, rfl, a0, -⟩ :=
    acctobj_of_rec hr hvx
  rw [longField_aobj hobj]
  simp only [nAt, Model.aId, Model.numOf, List.getD_cons_zero]
  exact beq_ofInt a0 hid

theorem tcMatch_cobj {σ : State} {v : Value} {x : List EquivLean.Cobol.Rec.FVal} (h : CObj σ v x)
    (acct cd : Int) (ty : List UInt8) (ha : (nAt x 0).natAbs < 10 ^ 18) (hc : (nAt x 2).natAbs < 10 ^ 18)
    (hacct : acct.natAbs < 10 ^ 18) (hcd : cd.natAbs < 10 ^ 18) :
    tcMatch σ (BitVec.ofInt 64 acct) (cp037Str ty) (BitVec.ofInt 64 cd) v =
      Model.catKey acct ty cd x := by
  obtain ⟨a, fs, s1, s4, rfl, hao, g0, g1, t1, g2, -⟩ := h
  simp only [tcMatch, longFieldOf, strFieldOf, hao, g0, g1, t1, g2, Model.catKey, Model.cAcct,
    Model.cType, Model.cCd]
  rw [beq_ofInt ha hacct, beq_cp037, beq_ofInt hc hcd]

theorem tcat_first {σ : State} {xs : List Value} {cats : List (List EquivLean.Cobol.Rec.FVal)}
    (h : Forall2 (JRecAt TranCatBalRecord "Cbtrn02c$TranCatBalRecord" σ) xs cats)
    (hv : ∀ x ∈ cats, TranCatBalRecord.Valid x) (acct cd : Int) (ty : List UInt8)
    (hacct : acct.natAbs < 10 ^ 18) (hcd : cd.natAbs < 10 ^ 18) :
    firstIdx (tcMatch σ (BitVec.ofInt 64 acct) (cp037Str ty) (BitVec.ofInt 64 cd)) xs =
      firstIdx (Model.catKey acct ty cd) cats := by
  apply firstIdx_congr
  refine forall2_imp_right (P := TranCatBalRecord.Valid) ?_ h hv
  intro v x hr hvx
  obtain ⟨hobj, n0, b1, n2, n3, b4, rfl, a0, a2, -⟩ := tcatobj_of_rec hr hvx
  exact tcMatch_cobj hobj acct cd ty a0 a2 hacct hcd

theorem xrefShapes_of {σ : State} {xs : List Value} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : ∀ v ∈ xs, ∃ x, x ∈ vals ∧ XObj σ v x) : XrefShapes σ xs := by
  intro v hv
  obtain ⟨x, -, a, fs, s0, s3, rfl, ha, g0, h0, -⟩ := h v hv
  exact ⟨a, fs, s0, _, rfl, ha, g0, h0⟩

theorem acctShapes_of {σ : State} {xs : List Value} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : ∀ v ∈ xs, ∃ x, x ∈ vals ∧ AObj σ v x) : AcctShapes σ xs := by
  intro v hv
  obtain ⟨x, -, a, fs, _, _, _, _, _, _, _, rfl, ha, g0, -⟩ := h v hv
  exact ⟨a, fs, _, rfl, ha, g0⟩

theorem tcatShapes_of {σ : State} {xs : List Value} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : ∀ v ∈ xs, ∃ x, x ∈ vals ∧ CObj σ v x) : TcatShapes σ xs := by
  intro v hv
  obtain ⟨x, -, a, fs, s1, s4, rfl, ha, g0, g1, t1, g2, -⟩ := h v hv
  exact ⟨a, fs, _, s1, _, _, rfl, ha, g0, g1, t1, g2⟩

theorem xref_first {σ : State} {xs : List Value} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : Forall2 (JRecAt CardXrefRecord "Cbtrn02c$CardXrefRecord" σ) xs vals)
    (hv : ∀ x ∈ vals, CardXrefRecord.Valid x) (card : List UInt8) :
    firstIdx (fun v => strFieldOf σ xrefCardKey v == some (cp037Str card)) xs =
      firstIdx (fun x => Model.xCard x == card) vals := by
  apply firstIdx_congr
  refine forall2_imp_right (P := CardXrefRecord.Valid) ?_ h hv
  intro v x hr hvx
  obtain ⟨hobj, b0, n1, n2, b3, rfl, -, -, -⟩ := xobj_of_rec hr hvx
  rw [strField_xobj hobj]
  simp only [bAt, Model.xCard, Model.strOf, List.getD_cons_zero]
  exact beq_cp037 b0 card

end EquivLean.Modernize.Cbtrn02c.Java
