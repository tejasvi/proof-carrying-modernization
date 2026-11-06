import EquivLean.Modernize.Cbstm03a.Java.RecDefs

/-!
# CBSTM03A → Java: record-object and record-text bridges

1. `jRecAt_to_trnxAtN`, `jRecAt_to_xrefAtN`, `jRecAt_to_custAtN`, `jRecAt_to_acctAtN` and their
   array lifts (`trnxFileAt_to_recsAt`, `xrefFileAt_to_recsAt`, `custFileAt_to_recsAt`,
   `acctFileAt_to_recsAt`).
2. `trnxTextR_eq`, `xrefTextR_eq`, `custTextR_eq`, `acctTextR_eq`: each record's `Iface3` text
   equals `jline ((S.encode v).map cp037Code)`.
-/

open Cobol.Digits EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.GlueKit
open EquivLean.Modernize.Cbstm03b.Java (fixStr fixStr_eq_self zpadStr digitChar cp037Str_length str_field_of)
open EquivLean.Modernize.Cbstm03a.StmBridge EquivLean.Modernize.Cbstm03a.Model

namespace EquivLean.Modernize.Cbstm03a.Java

/-! ## Part 1: `JRecAt` → `TrnxAtN` / `XrefAtN` / `CustAtN` / `AcctAtN` and `<File>At` → `RecsAt` -/

def IsAlnum (f : Field) : Bool :=
  match f.desc.kind with
  | .alnum _ => true
  | _ => false

def IsNumDisplay (f : Field) : Bool :=
  match f.desc.kind with
  | .num fmt => fmt.usage == .display
  | _ => false

theorem isAlnum_exists {f : Field} (h : IsAlnum f = true) : ∃ j, f.desc.kind = .alnum j := by
  unfold IsAlnum at h
  cases hk : f.desc.kind <;> simp_all

theorem isNumDisplay_exists {f : Field} (h : IsNumDisplay f = true) :
    ∃ fmt, f.desc.kind = .num fmt ∧ fmt.usage = .display := by
  unfold IsNumDisplay at h
  cases hk : f.desc.kind with
  | num fmt =>
    simp only [hk, beq_iff_eq] at h
    exact ⟨fmt, rfl, h⟩
  | _ => simp [hk] at h

theorem toInt_ofInt_of_natAbs_lt {n : Int} (h : n.natAbs < 10 ^ 18) :
    (BitVec.ofInt 64 n).toInt = n := by
  rw [BitVec.toInt_ofInt]
  have h1 : (-2 ^ 63 : Int) ≤ n := by omega
  have h2 : n < (2 ^ 63 : Int) := by omega
  rw [Int.bmod_eq_of_le_mul_two] <;> omega

theorem valid_alnum_getD {S : Schema} {v : List EquivLean.Cobol.Rec.FVal} (hv : S.Valid v) (i : Nat)
    (hi : i < S.fields.length) (hal : IsAlnum (S.fields.getD i default) = true) :
    ∃ bs, v.getD i default = .str bs ∧ bs.length = (S.fields.getD i default).desc.len := by
  obtain ⟨j, hk⟩ := isAlnum_exists hal
  exact str_of_valid hk (hv.getD i hi)

theorem valid_num_getD {S : Schema} {v : List EquivLean.Cobol.Rec.FVal} (hv : S.Valid v) (i : Nat)
    (hi : i < S.fields.length) (hnd : IsNumDisplay (S.fields.getD i default) = true) :
    ∃ fmt n, (S.fields.getD i default).desc.kind = .num fmt ∧
      v.getD i default = .num n ∧ n.natAbs < 10 ^ 18 ∧
      (BitVec.ofInt 64 n).toInt = n := by
  obtain ⟨fmt, hk, hu⟩ := isNumDisplay_exists hnd
  obtain ⟨n, hn, hvn⟩ := num_of_valid hk (hv.getD i hi)
  obtain ⟨fmt', hk', _, hd18, hh, _⟩ := hvn
  rw [hk] at hk'
  cases hk'
  have hlt1 : n.natAbs < 10 ^ fmt.digits := ((holds_display hu).mp hh).1
  have hlt2 : 10 ^ fmt.digits ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) hd18
  have hlt : n.natAbs < 10 ^ 18 := Nat.lt_of_lt_of_le hlt1 hlt2
  exact ⟨fmt, n, hk, hn, hlt, toInt_ofInt_of_natAbs_lt hlt⟩

theorem sfld_of_getD {S : Schema} {cls : ClassName} {σ : State} {fs : List (FieldKey × Value)}
    {v : List EquivLean.Cobol.Rec.FVal} {jname : String} (hf : Forall2 (jFieldAt σ cls fs) S.fields v) (hv : S.Valid v)
    (i : Nat) (hi : i < S.fields.length := by decide)
    (hjn : (S.fields.getD i default).jname = jname := by decide)
    (hal : IsAlnum (S.fields.getD i default) = true := by decide)
    (hlen : (S.fields.getD i default).desc.len < 2147483648 := by decide) :
    SFld σ cls fs jname (jStrOf v i) := by
  have hfi := hf.getD i hi
  have hvi := hv.getD i hi
  obtain ⟨bs, s, hbs, hbl, hg, ⟨x, rfl, hx⟩⟩ := str_field_of (isAlnum_exists hal) hvi hfi
  rw [hjn] at hg
  unfold jStrOf
  rw [hbs, StmBridge.strOf]
  exact ⟨x, hg, hx, by rw [cp037Str_length, hbl]; exact hlen⟩

theorem lfld_of_getD {S : Schema} {cls : ClassName} {σ : State} {fs : List (FieldKey × Value)}
    {v : List EquivLean.Cobol.Rec.FVal} {jname : String} (hf : Forall2 (jFieldAt σ cls fs) S.fields v) (hv : S.Valid v)
    (i : Nat) (hi : i < S.fields.length := by decide)
    (hjn : (S.fields.getD i default).jname = jname := by decide)
    (hnd : IsNumDisplay (S.fields.getD i default) = true := by decide) :
    LFld cls fs jname (i64Of v i) := by
  have hfi := hf.getD i hi
  obtain ⟨fmt, n, _, hn, hlt, htoInt⟩ := valid_num_getD hv i hi hnd
  rw [hn] at hfi
  simp only [jFieldAt, hjn] at hfi
  unfold i64Of
  rw [hn]
  exact ⟨hfi, by simp only [numOf, htoInt]; omega⟩

theorem jRecAt_to_trnxAtN {σ : State} {x : Value} {v : List EquivLean.Cobol.Rec.FVal}
    (h : JRecAt TrnxRecord "Cbstm03a$TrnxRecord" σ x v) (hv : TrnxRecord.Valid v) :
    TrnxAtN σ x (some (trnxROf v)) := by
  obtain ⟨a, fs, rfl, ha, hf⟩ := h
  exact ⟨a, rfl, fs, ha,
    sfld_of_getD hf hv 0, sfld_of_getD hf hv 1, sfld_of_getD hf hv 2, lfld_of_getD hf hv 3,
    sfld_of_getD hf hv 4, sfld_of_getD hf hv 5, lfld_of_getD hf hv 6, lfld_of_getD hf hv 7,
    sfld_of_getD hf hv 8, sfld_of_getD hf hv 9, sfld_of_getD hf hv 10, sfld_of_getD hf hv 11,
    sfld_of_getD hf hv 12, sfld_of_getD hf hv 13⟩

theorem jRecAt_to_xrefAtN {σ : State} {x : Value} {v : List EquivLean.Cobol.Rec.FVal}
    (h : JRecAt CardXrefRecord "Cbstm03a$CardXrefRecord" σ x v) (hv : CardXrefRecord.Valid v) :
    XrefAtN σ x (some (xrefROf v)) := by
  obtain ⟨a, fs, rfl, ha, hf⟩ := h
  exact ⟨a, rfl, fs, ha,
    sfld_of_getD hf hv 0, lfld_of_getD hf hv 1, lfld_of_getD hf hv 2, sfld_of_getD hf hv 3⟩

theorem jRecAt_to_custAtN {σ : State} {x : Value} {v : List EquivLean.Cobol.Rec.FVal}
    (h : JRecAt CustomerRecord "Cbstm03a$CustomerRecord" σ x v) (hv : CustomerRecord.Valid v) :
    CustAtN σ x (some (custROf v)) := by
  obtain ⟨a, fs, rfl, ha, hf⟩ := h
  exact ⟨a, rfl, fs, ha,
    lfld_of_getD hf hv 0, sfld_of_getD hf hv 1, sfld_of_getD hf hv 2, sfld_of_getD hf hv 3,
    sfld_of_getD hf hv 4, sfld_of_getD hf hv 5, sfld_of_getD hf hv 6, sfld_of_getD hf hv 7,
    sfld_of_getD hf hv 8, sfld_of_getD hf hv 9, sfld_of_getD hf hv 10, sfld_of_getD hf hv 11,
    lfld_of_getD hf hv 12, sfld_of_getD hf hv 13, sfld_of_getD hf hv 14, sfld_of_getD hf hv 15,
    sfld_of_getD hf hv 16, lfld_of_getD hf hv 17, sfld_of_getD hf hv 18⟩

theorem jRecAt_to_acctAtN {σ : State} {x : Value} {v : List EquivLean.Cobol.Rec.FVal}
    (h : JRecAt AccountRecord "Cbstm03a$AccountRecord" σ x v) (hv : AccountRecord.Valid v) :
    AcctAtN σ x (some (acctROf v)) := by
  obtain ⟨a, fs, rfl, ha, hf⟩ := h
  exact ⟨a, rfl, fs, ha,
    lfld_of_getD hf hv 0, sfld_of_getD hf hv 1, lfld_of_getD hf hv 2, lfld_of_getD hf hv 3,
    lfld_of_getD hf hv 4, sfld_of_getD hf hv 5, sfld_of_getD hf hv 6, sfld_of_getD hf hv 7,
    lfld_of_getD hf hv 8, lfld_of_getD hf hv 9, sfld_of_getD hf hv 10, sfld_of_getD hf hv 11,
    sfld_of_getD hf hv 12⟩

theorem forall2_map_right {α β γ : Type} {P : α → β → Prop} {Q : α → γ → Prop} {V : β → Prop}
    (f : β → γ) (hPQ : ∀ a b, P a b → V b → Q a (f b)) :
    ∀ {xs : List α} {ys : List β}, Forall2 P xs ys → (∀ y ∈ ys, V y) → Forall2 Q xs (ys.map f)
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons h hs, hv =>
    .cons (hPQ _ _ h (hv _ (List.mem_cons_self ..)))
      (forall2_map_right f hPQ hs (fun y hy => hv y (List.mem_cons_of_mem _ hy)))

theorem trnxFileAt_to_recsAt {σ : State} {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (ha : TrnxFileAt σ a vals) (hv : ∀ v ∈ vals, TrnxRecord.Valid v) :
    RecsAt TrnxAtN σ a (vals.map trnxROf) := by
  obtain ⟨et, xs, h1, h2, h3⟩ := ha
  exact ⟨et, xs, h1, h2, forall2_map_right trnxROf (fun _ _ => jRecAt_to_trnxAtN) h3 hv⟩

theorem xrefFileAt_to_recsAt {σ : State} {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (ha : XrefFileAt σ a vals) (hv : ∀ v ∈ vals, CardXrefRecord.Valid v) :
    RecsAt XrefAtN σ a (vals.map xrefROf) := by
  obtain ⟨et, xs, h1, h2, h3⟩ := ha
  exact ⟨et, xs, h1, h2, forall2_map_right xrefROf (fun _ _ => jRecAt_to_xrefAtN) h3 hv⟩

theorem custFileAt_to_recsAt {σ : State} {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (ha : CustFileAt σ a vals) (hv : ∀ v ∈ vals, CustomerRecord.Valid v) :
    RecsAt CustAtN σ a (vals.map custROf) := by
  obtain ⟨et, xs, h1, h2, h3⟩ := ha
  exact ⟨et, xs, h1, h2, forall2_map_right custROf (fun _ _ => jRecAt_to_custAtN) h3 hv⟩

theorem acctFileAt_to_recsAt {σ : State} {a : Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (ha : AcctFileAt σ a vals) (hv : ∀ v ∈ vals, AccountRecord.Valid v) :
    RecsAt AcctAtN σ a (vals.map acctROf) := by
  obtain ⟨et, xs, h1, h2, h3⟩ := ha
  exact ⟨et, xs, h1, h2, forall2_map_right acctROf (fun _ _ => jRecAt_to_acctAtN) h3 hv⟩

/-! ## Part 2: Record text equality (`trnxTextR_eq`, `xrefTextR_eq`, `custTextR_eq`, `acctTextR_eq`) -/

def encodeAt (S : Schema) (v : List EquivLean.Cobol.Rec.FVal) (i : Nat) : JStr :=
  jline (fieldTextS (S.fields.getD i default) (v.getD i default))

theorem cp037Str_eq_jline (bs : List UInt8) : cp037Str bs = jline (bs.map cp037Code) := by
  simp only [cp037Str, jline, List.map_map]
  rfl

theorem zpadStr_eq_jline_zpad : ∀ (m c : Nat), zpadStr c m = jline (zpad m c)
  | 0, _ => rfl
  | m + 1, c => by
    simp only [zpadStr, zpad, toDigits_succ, jline, List.map_append, List.map_singleton]
    rw [zpadStr_eq_jline_zpad m (c / 10)]
    rfl

theorem zsLast_eq (neg : Bool) (d : Nat) : zsLast neg d = BitVec.ofNat 16 (overpunch neg d) := by
  unfold zsLast overpunch
  split <;> split <;> rfl

theorem zsI_eq_jline (n : Int) (L : Nat) :
    zsI n L = jline (zpad (L - 1) (n.natAbs / 10) ++ [overpunch (decide (n < 0)) (n.natAbs % 10)]) := by
  rw [zsI, zpadStr_eq_jline_zpad, zsLast_eq]
  simp [jline]

def IsNumSigned (f : Field) (s : Bool) : Bool :=
  match f.desc.kind with
  | .num fmt => (fmt.usage == .display) && (fmt.signed == s)
  | _ => false

theorem isNumSigned_imp {f : Field} {s : Bool} (h : IsNumSigned f s = true) :
    IsNumDisplay f = true ∧ ∀ fmt, f.desc.kind = .num fmt → fmt.signed = s := by
  unfold IsNumSigned IsNumDisplay at *
  cases hk : f.desc.kind with
  | num fmt =>
    simp only [hk, Bool.and_eq_true, beq_iff_eq] at h ⊢
    exact ⟨h.1, fun _ e => by cases e; exact h.2⟩
  | _ => simp [hk] at h

theorem fixStr_jStrOf_eq {S : Schema} {v : List EquivLean.Cobol.Rec.FVal} (hv : S.Valid v) (i L : Nat)
    (hi : i < S.fields.length := by decide)
    (hal : IsAlnum (S.fields.getD i default) = true := by decide)
    (hlen : (S.fields.getD i default).desc.len = L := by decide) :
    fixStr (jStrOf v i) L = encodeAt S v i := by
  obtain ⟨bs, hbs, hbl⟩ := valid_alnum_getD hv i hi hal
  rw [hlen] at hbl
  unfold jStrOf encodeAt
  rw [hbs, StmBridge.strOf, fixStr_eq_self (by rw [cp037Str_length, hbl]), fieldTextS, cp037Str_eq_jline]

theorem zuI_i64Of_eq {S : Schema} {v : List EquivLean.Cobol.Rec.FVal} (hv : S.Valid v) (i L : Nat)
    (hi : i < S.fields.length := by decide)
    (hns : IsNumSigned (S.fields.getD i default) false = true := by decide)
    (hlen : (S.fields.getD i default).desc.len = L := by decide) :
    zuI (i64Of v i).toInt L = encodeAt S v i := by
  obtain ⟨hnd, hsig⟩ := isNumSigned_imp hns
  obtain ⟨fmt, n, hk, hn, _, htoInt⟩ := valid_num_getD hv i hi hnd
  have hs : fmt.signed = false := hsig fmt hk
  unfold i64Of zuI encodeAt
  rw [hn, numOf, htoInt, zpadStr_eq_jline_zpad]
  simp only [fieldTextS, hk, hs, Bool.false_eq_true, ↓reduceIte, hlen]

theorem zsI_i64Of_eq {S : Schema} {v : List EquivLean.Cobol.Rec.FVal} (hv : S.Valid v) (i L : Nat)
    (hi : i < S.fields.length := by decide)
    (hns : IsNumSigned (S.fields.getD i default) true = true := by decide)
    (hlen : (S.fields.getD i default).desc.len = L := by decide) :
    zsI (i64Of v i).toInt L = encodeAt S v i := by
  obtain ⟨hnd, hsig⟩ := isNumSigned_imp hns
  obtain ⟨fmt, n, hk, hn, _, htoInt⟩ := valid_num_getD hv i hi hnd
  have hs : fmt.signed = true := hsig fmt hk
  unfold i64Of encodeAt
  rw [hn, numOf, htoInt, zsI_eq_jline]
  simp only [fieldTextS, hk, hs, ↓reduceIte, hlen]

theorem zip_eq_map_range {α β : Type} [Inhabited α] [Inhabited β] {xs : List α} {ys : List β}
    (h : xs.length = ys.length) :
    xs.zip ys = (List.range xs.length).map fun i => (xs.getD i default, ys.getD i default) := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    have hix : i < xs.length := by simpa using h2
    have hiy : i < ys.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hix, List.getElem?_eq_getElem hiy]

theorem jline_encode_eq_range {S : Schema} {v : List EquivLean.Cobol.Rec.FVal} (hv : S.Valid v)
    (hu : ∀ f ∈ S.fields, DisplayNumeric f := by decide) :
    jline ((S.encode v).map cp037Code) =
      ((List.range S.fields.length).map (encodeAt S v)).flatten := by
  rw [← Schema.textS_eq hu hv]
  unfold Schema.textS jline encodeAt
  rw [zip_eq_map_range hv.length_eq, List.map_flatten, List.map_map, List.map_map]
  rfl

theorem trnxTextR_eq {v : List EquivLean.Cobol.Rec.FVal} (hv : TrnxRecord.Valid v) :
    trnxTextR (trnxROf v) = jline ((TrnxRecord.encode v).map cp037Code) := by
  rw [jline_encode_eq_range hv, show TrnxRecord.fields.length = 14 from rfl]
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, ← List.append_assoc]
  unfold trnxTextR trnxROf
  dsimp only
  rw [fixStr_jStrOf_eq hv 0 16, fixStr_jStrOf_eq hv 1 16, fixStr_jStrOf_eq hv 2 2,
    zuI_i64Of_eq hv 3 4, fixStr_jStrOf_eq hv 4 10, fixStr_jStrOf_eq hv 5 100,
    zsI_i64Of_eq hv 6 11, zuI_i64Of_eq hv 7 9, fixStr_jStrOf_eq hv 8 50,
    fixStr_jStrOf_eq hv 9 50, fixStr_jStrOf_eq hv 10 10, fixStr_jStrOf_eq hv 11 26,
    fixStr_jStrOf_eq hv 12 26, fixStr_jStrOf_eq hv 13 20]

theorem xrefTextR_eq {v : List EquivLean.Cobol.Rec.FVal} (hv : CardXrefRecord.Valid v) :
    xrefTextR (xrefROf v) = jline ((CardXrefRecord.encode v).map cp037Code) := by
  rw [jline_encode_eq_range hv, show CardXrefRecord.fields.length = 4 from rfl]
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, ← List.append_assoc]
  unfold xrefTextR xrefROf
  dsimp only
  rw [fixStr_jStrOf_eq hv 0 16, zuI_i64Of_eq hv 1 9, zuI_i64Of_eq hv 2 11, fixStr_jStrOf_eq hv 3 14]

theorem custTextR_eq {v : List EquivLean.Cobol.Rec.FVal} (hv : CustomerRecord.Valid v) :
    custTextR (custROf v) = jline ((CustomerRecord.encode v).map cp037Code) := by
  rw [jline_encode_eq_range hv, show CustomerRecord.fields.length = 19 from rfl]
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, ← List.append_assoc]
  unfold custTextR custROf
  dsimp only
  rw [zuI_i64Of_eq hv 0 9, fixStr_jStrOf_eq hv 1 25, fixStr_jStrOf_eq hv 2 25,
    fixStr_jStrOf_eq hv 3 25, fixStr_jStrOf_eq hv 4 50, fixStr_jStrOf_eq hv 5 50,
    fixStr_jStrOf_eq hv 6 50, fixStr_jStrOf_eq hv 7 2, fixStr_jStrOf_eq hv 8 3,
    fixStr_jStrOf_eq hv 9 10, fixStr_jStrOf_eq hv 10 15, fixStr_jStrOf_eq hv 11 15,
    zuI_i64Of_eq hv 12 9, fixStr_jStrOf_eq hv 13 20, fixStr_jStrOf_eq hv 14 10,
    fixStr_jStrOf_eq hv 15 10, fixStr_jStrOf_eq hv 16 1, zuI_i64Of_eq hv 17 3,
    fixStr_jStrOf_eq hv 18 168]

theorem acctTextR_eq {v : List EquivLean.Cobol.Rec.FVal} (hv : AccountRecord.Valid v) :
    acctTextR (acctROf v) = jline ((AccountRecord.encode v).map cp037Code) := by
  rw [jline_encode_eq_range hv, show AccountRecord.fields.length = 13 from rfl]
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, ← List.append_assoc]
  unfold acctTextR acctROf
  dsimp only
  rw [zuI_i64Of_eq hv 0 11, fixStr_jStrOf_eq hv 1 1, zsI_i64Of_eq hv 2 12,
    zsI_i64Of_eq hv 3 12, zsI_i64Of_eq hv 4 12, fixStr_jStrOf_eq hv 5 10,
    fixStr_jStrOf_eq hv 6 10, fixStr_jStrOf_eq hv 7 10, zsI_i64Of_eq hv 8 12,
    zsI_i64Of_eq hv 9 12, fixStr_jStrOf_eq hv 10 10, fixStr_jStrOf_eq hv 11 10,
    fixStr_jStrOf_eq hv 12 178]

#print axioms jRecAt_to_trnxAtN
#print axioms jRecAt_to_xrefAtN
#print axioms jRecAt_to_custAtN
#print axioms jRecAt_to_acctAtN
#print axioms trnxFileAt_to_recsAt
#print axioms xrefFileAt_to_recsAt
#print axioms custFileAt_to_recsAt
#print axioms acctFileAt_to_recsAt
#print axioms trnxTextR_eq
#print axioms xrefTextR_eq
#print axioms custTextR_eq
#print axioms acctTextR_eq

end EquivLean.Modernize.Cbstm03a.Java
