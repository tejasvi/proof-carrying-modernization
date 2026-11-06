import EquivLean.Modernize.Cbstm03b.RustRun2
import EquivLean.Modernize.Cbstm03b.RustSpec

/-!
# CBSTM03B → Rust: the translation's values as the model's

The facts that turn the value forms of `RustRun1`/`RustRun2` into the model's values (`RustSpec.lean`): CP037
is injective on Latin-1 bytes, so the translation's tests on the DD name and the operation byte are the model's
tests on their EBCDIC bytes; the literal statuses are the model's `stCp`/`stBytes`; a record image is
`intoBuf` of the record's encoding; a valid account id is in `0 ..< 10 ^ 11`; the customer key is the model's
`custKey`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Rust

/-! ## Latin-1 bytes as EBCDIC -/

theorem ebc_inj {a b : U8} (h : ebcdicOfLatin1 a.val = ebcdicOfLatin1 b.val) : a = b := by
  have ha := cp037_roundtrip ⟨a.val, by scalar_tac⟩
  have hb := cp037_roundtrip ⟨b.val, by scalar_tac⟩
  simp only at ha hb
  rw [UScalar.eq_equiv, ← ha, ← hb, h]

theorem ebc_map_inj {l1 l2 : List U8}
    (h : l1.map (fun u => ebcdicOfLatin1 u.val) = l2.map (fun u => ebcdicOfLatin1 u.val)) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a t ih => cases l2 with
    | nil => simp at h
    | cons b u =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [ebc_inj h.1, ih h.2]

/-- A DD name test: the bytes are the literal iff their EBCDIC bytes are the model's DD name. -/
theorem dd_iff {dd lit : List U8} {e : List UInt8} (h : lit.map (fun u => ebcdicOfLatin1 u.val) = e) :
    dd.map (fun u => ebcdicOfLatin1 u.val) = e ↔ dd = lit :=
  ⟨fun h' => ebc_map_inj (h'.trans h.symm), fun h' => h' ▸ h⟩

/-- An operation test: the byte is the literal iff its EBCDIC byte is the model's operation. -/
theorem op_iff {op lit : U8} {e : UInt8} (h : ebcdicOfLatin1 lit.val = e) :
    ebcdicOfLatin1 op.val = e ↔ op = lit :=
  ⟨fun h' => ebc_inj (h'.trans h.symm), fun h' => h' ▸ h⟩

theorem ebc_trnx : [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8].map
    (fun u : U8 => ebcdicOfLatin1 u.val) = ddTrnx := by decide +kernel
theorem ebc_xref : [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8].map
    (fun u : U8 => ebcdicOfLatin1 u.val) = ddXref := by decide +kernel
theorem ebc_cust : [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8].map
    (fun u : U8 => ebcdicOfLatin1 u.val) = ddCust := by decide +kernel
theorem ebc_acct : [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8].map
    (fun u : U8 => ebcdicOfLatin1 u.val) = ddAcct := by decide +kernel

theorem ebc_O : ebcdicOfLatin1 (79#u8 : U8).val = opOpen := by decide +kernel
theorem ebc_R : ebcdicOfLatin1 (82#u8 : U8).val = opRead := by decide +kernel
theorem ebc_K : ebcdicOfLatin1 (75#u8 : U8).val = opReadK := by decide +kernel
theorem ebc_C : ebcdicOfLatin1 (67#u8 : U8).val = opClose := by decide +kernel

theorem ebc_space : ebcdicOfLatin1 (32#u8 : U8).val = 64 := by decide +kernel

theorem ebc_spaces (n : Nat) :
    (List.replicate n (32#u8 : U8)).map (fun u => ebcdicOfLatin1 u.val) = List.replicate n 64 := by
  rw [List.map_replicate, ebc_space]

/-! ## Statuses -/

theorem ebc_digit48 : ∀ d, d < 10 → ebcdicOfLatin1 (48 + d) = UInt8.ofNat (240 + d) := by decide +kernel

theorem stCp_ebc (c : Nat) : (Model.stCp c).map ebcdicOfLatin1 = stBytes c := by
  have h1 := ebc_digit48 (c / 10 % 10) (Nat.mod_lt _ (by decide))
  have h2 := ebc_digit48 (c % 10) (Nat.mod_lt _ (by decide))
  simp only [Model.stCp, stBytes, List.map_cons, List.map_nil, h1, h2]

/-- A status item holding the code points of status `c` holds, as EBCDIC bytes, coblean's `stBytes c`. -/
theorem st_ebc {X : List U8} {c : Nat} (h : X.map (·.val) = Model.stCp c) :
    X.map (fun u => ebcdicOfLatin1 u.val) = stBytes c := by
  rw [← stCp_ebc, ← h, List.map_map]
  rfl

theorem st00 : (Array.make 2#usize [48#u8, 48#u8]).val.map (·.val) = Model.stCp 0 := by decide +kernel
theorem st10 : (Array.make 2#usize [49#u8, 48#u8]).val.map (·.val) = Model.stCp 10 := by decide +kernel
theorem st23 : (Array.make 2#usize [50#u8, 51#u8]).val.map (·.val) = Model.stCp 23 := by decide +kernel
theorem st41 : (Array.make 2#usize [52#u8, 49#u8]).val.map (·.val) = Model.stCp 41 := by decide +kernel
theorem st42 : (Array.make 2#usize [52#u8, 50#u8]).val.map (·.val) = Model.stCp 42 := by decide +kernel
theorem st46 : (Array.make 2#usize [52#u8, 54#u8]).val.map (·.val) = Model.stCp 46 := by decide +kernel
theorem st47 : (Array.make 2#usize [52#u8, 55#u8]).val.map (·.val) = Model.stCp 47 := by decide +kernel

/-! ## The area -/

theorem aDd_vals (q : cbstm03b.LkM03bArea) :
    Model.aDd (LkM03bArea.vals q) = q.lk_m03b_dd.val.map (fun u => ebcdicOfLatin1 u.val) := rfl

theorem aKey_vals (q : cbstm03b.LkM03bArea) :
    Model.aKey (LkM03bArea.vals q) = q.lk_m03b_key.val.map (fun u => ebcdicOfLatin1 u.val) := rfl

theorem aKeyLn_vals (q : cbstm03b.LkM03bArea) : Model.aKeyLn (LkM03bArea.vals q) = q.lk_m03b_key_ln.val := rfl

theorem aOp_vals (q : cbstm03b.LkM03bArea) :
    Model.aOp (LkM03bArea.vals q) = ebcdicOfLatin1 (q.lk_m03b_oper.val.getD 0 default).val := by
  have h1 : q.lk_m03b_oper.val.length = 1 := q.lk_m03b_oper.property
  show (List.map (fun u => ebcdicOfLatin1 u.val) q.lk_m03b_oper.val).headD 0 = _
  rcases hq : q.lk_m03b_oper.val with _ | ⟨x, _ | ⟨y, t⟩⟩
  · simp [hq] at h1
  · rfl
  · simp [hq] at h1

/-! ## Images and encodings -/

theorem trnx_image_rel (r : cbstm03b.FdTrnxfileRec) (out : Array U8 1000#usize)
    (h : out.val = r.fd_trnx_card.val ++ r.fd_trnx_id.val ++ r.fd_acct_data.val ++ List.replicate 650 32#u8) :
    out.val.map (fun u => ebcdicOfLatin1 u.val) =
      intoBuf (Model.FdTrnxfileRec.encode (FdTrnxfileRec.vals r)) := by
  have l1 : r.fd_trnx_card.val.length = 16 := r.fd_trnx_card.property
  have l2 : r.fd_trnx_id.val.length = 16 := r.fd_trnx_id.property
  have l3 : r.fd_acct_data.val.length = 318 := r.fd_acct_data.property
  rw [h]
  simp only [intoBuf, Schema.encode, FdTrnxfileRec.vals, List.zip_cons_cons, List.zip_nil_left,
    List.flatMap_cons, List.flatMap_nil, Field.encode, List.map_append, List.append_nil, List.length_append,
    List.length_map, l1, l2, l3, ebc_spaces, List.append_assoc]

theorem xref_image_rel (r : cbstm03b.FdXreffileRec) (out : Array U8 1000#usize)
    (h : out.val = r.fd_xref_card_num.val ++ r.fd_xref_data.val ++ List.replicate 950 32#u8) :
    out.val.map (fun u => ebcdicOfLatin1 u.val) =
      intoBuf (Model.FdXreffileRec.encode (FdXreffileRec.vals r)) := by
  have l1 : r.fd_xref_card_num.val.length = 16 := r.fd_xref_card_num.property
  have l2 : r.fd_xref_data.val.length = 34 := r.fd_xref_data.property
  rw [h]
  simp only [intoBuf, Schema.encode, FdXreffileRec.vals, List.zip_cons_cons, List.zip_nil_left,
    List.flatMap_cons, List.flatMap_nil, Field.encode, List.map_append, List.append_nil, List.length_append,
    List.length_map, l1, l2, ebc_spaces, List.append_assoc]

theorem cust_image_rel (r : cbstm03b.FdCustfileRec) (out : Array U8 1000#usize)
    (h : out.val = r.fd_cust_id.val ++ r.fd_cust_data.val ++ List.replicate 500 32#u8) :
    out.val.map (fun u => ebcdicOfLatin1 u.val) =
      intoBuf (Model.FdCustfileRec.encode (FdCustfileRec.vals r)) := by
  have l1 : r.fd_cust_id.val.length = 9 := r.fd_cust_id.property
  have l2 : r.fd_cust_data.val.length = 491 := r.fd_cust_data.property
  rw [h]
  simp only [intoBuf, Schema.encode, FdCustfileRec.vals, List.zip_cons_cons, List.zip_nil_left,
    List.flatMap_cons, List.flatMap_nil, Field.encode, List.map_append, List.append_nil, List.length_append,
    List.length_map, l1, l2, ebc_spaces, List.append_assoc]

/-- The 11 zero-padded digits as EBCDIC bytes: coblean's encoding of `PIC 9(11)`. -/
theorem zeroPad_ebc (x : Nat) :
    (zeroPad 11 x).map (fun u => ebcdicOfLatin1 u.val) = encodeNum {} { digits := 11 } (x : Int) := by
  have hd : ∀ d ∈ Cobol.Digits.toDigits 10 11 x,
      ebcdicOfLatin1 (byteOf (48 + d)).val = Config.digitByte {} d := by
    intro d hdm
    have := Cobol.Digits.toDigits_lt (by decide) 11 x d hdm
    rw [byteOf_val _ (by omega), ebc_digit48 d this]
    rfl
  simp only [zeroPad, EquivLean.Cobol.Rec.zpad, List.map_map]
  rw [List.map_congr_left (f := (fun u => ebcdicOfLatin1 u.val) ∘ byteOf ∘ (48 + ·))
    (g := Config.digitByte {}) hd]
  simp only [encodeNum, encZoned, Int.natAbs_natCast, Bool.false_eq_true, ↓reduceIte, Cobol.Digits.toDigits,
    List.map_append, List.map_cons, List.map_nil]

theorem acct_image_rel (r : cbstm03b.FdAcctfileRec) (out : Array U8 1000#usize) (h0 : 0 ≤ r.fd_acct_id.val)
    (h : out.val = zeroPad 11 r.fd_acct_id.val.toNat ++ r.fd_acct_data.val ++ List.replicate 700 32#u8) :
    out.val.map (fun u => ebcdicOfLatin1 u.val) =
      intoBuf (Model.FdAcctfileRec.encode (FdAcctfileRec.vals r)) := by
  have l2 : r.fd_acct_data.val.length = 289 := r.fd_acct_data.property
  have hx : ((r.fd_acct_id.val.toNat : Nat) : Int) = r.fd_acct_id.val := Int.toNat_of_nonneg h0
  have hz := zeroPad_ebc r.fd_acct_id.val.toNat
  rw [hx] at hz
  have hzl : (encodeNum {} { digits := 11 } r.fd_acct_id.val).length = 11 := by
    rw [← hz, List.length_map, zeroPad_length]
  rw [h]
  simp only [intoBuf, Schema.encode, FdAcctfileRec.vals, List.zip_cons_cons, List.zip_nil_left,
    List.flatMap_cons, List.flatMap_nil, Field.encode, List.map_append, List.append_nil, List.length_append,
    List.length_map, hz, hzl, l2, ebc_spaces, List.append_assoc]

/-- A valid account record's id is in `0 ..< 10 ^ 11` (`PIC 9(11)`). -/
theorem acct_id_range (r : cbstm03b.FdAcctfileRec) (h : FdAcctfileRec.Valid (FdAcctfileRec.vals r)) :
    0 ≤ r.fd_acct_id.val ∧ r.fd_acct_id.val < 100000000000 := by
  simp only [Schema.Valid, FdAcctfileRec.vals] at h
  cases h with
  | cons h1 _ =>
    obtain ⟨fmt, hk, -, -, hh, -⟩ := h1
    cases hk
    simp only [NumFmt.Holds, NumFmt.fullBinary] at hh
    simp at hh
    omega

/-! ## The customer key -/

theorem custKey_ebc (key : List U8) (hk : key.length = 25) (k : Nat) (hk25 : k ≤ 25) :
    (custKeyR key k).map (fun u => ebcdicOfLatin1 u.val) =
      Model.custKey (key.map (fun u => ebcdicOfLatin1 u.val)) k := by
  unfold custKeyR Model.custKey
  rw [List.map_append, ebc_spaces, List.map_take]
  rcases Nat.lt_or_ge k 9 with h | h
  · rw [Nat.min_eq_left (by omega)]
    exact (List.take_of_length_le (by simp [hk]; omega)).symm
  · rw [Nat.min_eq_right h, Nat.sub_self, show 9 - k = 0 by omega, List.replicate_zero, List.append_nil,
      List.append_nil, List.take_take, Nat.min_eq_left h]

end EquivLean.Modernize.Cbstm03b.Rust
