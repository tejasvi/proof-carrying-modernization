import EquivLean.Modernize.Cbstm03b.RustRun1
import EquivLean.Bridge.Aeneas.Digits

/-!
# CBSTM03B → Rust: the record images

Value forms of `trnx_image`, `xref_image`, `cust_image` (the record's fields in order, then spaces to 1000
bytes) and `acct_image` (the 11 low digits of the account id, zero-padded, the data, then spaces). Each copy
loop is an instance of `copy_loop`; the digit loop of `acct_image` is proved by `wp_loop`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Modernize.Cbstm03b.Rust

/-! ## Copy loops -/

/-- A copy loop `while i < N { out[off + i] = src[i]; i += 1 }` from `i = 0`, on a buffer holding `P` (`off`
bytes) and then spaces: the buffer then holds `P`, the first `N` bytes of `src`, then spaces. `hcont` and
`hdone` are one iteration of the generated body. -/
theorem copy_loop {β : Type} (P src : List U8) (off N : Nat) (hP : P.length = off) (hN : off + N ≤ 1000)
    (hsrc : N ≤ src.length)
    (body : Array U8 1000#usize × Usize → Result (ControlFlow (Array U8 1000#usize × Usize) β))
    (fin : Array U8 1000#usize → β)
    (hcont : ∀ (out : Array U8 1000#usize) (i : Usize), i.val < N →
      wp (body (out, i)) (fun o => ∃ v, o = .ok v ∧ ∃ (out' : Array U8 1000#usize) (i' : Usize),
        v = .cont (out', i') ∧ i'.val = i.val + 1 ∧ out'.val = out.val.set (off + i.val) (src.getD i.val default)))
    (hdone : ∀ (out : Array U8 1000#usize) (i : Usize), N ≤ i.val → body (out, i) = .ok (.done (fin out)))
    (out : Array U8 1000#usize) (hout : out.val = P ++ List.replicate (1000 - off) 32#u8) :
    ∃ out' : Array U8 1000#usize, loop body (out, 0#usize) = .ok (fin out') ∧
      out'.val = P ++ src.take N ++ List.replicate (1000 - (off + N)) 32#u8 := by
  have aux : ∀ (n : Nat) (out : Array U8 1000#usize) (i : Usize), N - i.val = n → i.val ≤ N →
      out.val = P ++ src.take i.val ++ List.replicate (1000 - (off + i.val)) 32#u8 →
      ∃ out' : Array U8 1000#usize, loop body (out, i) = .ok (fin out') ∧
        out'.val = P ++ src.take N ++ List.replicate (1000 - (off + N)) 32#u8 := by
    intro n
    induction n with
    | zero =>
      intro out i hn hi hout
      have hiN : i.val = N := by omega
      refine ⟨out, ?_, by rw [hout, hiN]⟩
      rw [loop_unfold, hdone out i (by omega), bind_ok]
    | succ n ih =>
      intro out i hn hi hout
      have hiN : i.val < N := by omega
      have hsi : i.val < src.length := by omega
      obtain ⟨v, hb, out', i', rfl, hi', hout'⟩ := exists_ok_of_wp (hcont out i hiN)
      have hout'' : out'.val = P ++ src.take i'.val ++ List.replicate (1000 - (off + i'.val)) 32#u8 := by
        rw [hout', hout, hi',
          show 1000 - (off + i.val) = (1000 - (off + (i.val + 1))) + 1 by omega,
          set_pad _ _ _ (by simp [hP]; omega), take_succ_of_lt hsi, List.getD_eq_getElem _ _ hsi]
        simp only [List.append_assoc, List.singleton_append]
      obtain ⟨out'', h1, h2⟩ := ih out' i' (by omega) (by omega) hout''
      refine ⟨out'', ?_, h2⟩
      rw [loop_unfold, hb, bind_ok]
      exact h1
  exact aux _ out 0#usize rfl (by simp) (by simpa using hout)

/-! ## The images -/

/-- `trnx_image`: the card number, the transaction id and the data, then spaces. -/
theorem trnx_image_eq (r : cbstm03b.FdTrnxfileRec) :
    ∃ out : Array U8 1000#usize, cbstm03b.trnx_image r = .ok out ∧
      out.val = r.fd_trnx_card.val ++ r.fd_trnx_id.val ++ r.fd_acct_data.val ++ List.replicate 650 32#u8 := by
  have l1 : r.fd_trnx_card.val.length = 16 := r.fd_trnx_card.property
  have l2 : r.fd_trnx_id.val.length = 16 := r.fd_trnx_id.property
  have l3 : r.fd_acct_data.val.length = 318 := r.fd_acct_data.property
  obtain ⟨o1, e1, v1⟩ : ∃ o : Array U8 1000#usize,
      cbstm03b.trnx_image_loop0 r (Array.repeat 1000#usize 32#u8) 0#usize = .ok (r, o) ∧
      o.val = [] ++ r.fd_trnx_card.val.take 16 ++ List.replicate (1000 - (0 + 16)) 32#u8 := by
    unfold cbstm03b.trnx_image_loop0
    refine copy_loop [] r.fd_trnx_card.val 0 16 rfl (by norm_num) (by omega) _ (fun out => (r, out)) ?_ ?_ _
      (by simp only [Array.repeat_val, uscalar_ofNat_val, Nat.sub_zero, List.nil_append])
    · intro out i hi
      have hl : out.val.length = 1000 := out.property
      have hs : i.val < r.fd_trnx_card.val.length := by omega
      have hb : i.val < out.val.length := by omega
      have hm : i.val + 1 ≤ Usize.max := by scalar_tac
      dsimp only
      aeneas_wp [rust_loop_body, index_usize_getD _ _ hs, array_update_eq, hi, hb, hm]
      refine ⟨_, rfl, _, _, rfl, ?_, ?_⟩ <;> simp [Array.from_val, UScalar.ofNatCore_val_eq]
    · intro out i hi
      have h : ¬ i < 16#usize := by scalar_tac
      simp only [cbstm03b.trnx_image_loop0.body, h, ↓reduceIte]
  obtain ⟨o2, e2, v2⟩ : ∃ o : Array U8 1000#usize,
      cbstm03b.trnx_image_loop1 r o1 0#usize = .ok (r, o) ∧
      o.val = r.fd_trnx_card.val ++ r.fd_trnx_id.val.take 16 ++ List.replicate (1000 - (16 + 16)) 32#u8 := by
    unfold cbstm03b.trnx_image_loop1
    refine copy_loop r.fd_trnx_card.val r.fd_trnx_id.val 16 16 l1 (by norm_num) (by omega) _ (fun out => (r, out))
      ?_ ?_ _ (by rw [v1, List.take_of_length_le (by omega), List.nil_append])
    · intro out i hi
      have hl : out.val.length = 1000 := out.property
      have hs : i.val < r.fd_trnx_id.val.length := by omega
      have hb : 16 + i.val < out.val.length := by omega
      have hm1 : 16 + i.val ≤ Usize.max := by scalar_tac
      have hm : i.val + 1 ≤ Usize.max := by scalar_tac
      dsimp only
      aeneas_wp [rust_loop_body, index_usize_getD _ _ hs, array_update_eq, hi, hb, hm1, hm]
      refine ⟨_, rfl, _, _, rfl, ?_, ?_⟩ <;> simp [Array.from_val, UScalar.ofNatCore_val_eq]
    · intro out i hi
      have h : ¬ i < 16#usize := by scalar_tac
      simp only [cbstm03b.trnx_image_loop1.body, h, ↓reduceIte]
  obtain ⟨o3, e3, v3⟩ : ∃ o : Array U8 1000#usize,
      cbstm03b.trnx_image_loop2 r o2 0#usize = .ok o ∧
      o.val = (r.fd_trnx_card.val ++ r.fd_trnx_id.val) ++ r.fd_acct_data.val.take 318 ++
        List.replicate (1000 - (32 + 318)) 32#u8 := by
    unfold cbstm03b.trnx_image_loop2
    refine copy_loop (r.fd_trnx_card.val ++ r.fd_trnx_id.val) r.fd_acct_data.val 32 318 (by simp [l1, l2])
      (by norm_num) (by omega) _ (fun out => out) ?_ ?_ _ (by rw [v2, List.take_of_length_le (by omega)])
    · intro out i hi
      have hl : out.val.length = 1000 := out.property
      have hs : i.val < r.fd_acct_data.val.length := by omega
      have hb : 32 + i.val < out.val.length := by omega
      have hm1 : 32 + i.val ≤ Usize.max := by scalar_tac
      have hm : i.val + 1 ≤ Usize.max := by scalar_tac
      dsimp only
      aeneas_wp [rust_loop_body, index_usize_getD _ _ hs, array_update_eq, hi, hb, hm1, hm]
      refine ⟨_, rfl, _, _, rfl, ?_, ?_⟩ <;> simp [Array.from_val, UScalar.ofNatCore_val_eq]
    · intro out i hi
      have h : ¬ i < 318#usize := by scalar_tac
      simp only [cbstm03b.trnx_image_loop2.body, h, ↓reduceIte]
  refine ⟨o3, ?_, ?_⟩
  · refine eq_ok_of_wp ?_
    simp only [cbstm03b.trnx_image]
    aeneas_wp [e1, e2, e3]
  · rw [v3, List.take_of_length_le (by omega)]

/-- `xref_image`: the card number and the data, then spaces. -/
theorem xref_image_eq (r : cbstm03b.FdXreffileRec) :
    ∃ out : Array U8 1000#usize, cbstm03b.xref_image r = .ok out ∧
      out.val = r.fd_xref_card_num.val ++ r.fd_xref_data.val ++ List.replicate 950 32#u8 := by
  have l1 : r.fd_xref_card_num.val.length = 16 := r.fd_xref_card_num.property
  have l2 : r.fd_xref_data.val.length = 34 := r.fd_xref_data.property
  obtain ⟨o1, e1, v1⟩ : ∃ o : Array U8 1000#usize,
      cbstm03b.xref_image_loop0 r (Array.repeat 1000#usize 32#u8) 0#usize = .ok (r, o) ∧
      o.val = [] ++ r.fd_xref_card_num.val.take 16 ++ List.replicate (1000 - (0 + 16)) 32#u8 := by
    unfold cbstm03b.xref_image_loop0
    refine copy_loop [] r.fd_xref_card_num.val 0 16 rfl (by norm_num) (by omega) _ (fun out => (r, out)) ?_ ?_ _
      (by simp only [Array.repeat_val, uscalar_ofNat_val, Nat.sub_zero, List.nil_append])
    · intro out i hi
      have hl : out.val.length = 1000 := out.property
      have hs : i.val < r.fd_xref_card_num.val.length := by omega
      have hb : i.val < out.val.length := by omega
      have hm : i.val + 1 ≤ Usize.max := by scalar_tac
      dsimp only
      aeneas_wp [rust_loop_body, index_usize_getD _ _ hs, array_update_eq, hi, hb, hm]
      refine ⟨_, rfl, _, _, rfl, ?_, ?_⟩ <;> simp [Array.from_val, UScalar.ofNatCore_val_eq]
    · intro out i hi
      have h : ¬ i < 16#usize := by scalar_tac
      simp only [cbstm03b.xref_image_loop0.body, h, ↓reduceIte]
  obtain ⟨o2, e2, v2⟩ : ∃ o : Array U8 1000#usize,
      cbstm03b.xref_image_loop1 r o1 0#usize = .ok o ∧
      o.val = r.fd_xref_card_num.val ++ r.fd_xref_data.val.take 34 ++ List.replicate (1000 - (16 + 34)) 32#u8 := by
    unfold cbstm03b.xref_image_loop1
    refine copy_loop r.fd_xref_card_num.val r.fd_xref_data.val 16 34 l1 (by norm_num) (by omega) _ (fun out => out)
      ?_ ?_ _ (by rw [v1, List.take_of_length_le (by omega), List.nil_append])
    · intro out i hi
      have hl : out.val.length = 1000 := out.property
      have hs : i.val < r.fd_xref_data.val.length := by omega
      have hb : 16 + i.val < out.val.length := by omega
      have hm1 : 16 + i.val ≤ Usize.max := by scalar_tac
      have hm : i.val + 1 ≤ Usize.max := by scalar_tac
      dsimp only
      aeneas_wp [rust_loop_body, index_usize_getD _ _ hs, array_update_eq, hi, hb, hm1, hm]
      refine ⟨_, rfl, _, _, rfl, ?_, ?_⟩ <;> simp [Array.from_val, UScalar.ofNatCore_val_eq]
    · intro out i hi
      have h : ¬ i < 34#usize := by scalar_tac
      simp only [cbstm03b.xref_image_loop1.body, h, ↓reduceIte]
  refine ⟨o2, ?_, ?_⟩
  · refine eq_ok_of_wp ?_
    simp only [cbstm03b.xref_image]
    aeneas_wp [e1, e2]
  · rw [v2, List.take_of_length_le (by omega)]

/-- `cust_image`: the customer id and the data, then spaces. -/
theorem cust_image_eq (r : cbstm03b.FdCustfileRec) :
    ∃ out : Array U8 1000#usize, cbstm03b.cust_image r = .ok out ∧
      out.val = r.fd_cust_id.val ++ r.fd_cust_data.val ++ List.replicate 500 32#u8 := by
  have l1 : r.fd_cust_id.val.length = 9 := r.fd_cust_id.property
  have l2 : r.fd_cust_data.val.length = 491 := r.fd_cust_data.property
  obtain ⟨o1, e1, v1⟩ : ∃ o : Array U8 1000#usize,
      cbstm03b.cust_image_loop0 r (Array.repeat 1000#usize 32#u8) 0#usize = .ok (r, o) ∧
      o.val = [] ++ r.fd_cust_id.val.take 9 ++ List.replicate (1000 - (0 + 9)) 32#u8 := by
    unfold cbstm03b.cust_image_loop0
    refine copy_loop [] r.fd_cust_id.val 0 9 rfl (by norm_num) (by omega) _ (fun out => (r, out)) ?_ ?_ _
      (by simp only [Array.repeat_val, uscalar_ofNat_val, Nat.sub_zero, List.nil_append])
    · intro out i hi
      have hl : out.val.length = 1000 := out.property
      have hs : i.val < r.fd_cust_id.val.length := by omega
      have hb : i.val < out.val.length := by omega
      have hm : i.val + 1 ≤ Usize.max := by scalar_tac
      dsimp only
      aeneas_wp [rust_loop_body, index_usize_getD _ _ hs, array_update_eq, hi, hb, hm]
      refine ⟨_, rfl, _, _, rfl, ?_, ?_⟩ <;> simp [Array.from_val, UScalar.ofNatCore_val_eq]
    · intro out i hi
      have h : ¬ i < 9#usize := by scalar_tac
      simp only [cbstm03b.cust_image_loop0.body, h, ↓reduceIte]
  obtain ⟨o2, e2, v2⟩ : ∃ o : Array U8 1000#usize,
      cbstm03b.cust_image_loop1 r o1 0#usize = .ok o ∧
      o.val = r.fd_cust_id.val ++ r.fd_cust_data.val.take 491 ++ List.replicate (1000 - (9 + 491)) 32#u8 := by
    unfold cbstm03b.cust_image_loop1
    refine copy_loop r.fd_cust_id.val r.fd_cust_data.val 9 491 l1 (by norm_num) (by omega) _ (fun out => out)
      ?_ ?_ _ (by rw [v1, List.take_of_length_le (by omega), List.nil_append])
    · intro out i hi
      have hl : out.val.length = 1000 := out.property
      have hs : i.val < r.fd_cust_data.val.length := by omega
      have hb : 9 + i.val < out.val.length := by omega
      have hm1 : 9 + i.val ≤ Usize.max := by scalar_tac
      have hm : i.val + 1 ≤ Usize.max := by scalar_tac
      dsimp only
      aeneas_wp [rust_loop_body, index_usize_getD _ _ hs, array_update_eq, hi, hb, hm1, hm]
      refine ⟨_, rfl, _, _, rfl, ?_, ?_⟩ <;> simp [Array.from_val, UScalar.ofNatCore_val_eq]
    · intro out i hi
      have h : ¬ i < 491#usize := by scalar_tac
      simp only [cbstm03b.cust_image_loop1.body, h, ↓reduceIte]
  refine ⟨o2, ?_, ?_⟩
  · refine eq_ok_of_wp ?_
    simp only [cbstm03b.cust_image]
    aeneas_wp [e1, e2]
  · rw [v2, List.take_of_length_le (by omega)]

/-- The digit `(w % 10) as u8` of the digit loop, for `w ≥ 0`. -/
theorem digit_hcast_val (w : I64) (hw : 0 ≤ w.val) :
    ((IScalar.hcast .U8 (IScalar.mk (BitVec.srem (IScalar.bv w) (IScalar.bv (10#i64))) : I64)).val : Int) =
      w.val % 10 := by
  rw [IScalar.hcast_val_eq, srem_val]
  have h10 : (10#i64).val = 10 := by simp
  have h1 : 0 ≤ w.val % 10 := Int.emod_nonneg _ (by norm_num)
  have h2 : w.val % 10 < 10 := Int.emod_lt_of_pos _ (by norm_num)
  rw [h10, Int.tmod_eq_emod_of_nonneg hw, Int.emod_eq_of_lt h1 (by simp only [UScalarTy.numBits]; omega)]
  exact Int.toNat_of_nonneg h1

/-- The next value of the digit loop: `w / 10`. -/
theorem digit_div (x n : Nat) (hn : 0 < n) (hn11 : n ≤ 11) :
    ((x / 10 ^ (11 - n) : Nat) : Int).tdiv 10 = ((x / 10 ^ (11 - (n - 1)) : Nat) : Int) := by
  rw [Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg _), show (10 : Int) = ((10 : Nat) : Int) from rfl,
    ← Int.natCast_ediv, Nat.div_div_eq_div_mul, ← Nat.pow_succ, Nat.succ_eq_add_one,
    show 11 - n + 1 = 11 - (n - 1) by omega]

/-- The buffer of the digit loop after writing digit `11 - n` at position `n - 1`. -/
theorem digit_set (n x : Nat) (hn : 0 < n) (hn11 : n ≤ 11) (R : List U8) (b : U8)
    (hb : b.val = 48 + x / 10 ^ (11 - n) % 10) :
    (List.replicate n 32#u8 ++ zeroPad (11 - n) x ++ R).set (n - 1) b =
      List.replicate (n - 1) 32#u8 ++ zeroPad (11 - (n - 1)) x ++ R := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hd : x / 10 ^ (11 - (k + 1)) % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hbe : b = byteOf (48 + x / 10 ^ (11 - (k + 1)) % 10) := by
    rw [UScalar.eq_equiv, hb, byteOf_val _ (by omega)]
  rw [Nat.add_sub_cancel, List.append_assoc, set_replicate_end, show 11 - k = (11 - (k + 1)) + 1 by omega,
    zeroPad_succ_left, hbe]
  simp only [List.append_assoc]

set_option maxHeartbeats 1000000 in
/-- The digit loop of `acct_image`, from position 11 down: the 11 low digits of `x`, zero-padded, then
spaces. -/
theorem acct_image_loop0_eq (x : Nat) (v : I64) (hv : v.val = (x : Int)) :
    ∃ out : Array U8 1000#usize,
      cbstm03b.acct_image_loop0 (Array.repeat 1000#usize 32#u8) v 11#usize = .ok out ∧
      out.val = zeroPad 11 x ++ List.replicate 989 32#u8 := by
  -- the spaces after the digits as a variable (`simp` would unfold `List.replicate 989`)
  generalize hR : List.replicate 989 32#u8 = R
  refine exists_ok_of_wp ?_
  simp only [cbstm03b.acct_image_loop0]
  refine wp_loop (loop_shape _) (fun s : Array U8 1000#usize × I64 × Usize => s.2.2.val ≤ 11 ∧
      s.2.1.val = ((x / 10 ^ (11 - s.2.2.val) : Nat) : Int) ∧
      s.1.val = List.replicate s.2.2.val 32#u8 ++ zeroPad (11 - s.2.2.val) x ++ R)
    (fun s => s.2.2.val) ?_ _ ?_
  · rintro ⟨out, w, i⟩ ⟨hi, hw, hout⟩
    clear hR
    simp only at hi hw hout
    have hlen : out.val.length = 1000 := out.property
    by_cases h0 : 0 < i.val
    · have hb : i.val - 1 < out.val.length := by omega
      have hw0 : 0 ≤ w.val := by rw [hw]; exact Int.natCast_nonneg _
      have hdv := digit_hcast_val w hw0
      aeneas_wp [rust_loop_body, h0, array_update_eq, hb]
      split_ifs
      all_goals try first
        | (exfalso; omega)
        | (simp at *; done)
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq, Array.from_val]
      refine ⟨⟨by omega, ?_, ?_⟩, by omega⟩
      · rw [hw]
        exact digit_div x i.val h0 hi
      · rw [hout]
        refine digit_set i.val x h0 hi R _ ?_
        rw [UScalar.ofNatCore_val_eq]
        omega
    · have hi0 : i.val = 0 := by omega
      aeneas_wp [rust_loop_body, h0]
      simp only [loopCls_done]
      refine ⟨out, rfl, ?_⟩
      rw [hout, hi0]
      simp only [List.replicate_zero, List.nil_append, Nat.sub_zero]
  · refine ⟨by simp, by simp [hv], ?_⟩
    simp only [Array.repeat_val, uscalar_ofNat_val, Nat.sub_self]
    have z : zeroPad 0 x = [] := by simp [zeroPad, EquivLean.Cobol.Rec.zpad, Cobol.Digits.toDigits]
    rw [z, List.append_nil, ← hR, ← List.replicate_add]

/-- `acct_image`, for an account id in `0 ..< 10 ^ 11` (what the schema's `PIC 9(11)` holds): the id's 11
digits, zero-padded, the data, then spaces. -/
theorem acct_image_eq (r : cbstm03b.FdAcctfileRec) (h0 : 0 ≤ r.fd_acct_id.val)
    (h1 : r.fd_acct_id.val < 100000000000) :
    ∃ out : Array U8 1000#usize, cbstm03b.acct_image r = .ok out ∧
      out.val = zeroPad 11 r.fd_acct_id.val.toNat ++ r.fd_acct_data.val ++ List.replicate 700 32#u8 := by
  have l2 : r.fd_acct_data.val.length = 289 := r.fd_acct_data.property
  have hm : cbstm03b.ACCT_MOD.val = 100000000000 := by simp [cbstm03b.ACCT_MOD]
  have hv : (IScalar.mk (BitVec.srem (IScalar.bv r.fd_acct_id) (IScalar.bv cbstm03b.ACCT_MOD)) : I64).val =
      ((r.fd_acct_id.val.toNat : Nat) : Int) := by
    rw [srem_val, hm, Int.tmod_eq_emod_of_nonneg h0, Int.emod_eq_of_lt h0 h1, Int.toNat_of_nonneg h0]
  have hneg : ¬ (IScalar.mk (BitVec.srem (IScalar.bv r.fd_acct_id) (IScalar.bv cbstm03b.ACCT_MOD)) : I64) <
      0#i64 := by scalar_tac
  obtain ⟨o1, e1, v1⟩ := acct_image_loop0_eq _ _ hv
  obtain ⟨o2, e2, v2⟩ : ∃ o : Array U8 1000#usize,
      cbstm03b.acct_image_loop1 r.fd_acct_data o1 0#usize = .ok o ∧
      o.val = zeroPad 11 r.fd_acct_id.val.toNat ++ r.fd_acct_data.val.take 289 ++
        List.replicate (1000 - (11 + 289)) 32#u8 := by
    unfold cbstm03b.acct_image_loop1
    refine copy_loop (zeroPad 11 r.fd_acct_id.val.toNat) r.fd_acct_data.val 11 289 (zeroPad_length _ _)
      (by norm_num) (by omega) _ (fun out => out) ?_ ?_ _ (by rw [v1])
    · intro out i hi
      have hl : out.val.length = 1000 := out.property
      have hs : i.val < r.fd_acct_data.val.length := by omega
      have hb : 11 + i.val < out.val.length := by omega
      have hm1 : 11 + i.val ≤ Usize.max := by scalar_tac
      have hm : i.val + 1 ≤ Usize.max := by scalar_tac
      dsimp only
      aeneas_wp [rust_loop_body, index_usize_getD _ _ hs, array_update_eq, hi, hb, hm1, hm]
      refine ⟨_, rfl, _, _, rfl, ?_, ?_⟩ <;> simp [Array.from_val, UScalar.ofNatCore_val_eq]
    · intro out i hi
      have h : ¬ i < 289#usize := by scalar_tac
      simp only [cbstm03b.acct_image_loop1.body, h, ↓reduceIte]
  refine ⟨o2, ?_, ?_⟩
  · refine eq_ok_of_wp ?_
    simp only [cbstm03b.acct_image]
    aeneas_wp [hm, hneg, e1, e2]
    rw [ite_eq_left (by norm_num), ite_eq_right (by rw [hv]; exact not_lt.2 (Int.natCast_nonneg _))]
    trivial
  · rw [v2, List.take_of_length_le (by omega)]

end EquivLean.Modernize.Cbstm03b.Rust
