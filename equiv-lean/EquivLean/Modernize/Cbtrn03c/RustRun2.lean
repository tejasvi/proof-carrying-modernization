import EquivLean.Modernize.Cbtrn03c.RustRun1

/-!
# CBTRN03C → Rust, part 2: the edited amounts

`edit_amount v plus`: the 15 bytes of `Model.editAmt v plus`.  Its first loop writes the 9 digits
of the integer part into a buffer from the right (as the digit loops of part 1); its second loop
walks the pattern `ZZZ,ZZZ,ZZZ` with the zero-suppression flag, and its invariant is "the bytes
written so far, then the rest of `Model.zzz`": `pre ++ zzz (pattern after p) (digits after k) sup`
is the whole of `zzz pattern digits true`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Rust
open Cobol.Digits (toDigits)

/-- Writing after a prefix, into a run of `k + 1` copies. -/
theorem set_after {α : Type _} (pre : List α) (k : Nat) (a c : α) :
    (pre ++ List.replicate (k + 1) a).set pre.length c = pre ++ c :: List.replicate k a := by
  rw [List.set_append_right _ _ (le_refl _), Nat.sub_self, List.replicate_succ]
  rfl

set_option maxHeartbeats 2000000 in
/-- The digit loop of `edit_amount`: the 9 digits of `x`, most significant first (as values). -/
theorem edit_amount_loop0_spec (x : Nat) (t : U64) (ht : t.val = x) :
    wp (cbtrn03c.edit_amount_loop0 (Array.repeat 9#usize 0#u8) t 0#usize)
      (fun o => ∃ b, o = .ok b ∧ b.val = (toDigits 10 9 x).map byteOf) := by
  simp only [cbtrn03c.edit_amount_loop0]
  refine wp_loop (loop_shape _) (fun s => s.2.2.val ≤ 9 ∧ s.2.1.val = x / 10 ^ s.2.2.val ∧
      s.1.val = List.replicate (9 - s.2.2.val) 0#u8 ++ (toDigits 10 s.2.2.val x).map byteOf ++ [])
    (fun s => 9 - s.2.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro buf t' i hinv
    obtain ⟨hi, ht', hbuf⟩ := hinv
    have hlen : buf.val.length = 9 := buf.property
    aeneas_wp [rust_loop_body, array_update_eq, Array.from_val, hlen]
    by_cases h1 : i.val < 9
    · simp only [h1, _root_.ite_true]
      split_ifs
      all_goals try (exfalso; omega)
      all_goals try (exfalso; scalar_tac)
      simp only [loopCls_cont]
      refine ⟨⟨by simp only [UScalar.ofNatCore_val_eq]; omega, ?_, ?_⟩, by
        simp only [UScalar.ofNatCore_val_eq]; omega⟩
      · rw [UScalar.ofNatCore_val_eq, UScalar.ofNatCore_val_eq, ht', Nat.div_div_eq_div_mul,
          ← Nat.pow_succ]
      · simp only [Array.from_val, hbuf, UScalar.ofNatCore_val_eq]
        rw [show 8 - i.val = 9 - 1 - i.val by omega, set_mid _ _ h1, toDigits_succ_left,
          show 9 - (i.val + 1) = 9 - 1 - i.val by omega]
        simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          List.singleton_append, List.cons_append, List.append_cancel_left_eq, List.cons.injEq,
          and_true, List.append_nil]
        have hd10 : t'.val % 10 < 10 := Nat.mod_lt _ (by norm_num)
        rw [UScalar.eq_equiv, UScalar.cast_val_eq, UScalar.ofNatCore_val_eq,
          byteOf_val _ (by omega), ht']
        simp only [UScalarTy.U8_numBits_eq]
        omega
    · simp only [h1, _root_.ite_false, loopCls_done]
      refine ⟨buf, rfl, ?_⟩
      have e : i.val = 9 := by omega
      rw [hbuf, e]
      simp
  · refine ⟨by simp, by simp [ht], ?_⟩
    simp [Array.repeat_val, toDigits]

/-- A byte literal of the code. -/
theorem ofNatCore_byteOf (c : Nat) (hc : c < 256) (h : c < 2 ^ UScalarTy.U8.numBits) :
    (UScalar.ofNatCore c h : U8) = byteOf c := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.ofNatCore_val_eq, byteOf_val _ hc]

/-- The pattern of the integer part, as `Model.editAmt` reads it. -/
def patC : List Char := "ZZZ,ZZZ,ZZZ".toList

/-- The pattern as `edit_amount` holds it (`b"ZZZ,ZZZ,ZZZ"`). -/
def patA : Array U8 11#usize :=
  Array.make 11#usize [90#u8, 90#u8, 90#u8, 44#u8, 90#u8, 90#u8, 90#u8, 44#u8, 90#u8, 90#u8, 90#u8]

/-- The digits consumed after `p` characters of the pattern. -/
def kOf (p : Nat) : Nat := if p ≤ 3 then p else if p ≤ 7 then p - 1 else p - 2

theorem patA_at : ∀ p : Fin 11, (patA.val[p.val]'(by simp [patA])).val =
    if p.val = 3 ∨ p.val = 7 then 44 else 90 := by
  decide +kernel

theorem patC_drop : ∀ p : Fin 11, patC.drop p.val =
    (if p.val = 3 ∨ p.val = 7 then ',' else 'Z') :: patC.drop (p.val + 1) := by
  decide +kernel

theorem patC_drop11 : patC.drop 11 = [] := by decide



set_option maxHeartbeats 4000000 in
/-- The pattern loop of `edit_amount`: `Model.zzz` on the digits, after the sign. -/
theorem edit_amount_loop1_spec (out : Array U8 15#usize) (digits : Array U8 9#usize) (sign : U8)
    (ds : List Nat) (hout : out.val = sign :: List.replicate 14 32#u8)
    (hd : digits.val = ds.map byteOf) (hds : ds.length = 9) (hlt : ∀ d ∈ ds, d < 10) :
    wp (cbtrn03c.edit_amount_loop1 out digits patA true 0#usize 0#usize)
      (fun o => ∃ b, o = .ok b ∧
        b.val = sign :: ((Model.zzz patC ds true).map byteOf ++ List.replicate 3 32#u8)) := by
  simp only [cbtrn03c.edit_amount_loop1]
  refine wp_loop (loop_shape _) (fun s => s.2.2.2.val ≤ 11 ∧ s.2.2.1.val = kOf s.2.2.2.val ∧
      ∃ pre : List Nat, pre.length = s.2.2.2.val ∧
        s.1.val = sign :: (pre.map byteOf ++ List.replicate (14 - s.2.2.2.val) 32#u8) ∧
        pre ++ Model.zzz (patC.drop s.2.2.2.val) (ds.drop s.2.2.1.val) s.2.1 =
          Model.zzz patC ds true)
    (fun s => 11 - s.2.2.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro o sup k p hinv
    obtain ⟨hp, hk, pre, hpre, ho, hz⟩ := hinv
    have hlen : o.val.length = 15 := o.property
    have hdl : digits.val.length = 9 := digits.property
    aeneas_wp [rust_loop_body, array_update_eq, array_index_usize_eq, Array.from_val, hlen, hdl]
    have hpl : patA.val.length = 11 := by simp [patA]
    -- writing the next character after the prefix
    have hset : ∀ x : U8, (o.val.set (1 + p.val) x) =
        sign :: (pre.map byteOf ++ x :: List.replicate (14 - (p.val + 1)) 32#u8) := by
      intro x
      have hlp : (pre.map byteOf).length = p.val := by simp [hpre]
      rw [ho, Nat.add_comm, List.set_cons_succ, show 14 - p.val = (14 - (p.val + 1)) + 1 by omega,
        set_after' _ _ _ _ _ hlp]
    by_cases h1 : p.val < 11
    · have hdrop := patC_drop ⟨p.val, h1⟩
      simp only at hdrop
      simp only [h1, _root_.ite_true, _root_.dite_true, hpl, patA_at ⟨p.val, h1⟩]
      simp (disch := first | omega | scalar_tac) only [dite_eq_left]
      by_cases hc : p.val = 3 ∨ p.val = 7
      · rw [hdrop] at hz
        simp only [hc, _root_.ite_true, Model.zzz] at hz ⊢
        have hk1 : k.val = kOf (p.val + 1) := by
          rw [hk]; rcases hc with h | h <;> simp [kOf, h]
        cases sup
        all_goals simp only [Bool.false_eq_true, _root_.ite_true, _root_.ite_false] at hz ⊢
        all_goals simp only [loopCls_cont, UScalar.ofNatCore_val_eq, Array.from_val, hset]
        · refine ⟨⟨by omega, hk1, pre ++ [44], by simp [hpre], ?_, ?_⟩, by omega⟩
          · simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
              List.singleton_append]
            rfl
          · rw [← hz, List.append_assoc]; rfl
        · refine ⟨⟨by omega, hk1, pre ++ [32], by simp [hpre], ?_, ?_⟩, by omega⟩
          · simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
              List.singleton_append]
            rfl
          · rw [← hz, List.append_assoc]; rfl
      · have hk9 : k.val < 9 := by rw [hk]; simp only [kOf]; split_ifs <;> omega
        have hk1 : k.val + 1 = kOf (p.val + 1) := by
          rw [hk]; simp only [kOf]; split_ifs <;> omega
        have hdk : ds.drop k.val = ds[k.val]'(by omega) :: ds.drop (k.val + 1) :=
          List.drop_eq_getElem_cons (by omega)
        have hdv : digits.val[k.val]'(by omega) = byteOf (ds[k.val]'(by omega)) := by simp [hd]
        have hd10 : ds[k.val]'(by omega) < 10 := hlt _ (List.getElem_mem _)
        have hdb : (byteOf (ds[k.val]'(by omega))).val = ds[k.val]'(by omega) :=
          byteOf_val _ (by omega)
        rw [hdrop, hdk] at hz
        simp only [hc, _root_.ite_false, Model.zzz,
          show ('Z' = ',') = False from eq_false (by decide)] at hz
        simp only [hc, _root_.ite_false, Nat.reduceEqDiff]
        simp (disch := first | omega | scalar_tac) only [dite_eq_left]
        simp only [hdv, hdb]
        cases sup
        · simp only [Bool.false_and, Bool.false_eq_true, _root_.ite_false] at hz ⊢
          simp only [loopCls_cont, UScalar.ofNatCore_val_eq, Array.from_val, hset]
          refine ⟨⟨by omega, hk1, pre ++ [48 + ds[k.val]'(by omega)], by simp [hpre], ?_, ?_⟩,
            by omega⟩
          · simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
              List.singleton_append, ofNatCore_byteOf _ (show 48 + ds[k.val]'(by omega) < 256 by omega)]
          · rw [← hz, List.append_assoc]; rfl
        · by_cases h0 : ds[k.val]'(by omega) = 0
          · simp only [h0, Bool.true_and, beq_self_eq_true, _root_.ite_true] at hz ⊢
            simp only [loopCls_cont, UScalar.ofNatCore_val_eq, Array.from_val, hset]
            refine ⟨⟨by omega, hk1, pre ++ [32], by simp [hpre], ?_, ?_⟩, by omega⟩
            · simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
                List.singleton_append]
              rfl
            · rw [← hz, List.append_assoc]; rfl
          · have h0' : (ds[k.val]'(by omega) == 0) = false := by simp [h0]
            simp only [h0, h0', Bool.true_and, Bool.false_eq_true, _root_.ite_true,
              _root_.ite_false] at hz ⊢
            simp only [loopCls_cont, UScalar.ofNatCore_val_eq, Array.from_val, hset]
            refine ⟨⟨by omega, hk1, pre ++ [48 + ds[k.val]'(by omega)], by simp [hpre], ?_, ?_⟩,
              by omega⟩
            · simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
                List.singleton_append, ofNatCore_byteOf _ (show 48 + ds[k.val]'(by omega) < 256 by omega)]
            · rw [← hz, List.append_assoc]; rfl
    · simp only [h1, _root_.ite_false, loopCls_done]
      refine ⟨o, rfl, ?_⟩
      have e : p.val = 11 := by omega
      rw [e, patC_drop11] at hz
      simp only [Model.zzz, List.append_nil] at hz
      rw [ho, e, hz]
  · refine ⟨by simp, by simp [kOf], [], rfl, by simp [hout], by simp⟩

theorem zzz_length : ∀ (p : List Char) (ds : List Nat) (sup : Bool),
    (p.filter (· ≠ ',')).length ≤ ds.length → (Model.zzz p ds sup).length = p.length
  | [], _, _, _ => rfl
  | c :: p, ds, sup, h => by
    by_cases hc : c = ','
    · simp only [Model.zzz, hc, _root_.ite_true, List.length_cons]
      rw [zzz_length p ds sup (by simpa [hc] using h)]
    · simp only [Model.zzz, hc, _root_.ite_false]
      match ds, h with
      | [], h => simp [List.filter_cons, hc] at h
      | d :: ds, h =>
        simp only [List.filter_cons, hc, ne_eq, not_false_eq_true, decide_true, _root_.ite_true,
          List.length_cons, Nat.add_le_add_iff_right] at h
        dsimp only
        split_ifs <;> simp only [List.length_cons] <;> rw [zzz_length p ds _ h]

theorem zzz9 (x : Nat) (sup : Bool) : (Model.zzz patC (toDigits 10 9 x) sup).length = 11 := by
  rw [zzz_length _ _ _ (by rw [Cobol.Digits.length_toDigits]; decide)]
  rfl

theorem zzz9' (x : Nat) (sup : Bool) :
    (Model.zzz "ZZZ,ZZZ,ZZZ".toList (toDigits 10 9 x) sup).length = 11 := zzz9 x sup

theorem editAmt_length (v : Int) (plus : Bool) : (Model.editAmt v plus).length = 15 := by
  unfold Model.editAmt
  dsimp only
  split_ifs <;> simp only [List.length_cons, List.length_append, List.length_nil,
    List.length_replicate, zzz9', Nat.reduceAdd]

/-- The last three bytes of the edited amount written at positions 12, 13, 14. -/
theorem set_tail3 (s : U8) (Z : List U8) (hZ : Z.length = 11) (a x y z : U8) :
    (((s :: (Z ++ List.replicate 3 a)).set 12 x).set 13 y).set 14 z = s :: (Z ++ [x, y, z]) := by
  simp only [show (12 : Nat) = 11 + 1 from rfl, show (13 : Nat) = 12 + 1 from rfl,
    show (14 : Nat) = 13 + 1 from rfl, List.set_cons_succ]
  rw [List.set_append_right _ _ (by omega), List.set_append_right _ _ (by simp; omega),
    List.set_append_right _ _ (by simp; omega)]
  simp [hZ]

/-- The edited amount as `edit_amount` returns it. -/
def editArr (v : Int) (plus : Bool) : Array U8 15#usize :=
  Array.from ((Model.editAmt v plus).map byteOf) (by simp [editAmt_length])

set_option maxHeartbeats 2000000 in
/-- `edit_amount v plus`: the bytes of `Model.editAmt v plus`. -/
theorem edit_amount_eq (v : I64) (plus : Bool) (hmin : -9223372036854775808 < v.val) :
    cbtrn03c.edit_amount v plus = .ok (editArr v.val plus) := by
  refine eq_ok_of_wp ?_
  unfold cbtrn03c.edit_amount
  aeneas_wp [IScalar.cast_val_eq]
  have hb := v.hBounds
  simp only [IScalarTy.I64_numBits_eq, Nat.reduceSub, Int.reducePow] at hb
  by_cases hv : v.val < 0
  · have hm : (IScalar.hcast UScalarTy.U64 (IScalar.ofIntCore (ty := .I64) (-v.val) (by
        simp only [IScalarTy.I64_numBits_eq, Nat.reduceSub, Int.reducePow]; omega)) : U64).val =
        v.val.natAbs := by
      simp only [IScalar.hcast_val_eq, IScalar.ofInt_val_eq, UScalarTy.U64_numBits_eq,
        Int.reducePow]
      omega
    simp only [hv, _root_.ite_true]
    simp (disch := omega) only [dite_eq_left]
    simp only [hm, Nat.reduceEqDiff, not_false_eq_true, _root_.ite_true]
    simp only [UScalar.cast_val_eq, UScalar.ofNatCore_val_eq, UScalarTy.U8_numBits_eq,
      Nat.reducePow]
    simp (disch := omega) only [dite_eq_left]
    by_cases hz : v.val.natAbs % 100000000000 = 0
    · simp only [hz, _root_.ite_true, Except.ok.injEq, Array.eq_iff, editArr, Array.from_val, Array.repeat_val,
        Model.editAmt, hz, _root_.ite_true, List.map_replicate]
      rfl
    · simp only [hz, _root_.ite_false]
      aeneas_wp [array_update_eq, Array.from_val]
      refine wp_mono (edit_amount_loop0_spec (v.val.natAbs % 100000000000 / 100) _
        (by simp only [UScalar.ofNatCore_val_eq])) ?_
      rintro _ ⟨b, rfl, hbv⟩
      dsimp only
      refine wp_mono (edit_amount_loop1_spec _ b 45#u8 (toDigits 10 9
        (v.val.natAbs % 100000000000 / 100)) ?_ hbv (by simp)
        (fun d hd => Cobol.Digits.toDigits_lt (by decide) _ _ d hd)) ?_
      · simp [Array.repeat_val, List.replicate_succ]
      rintro _ ⟨c, rfl, hcv⟩
      dsimp only
      have hcl : c.val.length = 15 := c.property
      simp (disch := simp [hcl]) only [dite_eq_left]
      have hZ : (List.map byteOf (Model.zzz patC (toDigits 10 9
          (v.val.natAbs % 100000000000 / 100)) true)).length = 11 := by simp [zzz9]
      simp only [Except.ok.injEq, Array.eq_iff, Array.from_val, editArr, hcv]
      simp (disch := omega) only [ofNatCore_byteOf, Nat.mod_eq_of_lt,
        Nat.mod_mod_of_dvd _ (show 10 ∣ 100 by norm_num)]
      rw [set_tail3 _ _ hZ]
      simp only [Model.editAmt, hz, hv, _root_.ite_false, _root_.ite_true, decide_true,
        List.map_cons, List.map_append, List.map_nil, patC]
  · have hm : (IScalar.hcast UScalarTy.U64 v : U64).val = v.val.natAbs := by
      simp only [IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq, Int.reducePow]
      omega
    simp only [hv, _root_.ite_false]
    simp only [hm, Nat.reduceEqDiff, not_false_eq_true, _root_.ite_true]
    simp only [UScalar.cast_val_eq, UScalar.ofNatCore_val_eq, UScalarTy.U8_numBits_eq,
      Nat.reducePow]
    simp (disch := omega) only [dite_eq_left]
    cases plus
    · simp only [Bool.false_eq_true, _root_.ite_false]
      by_cases hz : v.val.natAbs % 100000000000 = 0
      · simp only [hz, _root_.ite_true, Except.ok.injEq, Array.eq_iff, editArr, Array.from_val,
          Array.repeat_val, Model.editAmt, hz, _root_.ite_true, List.map_replicate]
        rfl
      · simp only [hz, _root_.ite_false]
        aeneas_wp [array_update_eq, Array.from_val]
        refine wp_mono (edit_amount_loop0_spec (v.val.natAbs % 100000000000 / 100) _
          (by simp only [UScalar.ofNatCore_val_eq])) ?_
        rintro _ ⟨b, rfl, hbv⟩
        dsimp only
        refine wp_mono (edit_amount_loop1_spec _ b 32#u8 (toDigits 10 9
          (v.val.natAbs % 100000000000 / 100)) ?_ hbv (by simp)
          (fun d hd => Cobol.Digits.toDigits_lt (by decide) _ _ d hd)) ?_
        · simp [Array.repeat_val, List.replicate_succ]
        rintro _ ⟨c, rfl, hcv⟩
        dsimp only
        have hcl : c.val.length = 15 := c.property
        simp (disch := simp [hcl]) only [dite_eq_left]
        have hZ : (List.map byteOf (Model.zzz patC (toDigits 10 9
            (v.val.natAbs % 100000000000 / 100)) true)).length = 11 := by simp [zzz9]
        simp only [Except.ok.injEq, Array.eq_iff, Array.from_val, editArr, hcv]
        simp (disch := omega) only [ofNatCore_byteOf, Nat.mod_eq_of_lt,
          Nat.mod_mod_of_dvd _ (show 10 ∣ 100 by norm_num)]
        rw [set_tail3 _ _ hZ]
        simp only [Model.editAmt, hz, hv, _root_.ite_false, _root_.ite_true, decide_true,
          decide_false, Bool.false_eq_true, List.map_cons, List.map_append, List.map_nil, patC]
    · simp only [_root_.ite_true]
      by_cases hz : v.val.natAbs % 100000000000 = 0
      · simp only [hz, _root_.ite_true, Except.ok.injEq, Array.eq_iff, editArr, Array.from_val,
          Array.repeat_val, Model.editAmt, hz, _root_.ite_true, List.map_replicate]
        rfl
      · simp only [hz, _root_.ite_false]
        aeneas_wp [array_update_eq, Array.from_val]
        refine wp_mono (edit_amount_loop0_spec (v.val.natAbs % 100000000000 / 100) _
          (by simp only [UScalar.ofNatCore_val_eq])) ?_
        rintro _ ⟨b, rfl, hbv⟩
        dsimp only
        refine wp_mono (edit_amount_loop1_spec _ b 43#u8 (toDigits 10 9
          (v.val.natAbs % 100000000000 / 100)) ?_ hbv (by simp)
          (fun d hd => Cobol.Digits.toDigits_lt (by decide) _ _ d hd)) ?_
        · simp [Array.repeat_val, List.replicate_succ]
        rintro _ ⟨c, rfl, hcv⟩
        dsimp only
        have hcl : c.val.length = 15 := c.property
        simp (disch := simp [hcl]) only [dite_eq_left]
        have hZ : (List.map byteOf (Model.zzz patC (toDigits 10 9
            (v.val.natAbs % 100000000000 / 100)) true)).length = 11 := by simp [zzz9]
        simp only [Except.ok.injEq, Array.eq_iff, Array.from_val, editArr, hcv]
        simp (disch := omega) only [ofNatCore_byteOf, Nat.mod_eq_of_lt,
          Nat.mod_mod_of_dvd _ (show 10 ∣ 100 by norm_num)]
        rw [set_tail3 _ _ hZ]
        simp only [Model.editAmt, hz, hv, _root_.ite_false, _root_.ite_true, decide_true,
          decide_false, Bool.false_eq_true, List.map_cons, List.map_append, List.map_nil, patC]

end EquivLean.Modernize.Cbtrn03c.Rust
