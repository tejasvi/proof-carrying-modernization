import EquivLean.Modernize.Cbstm03a.RustDefs
import EquivLean.Modernize.Cbstm03a.RustRun1

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol Cobol.StmCore EquivLean.Cobol.Rec
open EquivLean.Modernize.Cbstm03a.StmBridge EquivLean.Modernize.Cbstm03a.Model

set_option maxRecDepth 20000

namespace EquivLean.Modernize.Cbstm03a.Rust

/-! ## 1. `put_unum` and `put_snum` value forms -/

private theorem set_take_zeroPad (dst : List U8) (off n k x : Nat) (b : U8)
    (hk : k < n) (hd : off + n ≤ dst.length)
    (hb : b = byteOf (48 + x / 10 ^ (n - (k + 1)) % 10)) :
    (dst.take (off + (k + 1)) ++ zeroPad (n - (k + 1)) x ++ dst.drop (off + n)).set (off + k) b =
      dst.take (off + k) ++ zeroPad (n - k) x ++ dst.drop (off + n) := by
  have hlt : off + k < dst.length := by omega
  have htl : (dst.take (off + k)).length = off + k := by simp; omega
  rw [show off + (k + 1) = (off + k) + 1 by omega, take_succ_of_lt hlt,
    List.append_assoc, List.append_assoc, List.set_append_right _ _ (by omega),
    htl, Nat.sub_self, List.singleton_append, List.set_cons_zero,
    show n - k = (n - (k + 1)) + 1 by omega, zeroPad_succ_left, hb]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

private theorem putL_of_len_eq (dst : List U8) (off len : Nat) (src : List U8)
    (hs : src.length = len) :
    putL dst off len src = dst.take off ++ src ++ dst.drop (off + len) := by
  subst hs
  unfold putL
  rw [List.take_length, Nat.sub_self, List.replicate_zero, List.append_nil]

private theorem put_unum_val (dst : Slice U8) (off n : Usize) (v : I64)
    (h : off.val + n.val ≤ dst.val.length) :
    ∃ s' : Slice U8, cbstm03a.put_unum dst off n v = .ok s' ∧
      s'.val = putL dst.val off.val n.val (zeroPad n.val v.val.natAbs) := by
  refine exists_ok_of_wp ?_
  unfold cbstm03a.put_unum
  have hb := v.hBounds
  simp only [IScalarTy.I64_numBits_eq] at hb
  by_cases hv : v.val < 0
  · have hlt : (v < 0#i64) = True := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_true]
    aeneas_wp [IScalar.cast_val_eq]
    have hmin : -170141183460469231731687303715884105728 ≤ -v.val ∧
        -v.val ≤ 170141183460469231731687303715884105727 := by omega
    rw [dite_eq_left_of_eq_true (eq_true hmin)]
    refine put_unum_loop_spec dst off n v.val.natAbs _ h ?_
    simp only [IScalar.hcast_val_eq, IScalar.ofInt_val_eq, UScalarTy.U64_numBits_eq, Int.reducePow]
    omega
  · have hlt : (v < 0#i64) = False := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_false, wp_bind, wp_ok]
    refine put_unum_loop_spec dst off n v.val.natAbs _ h ?_
    simp only [IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq, Int.reducePow]
    omega

/-- The `n` signed DISPLAY bytes of `v`: `n - 1` leading digits, then the overpunched last digit. -/
private def sdigs (n : Nat) (v : Int) : List U8 :=
  zeroPad (n - 1) (v.natAbs / 10) ++ [byteOf (overpunch (decide (v < 0)) (v.natAbs % 10))]

private theorem length_sdigs (n : Nat) (v : Int) (hn : 0 < n) :
    (sdigs n v).length = n := by
  simp only [sdigs, List.length_append, zeroPad_length, List.length_singleton]; omega

private theorem overpunch_lt (neg : Bool) (d : Nat) (hd : d < 10) : overpunch neg d < 256 := by
  unfold overpunch; split_ifs <;> omega

set_option maxHeartbeats 2000000 in
private theorem put_snum_val (dst : Slice U8) (off n : Usize) (v : I64)
    (hn : 0 < n.val) (h : off.val + n.val ≤ dst.val.length) :
    ∃ s' : Slice U8, cbstm03a.put_snum dst off n v = .ok s' ∧
      s'.val = putL dst.val off.val n.val (sdigs n.val v.val) := by
  have hd : dst.val.length ≤ Usize.max := dst.property
  have hmod : v.val.natAbs % 10 < 10 := Nat.mod_lt _ (by norm_num)
  obtain ⟨dst1, hpu, hdst1⟩ := put_unum_val dst off n v h
  have hdst1_len : dst1.val.length = dst.val.length := by
    rw [hdst1, length_putL _ _ _ _ h]
  have hget : dst1.val.getD (off.val + n.val - 1) default = byteOf (48 + v.val.natAbs % 10) := by
    rw [hdst1]
    exact putL_zeroPad_getD dst.val off.val n.val v.val.natAbs hn h
  have hset : ∀ c : U8, c = overByte v.val →
      dst1.val.set (off.val + n.val - 1) c =
        putL dst.val off.val n.val (sdigs n.val v.val) := by
    intro c hc
    rw [hdst1]
    exact putL_zeroPad_set_last dst.val off.val n.val v.val c hn h hc
  have hb_val : (byteOf (48 + v.val.natAbs % 10)).val = 48 + v.val.natAbs % 10 :=
    byteOf_val _ (by omega)
  have hmax1 : off.val + n.val ≤ Usize.max := by omega
  have h1le : 1 ≤ off.val + n.val := by omega
  have hlt_len : off.val + n.val - 1 < dst.val.length := by omega
  have h48 : 48 ≤ 48 + v.val.natAbs % 10 := by omega
  have h74a : 74 + v.val.natAbs % 10 ≤ 255 := by omega
  have h65a : 65 + v.val.natAbs % 10 ≤ 255 := by omega
  have h74b : 1 ≤ 74 + v.val.natAbs % 10 := by omega
  have h65b : 1 ≤ 65 + v.val.natAbs % 10 := by omega
  refine exists_ok_of_wp ?_
  simp only [cbstm03a.put_snum, hpu, wp_bind, wp_ok]
  aeneas_wp [slice_index_usize_getD, slice_update_eq, Slice.from_val, uscalar_ofNat_val,
    iscalar_ofInt_val, hdst1_len, hn, hmax1, h1le, hlt_len, hget, hb_val, Nat.add_sub_cancel_left,
    h48, h74a, h65a, h74b, h65b]
  split_ifs with hv hd0 hd0
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals rw [Slice.from_val]
  all_goals apply hset
  all_goals apply UScalar.eq_of_val_eq
  all_goals rw [overByte_val]
  · have : decide (v.val < 0) = true := decide_eq_true hv
    simp only [overpunch, this, hd0, uscalar_ofNat_val, _root_.ite_true]
  · have : decide (v.val < 0) = true := decide_eq_true hv
    simp only [overpunch, this, hd0, UScalar.ofNatCore_val_eq, _root_.ite_true, _root_.ite_false]; omega
  · have : decide (v.val < 0) = false := decide_eq_false hv
    simp only [overpunch, this, hd0, uscalar_ofNat_val, Bool.false_eq_true, _root_.ite_true, _root_.ite_false]
  · have : decide (v.val < 0) = false := decide_eq_false hv
    simp only [overpunch, this, hd0, UScalar.ofNatCore_val_eq, Bool.false_eq_true, _root_.ite_false]; omega

/-! ## 3. Fast step lemmas for record serializers -/

private theorem drop_append_add_len {α : Type _} (P R : List α) (n : Nat) :
    (P ++ R).drop (P.length + n) = R.drop n := by
  induction P with
  | nil => simp
  | cons _ ps ih =>
    simp only [List.cons_append, List.length_cons, Nat.add_right_comm, List.drop_succ_cons, ih]

private theorem putL_append_rep (P X : List U8) (off len R : Nat)
    (hP : P.length = off) (hX : X.length = len) (_hR : len ≤ R) :
    putL (P ++ List.replicate R 32#u8) off len X =
      (P ++ X) ++ List.replicate (R - len) 32#u8 := by
  subst hP hX
  rw [putL_of_len_eq _ _ _ _ rfl, List.take_left, drop_append_add_len, List.drop_replicate]

private theorem repeat_nil_append (n : Usize) (c : U8) :
    (Array.repeat n c).val = [] ++ List.replicate n.val c := by
  rw [Array.repeat_val, List.nil_append]

private theorem step_put_arr {α : Type} {N len : Usize} (b : Array U8 N) (off : Usize)
    (fld : Array U8 len) (P : List U8) (R : Nat)
    (k : Slice U8 → Result α) (Q : Except Error α → Prop)
    (hb : b.val = P ++ List.replicate R 32#u8)
    (hP : P.length = off.val) (hR : len.val ≤ R)
    (hk : ∀ s2 : Slice U8,
      (b.from_slice s2).val = (P ++ fld.val) ++ List.replicate (R - len.val) 32#u8 →
      (P ++ fld.val).length = off.val + len.val →
      wp (k s2) Q) :
    wp (Std.bind (cbstm03a.put b.to_slice off len fld.to_slice) k) Q := by
  have hbn : b.val.length = N.val := b.property
  have hfl : fld.val.length = len.val := fld.property
  have hbound : off.val + len.val ≤ (Array.to_slice b).val.length := by
    rw [Array.to_slice, Slice.from_val, hb, List.length_append, hP, List.length_replicate]; omega
  rw [wp_bind, put_val _ _ _ _ hbound, wp_ok]
  have hL : putL (Array.to_slice b).val off.val len.val (Array.to_slice fld).val =
      (P ++ fld.val) ++ List.replicate (R - len.val) 32#u8 := by
    rw [Array.to_slice, Slice.from_val, Array.to_slice, Slice.from_val, hb]
    exact putL_append_rep P fld.val off.val len.val R hP hfl hR
  refine hk _ ?_ (by rw [List.length_append, hP, hfl])
  rw [Array.from_slice_val _ _ (by
    rw [Slice.from_val, hL, List.length_append, List.length_append, List.length_replicate, hP, hfl]
    rw [hb, List.length_append, hP, List.length_replicate] at hbn
    omega), Slice.from_val, hL]

private theorem last_put_arr {N len : Usize} (b : Array U8 N) (off : Usize)
    (fld : Array U8 len) (P : List U8) (R : Nat)
    (Q : Except Error (Array U8 N) → Prop)
    (hb : b.val = P ++ List.replicate R 32#u8)
    (hP : P.length = off.val) (hR : len.val = R)
    (hQ : ∀ b' : Array U8 N, b'.val = P ++ fld.val → Q (.ok b')) :
    wp (Std.bind (cbstm03a.put b.to_slice off len fld.to_slice)
      (fun s2 => Result.ok (b.from_slice s2))) Q := by
  refine step_put_arr b off fld P R (fun s2 => Result.ok (b.from_slice s2)) Q hb hP (by omega) ?_
  intro s2 hb' _
  rw [hR, Nat.sub_self, List.replicate_zero, List.append_nil] at hb'
  rw [wp_ok]
  exact hQ (b.from_slice s2) hb'

private theorem step_put_unum {α : Type} {N : Usize} (b : Array U8 N) (off len : Usize)
    (v : I64) (P : List U8) (R : Nat)
    (k : Slice U8 → Result α) (Q : Except Error α → Prop)
    (hb : b.val = P ++ List.replicate R 32#u8)
    (hP : P.length = off.val) (hR : len.val ≤ R)
    (hk : ∀ s1 : Slice U8,
      (b.from_slice s1).val = (P ++ zeroPad len.val v.val.natAbs) ++ List.replicate (R - len.val) 32#u8 →
      (P ++ zeroPad len.val v.val.natAbs).length = off.val + len.val →
      wp (k s1) Q) :
    wp (Std.bind (cbstm03a.put_unum b.to_slice off len v) k) Q := by
  have hbn : b.val.length = N.val := b.property
  have hzl : (zeroPad len.val v.val.natAbs).length = len.val := zeroPad_length _ _
  have hbound : off.val + len.val ≤ (Array.to_slice b).val.length := by
    rw [Array.to_slice, Slice.from_val, hb, List.length_append, hP, List.length_replicate]; omega
  obtain ⟨s1, hs1, hs1v⟩ := put_unum_val b.to_slice off len v hbound
  rw [wp_bind, hs1, wp_ok]
  have hL : putL (Array.to_slice b).val off.val len.val (zeroPad len.val v.val.natAbs) =
      (P ++ zeroPad len.val v.val.natAbs) ++ List.replicate (R - len.val) 32#u8 := by
    rw [Array.to_slice, Slice.from_val, hb]
    exact putL_append_rep P _ off.val len.val R hP hzl hR
  refine hk s1 ?_ (by rw [List.length_append, hP, hzl])
  rw [Array.from_slice_val _ _ (by
    rw [hs1v, hL, List.length_append, List.length_append, List.length_replicate, hP, hzl]
    rw [hb, List.length_append, hP, List.length_replicate] at hbn
    omega), hs1v, hL]

private theorem step_put_snum {α : Type} {N : Usize} (b : Array U8 N) (off len : Usize)
    (v : I64) (P : List U8) (R : Nat)
    (k : Slice U8 → Result α) (Q : Except Error α → Prop)
    (hb : b.val = P ++ List.replicate R 32#u8)
    (hP : P.length = off.val) (hn : 0 < len.val) (hR : len.val ≤ R)
    (hk : ∀ s1 : Slice U8,
      (b.from_slice s1).val = (P ++ sdigs len.val v.val) ++ List.replicate (R - len.val) 32#u8 →
      (P ++ sdigs len.val v.val).length = off.val + len.val →
      wp (k s1) Q) :
    wp (Std.bind (cbstm03a.put_snum b.to_slice off len v) k) Q := by
  have hbn : b.val.length = N.val := b.property
  have hsl : (sdigs len.val v.val).length = len.val := length_sdigs _ _ hn
  have hbound : off.val + len.val ≤ (Array.to_slice b).val.length := by
    rw [Array.to_slice, Slice.from_val, hb, List.length_append, hP, List.length_replicate]; omega
  obtain ⟨s1, hs1, hs1v⟩ := put_snum_val b.to_slice off len v hn hbound
  rw [wp_bind, hs1, wp_ok]
  have hL : putL (Array.to_slice b).val off.val len.val (sdigs len.val v.val) =
      (P ++ sdigs len.val v.val) ++ List.replicate (R - len.val) 32#u8 := by
    rw [Array.to_slice, Slice.from_val, hb]
    exact putL_append_rep P _ off.val len.val R hP hsl hR
  refine hk s1 ?_ (by rw [List.length_append, hP, hsl])
  rw [Array.from_slice_val _ _ (by
    rw [hs1v, hL, List.length_append, List.length_append, List.length_replicate, hP, hsl]
    rw [hb, List.length_append, hP, List.length_replicate] at hbn
    omega), hs1v, hL]

/-! ## 4. Encoding bridge for `latL (S.encode (S.vals r))` -/

private theorem latL_map_ebc (l : List U8) :
    latL (l.map fun u => ebcdicOfLatin1 u.val) = l := by
  induction l with
  | nil => rfl
  | cons u us ih =>
    simp only [latL, List.map_cons]
    refine congrArg₂ List.cons ?_ ih
    apply UScalar.eq_of_val_eq
    rw [lat_val, cp037_roundtrip ⟨u.val, by have := u.hBounds; simpa using this⟩]

private theorem latL_encodeNum_unsigned' {fmt : NumFmt}
    (hu : fmt.usage = .display) (hs : fmt.signed = false) (hd : 0 < fmt.digits) (v : Int) :
    latL (encodeNum {} fmt v) = zeroPad fmt.digits v.natAbs := by
  rw [latL_eq_u8Line, text_unsigned hu hs hd, u8Line, zeroPad]

private theorem latL_encodeNum_signed' {fmt : NumFmt}
    (hu : fmt.usage = .display) (hs : fmt.signed = true)
    (hsep : fmt.signSep = false) (hlead : fmt.signLead = false) (v : Int) :
    latL (encodeNum {} fmt v) = sdigs fmt.digits v := by
  rw [latL_eq_u8Line, text_signed hu hs hsep hlead, u8Line, List.map_append,
    List.map_singleton, sdigs, zeroPad]

/-! ## 5. Record serializers: `ser_trnx`, `ser_xref`, `ser_cust`, `ser_acct` -/

theorem ser_trnx_val (r : cbstm03a.TrnxRecord) :
    ∃ b : Array U8 350#usize, cbstm03a.ser_trnx r = .ok b ∧
      b.val = latL (TrnxRecord.encode (TrnxRecord.vals r)) := by
  refine exists_ok_of_wp ?_
  dsimp only [cbstm03a.ser_trnx]
  simp only [lift, bind_ok, Aeneas.Std.uncurry_apply_pair, Array.to_slice_mut]
  refine step_put_arr _ 0#usize r.trnx_card_num [] 350 _ _
    (repeat_nil_append 350#usize 32#u8) rfl (by decide) (fun _ hb1 hP1 => ?_)
  refine step_put_arr _ 16#usize r.trnx_id _ 334 _ _
    hb1 hP1 (by decide) (fun _ hb2 hP2 => ?_)
  refine step_put_arr _ 32#usize r.trnx_type_cd _ 318 _ _
    hb2 hP2 (by decide) (fun _ hb3 hP3 => ?_)
  refine step_put_unum _ 34#usize 4#usize r.trnx_cat_cd _ 316 _ _
    hb3 hP3 (by decide) (fun _ hb4 hP4 => ?_)
  refine step_put_arr _ 38#usize r.trnx_source _ 312 _ _
    hb4 hP4 (by decide) (fun _ hb5 hP5 => ?_)
  refine step_put_arr _ 48#usize r.trnx_desc _ 302 _ _
    hb5 hP5 (by decide) (fun _ hb6 hP6 => ?_)
  refine step_put_snum _ 148#usize 11#usize r.trnx_amt _ 202 _ _
    hb6 hP6 (by decide) (by decide) (fun _ hb7 hP7 => ?_)
  refine step_put_unum _ 159#usize 9#usize r.trnx_merchant_id _ 191 _ _
    hb7 hP7 (by decide) (fun _ hb8 hP8 => ?_)
  refine step_put_arr _ 168#usize r.trnx_merchant_name _ 182 _ _
    hb8 hP8 (by decide) (fun _ hb9 hP9 => ?_)
  refine step_put_arr _ 218#usize r.trnx_merchant_city _ 132 _ _
    hb9 hP9 (by decide) (fun _ hb10 hP10 => ?_)
  refine step_put_arr _ 268#usize r.trnx_merchant_zip _ 82 _ _
    hb10 hP10 (by decide) (fun _ hb11 hP11 => ?_)
  refine step_put_arr _ 278#usize r.trnx_orig_ts _ 72 _ _
    hb11 hP11 (by decide) (fun _ hb12 hP12 => ?_)
  refine step_put_arr _ 304#usize r.trnx_proc_ts _ 46 _ _
    hb12 hP12 (by decide) (fun _ hb13 hP13 => ?_)
  refine last_put_arr _ 330#usize r.filler1 _ 20 _
    hb13 hP13 rfl (fun b14 hb14 => ⟨b14, rfl, ?_⟩)
  rw [hb14]
  simp only [TrnxRecord.vals, Schema.encode, List.zip_cons_cons,
    List.zip_nil_left, List.flatMap_cons, List.flatMap_nil, Field.encode,
    latL_append, latL_map_ebc, List.nil_append, List.append_nil, List.append_assoc]
  simp (disch := decide) only [latL_encodeNum_unsigned', latL_encodeNum_signed']
  simp only [uscalar_ofNat_val]

theorem ser_trnx_eq (r : cbstm03a.TrnxRecord) (_hr : TrnxRecord.Valid (TrnxRecord.vals r)) :
    ∃ b : Array U8 350#usize, cbstm03a.ser_trnx r = .ok b ∧
      b.val = latL (TrnxRecord.encode (TrnxRecord.vals r)) :=
  ser_trnx_val r

theorem ser_xref_val (r : cbstm03a.CardXrefRecord) :
    ∃ b : Array U8 50#usize, cbstm03a.ser_xref r = .ok b ∧
      b.val = latL (CardXrefRecord.encode (CardXrefRecord.vals r)) := by
  refine exists_ok_of_wp ?_
  dsimp only [cbstm03a.ser_xref]
  simp only [lift, bind_ok, Aeneas.Std.uncurry_apply_pair, Array.to_slice_mut]
  refine step_put_arr _ 0#usize r.xref_card_num [] 50 _ _
    (repeat_nil_append 50#usize 32#u8) rfl (by decide) (fun _ hb1 hP1 => ?_)
  refine step_put_unum _ 16#usize 9#usize r.xref_cust_id _ 34 _ _
    hb1 hP1 (by decide) (fun _ hb2 hP2 => ?_)
  refine step_put_unum _ 25#usize 11#usize r.xref_acct_id _ 25 _ _
    hb2 hP2 (by decide) (fun _ hb3 hP3 => ?_)
  refine last_put_arr _ 36#usize r.filler1 _ 14 _
    hb3 hP3 rfl (fun b4 hb4 => ⟨b4, rfl, ?_⟩)
  rw [hb4]
  simp only [CardXrefRecord.vals, Schema.encode, List.zip_cons_cons,
    List.zip_nil_left, List.flatMap_cons, List.flatMap_nil, Field.encode,
    latL_append, latL_map_ebc, List.nil_append, List.append_nil, List.append_assoc]
  simp (disch := decide) only [latL_encodeNum_unsigned']
  simp only [uscalar_ofNat_val]

theorem ser_xref_eq (r : cbstm03a.CardXrefRecord) (_hr : CardXrefRecord.Valid (CardXrefRecord.vals r)) :
    ∃ b : Array U8 50#usize, cbstm03a.ser_xref r = .ok b ∧
      b.val = latL (CardXrefRecord.encode (CardXrefRecord.vals r)) :=
  ser_xref_val r

theorem ser_cust_val (r : cbstm03a.CustomerRecord) :
    ∃ b : Array U8 500#usize, cbstm03a.ser_cust r = .ok b ∧
      b.val = latL (CustomerRecord.encode (CustomerRecord.vals r)) := by
  refine exists_ok_of_wp ?_
  dsimp only [cbstm03a.ser_cust]
  simp only [lift, bind_ok, Aeneas.Std.uncurry_apply_pair, Array.to_slice_mut]
  refine step_put_unum _ 0#usize 9#usize r.cust_id [] 500 _ _
    (repeat_nil_append 500#usize 32#u8) rfl (by decide) (fun _ hb1 hP1 => ?_)
  refine step_put_arr _ 9#usize r.cust_first_name _ 491 _ _
    hb1 hP1 (by decide) (fun _ hb2 hP2 => ?_)
  refine step_put_arr _ 34#usize r.cust_middle_name _ 466 _ _
    hb2 hP2 (by decide) (fun _ hb3 hP3 => ?_)
  refine step_put_arr _ 59#usize r.cust_last_name _ 441 _ _
    hb3 hP3 (by decide) (fun _ hb4 hP4 => ?_)
  refine step_put_arr _ 84#usize r.cust_addr_line_1 _ 416 _ _
    hb4 hP4 (by decide) (fun _ hb5 hP5 => ?_)
  refine step_put_arr _ 134#usize r.cust_addr_line_2 _ 366 _ _
    hb5 hP5 (by decide) (fun _ hb6 hP6 => ?_)
  refine step_put_arr _ 184#usize r.cust_addr_line_3 _ 316 _ _
    hb6 hP6 (by decide) (fun _ hb7 hP7 => ?_)
  refine step_put_arr _ 234#usize r.cust_addr_state_cd _ 266 _ _
    hb7 hP7 (by decide) (fun _ hb8 hP8 => ?_)
  refine step_put_arr _ 236#usize r.cust_addr_country_cd _ 264 _ _
    hb8 hP8 (by decide) (fun _ hb9 hP9 => ?_)
  refine step_put_arr _ 239#usize r.cust_addr_zip _ 261 _ _
    hb9 hP9 (by decide) (fun _ hb10 hP10 => ?_)
  refine step_put_arr _ 249#usize r.cust_phone_num_1 _ 251 _ _
    hb10 hP10 (by decide) (fun _ hb11 hP11 => ?_)
  refine step_put_arr _ 264#usize r.cust_phone_num_2 _ 236 _ _
    hb11 hP11 (by decide) (fun _ hb12 hP12 => ?_)
  refine step_put_unum _ 279#usize 9#usize r.cust_ssn _ 221 _ _
    hb12 hP12 (by decide) (fun _ hb13 hP13 => ?_)
  refine step_put_arr _ 288#usize r.cust_govt_issued_id _ 212 _ _
    hb13 hP13 (by decide) (fun _ hb14 hP14 => ?_)
  refine step_put_arr _ 308#usize r.cust_dob_yyyymmdd _ 192 _ _
    hb14 hP14 (by decide) (fun _ hb15 hP15 => ?_)
  refine step_put_arr _ 318#usize r.cust_eft_account_id _ 182 _ _
    hb15 hP15 (by decide) (fun _ hb16 hP16 => ?_)
  refine step_put_arr _ 328#usize r.cust_pri_card_holder_ind _ 172 _ _
    hb16 hP16 (by decide) (fun _ hb17 hP17 => ?_)
  refine step_put_unum _ 329#usize 3#usize r.cust_fico_credit_score _ 171 _ _
    hb17 hP17 (by decide) (fun _ hb18 hP18 => ?_)
  refine last_put_arr _ 332#usize r.filler1 _ 168 _
    hb18 hP18 rfl (fun b19 hb19 => ⟨b19, rfl, ?_⟩)
  rw [hb19]
  simp only [CustomerRecord.vals, Schema.encode, List.zip_cons_cons,
    List.zip_nil_left, List.flatMap_cons, List.flatMap_nil, Field.encode,
    latL_append, latL_map_ebc, List.nil_append, List.append_nil, List.append_assoc]
  simp (disch := decide) only [latL_encodeNum_unsigned']
  simp only [uscalar_ofNat_val]

theorem ser_cust_eq (r : cbstm03a.CustomerRecord) (_hr : CustomerRecord.Valid (CustomerRecord.vals r)) :
    ∃ b : Array U8 500#usize, cbstm03a.ser_cust r = .ok b ∧
      b.val = latL (CustomerRecord.encode (CustomerRecord.vals r)) :=
  ser_cust_val r

theorem ser_acct_val (r : cbstm03a.AccountRecord) :
    ∃ b : Array U8 300#usize, cbstm03a.ser_acct r = .ok b ∧
      b.val = latL (AccountRecord.encode (AccountRecord.vals r)) := by
  refine exists_ok_of_wp ?_
  dsimp only [cbstm03a.ser_acct]
  simp only [lift, bind_ok, Aeneas.Std.uncurry_apply_pair, Array.to_slice_mut]
  refine step_put_unum _ 0#usize 11#usize r.acct_id [] 300 _ _
    (repeat_nil_append 300#usize 32#u8) rfl (by decide) (fun _ hb1 hP1 => ?_)
  refine step_put_arr _ 11#usize r.acct_active_status _ 289 _ _
    hb1 hP1 (by decide) (fun _ hb2 hP2 => ?_)
  refine step_put_snum _ 12#usize 12#usize r.acct_curr_bal _ 288 _ _
    hb2 hP2 (by decide) (by decide) (fun _ hb3 hP3 => ?_)
  refine step_put_snum _ 24#usize 12#usize r.acct_credit_limit _ 276 _ _
    hb3 hP3 (by decide) (by decide) (fun _ hb4 hP4 => ?_)
  refine step_put_snum _ 36#usize 12#usize r.acct_cash_credit_limit _ 264 _ _
    hb4 hP4 (by decide) (by decide) (fun _ hb5 hP5 => ?_)
  refine step_put_arr _ 48#usize r.acct_open_date _ 252 _ _
    hb5 hP5 (by decide) (fun _ hb6 hP6 => ?_)
  refine step_put_arr _ 58#usize r.acct_expiraion_date _ 242 _ _
    hb6 hP6 (by decide) (fun _ hb7 hP7 => ?_)
  refine step_put_arr _ 68#usize r.acct_reissue_date _ 232 _ _
    hb7 hP7 (by decide) (fun _ hb8 hP8 => ?_)
  refine step_put_snum _ 78#usize 12#usize r.acct_curr_cyc_credit _ 222 _ _
    hb8 hP8 (by decide) (by decide) (fun _ hb9 hP9 => ?_)
  refine step_put_snum _ 90#usize 12#usize r.acct_curr_cyc_debit _ 210 _ _
    hb9 hP9 (by decide) (by decide) (fun _ hb10 hP10 => ?_)
  refine step_put_arr _ 102#usize r.acct_addr_zip _ 198 _ _
    hb10 hP10 (by decide) (fun _ hb11 hP11 => ?_)
  refine step_put_arr _ 112#usize r.acct_group_id _ 188 _ _
    hb11 hP11 (by decide) (fun _ hb12 hP12 => ?_)
  refine last_put_arr _ 122#usize r.filler1 _ 178 _
    hb12 hP12 rfl (fun b13 hb13 => ⟨b13, rfl, ?_⟩)
  rw [hb13]
  simp only [AccountRecord.vals, Schema.encode, List.zip_cons_cons,
    List.zip_nil_left, List.flatMap_cons, List.flatMap_nil, Field.encode,
    latL_append, latL_map_ebc, List.nil_append, List.append_nil, List.append_assoc]
  simp (disch := decide) only [latL_encodeNum_unsigned', latL_encodeNum_signed']
  simp only [uscalar_ofNat_val]

theorem ser_acct_eq (r : cbstm03a.AccountRecord) (_hr : AccountRecord.Valid (AccountRecord.vals r)) :
    ∃ b : Array U8 300#usize, cbstm03a.ser_acct r = .ok b ∧
      b.val = latL (AccountRecord.encode (AccountRecord.vals r)) :=
  ser_acct_val r

/-! ## 6. `digits11` and `zoned` on 11-digit zero-padded buffers -/

open Cobol.Digits (toDigits)

private theorem digits11_of_nonneg (v : I64) (hv0 : 0 ≤ v.val) (hv11 : v.val.natAbs < 10 ^ 11) :
    ∃ d : Array U8 11#usize, cbstm03a.digits11 v = .ok d ∧
      d.val = zeroPad 11 v.val.natAbs := by
  refine exists_ok_of_wp ?_
  unfold cbstm03a.digits11
  have hlt : (v < 0#i64) = False := by simp [IScalar.lt_equiv]; omega
  simp only [hlt, _root_.ite_false, wp_bind, wp_ok]
  aeneas_wp []
  simp (disch := omega) only [ite_eq_left]
  refine digits11_loop_spec v.val.natAbs _ ?_
  have hv_lt : v.val < 100000000000 := by omega
  rw [iscalar_srem_val, iscalar_ofInt_val, Int.tmod_eq_emod_of_nonneg hv0,
    Int.emod_eq_of_lt hv0 hv_lt]
  omega

private theorem zoned_loop_body_digit (b : Slice U8) (n : Usize) (v : I64) (neg : Bool) (i : Usize)
    (c : U8) (hi : i < n) (hidx : Slice.index_usize b i = .ok c)
    (hc1 : c >= 48#u8) (hc2 : c <= 57#u8) :
    cbstm03a.zoned_loop.body b n v neg i = (do
      let i1 ← c - 48#u8
      let d1 ← lift (UScalar.hcast .I64 i1)
      let i2 ← v * 10#i64
      let v1 ← i2 + d1
      let i3 ← i + 1#usize
      Result.ok (ControlFlow.cont (v1, neg, i3))) := by
  unfold cbstm03a.zoned_loop.body
  rw [ite_eq_left hi, hidx, bind_ok, ite_eq_left hc1, ite_eq_left hc2]
  simp only [Std.bind_assoc, lift, bind_ok, Aeneas.Std.uncurry_apply_pair]

private theorem zoned_loop_body_done (b : Slice U8) (n : Usize) (v : I64) (neg : Bool) (i : Usize)
    (hi : ¬ i < n) :
    cbstm03a.zoned_loop.body b n v neg i = Result.ok (ControlFlow.done (v, neg)) := by
  unfold cbstm03a.zoned_loop.body
  rw [ite_eq_right hi]

private theorem zeroPad_index_usize (b : Slice U8) (n x : Nat) (i : Usize)
    (hb : b.val = zeroPad n x) (hi : i.val < n) :
    Slice.index_usize b i = .ok (byteOf (48 + x / 10 ^ (n - 1 - i.val) % 10)) := by
  have hbl : i.val < b.val.length := by rw [hb, zeroPad_length]; exact hi
  rw [Slice.index_usize, Slice.getElem?_Usize_eq, List.getElem?_eq_getElem hbl]
  dsimp only
  congr 1
  rw [List.getElem_of_eq hb hbl]
  simp only [zeroPad, zpad, List.getElem_map, toDigits_getElem n x i.val hi]

private theorem zoned_loop_zeroPad11_spec (b : Slice U8) (x : Nat)
    (hx : x < 10 ^ 11) (hb : b.val = zeroPad 11 x) :
    wp (cbstm03a.zoned_loop b 0#i64 false (Slice.len b) 0#usize)
      (fun o => ∃ r : I64 × Bool, o = .ok r ∧ r.2 = false ∧ r.1.val = (x : Int)) := by
  have hbl : b.val.length = 11 := by rw [hb, zeroPad_length]
  have hmax0 : b.val.length ≤ Usize.max := b.property
  simp only [cbstm03a.zoned_loop]
  refine wp_loop (loop_shape _)
    (fun (s : I64 × Bool × Usize) =>
      s.2.2.val ≤ 11 ∧ s.2.1 = false ∧
      s.1.val = ((x / 10 ^ (11 - s.2.2.val) : Nat) : Int))
    (fun s => 11 - s.2.2.val) ?_ _ ?_
  · rintro ⟨v, neg, i⟩ ⟨hi, hneg, hv⟩
    simp only at hi hneg hv
    by_cases hlt : i.val < 11
    · have hlt_u : i < Slice.len b := by simp [hbl, UScalar.lt_equiv, hlt]
      let d := x / 10 ^ (11 - 1 - i.val) % 10
      have hd10 : d < 10 := Nat.mod_lt _ (by norm_num)
      have hidx : Slice.index_usize b i = .ok (byteOf (48 + d)) :=
        zeroPad_index_usize b 11 x i hb hlt
      have hc_val : (byteOf (48 + d)).val = 48 + d := byteOf_val _ (by omega)
      have hc1 : byteOf (48 + d) >= 48#u8 := by simp [ge_iff_le, UScalar.le_equiv, hc_val]
      have hc2 : byteOf (48 + d) <= 57#u8 := by simp [UScalar.le_equiv, hc_val]; omega
      rw [zoned_loop_body_digit b (Slice.len b) v neg i (byteOf (48 + d)) hlt_u hidx hc1 hc2]
      have hstep : (x / 10 ^ (11 - i.val)) * 10 + d = x / 10 ^ (11 - (i.val + 1)) := by
        have hpow : 11 - i.val = (11 - 1 - i.val) + 1 := by omega
        have hpow2 : 11 - (i.val + 1) = 11 - 1 - i.val := by omega
        rw [hpow, hpow2, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
        have := Nat.div_add_mod (x / 10 ^ (11 - 1 - i.val)) 10
        omega
      have hv_le : x / 10 ^ (11 - i.val) ≤ x := Nat.div_le_self _ _
      aeneas_wp [hc_val, UScalar.hcast_val_of_numBits_lt]
      simp (disch := omega) only [dite_eq_left, ite_eq_left, loopCls_cont,
        UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq]
      refine ⟨⟨by omega, hneg, ?_⟩, by omega⟩
      rw [hv, Nat.add_sub_cancel_left]
      exact_mod_cast hstep
    · have hnlt_u : ¬ i < Slice.len b := by simp [hbl, UScalar.lt_equiv]; omega
      rw [zoned_loop_body_done b (Slice.len b) v neg i hnlt_u]
      simp only [wp_ok, loopCls_done]
      have hi11 : i.val = 11 := by omega
      refine ⟨(v, neg), rfl, hneg, ?_⟩
      rw [hv, hi11, Nat.sub_self, Nat.pow_zero, Nat.div_one]
  · refine ⟨by simp, rfl, ?_⟩
    simp only [uscalar_ofNat_val, iscalar_ofInt_val, Nat.sub_zero, Nat.div_eq_of_lt hx, Int.natCast_zero]

private theorem zoned_zeroPad11_eq (b : Slice U8) (x : Nat)
    (hx : x < 10 ^ 11) (hb : b.val = zeroPad 11 x) :
    ∃ v : I64, cbstm03a.zoned b = .ok v ∧ v.val = (x : Int) := by
  obtain ⟨⟨v, neg⟩, hloop, rfl, hv⟩ := exists_ok_of_wp (zoned_loop_zeroPad11_spec b x hx hb)
  refine ⟨v, ?_, hv⟩
  dsimp only [cbstm03a.zoned]
  rw [hloop, bind_ok]
  rfl

private theorem zoned_digits11_of_nonneg (v : I64) (hv0 : 0 ≤ v.val) (hv11 : v.val.natAbs < 10 ^ 11) :
    ∃ (rk : Array U8 11#usize) (i1 : I64),
      cbstm03a.digits11 v = .ok rk ∧
      cbstm03a.zoned rk.to_slice = .ok i1 ∧
      i1 = v := by
  obtain ⟨rk, hrk, hrkv⟩ := digits11_of_nonneg v hv0 hv11
  obtain ⟨i1, hi1, hi1v⟩ := zoned_zeroPad11_eq rk.to_slice v.val.natAbs hv11
    (by simp [Array.to_slice, hrkv])
  refine ⟨rk, i1, hrk, hi1, ?_⟩
  apply IScalar.eq_of_val_eq
  omega

/-! ## 7. Keyed lookup loops (`call_m03b_loop0` .. `call_m03b_loop3`) -/

private theorem index_usize_getD {α : Type _} [Inhabited α] {n : Usize} (a : Array α n) (i : Usize)
    (h : i.val < a.val.length) : Array.index_usize a i = .ok (a.val.getD i.val default) := by
  rw [array_index_usize_eq, dite_eq_left h, List.getD_eq_getElem _ _ h]

private theorem call_m03b_loop0_eq (a : Array U8 25#usize) :
    ∃ key1 : Array U8 9#usize,
      cbstm03a.call_m03b_loop0 a 9#usize (Array.repeat 9#usize 32#u8) 0#usize = .ok key1 ∧
      key1.val = a.val.take 9 := by
  have ha : a.val.length = 25 := a.property
  refine exists_ok_of_wp ?_
  simp only [cbstm03a.call_m03b_loop0]
  refine wp_loop (loop_shape _)
    (fun (s : Array U8 9#usize × Usize) =>
      s.2.val ≤ 9 ∧
      s.1.val = a.val.take s.2.val ++ List.replicate (9 - s.2.val) 32#u8)
    (fun s => 9 - s.2.val) ?_ _ ?_
  · rintro ⟨key, i⟩ ⟨hi, hkey⟩
    simp only at hi hkey
    have hkl : key.val.length = 9 := key.property
    aeneas_wp [rust_loop_body, array_index_usize_eq, array_update_eq, ha, hkl]
    by_cases hlt : i.val < 9
    · have hlt25 : i.val < 25 := by omega
      have hmax : i.val + 1 ≤ Usize.max := by scalar_tac
      have htl : (a.val.take i.val).length = i.val := by simp [ha]; omega
      simp only [hlt, hlt25, hmax, _root_.dite_true, _root_.ite_true,
        loopCls_cont, UScalar.ofNatCore_val_eq, Array.from_val]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hkey, show 9 - i.val = (9 - (i.val + 1)) + 1 by omega,
        List.replicate_succ, List.set_append_right _ _ (by omega), htl, Nat.sub_self,
        List.set_cons_zero, take_succ_of_lt (by omega)]
      simp only [List.append_assoc, List.singleton_append]
    · simp only [hlt, _root_.ite_false, loopCls_done]
      have hi9 : i.val = 9 := by omega
      refine ⟨key, rfl, ?_⟩
      rw [hkey, hi9, Nat.sub_self, List.replicate_zero, List.append_nil]
  · simp

private theorem call_m03b_loop2_eq (a : Array U8 25#usize) :
    ∃ key1 : Array U8 11#usize,
      cbstm03a.call_m03b_loop2 a 11#usize (Array.repeat 11#usize 48#u8) 0#usize = .ok key1 ∧
      key1.val = a.val.take 11 := by
  have ha : a.val.length = 25 := a.property
  have hidxG : ∀ j : Usize, j.val < a.val.length → Array.index_usize a j = .ok (a.val.getD j.val default) :=
    fun j hj => index_usize_getD _ _ hj
  generalize a.val = ks at ha hidxG ⊢
  have hK : (ks.take 11).length = 11 := by simp [ha]
  refine exists_ok_of_wp ?_
  simp only [cbstm03a.call_m03b_loop2]
  refine wp_loop (loop_shape _)
    (fun (s : Array U8 11#usize × Usize) =>
      s.2.val ≤ 11 ∧
      s.1.val = List.replicate (11 - s.2.val) 48#u8 ++ (ks.take 11).drop (11 - s.2.val))
    (fun s => 11 - s.2.val) ?_ _ ?_
  · rintro ⟨key, i⟩ ⟨hi, hkey⟩
    simp only at hi hkey
    have hkl : key.val.length = 11 := key.property
    by_cases hlt : i.val < 11
    · have hle10 : i.val ≤ 10 := by omega
      have hidx25 : 10 - i.val < ks.length := by omega
      have hidx11 : 10 - i.val < key.val.length := by omega
      have hmax : i.val + 1 ≤ Usize.max := by scalar_tac
      have hidx : Array.index_usize a (UScalar.ofNatCore (11 - 1 - i.val) (by scalar_tac)) =
          .ok (ks.getD (10 - i.val) default) := by
        rw [hidxG _ (by rw [UScalar.ofNatCore_val_eq]; omega), UScalar.ofNatCore_val_eq]
      aeneas_wp [rust_loop_body, array_update_eq, hlt, hle10, hidx11, hmax, hidx]
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq, Array.from_val]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      obtain ⟨k, hk⟩ : ∃ k, 11 - i.val = k + 1 := ⟨10 - i.val, by omega⟩
      have hk10 : 10 - i.val = k := by omega
      have hk11 : 11 - (i.val + 1) = k := by omega
      have hget : ks.getD k default = (ks.take 11)[k]'(by omega) := by
        rw [List.getElem_take, List.getD_eq_getElem _ _ (by omega)]
      rw [hkey, show 11 - 1 - i.val = k by omega, hk, hk11, set_replicate_end, hget,
        List.drop_eq_getElem_cons (l := ks.take 11) (i := k) (by omega)]
      simp only [List.append_assoc, List.singleton_append]
    · aeneas_wp [rust_loop_body, hlt]
      simp only [loopCls_done]
      have hi11 : i.val = 11 := by omega
      refine ⟨key, rfl, ?_⟩
      rw [hkey, hi11, Nat.sub_self, List.replicate_zero, List.nil_append, List.drop_zero]
  · simp [hK]

private theorem cust_id_match_eq (r : cbstm03a.CustomerRecord)
    (hr : CustomerRecord.Valid (CustomerRecord.vals r))
    (cid : Int) (hcid0 : 0 ≤ cid) (hcid9 : cid.natAbs < 10 ^ 9) :
    decide (zeroPad 9 r.cust_id.val.natAbs = zeroPad 9 cid.natAbs) =
      (numOf ((CustomerRecord.vals r).getD 0 default) == cid) := by
  have hcid_holds : ({ digits := 9 } : NumFmt).Holds {} cid :=
    (EquivLean.Modernize.GlueKit.holds_display rfl).mpr ⟨hcid9, fun _ => hcid0⟩
  have hbeq := cust_key_beq hr hcid_holds
  have hcf := (cust_fields hr).1
  have h0 : numOf ((CustomerRecord.vals r).getD 0 default) = r.cust_id.val := rfl
  simp only [Sem.keyOf, List.drop_zero, hcf, h0] at hbeq
  rw [h0, ← hbeq, ← latL_digitChars 9 r.cust_id.val.natAbs, ← latL_digitChars 9 cid.natAbs]
  cases h : decide (Sem.digitChars {} 9 r.cust_id.val.natAbs = Sem.digitChars {} 9 cid.natAbs)
  · have hne : Sem.digitChars {} 9 r.cust_id.val.natAbs ≠ Sem.digitChars {} 9 cid.natAbs :=
      of_decide_eq_false h
    rw [decide_eq_false (mt latL_inj.mp hne), beq_eq_false_iff_ne.mpr hne]
  · have heq : Sem.digitChars {} 9 r.cust_id.val.natAbs = Sem.digitChars {} 9 cid.natAbs :=
      of_decide_eq_true h
    rw [decide_eq_true (latL_inj.mpr heq), beq_iff_eq.mpr heq]

private theorem put_unum_repeat9 (v : I64) :
    ∃ s1 : Slice U8,
      cbstm03a.put_unum (Array.repeat 9#usize 48#u8).to_slice 0#usize 9#usize v = .ok s1 ∧
      ((Array.repeat 9#usize 48#u8).from_slice s1).val = zeroPad 9 v.val.natAbs := by
  obtain ⟨s1, hs1, hs1v⟩ := put_unum_val (Array.repeat 9#usize 48#u8).to_slice 0#usize 9#usize v
    (by simp [Array.to_slice, Array.repeat_val])
  have hL : s1.val = zeroPad 9 v.val.natAbs := by
    rw [hs1v]
    simp only [uscalar_ofNat_val, Array.to_slice, Slice.from_val, Array.repeat_val,
      putL_of_len_eq _ _ _ _ (zeroPad_length _ _), List.take_zero, List.nil_append,
      Nat.zero_add, List.drop_replicate, Nat.sub_self, List.replicate_zero, List.append_nil]
  refine ⟨s1, hs1, ?_⟩
  rw [Array.from_slice_val _ _ (by rw [hL, zeroPad_length]; rfl), hL]

private theorem put_repeat1000 {L : Usize} (img : Array U8 L) (hL : L.val ≤ 1000) :
    ∃ s : Slice U8,
      cbstm03a.put (Array.repeat 1000#usize 32#u8).to_slice 0#usize L img.to_slice = .ok s ∧
      ((Array.repeat 1000#usize 32#u8).from_slice s).val =
        img.val ++ List.replicate (1000 - L.val) 32#u8 := by
  have himg : img.val.length = L.val := img.property
  have hbound : 0 + L.val ≤ (Array.repeat 1000#usize 32#u8).to_slice.val.length := by
    simp [Array.to_slice, Array.repeat_val]; omega
  obtain ⟨s, hs, hsv⟩ := put_eq (Array.repeat 1000#usize 32#u8).to_slice 0#usize L img.to_slice hbound
  have hput : s.val = img.val ++ List.replicate (1000 - L.val) 32#u8 := by
    rw [hsv]
    simp only [Array.to_slice, Slice.from_val, Array.repeat_val, uscalar_ofNat_val]
    rw [putL_of_len_eq _ _ _ _ himg, List.take_zero, List.nil_append, Nat.zero_add,
      List.drop_replicate]
  refine ⟨s, hs, ?_⟩
  rw [Array.from_slice_val _ _ (by
    rw [hput, List.length_append, himg, List.length_replicate, uscalar_ofNat_val]; omega), hput]

private theorem find?_of_take_some {α : Type _} {l : List α} {p : α → Bool} {j : Nat} {v : α}
    (h : (l.take j).find? p = some v) :
    l.find? p = some v := by
  rw [← List.take_append_drop j l, List.find?_append, h, Option.some_or]

private theorem find?_take_succ_of_none {α : Type _} {l : List α} {p : α → Bool} {j : Nat}
    (hj : j < l.length) (h : (l.take j).find? p = none) :
    (l.take (j + 1)).find? p = if p (l[j]'hj) then some (l[j]'hj) else none := by
  rw [take_succ_of_lt hj, List.find?_append, h, Option.none_or, List.find?_singleton]

private theorem slice_index_usize_eq_of {α : Type _} (s : Slice α) (i : Usize) (r : α)
    (hlt : i.val < s.val.length) (hr : s.val[i.val]'hlt = r) :
    Slice.index_usize s i = .ok r := by
  rw [Slice.index_usize, Slice.getElem?_Usize_eq, List.getElem?_eq_getElem hlt, hr]

set_option maxHeartbeats 2000000 in
private theorem call_m03b_loop1_eq (a0 : Array U8 1000#usize)
    (cust : Slice cbstm03a.CustomerRecord) (key : Array U8 9#usize)
    (custs : List (List FVal)) (cid : Int)
    (hcust : cust.val.map CustomerRecord.vals = custs)
    (hvalid : ∀ v ∈ custs, CustomerRecord.Valid v)
    (hcid0 : 0 ≤ cid) (hcid9 : cid.natAbs < 10 ^ 9)
    (hkey : key.val = zeroPad 9 cid.natAbs) :
    ∃ p : Array U8 1000#usize × Bool,
      cbstm03a.call_m03b_loop1 a0 cust key false 0#usize = .ok p ∧
      match custs.find? (fun v => numOf (v.getD 0 default) == cid) with
      | none => p.2 = false
      | some cval =>
        p.2 = true ∧ p.1.val = latL (CustomerRecord.encode cval) ++ List.replicate 500 32#u8 := by
  have hlen : cust.val.length = custs.length := by rw [← hcust, List.length_map]
  have hmax0 : cust.val.length ≤ Usize.max := cust.property
  let p : List FVal → Bool := fun v => numOf (v.getD 0 default) == cid
  refine exists_ok_of_wp ?_
  simp only [cbstm03a.call_m03b_loop1]
  refine wp_loop (loop_shape _)
    (fun (s : Array U8 1000#usize × Bool × Usize) =>
      s.2.2.val ≤ custs.length ∧
      match (custs.take s.2.2.val).find? p with
      | none => s.2.1 = false
      | some cval =>
        s.2.1 = true ∧ s.1.val = latL (CustomerRecord.encode cval) ++ List.replicate 500 32#u8)
    (fun s => if s.2.1 then 0 else custs.length - s.2.2.val + 1) ?_ _ ?_
  · rintro ⟨a, found, j⟩ ⟨hj, hinv⟩
    simp only at hj hinv
    by_cases hf : found = true
    · subst hf
      simp only [cbstm03a.call_m03b_loop1.body, ↓reduceIte, wp_ok, loopCls_done]
      refine ⟨(a, true), rfl, ?_⟩
      cases htake : (custs.take j.val).find? p with
      | none => rw [htake] at hinv; cases hinv
      | some cval =>
        rw [htake] at hinv
        rw [find?_of_take_some htake]
        exact hinv
    · have hf' : found = false := by simpa using hf
      subst hf'
      have hnone : (custs.take j.val).find? p = none := by
        cases htake : (custs.take j.val).find? p with
        | none => rfl
        | some cval => rw [htake] at hinv; cases hinv.1
      by_cases hlt : j.val < cust.val.length
      · have hlt_c : j.val < custs.length := by omega
        have hmax : j.val + 1 ≤ Usize.max := by omega
        obtain ⟨r, hr_eq⟩ : ∃ r, cust.val[j.val]'hlt = r := ⟨_, rfl⟩
        have hidx := slice_index_usize_eq_of cust j r hlt hr_eq
        have hr_mem : CustomerRecord.vals r ∈ custs := by
          rw [← hcust, ← hr_eq]; exact List.mem_map_of_mem (List.getElem_mem hlt)
        have hr_val : CustomerRecord.Valid (CustomerRecord.vals r) := hvalid _ hr_mem
        have hcust_j : custs[j.val]'hlt_c = CustomerRecord.vals r := by
          subst hcust; simp [hr_eq]
        obtain ⟨s1, hs1, hs1v⟩ := put_unum_repeat9 r.cust_id
        obtain ⟨img, himg, himgv⟩ := ser_cust_val r
        obtain ⟨s6, hs6, hs6v⟩ := put_repeat1000 img (by decide)
        have hmatch := cust_id_match_eq r hr_val cid hcid0 hcid9
        have heqb : cbstm03a.eq_bytes ((Array.repeat 9#usize 48#u8).from_slice s1).to_slice key.to_slice =
            .ok (p (CustomerRecord.vals r)) := by
          rw [eq_bytes_eq]
          simp only [Array.to_slice, Slice.from_val, hs1v, hkey, hmatch]
          rfl
        have hfind_next : (custs.take (j.val + 1)).find? p =
            if p (CustomerRecord.vals r) then some (CustomerRecord.vals r) else none := by
          rw [find?_take_succ_of_none hlt_c hnone, hcust_j]
        by_cases hp : p (CustomerRecord.vals r) = true
        · dsimp only [cbstm03a.call_m03b_loop1.body]
          aeneas_wp [hr_eq, Array.to_slice_mut, heqb, hp, hlt, hmax, hs1, himg, hs6]
          simp only [Bool.false_eq_true, ↓reduceIte, loopCls_cont, UScalar.ofNatCore_val_eq]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          simp only [hfind_next, hp, ↓reduceIte]
          exact ⟨trivial, by rw [hs6v, himgv]; rfl⟩
        · have hp' : p (CustomerRecord.vals r) = false := by simpa using hp
          dsimp only [cbstm03a.call_m03b_loop1.body]
          aeneas_wp [hr_eq, Array.to_slice_mut, heqb, hp', hlt, hmax, hs1]
          simp only [Bool.false_eq_true, ↓reduceIte, loopCls_cont, UScalar.ofNatCore_val_eq]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          simp only [hfind_next, hp', Bool.false_eq_true, ↓reduceIte]
      · dsimp only [cbstm03a.call_m03b_loop1.body]
        aeneas_wp [hlt]
        simp only [loopCls_done]
        have hjeq : j.val = custs.length := by omega
        rw [hjeq, List.take_length] at hnone
        refine ⟨(a, false), rfl, ?_⟩
        rw [hnone]
  · simp

set_option maxHeartbeats 2000000 in
private theorem call_m03b_loop3_eq (a0 : Array U8 1000#usize)
    (acct : Slice cbstm03a.AccountRecord) (kv : I64)
    (accts : List (List FVal)) (aid : Int)
    (hacct : acct.val.map AccountRecord.vals = accts)
    (hvalid : ∀ v ∈ accts, AccountRecord.Valid v)
    (hkv : kv.val = aid) :
    ∃ p : Array U8 1000#usize × Bool,
      cbstm03a.call_m03b_loop3 a0 acct kv false 0#usize = .ok p ∧
      match accts.find? (fun v => numOf (v.getD 0 default) == aid) with
      | none => p.2 = false
      | some aval =>
        p.2 = true ∧ p.1.val = latL (AccountRecord.encode aval) ++ List.replicate 700 32#u8 := by
  have hlen : acct.val.length = accts.length := by rw [← hacct, List.length_map]
  have hmax0 : acct.val.length ≤ Usize.max := acct.property
  let p : List FVal → Bool := fun v => numOf (v.getD 0 default) == aid
  refine exists_ok_of_wp ?_
  simp only [cbstm03a.call_m03b_loop3]
  refine wp_loop (loop_shape _)
    (fun (s : Array U8 1000#usize × Bool × Usize) =>
      s.2.2.val ≤ accts.length ∧
      match (accts.take s.2.2.val).find? p with
      | none => s.2.1 = false
      | some aval =>
        s.2.1 = true ∧ s.1.val = latL (AccountRecord.encode aval) ++ List.replicate 700 32#u8)
    (fun s => if s.2.1 then 0 else accts.length - s.2.2.val + 1) ?_ _ ?_
  · rintro ⟨a, found, j⟩ ⟨hj, hinv⟩
    simp only at hj hinv
    by_cases hf : found = true
    · subst hf
      simp only [cbstm03a.call_m03b_loop3.body, ↓reduceIte, wp_ok, loopCls_done]
      refine ⟨(a, true), rfl, ?_⟩
      cases htake : (accts.take j.val).find? p with
      | none => rw [htake] at hinv; cases hinv
      | some aval =>
        rw [htake] at hinv
        rw [find?_of_take_some htake]
        exact hinv
    · have hf' : found = false := by simpa using hf
      subst hf'
      have hnone : (accts.take j.val).find? p = none := by
        cases htake : (accts.take j.val).find? p with
        | none => rfl
        | some aval => rw [htake] at hinv; cases hinv.1
      by_cases hlt : j.val < acct.val.length
      · have hlt_a : j.val < accts.length := by omega
        have hmax : j.val + 1 ≤ Usize.max := by omega
        obtain ⟨r, hr_eq⟩ : ∃ r, acct.val[j.val]'hlt = r := ⟨_, rfl⟩
        have hidx := slice_index_usize_eq_of acct j r hlt hr_eq
        have hr_mem : AccountRecord.vals r ∈ accts := by
          rw [← hacct, ← hr_eq]; exact List.mem_map_of_mem (List.getElem_mem hlt)
        have hr_val : AccountRecord.Valid (AccountRecord.vals r) := hvalid _ hr_mem
        have hacct_j : accts[j.val]'hlt_a = AccountRecord.vals r := by
          subst hacct; simp [hr_eq]
        have haf := acct_fields hr_val
        have hr0 : 0 ≤ r.acct_id.val := haf.2.2.2.1
        have hr11 : r.acct_id.val.natAbs < 10 ^ 11 := haf.2.2.2.2.1
        obtain ⟨rk, i1, hrk, hi1, rfl⟩ := zoned_digits11_of_nonneg r.acct_id hr0 hr11
        obtain ⟨img, himg, himgv⟩ := ser_acct_val r
        obtain ⟨s3, hs3, hs3v⟩ := put_repeat1000 img (by decide)
        have hfind_next : (accts.take (j.val + 1)).find? p =
            if p (AccountRecord.vals r) then some (AccountRecord.vals r) else none := by
          rw [find?_take_succ_of_none hlt_a hnone, hacct_j]
        have hp_iff : (r.acct_id.val = kv.val) ↔ p (AccountRecord.vals r) = true := by
          rw [hkv]; exact beq_iff_eq.symm
        by_cases hp : p (AccountRecord.vals r) = true
        · have heq_kv : r.acct_id.val = kv.val := hp_iff.2 hp
          dsimp only [cbstm03a.call_m03b_loop3.body]
          aeneas_wp [hr_eq, Array.to_slice_mut,
            hlt, hmax, hrk, hi1, himg, hs3, heq_kv]
          simp only [Bool.false_eq_true, ↓reduceIte, loopCls_cont, UScalar.ofNatCore_val_eq]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          simp only [hfind_next, hp, ↓reduceIte]
          exact ⟨trivial, by rw [hs3v, himgv]; rfl⟩
        · have hp' : p (AccountRecord.vals r) = false := by simpa using hp
          have hne_kv : ¬ r.acct_id.val = kv.val := mt hp_iff.1 hp
          dsimp only [cbstm03a.call_m03b_loop3.body]
          aeneas_wp [hr_eq, Array.to_slice_mut,
            hlt, hmax, hrk, hi1, hne_kv]
          simp only [Bool.false_eq_true, ↓reduceIte, loopCls_cont, UScalar.ofNatCore_val_eq]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          simp only [hfind_next, hp', Bool.false_eq_true, ↓reduceIte]
      · dsimp only [cbstm03a.call_m03b_loop3.body]
        aeneas_wp [hlt]
        simp only [loopCls_done]
        have hjeq : j.val = accts.length := by omega
        rw [hjeq, List.take_length] at hnone
        refine ⟨(a, false), rfl, ?_⟩
        rw [hnone]
  · simp

/-! ## 8. Simple `Ctx` helpers: `sw`, `hw`, `rc_ok`, `set_dd`, `err_abend`, `finish` -/

theorem sw_eq (c : cbstm03a.Ctx) (line : Array U8 80#usize)
    (h : c.stmt.val.length < Usize.max) :
    cbstm03a.sw c line = .ok { c with
      stmt := alloc.vec.Vec.from (c.stmt.val ++ [alloc.vec.Vec.from line.val (by scalar_tac)])
        (by simp; omega) } := by
  refine eq_ok_of_wp ?_
  unfold cbstm03a.sw
  aeneas_wp [vb_eq, Array.to_slice, Slice.from_val, h]

theorem hw_eq (c : cbstm03a.Ctx) (lit : Slice U8)
    (h : c.html.val.length < Usize.max) :
    ∃ v : alloc.vec.Vec U8,
      v.val = putL (List.replicate 100 32#u8) 0 100 lit.val ∧
      cbstm03a.hw c lit = .ok { c with
        html := alloc.vec.Vec.from (c.html.val ++ [v]) (by simp; omega) } := by
  have hbound : (0#usize).val + (100#usize).val ≤ (Array.repeat 100#usize 32#u8).to_slice.val.length := by
    simp [Array.to_slice, Array.repeat_val]
  obtain ⟨s1, hs1, hs1v⟩ := put_eq (Array.repeat 100#usize 32#u8).to_slice 0#usize 100#usize lit hbound
  have hs1_val : s1.val = putL (List.replicate 100 32#u8) 0 100 lit.val := by
    rw [hs1v]
    simp only [Array.to_slice, Slice.from_val, Array.repeat_val, uscalar_ofNat_val]
  have hs1_len : s1.val.length = (100#usize).val := by
    rw [hs1_val, length_putL _ _ _ _ (by simp)]
    simp
  let r1 := (Array.repeat 100#usize 32#u8).from_slice s1
  have hr1_val : r1.val = putL (List.replicate 100 32#u8) 0 100 lit.val := by
    rw [Array.from_slice_val _ _ hs1_len, hs1_val]
  refine ⟨alloc.vec.Vec.from r1.to_slice.val (by scalar_tac), ?_, ?_⟩
  · simp [Array.to_slice, hr1_val]
  · refine eq_ok_of_wp ?_
    dsimp only [cbstm03a.hw]
    aeneas_wp [Array.to_slice_mut, hs1, vb_eq, h]
    rfl

theorem rc_ok_eq (c : cbstm03a.Ctx) :
    cbstm03a.rc_ok c =
      .ok (decide (c.m_rc.val = [48#u8, 48#u8]) || decide (c.m_rc.val = [48#u8, 52#u8])) := by
  refine eq_ok_of_wp ?_
  unfold cbstm03a.rc_ok
  aeneas_wp [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.make_val]
  by_cases h1 : c.m_rc.val = [48#u8, 48#u8] <;> simp [h1]

theorem rc_ok_00 (c : cbstm03a.Ctx) (h : c.m_rc.val = [48#u8, 48#u8]) :
    cbstm03a.rc_ok c = .ok true := by
  rw [rc_ok_eq, h]; rfl

theorem set_dd_eq (c : cbstm03a.Ctx) (dd : Slice U8) :
    cbstm03a.set_dd c dd = .ok { c with
      m_dd := Array.from (putL c.m_dd.val 0 8 dd.val)
        (by rw [length_putL _ _ _ _ (by rw [c.m_dd.property]; decide)]; exact c.m_dd.property) } := by
  have hmdd : c.m_dd.val.length = 8 := c.m_dd.property
  have hbound : (0#usize).val + (8#usize).val ≤ c.m_dd.to_slice.val.length := by
    simp [Array.to_slice, hmdd]
  obtain ⟨s1, hs1, hs1v⟩ := put_eq c.m_dd.to_slice 0#usize 8#usize dd hbound
  have hs1_len : s1.val.length = (8#usize).val := by
    rw [hs1v, length_putL _ _ _ _ hbound]
    simp [Array.to_slice, hmdd]
  have heq : c.m_dd.from_slice s1 = Array.from (putL c.m_dd.val 0 8 dd.val)
      (by rw [length_putL _ _ _ _ (by rw [c.m_dd.property]; decide)]; exact c.m_dd.property) := by
    rw [Array.eq_iff, Array.from_slice_val _ _ hs1_len, hs1v, Array.from_val]
    simp [Array.to_slice]
  refine eq_ok_of_wp ?_
  dsimp only [cbstm03a.set_dd]
  aeneas_wp [Array.to_slice_mut, hs1, heq]

theorem set_dd_of_len8 (c : cbstm03a.Ctx) (dd : Slice U8) (arr : Array U8 8#usize)
    (hdd : dd.val = arr.val) :
    cbstm03a.set_dd c dd = .ok { c with m_dd := arr } := by
  have harr : arr.val.length = 8 := arr.property
  have hmdd : c.m_dd.val.length = 8 := c.m_dd.property
  have heq : Array.from (putL c.m_dd.val 0 8 dd.val)
      (by rw [length_putL _ _ _ _ (by rw [c.m_dd.property]; decide)]; exact c.m_dd.property) = arr := by
    rw [Array.eq_iff, Array.from_val, hdd, putL_of_len_eq _ _ _ _ harr,
      List.take_zero, List.nil_append, Nat.zero_add,
      List.drop_of_length_le (by omega), List.append_nil]
  rw [set_dd_eq, heq]

theorem set_dd_8 (c : cbstm03a.Ctx) (dd : Array U8 8#usize) :
    cbstm03a.set_dd c dd.to_slice = .ok { c with m_dd := dd } :=
  set_dd_of_len8 c dd.to_slice dd (by simp [Array.to_slice])

private theorem usize_max_ge_256 : 256 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max_eq, U64.max_eq]

theorem err_abend_eq (c : cbstm03a.Ctx) (msg : Slice U8)
    (h : c.displays.val.length + 3 ≤ Usize.max) :
    ∃ c' : cbstm03a.Ctx, cbstm03a.err_abend c msg = .ok c' ∧
      c'.displays.val.map (·.val) = c.displays.val.map (·.val) ++
        [msg.val,
         [82#u8, 69#u8, 84#u8, 85#u8, 82#u8, 78#u8, 32#u8, 67#u8, 79#u8, 68#u8, 69#u8, 58#u8, 32#u8] ++ c.m_rc.val,
         [65#u8, 66#u8, 69#u8, 78#u8, 68#u8, 73#u8, 78#u8, 71#u8, 32#u8, 80#u8, 82#u8, 79#u8, 71#u8, 82#u8, 65#u8, 77#u8]] ∧
      c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = true := by
  have hm := usize_max_ge_256
  have hrc : c.m_rc.val.length = 2 := c.m_rc.property
  have hd_eq : ∀ (a13 : Array U8 13#usize),
      cbstm03a.app (alloc.vec.Vec.new U8) a13.to_slice =
        .ok (alloc.vec.Vec.from a13.val (by have h1 : a13.val.length = 13 := a13.property; omega)) := by
    intro a13
    have h1 : a13.val.length = 13 := a13.property
    rw [app_eq _ _ (by simp [Array.to_slice, h1]; omega)]
    congr 1; simp [Array.to_slice]
  have hd1_eq : ∀ (a13 : Array U8 13#usize) (h13 : a13.val.length ≤ Usize.max),
      cbstm03a.app (alloc.vec.Vec.from a13.val h13) c.m_rc.to_slice =
        .ok (alloc.vec.Vec.from (a13.val ++ c.m_rc.val)
          (by have h1 : a13.val.length = 13 := a13.property; simp [h1, hrc]; omega)) := by
    intro a13 h13
    have h1 : a13.val.length = 13 := a13.property
    rw [app_eq _ _ (by simp [Array.to_slice, h1, hrc]; omega)]
    congr 1; simp [Array.to_slice]
  have hl1 : c.displays.val.length < Usize.max := by omega
  have hl2 : c.displays.val.length + 1 < Usize.max := by omega
  have hl3 : c.displays.val.length + 1 + 1 < Usize.max := by omega
  refine exists_ok_of_wp ?_
  dsimp only [cbstm03a.err_abend]
  aeneas_wp [vb_eq, hd_eq, hd1_eq, List.length_append, List.length_singleton, hl1, hl2, hl3]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl⟩
  simp [Array.to_slice, Array.make_val, List.map_append]

theorem err_abend_cust (c : cbstm03a.Ctx)
    (hd : c.displays.val = [])
    (hrc : c.m_rc.val = [50#u8, 51#u8]) :
    ∃ c' : cbstm03a.Ctx,
      cbstm03a.err_abend c (Array.make 22#usize
        [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 82#u8, 69#u8, 65#u8, 68#u8, 73#u8, 78#u8,
         71#u8, 32#u8, 67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]).to_slice = .ok c' ∧
      c'.displays.val.map (fun l => l.val.map (·.val)) = modelCustAbortDisp ∧
      c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = true := by
  have hm := usize_max_ge_256
  obtain ⟨c', hc', hdisp, hstmt, hhtml, hab⟩ := err_abend_eq c _ (by rw [hd]; simp; omega)
  refine ⟨c', hc', ?_, hstmt, hhtml, hab⟩
  have hmap := congrArg (List.map (List.map UScalar.val)) hdisp
  rw [List.map_map] at hmap
  change c'.displays.val.map (fun l => l.val.map (·.val)) = _ at hmap
  rw [hmap, hd, hrc]
  decide +kernel

theorem err_abend_acct (c : cbstm03a.Ctx)
    (hd : c.displays.val = [])
    (hrc : c.m_rc.val = [50#u8, 51#u8]) :
    ∃ c' : cbstm03a.Ctx,
      cbstm03a.err_abend c (Array.make 22#usize
        [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 82#u8, 69#u8, 65#u8, 68#u8, 73#u8, 78#u8,
         71#u8, 32#u8, 65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]).to_slice = .ok c' ∧
      c'.displays.val.map (fun l => l.val.map (·.val)) = modelAcctAbortDisp ∧
      c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = true := by
  have hm := usize_max_ge_256
  obtain ⟨c', hc', hdisp, hstmt, hhtml, hab⟩ := err_abend_eq c _ (by rw [hd]; simp; omega)
  refine ⟨c', hc', ?_, hstmt, hhtml, hab⟩
  have hmap := congrArg (List.map (List.map UScalar.val)) hdisp
  rw [List.map_map] at hmap
  change c'.displays.val.map (fun l => l.val.map (·.val)) = _ at hmap
  rw [hmap, hd, hrc]
  decide +kernel

theorem finish_eq (c : cbstm03a.Ctx) :
    cbstm03a.finish c = .ok
      { displays := c.displays, stmt_file_writes := c.stmt, html_file_writes := c.html,
        abended := c.abended } := rfl

/-! ## 9. `call_m03b` branch dispatch and `open_file` / `close_file` -/

theorem call_m03b_trnx_open (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : c.m_dd.val = [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 79#u8) :
    cbstm03a.call_m03b c trnx xref cust acct = .ok { c with
      trnx_pos := 0#usize,
      trnx_eof := false,
      trnx_status := Array.make 2#usize [48#u8, 48#u8],
      m_rc := Array.make 2#usize [48#u8, 48#u8] } := by
  refine eq_ok_of_wp ?_
  dsimp only [cbstm03a.call_m03b]
  aeneas_wp [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.make_val,
    hdd, hop, List.cons.injEq, uscalar_ofNat_val, Nat.reduceEqDiff]

theorem call_m03b_trnx_close (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : c.m_dd.val = [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 67#u8) :
    cbstm03a.call_m03b c trnx xref cust acct = .ok { c with
      trnx_status := Array.make 2#usize [48#u8, 48#u8],
      m_rc := Array.make 2#usize [48#u8, 48#u8] } := by
  refine eq_ok_of_wp ?_
  dsimp only [cbstm03a.call_m03b]
  aeneas_wp [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.make_val,
    hdd, hop, List.cons.injEq, uscalar_ofNat_val, Nat.reduceEqDiff]

theorem call_m03b_xref_open (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : c.m_dd.val = [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 79#u8) :
    cbstm03a.call_m03b c trnx xref cust acct = .ok { c with
      xref_pos := 0#usize,
      xref_eof := false,
      xref_status := Array.make 2#usize [48#u8, 48#u8],
      m_rc := Array.make 2#usize [48#u8, 48#u8] } := by
  refine eq_ok_of_wp ?_
  dsimp only [cbstm03a.call_m03b]
  aeneas_wp [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.make_val,
    hdd, hop, List.cons.injEq, uscalar_ofNat_val, Nat.reduceEqDiff]

theorem call_m03b_xref_close (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : c.m_dd.val = [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 67#u8) :
    cbstm03a.call_m03b c trnx xref cust acct = .ok { c with
      xref_status := Array.make 2#usize [48#u8, 48#u8],
      m_rc := Array.make 2#usize [48#u8, 48#u8] } := by
  refine eq_ok_of_wp ?_
  dsimp only [cbstm03a.call_m03b]
  aeneas_wp [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.make_val,
    hdd, hop, List.cons.injEq, uscalar_ofNat_val, Nat.reduceEqDiff]

theorem call_m03b_cust_open (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : c.m_dd.val = [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 79#u8) :
    cbstm03a.call_m03b c trnx xref cust acct = .ok { c with
      cust_status := Array.make 2#usize [48#u8, 48#u8],
      m_rc := Array.make 2#usize [48#u8, 48#u8] } := by
  refine eq_ok_of_wp ?_
  dsimp only [cbstm03a.call_m03b]
  aeneas_wp [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.make_val,
    hdd, hop, List.cons.injEq, uscalar_ofNat_val, Nat.reduceEqDiff]

theorem call_m03b_cust_close (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : c.m_dd.val = [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 67#u8) :
    cbstm03a.call_m03b c trnx xref cust acct = .ok { c with
      cust_status := Array.make 2#usize [48#u8, 48#u8],
      m_rc := Array.make 2#usize [48#u8, 48#u8] } := by
  refine eq_ok_of_wp ?_
  dsimp only [cbstm03a.call_m03b]
  aeneas_wp [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.make_val,
    hdd, hop, List.cons.injEq, uscalar_ofNat_val, Nat.reduceEqDiff]

theorem call_m03b_acct_open (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : c.m_dd.val = [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 79#u8) :
    cbstm03a.call_m03b c trnx xref cust acct = .ok { c with
      acct_status := Array.make 2#usize [48#u8, 48#u8],
      m_rc := Array.make 2#usize [48#u8, 48#u8] } := by
  refine eq_ok_of_wp ?_
  dsimp only [cbstm03a.call_m03b]
  aeneas_wp [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.make_val,
    hdd, hop, List.cons.injEq, uscalar_ofNat_val, Nat.reduceEqDiff]

theorem call_m03b_acct_close (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : c.m_dd.val = [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 67#u8) :
    cbstm03a.call_m03b c trnx xref cust acct = .ok { c with
      acct_status := Array.make 2#usize [48#u8, 48#u8],
      m_rc := Array.make 2#usize [48#u8, 48#u8] } := by
  refine eq_ok_of_wp ?_
  dsimp only [cbstm03a.call_m03b]
  aeneas_wp [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.make_val,
    hdd, hop, List.cons.injEq, uscalar_ofNat_val, Nat.reduceEqDiff]

theorem open_file_trnx (c : cbstm03a.Ctx) (dd msg : Slice U8)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : dd.val = [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8]) :
    cbstm03a.open_file c dd msg trnx xref cust acct =
      .ok (true, { c with
        m_dd := Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8],
        m_oper := 79#u8,
        m_rc := Array.make 2#usize [48#u8, 48#u8],
        trnx_pos := 0#usize,
        trnx_eof := false,
        trnx_status := Array.make 2#usize [48#u8, 48#u8] }) := by
  have hsdd := set_dd_of_len8 c dd
    (Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (by rw [Array.make_val, hdd])
  have hm03b := call_m03b_trnx_open
    { c with m_dd := Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8],
             m_oper := 79#u8, m_rc := Array.make 2#usize [48#u8, 48#u8] }
    trnx xref cust acct rfl rfl
  unfold cbstm03a.open_file
  rw [hsdd, bind_ok, hm03b, bind_ok, rc_ok_00 _ rfl, bind_ok]
  rfl

theorem open_file_xref (c : cbstm03a.Ctx) (dd msg : Slice U8)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : dd.val = [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8]) :
    cbstm03a.open_file c dd msg trnx xref cust acct =
      .ok (true, { c with
        m_dd := Array.make 8#usize [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8],
        m_oper := 79#u8,
        m_rc := Array.make 2#usize [48#u8, 48#u8],
        xref_pos := 0#usize,
        xref_eof := false,
        xref_status := Array.make 2#usize [48#u8, 48#u8] }) := by
  have hsdd := set_dd_of_len8 c dd
    (Array.make 8#usize [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (by rw [Array.make_val, hdd])
  have hm03b := call_m03b_xref_open
    { c with m_dd := Array.make 8#usize [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8],
             m_oper := 79#u8, m_rc := Array.make 2#usize [48#u8, 48#u8] }
    trnx xref cust acct rfl rfl
  unfold cbstm03a.open_file
  rw [hsdd, bind_ok, hm03b, bind_ok, rc_ok_00 _ rfl, bind_ok]
  rfl

theorem open_file_cust (c : cbstm03a.Ctx) (dd msg : Slice U8)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : dd.val = [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]) :
    cbstm03a.open_file c dd msg trnx xref cust acct =
      .ok (true, { c with
        m_dd := Array.make 8#usize [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8],
        m_oper := 79#u8,
        m_rc := Array.make 2#usize [48#u8, 48#u8],
        cust_status := Array.make 2#usize [48#u8, 48#u8] }) := by
  have hsdd := set_dd_of_len8 c dd
    (Array.make 8#usize [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (by rw [Array.make_val, hdd])
  have hm03b := call_m03b_cust_open
    { c with m_dd := Array.make 8#usize [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8],
             m_oper := 79#u8, m_rc := Array.make 2#usize [48#u8, 48#u8] }
    trnx xref cust acct rfl rfl
  unfold cbstm03a.open_file
  rw [hsdd, bind_ok, hm03b, bind_ok, rc_ok_00 _ rfl, bind_ok]
  rfl

theorem open_file_acct (c : cbstm03a.Ctx) (dd msg : Slice U8)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : dd.val = [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]) :
    cbstm03a.open_file c dd msg trnx xref cust acct =
      .ok (true, { c with
        m_dd := Array.make 8#usize [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8],
        m_oper := 79#u8,
        m_rc := Array.make 2#usize [48#u8, 48#u8],
        acct_status := Array.make 2#usize [48#u8, 48#u8] }) := by
  have hsdd := set_dd_of_len8 c dd
    (Array.make 8#usize [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (by rw [Array.make_val, hdd])
  have hm03b := call_m03b_acct_open
    { c with m_dd := Array.make 8#usize [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8],
             m_oper := 79#u8, m_rc := Array.make 2#usize [48#u8, 48#u8] }
    trnx xref cust acct rfl rfl
  unfold cbstm03a.open_file
  rw [hsdd, bind_ok, hm03b, bind_ok, rc_ok_00 _ rfl, bind_ok]
  rfl

theorem close_file_trnx (c : cbstm03a.Ctx) (dd msg : Slice U8)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : dd.val = [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8]) :
    cbstm03a.close_file c dd msg trnx xref cust acct =
      .ok (true, { c with
        m_dd := Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8],
        m_oper := 67#u8,
        m_rc := Array.make 2#usize [48#u8, 48#u8],
        trnx_status := Array.make 2#usize [48#u8, 48#u8] }) := by
  have hsdd := set_dd_of_len8 c dd
    (Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (by rw [Array.make_val, hdd])
  have hm03b := call_m03b_trnx_close
    { c with m_dd := Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8],
             m_oper := 67#u8, m_rc := Array.make 2#usize [48#u8, 48#u8] }
    trnx xref cust acct rfl rfl
  unfold cbstm03a.close_file
  rw [hsdd, bind_ok, hm03b, bind_ok, rc_ok_00 _ rfl, bind_ok]
  rfl

theorem close_file_xref (c : cbstm03a.Ctx) (dd msg : Slice U8)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : dd.val = [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8]) :
    cbstm03a.close_file c dd msg trnx xref cust acct =
      .ok (true, { c with
        m_dd := Array.make 8#usize [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8],
        m_oper := 67#u8,
        m_rc := Array.make 2#usize [48#u8, 48#u8],
        xref_status := Array.make 2#usize [48#u8, 48#u8] }) := by
  have hsdd := set_dd_of_len8 c dd
    (Array.make 8#usize [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (by rw [Array.make_val, hdd])
  have hm03b := call_m03b_xref_close
    { c with m_dd := Array.make 8#usize [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8],
             m_oper := 67#u8, m_rc := Array.make 2#usize [48#u8, 48#u8] }
    trnx xref cust acct rfl rfl
  unfold cbstm03a.close_file
  rw [hsdd, bind_ok, hm03b, bind_ok, rc_ok_00 _ rfl, bind_ok]
  rfl

theorem close_file_cust (c : cbstm03a.Ctx) (dd msg : Slice U8)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : dd.val = [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]) :
    cbstm03a.close_file c dd msg trnx xref cust acct =
      .ok (true, { c with
        m_dd := Array.make 8#usize [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8],
        m_oper := 67#u8,
        m_rc := Array.make 2#usize [48#u8, 48#u8],
        cust_status := Array.make 2#usize [48#u8, 48#u8] }) := by
  have hsdd := set_dd_of_len8 c dd
    (Array.make 8#usize [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (by rw [Array.make_val, hdd])
  have hm03b := call_m03b_cust_close
    { c with m_dd := Array.make 8#usize [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8],
             m_oper := 67#u8, m_rc := Array.make 2#usize [48#u8, 48#u8] }
    trnx xref cust acct rfl rfl
  unfold cbstm03a.close_file
  rw [hsdd, bind_ok, hm03b, bind_ok, rc_ok_00 _ rfl, bind_ok]
  rfl

theorem close_file_acct (c : cbstm03a.Ctx) (dd msg : Slice U8)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (hdd : dd.val = [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]) :
    cbstm03a.close_file c dd msg trnx xref cust acct =
      .ok (true, { c with
        m_dd := Array.make 8#usize [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8],
        m_oper := 67#u8,
        m_rc := Array.make 2#usize [48#u8, 48#u8],
        acct_status := Array.make 2#usize [48#u8, 48#u8] }) := by
  have hsdd := set_dd_of_len8 c dd
    (Array.make 8#usize [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (by rw [Array.make_val, hdd])
  have hm03b := call_m03b_acct_close
    { c with m_dd := Array.make 8#usize [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8],
             m_oper := 67#u8, m_rc := Array.make 2#usize [48#u8, 48#u8] }
    trnx xref cust acct rfl rfl
  unfold cbstm03a.close_file
  rw [hsdd, bind_ok, hm03b, bind_ok, rc_ok_00 _ rfl, bind_ok]
  rfl

/-! ## 10. `call_m03b` for sequential and keyed reads -/

theorem call_m03b_trnx_read_lt (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (vals1 : List (List FVal))
    (hdd : c.m_dd.val = [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 82#u8)
    (heof : c.trnx_eof = false)
    (htrnx : trnx.val.map TrnxRecord.vals = vals1)
    (hpos : c.trnx_pos.val < vals1.length) :
    ∃ c' : cbstm03a.Ctx,
      cbstm03a.call_m03b c trnx xref cust acct = .ok c' ∧
      c'.m_rc = Array.make 2#usize [48#u8, 48#u8] ∧
      c'.trnx_status = Array.make 2#usize [48#u8, 48#u8] ∧
      c'.trnx_pos.val = c.trnx_pos.val + 1 ∧
      c'.trnx_eof = false ∧
      c'.m_fldt.val = latL (TrnxRecord.encode (vals1.getD c.trnx_pos.val [])) ++ List.replicate 650 32#u8 ∧
      c'.displays = c.displays ∧ c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = c.abended ∧
      c'.xref_pos = c.xref_pos ∧ c'.xref_eof = c.xref_eof := by
  have hlen : trnx.val.length = vals1.length := by rw [← htrnx, List.length_map]
  have hlt : c.trnx_pos.val < trnx.val.length := by omega
  have hmax : c.trnx_pos.val + 1 ≤ Usize.max := by have := trnx.property; omega
  obtain ⟨r, hr_eq⟩ : ∃ r, trnx.val[c.trnx_pos.val]'hlt = r := ⟨_, rfl⟩
  have hvals_r : vals1.getD c.trnx_pos.val [] = TrnxRecord.vals r := by
    subst htrnx; rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, hr_eq]
  obtain ⟨img, himg, himgv⟩ := ser_trnx_val r
  obtain ⟨s4, hs4, hs4v⟩ := put_repeat1000 img (by decide)
  have hdd_eq : ∀ (lit : Array U8 8#usize),
      cbstm03a.eq_bytes c.m_dd.to_slice lit.to_slice = .ok (decide (c.m_dd.val = lit.val)) := by
    intro lit; rw [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.to_slice, Slice.from_val]
  refine exists_ok_of_wp ?_
  dsimp only [cbstm03a.call_m03b]
  aeneas_wp [hdd_eq, Array.make_val, hdd, List.cons.injEq, Nat.reduceEqDiff,
    hop, heof, hlt, hr_eq, hmax, himg, Array.to_slice_mut, hs4, uscalar_ofNat_val]
  refine ⟨_, rfl, rfl, rfl, UScalar.ofNatCore_val_eq _, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [hs4v, himgv, hvals_r]; rfl

theorem call_m03b_trnx_read_eof (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (vals1 : List (List FVal))
    (hdd : c.m_dd.val = [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 82#u8)
    (heof : c.trnx_eof = false)
    (htrnx : trnx.val.map TrnxRecord.vals = vals1)
    (hpos : vals1.length ≤ c.trnx_pos.val) :
    cbstm03a.call_m03b c trnx xref cust acct = .ok { c with
      trnx_eof := true,
      trnx_status := Array.make 2#usize [49#u8, 48#u8],
      m_rc := Array.make 2#usize [49#u8, 48#u8] } := by
  have hlen : trnx.val.length = vals1.length := by rw [← htrnx, List.length_map]
  have hnlt : ¬ c.trnx_pos.val < trnx.val.length := by omega
  refine eq_ok_of_wp ?_
  dsimp only [cbstm03a.call_m03b]
  aeneas_wp [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.make_val,
    hdd, List.cons.injEq, Nat.reduceEqDiff, hop, heof, hnlt, uscalar_ofNat_val]
  simp

theorem call_m03b_trnx_read (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (vals1 : List (List FVal))
    (hdd : c.m_dd.val = [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 82#u8)
    (heof : c.trnx_eof = false)
    (htrnx : trnx.val.map TrnxRecord.vals = vals1)
    (_hvalid : ∀ v ∈ vals1, TrnxRecord.Valid v) :
    ∃ c' : cbstm03a.Ctx,
      cbstm03a.call_m03b c trnx xref cust acct = .ok c' ∧
      c'.displays = c.displays ∧ c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = c.abended ∧
      c'.xref_pos = c.xref_pos ∧ c'.xref_eof = c.xref_eof ∧
      if c.trnx_pos.val < vals1.length then
        c'.m_rc = Array.make 2#usize [48#u8, 48#u8] ∧
        c'.trnx_pos.val = c.trnx_pos.val + 1 ∧
        c'.trnx_eof = false ∧
        c'.m_fldt.val = latL (TrnxRecord.encode (vals1.getD c.trnx_pos.val [])) ++ List.replicate 650 32#u8
      else
        c'.m_rc = Array.make 2#usize [49#u8, 48#u8] ∧
        c'.trnx_eof = true := by
  by_cases hpos : c.trnx_pos.val < vals1.length
  · obtain ⟨c', hc', hrc, _, hpos', heof', hfldt, hd, hs, hh, ha, hxp, hxe⟩ :=
      call_m03b_trnx_read_lt c trnx xref cust acct vals1 hdd hop heof htrnx hpos
    exact ⟨c', hc', hd, hs, hh, ha, hxp, hxe, by simp [hpos, hrc, hpos', heof', hfldt]⟩
  · have hc' := call_m03b_trnx_read_eof c trnx xref cust acct vals1 hdd hop heof htrnx (by omega)
    exact ⟨_, hc', rfl, rfl, rfl, rfl, rfl, rfl, by simp [hpos]⟩

theorem call_m03b_xref_read_lt (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (vals2 : List (List FVal))
    (hdd : c.m_dd.val = [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 82#u8)
    (heof : c.xref_eof = false)
    (hxref : xref.val.map CardXrefRecord.vals = vals2)
    (hpos : c.xref_pos.val < vals2.length) :
    ∃ c' : cbstm03a.Ctx,
      cbstm03a.call_m03b c trnx xref cust acct = .ok c' ∧
      c'.m_rc = Array.make 2#usize [48#u8, 48#u8] ∧
      c'.xref_status = Array.make 2#usize [48#u8, 48#u8] ∧
      c'.xref_pos.val = c.xref_pos.val + 1 ∧
      c'.xref_eof = false ∧
      c'.m_fldt.val = latL (CardXrefRecord.encode (vals2.getD c.xref_pos.val [])) ++ List.replicate 950 32#u8 ∧
      c'.displays = c.displays ∧ c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = c.abended := by
  have hlen : xref.val.length = vals2.length := by rw [← hxref, List.length_map]
  have hlt : c.xref_pos.val < xref.val.length := by omega
  have hmax : c.xref_pos.val + 1 ≤ Usize.max := by have := xref.property; omega
  obtain ⟨r, hr_eq⟩ : ∃ r, xref.val[c.xref_pos.val]'hlt = r := ⟨_, rfl⟩
  have hvals_r : vals2.getD c.xref_pos.val [] = CardXrefRecord.vals r := by
    subst hxref; rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, hr_eq]
  obtain ⟨img, himg, himgv⟩ := ser_xref_val r
  obtain ⟨s6, hs6, hs6v⟩ := put_repeat1000 img (by decide)
  have hdd_eq : ∀ (lit : Array U8 8#usize),
      cbstm03a.eq_bytes c.m_dd.to_slice lit.to_slice = .ok (decide (c.m_dd.val = lit.val)) := by
    intro lit; rw [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.to_slice, Slice.from_val]
  refine exists_ok_of_wp ?_
  dsimp only [cbstm03a.call_m03b]
  aeneas_wp [hdd_eq, Array.make_val, hdd, List.cons.injEq, Nat.reduceEqDiff,
    hop, heof, hlt, hr_eq, hmax, himg, Array.to_slice_mut, hs6, uscalar_ofNat_val]
  refine ⟨_, rfl, rfl, rfl, UScalar.ofNatCore_val_eq _, rfl, ?_, rfl, rfl, rfl, rfl⟩
  rw [hs6v, himgv, hvals_r]; rfl

theorem call_m03b_xref_read_eof (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (vals2 : List (List FVal))
    (hdd : c.m_dd.val = [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 82#u8)
    (heof : c.xref_eof = false)
    (hxref : xref.val.map CardXrefRecord.vals = vals2)
    (hpos : vals2.length ≤ c.xref_pos.val) :
    cbstm03a.call_m03b c trnx xref cust acct = .ok { c with
      xref_eof := true,
      xref_status := Array.make 2#usize [49#u8, 48#u8],
      m_rc := Array.make 2#usize [49#u8, 48#u8] } := by
  have hlen : xref.val.length = vals2.length := by rw [← hxref, List.length_map]
  have hnlt : ¬ c.xref_pos.val < xref.val.length := by omega
  refine eq_ok_of_wp ?_
  dsimp only [cbstm03a.call_m03b]
  aeneas_wp [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.make_val,
    hdd, List.cons.injEq, Nat.reduceEqDiff, hop, heof, hnlt, uscalar_ofNat_val]
  simp

theorem call_m03b_xref_read (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (vals2 : List (List FVal))
    (hdd : c.m_dd.val = [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 82#u8)
    (heof : c.xref_eof = false)
    (hxref : xref.val.map CardXrefRecord.vals = vals2)
    (_hvalid : ∀ v ∈ vals2, CardXrefRecord.Valid v) :
    ∃ c' : cbstm03a.Ctx,
      cbstm03a.call_m03b c trnx xref cust acct = .ok c' ∧
      c'.displays = c.displays ∧ c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = c.abended ∧
      if c.xref_pos.val < vals2.length then
        c'.m_rc = Array.make 2#usize [48#u8, 48#u8] ∧
        c'.xref_pos.val = c.xref_pos.val + 1 ∧
        c'.xref_eof = false ∧
        c'.m_fldt.val = latL (CardXrefRecord.encode (vals2.getD c.xref_pos.val [])) ++ List.replicate 950 32#u8
      else
        c'.m_rc = Array.make 2#usize [49#u8, 48#u8] ∧
        c'.xref_eof = true := by
  by_cases hpos : c.xref_pos.val < vals2.length
  · obtain ⟨c', hc', hrc, _, hpos', heof', hfldt, hd, hs, hh, ha⟩ :=
      call_m03b_xref_read_lt c trnx xref cust acct vals2 hdd hop heof hxref hpos
    exact ⟨c', hc', hd, hs, hh, ha, by simp [hpos, hrc, hpos', heof', hfldt]⟩
  · have hc' := call_m03b_xref_read_eof c trnx xref cust acct vals2 hdd hop heof hxref (by omega)
    exact ⟨_, hc', rfl, rfl, rfl, rfl, by simp [hpos]⟩

private theorem hcast_usize_9 : (IScalar.hcast .Usize (9#i64) : Usize) = 9#usize := by
  apply UScalar.eq_of_val_eq
  have hb : (9 : Int) < 2 ^ UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp only [UScalarTy.numBits, h] <;> omega
  rw [IScalar.hcast_val_eq, iscalar_ofInt_val, Int.emod_eq_of_lt (by omega) hb, uscalar_ofNat_val]; rfl

private theorem hcast_usize_11 : (IScalar.hcast .Usize (11#i64) : Usize) = 11#usize := by
  apply UScalar.eq_of_val_eq
  have hb : (11 : Int) < 2 ^ UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp only [UScalarTy.numBits, h] <;> omega
  rw [IScalar.hcast_val_eq, iscalar_ofInt_val, Int.emod_eq_of_lt (by omega) hb, uscalar_ofNat_val]; rfl

theorem call_m03b_cust_key (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (custs : List (List FVal)) (cid : Int)
    (hdd : c.m_dd.val = [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 75#u8)
    (hkln : c.m_key_ln = 9#i64)
    (hcid0 : 0 ≤ cid) (hcid9 : cid.natAbs < 10 ^ 9)
    (hkey : c.m_key.val.take 9 = latL (Sem.digitChars {} 9 cid.natAbs))
    (hcust : cust.val.map CustomerRecord.vals = custs)
    (hvalid : ∀ v ∈ custs, CustomerRecord.Valid v) :
    ∃ c' : cbstm03a.Ctx,
      cbstm03a.call_m03b c trnx xref cust acct = .ok c' ∧
      c'.displays = c.displays ∧ c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = c.abended ∧
      c'.xref_pos = c.xref_pos ∧ c'.xref_eof = c.xref_eof ∧
      match custs.find? (fun v => numOf (v.getD 0 default) == cid) with
      | none => c'.m_rc = Array.make 2#usize [50#u8, 51#u8]
      | some cval =>
        c'.m_rc = Array.make 2#usize [48#u8, 48#u8] ∧
        c'.m_fldt.val = latL (CustomerRecord.encode cval) ++ List.replicate 500 32#u8 := by
  obtain ⟨key1, hloop0, hkey1_val⟩ := call_m03b_loop0_eq c.m_key
  rw [hkey, latL_digitChars] at hkey1_val
  obtain ⟨⟨a, found⟩, hloop1, hmatch⟩ :=
    call_m03b_loop1_eq c.m_fldt cust key1 custs cid hcust hvalid hcid0 hcid9 hkey1_val
  have hdd_eq : ∀ (lit : Array U8 8#usize),
      cbstm03a.eq_bytes c.m_dd.to_slice lit.to_slice = .ok (decide (c.m_dd.val = lit.val)) := by
    intro lit; rw [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.to_slice, Slice.from_val]
  refine exists_ok_of_wp ?_
  dsimp only [cbstm03a.call_m03b]
  dsimp only at hmatch
  cases hfind : custs.find? (fun v => numOf (v.getD 0 default) == cid) with
  | none =>
    rw [hfind] at hmatch
    subst hmatch
    aeneas_wp [hdd_eq, Array.make_val, hdd, List.cons.injEq, Nat.reduceEqDiff,
      hop, hkln, hcast_usize_9, hloop0, hloop1, uscalar_ofNat_val, iscalar_ofInt_val]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | some cval =>
    rw [hfind] at hmatch
    rcases hmatch with ⟨rfl, hfldt⟩
    aeneas_wp [hdd_eq, Array.make_val, hdd, List.cons.injEq, Nat.reduceEqDiff,
      hop, hkln, hcast_usize_9, hloop0, hloop1, uscalar_ofNat_val, iscalar_ofInt_val]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hfldt⟩

theorem call_m03b_acct_key (c : cbstm03a.Ctx)
    (trnx : Slice cbstm03a.TrnxRecord) (xref : Slice cbstm03a.CardXrefRecord)
    (cust : Slice cbstm03a.CustomerRecord) (acct : Slice cbstm03a.AccountRecord)
    (accts : List (List FVal)) (aid : Int)
    (hdd : c.m_dd.val = [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hop : c.m_oper = 75#u8)
    (hkln : c.m_key_ln = 11#i64)
    (haid0 : 0 ≤ aid) (haid11 : aid.natAbs < 10 ^ 11)
    (hkey : c.m_key.val.take 11 = latL (Sem.digitChars {} 11 aid.natAbs))
    (hacct : acct.val.map AccountRecord.vals = accts)
    (hvalid : ∀ v ∈ accts, AccountRecord.Valid v) :
    ∃ c' : cbstm03a.Ctx,
      cbstm03a.call_m03b c trnx xref cust acct = .ok c' ∧
      c'.displays = c.displays ∧ c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = c.abended ∧
      c'.xref_pos = c.xref_pos ∧ c'.xref_eof = c.xref_eof ∧
      match accts.find? (fun v => numOf (v.getD 0 default) == aid) with
      | none => c'.m_rc = Array.make 2#usize [50#u8, 51#u8]
      | some aval =>
        c'.m_rc = Array.make 2#usize [48#u8, 48#u8] ∧
        c'.m_fldt.val = latL (AccountRecord.encode aval) ++ List.replicate 700 32#u8 := by
  obtain ⟨key1, hloop2, hkey1_val⟩ := call_m03b_loop2_eq c.m_key
  rw [hkey, latL_digitChars] at hkey1_val
  obtain ⟨kv, hkv, hkv_val⟩ := zoned_zeroPad11_eq key1.to_slice aid.natAbs haid11
    (by simp [Array.to_slice, hkey1_val])
  have hkv_aid : kv.val = aid := by omega
  obtain ⟨⟨a, found⟩, hloop3, hmatch⟩ :=
    call_m03b_loop3_eq c.m_fldt acct kv accts aid hacct hvalid hkv_aid
  have hdd_eq : ∀ (lit : Array U8 8#usize),
      cbstm03a.eq_bytes c.m_dd.to_slice lit.to_slice = .ok (decide (c.m_dd.val = lit.val)) := by
    intro lit; rw [eq_bytes_eq, Array.to_slice, Slice.from_val, Array.to_slice, Slice.from_val]
  refine exists_ok_of_wp ?_
  dsimp only [cbstm03a.call_m03b]
  dsimp only at hmatch
  cases hfind : accts.find? (fun v => numOf (v.getD 0 default) == aid) with
  | none =>
    rw [hfind] at hmatch
    subst hmatch
    aeneas_wp [hdd_eq, Array.make_val, hdd, List.cons.injEq, Nat.reduceEqDiff,
      hop, hkln, hcast_usize_11, hloop2, hkv, hloop3, uscalar_ofNat_val, iscalar_ofInt_val]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | some aval =>
    rw [hfind] at hmatch
    rcases hmatch with ⟨rfl, hfldt⟩
    aeneas_wp [hdd_eq, Array.make_val, hdd, List.cons.injEq, Nat.reduceEqDiff,
      hop, hkln, hcast_usize_11, hloop2, hkv, hloop3, uscalar_ofNat_val, iscalar_ofInt_val]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hfldt⟩

end EquivLean.Modernize.Cbstm03a.Rust
