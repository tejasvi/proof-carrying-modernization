import EquivLean.Modernize.Cbstm03a.RustDefs

/-!
# CBSTM03A → Rust, part 1: byte, table, string, and numeric helper specifications

Proves pure-Lean specifications in `EquivLean.Modernize.Cbstm03a.Rust` for all helper functions
of `cbstm03a` (`Demo/Gen/Aeneas/ModCbstm03a/Funs.lean`):
1. `vb_eq` and `app_eq`
2. `put_eq` (`put_val`) and `fill_eq` (`fill_val`)
3. `eq_bytes_eq`
4. `lat2ebc_table_eq` and `gt_bytes_eq`
5. `put_unum_eq` and `put_snum_eq` (with `.Holds` and `zeroPad` forms)
6. `digits11_eq`, `fmt_9_99_eq`, and `fmt_z_99_eq`
7. `zoned_eq` and `zoned_digitChars_eq`
8. `str_part_empty_eq` (`str_part_empty_fit`, `str_part_empty_ovw`), `str_part_single_eq`
   (`str_part_single_ovw`), and `str_part_double_eq` (`str_part_double_ovw`)
9. `add1_eq` and `add_trunc11_eq`
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol Cobol.StmCore EquivLean.Cobol.Rec
open EquivLean.Modernize.Cbstm03a.StmBridge EquivLean.Modernize.Cbstm03a.Model

namespace EquivLean.Modernize.Cbstm03a.Rust

open Cobol.Digits (toDigits)

theorem usize_max_ge : 4294967295 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max_eq, U64.max_eq]

/-! ## 1. `vb` and `app` -/

theorem app_loop_spec (s : Slice U8) (v0 : alloc.vec.Vec U8)
    (h : v0.val.length + s.val.length ≤ Usize.max) :
    wp (loop (fun (v1, i1) => cbstm03a.app_loop.body s v1 i1) (v0, 0#usize))
      (fun o => o = .ok (alloc.vec.Vec.from (v0.val ++ s.val) (by simp; omega))) := by
  refine wp_loop (loop_shape _)
    (fun x => x.2.val ≤ s.val.length ∧ x.1.val = v0.val ++ s.val.take x.2.val)
    (fun x => s.val.length - x.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro v i ⟨hi, hv⟩
    aeneas_wp [rust_loop_body]
    by_cases hlt : i.val < s.val.length
    · have hvl : v.val.length < Usize.max := by
        rw [hv]; simp only [List.length_append, List.length_take]; omega
      have hov : i.val + 1 ≤ Usize.max := by omega
      simp only [hlt, hvl, hov, _root_.dite_true, _root_.ite_true, loopCls_cont,
        UScalar.ofNatCore_val_eq, alloc.vec.Vec.from_val]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hv, take_succ_of_lt hlt, List.append_assoc]
    · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq, alloc.vec.Vec.eq_iff,
        alloc.vec.Vec.from_val]
      rw [hv, List.take_of_length_le (by omega)]
  · simp

theorem app_eq (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.val.length + s.val.length ≤ Usize.max) :
    cbstm03a.app v s = .ok (alloc.vec.Vec.from (v.val ++ s.val) (by simp; omega)) := by
  refine eq_ok_of_wp ?_
  simp only [cbstm03a.app, cbstm03a.app_loop]
  exact app_loop_spec s v h

theorem vb_eq (s : Slice U8) :
    cbstm03a.vb s = .ok (alloc.vec.Vec.from s.val (by scalar_tac)) := by
  have hs : s.val.length ≤ Usize.max := by scalar_tac
  refine eq_ok_of_wp ?_
  simp only [cbstm03a.vb, cbstm03a.vb_loop]
  have hb : cbstm03a.vb_loop.body = cbstm03a.app_loop.body := rfl
  rw [hb]
  have := app_loop_spec s (alloc.vec.Vec.new U8) (by simp [hs])
  simpa using this

/-! ## 2. `put` and `fill` -/

theorem putL_zero (dst : List U8) (off : Nat) (src : List U8) :
    putL dst off 0 src = dst := by
  simp [putL]

theorem putL_eq_of_length_eq (dst : List U8) (off len : Nat) (src : List U8)
    (hs : src.length = len) :
    putL dst off len src = dst.take off ++ src ++ dst.drop (off + len) := by
  simp [putL, hs]

theorem putL_step (dst : List U8) (off i : Nat) (src : List U8)
    (h : off + i < dst.length) :
    (putL dst off i src).set (off + i)
      (if hlt : i < src.length then src[i] else 32#u8) =
      putL dst off (i + 1) src := by
  unfold putL
  have h1 : (dst.take off).length = off := by simp; omega
  have h2 : (src.take i ++ List.replicate (i - src.length) 32#u8).length = i := by simp; omega
  have h12 : (dst.take off ++ (src.take i ++ List.replicate (i - src.length) 32#u8)).length =
      off + i := by rw [List.length_append, h1, h2]
  rw [List.set_append_right _ _ (by omega), h12, Nat.sub_self, List.drop_eq_getElem_cons h,
    List.set_cons_zero, drop_add_add_one]
  by_cases hlt : i < src.length
  · have hsub1 : i - src.length = 0 := by omega
    have hsub2 : i + 1 - src.length = 0 := by omega
    simp only [hlt, ↓reduceDIte, hsub1, hsub2, List.replicate_zero, List.append_nil,
      take_succ_of_lt hlt, List.append_assoc, List.singleton_append]
  · have hge : src.length ≤ i := by omega
    simp only [hlt, ↓reduceDIte, List.take_of_length_le hge,
      List.take_of_length_le (show src.length ≤ i + 1 by omega),
      replicate_succ_sub i src.length 32#u8 hge, List.append_assoc, List.singleton_append]

theorem put_val (dst : Slice U8) (off len : Usize) (src : Slice U8)
    (h : off.val + len.val ≤ dst.val.length) :
    cbstm03a.put dst off len src =
      .ok (Slice.from (putL dst.val off.val len.val src.val)
        (by rw [length_putL _ _ _ _ h]; exact dst.property)) := by
  have hd : dst.val.length ≤ Usize.max := dst.property
  refine eq_ok_of_wp ?_
  simp only [cbstm03a.put, cbstm03a.put_loop]
  refine wp_loop (loop_shape _)
    (fun (s : Slice U8 × Usize) => s.2.val ≤ len.val ∧
      s.1.val = putL dst.val off.val s.2.val src.val)
    (fun s => len.val - s.2.val) ?_ _ ?_
  · rintro ⟨cur, i⟩ ⟨hi, hcur⟩
    simp only at hi hcur
    have hcl : cur.val.length = dst.val.length := by
      rw [hcur, length_putL _ _ _ _ (by omega)]
    aeneas_wp [rust_loop_body, slice_update_eq, hcl]
    by_cases hlt : i.val < len.val
    · have hoi : off.val + i.val < dst.val.length := by omega
      have hmax1 : off.val + i.val ≤ Usize.max := by omega
      have hmax2 : i.val + 1 ≤ Usize.max := by omega
      by_cases hsi : i.val < src.val.length
      · simp only [hlt, hoi, hmax1, hmax2, hsi, _root_.dite_true, _root_.ite_true,
          loopCls_cont, UScalar.ofNatCore_val_eq, Slice.from_val]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [hcur, ← putL_step dst.val off.val i.val src.val hoi]
        simp [hsi]
      · simp only [hlt, hoi, hmax1, hmax2, hsi, _root_.dite_true, _root_.ite_true,
          _root_.ite_false, loopCls_cont, UScalar.ofNatCore_val_eq, Slice.from_val]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [hcur, ← putL_step dst.val off.val i.val src.val hoi]
        simp [hsi]
    · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq, Slice.eq_iff,
        Slice.from_val]
      rw [hcur, show i.val = len.val by omega]
  · simp [putL_zero]

theorem put_eq (dst : Slice U8) (off len : Usize) (src : Slice U8)
    (h : off.val + len.val ≤ dst.val.length) :
    ∃ s' : Slice U8, cbstm03a.put dst off len src = .ok s' ∧
      s'.val = putL dst.val off.val len.val src.val :=
  ⟨_, put_val dst off len src h, Slice.from_val _ _⟩

theorem fillL_zero (dst : List U8) (off : Nat) (ch : U8) :
    fillL dst off 0 ch = dst := by
  simp [fillL]

theorem fillL_step (dst : List U8) (off i : Nat) (ch : U8)
    (h : off + i < dst.length) :
    (fillL dst off i ch).set (off + i) ch = fillL dst off (i + 1) ch := by
  unfold fillL
  have h1 : (dst.take off ++ List.replicate i ch).length = off + i := by simp; omega
  rw [List.set_append_right _ _ (by omega), h1, Nat.sub_self, List.drop_eq_getElem_cons h,
    List.set_cons_zero, List.replicate_succ', drop_add_add_one]
  simp only [List.append_assoc, List.singleton_append]

theorem fill_val (dst : Slice U8) (off len : Usize) (ch : U8)
    (h : off.val + len.val ≤ dst.val.length) :
    cbstm03a.fill dst off len ch =
      .ok (Slice.from (fillL dst.val off.val len.val ch)
        (by rw [length_fillL _ _ _ _ h]; exact dst.property)) := by
  have hd : dst.val.length ≤ Usize.max := dst.property
  refine eq_ok_of_wp ?_
  simp only [cbstm03a.fill, cbstm03a.fill_loop]
  refine wp_loop (loop_shape _)
    (fun (s : Slice U8 × Usize) => s.2.val ≤ len.val ∧
      s.1.val = fillL dst.val off.val s.2.val ch)
    (fun s => len.val - s.2.val) ?_ _ ?_
  · rintro ⟨cur, i⟩ ⟨hi, hcur⟩
    simp only at hi hcur
    have hcl : cur.val.length = dst.val.length := by
      rw [hcur, length_fillL _ _ _ _ (by omega)]
    aeneas_wp [rust_loop_body, slice_update_eq, hcl]
    by_cases hlt : i.val < len.val
    · have hoi : off.val + i.val < dst.val.length := by omega
      have hmax1 : off.val + i.val ≤ Usize.max := by omega
      have hmax2 : i.val + 1 ≤ Usize.max := by omega
      simp only [hlt, hoi, hmax1, hmax2, _root_.dite_true, _root_.ite_true,
        loopCls_cont, UScalar.ofNatCore_val_eq, Slice.from_val]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hcur, fillL_step dst.val off.val i.val ch hoi]
    · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq, Slice.eq_iff,
        Slice.from_val]
      rw [hcur, show i.val = len.val by omega]
  · simp [fillL_zero]

theorem fill_eq (dst : Slice U8) (off len : Usize) (ch : U8)
    (h : off.val + len.val ≤ dst.val.length) :
    ∃ s' : Slice U8, cbstm03a.fill dst off len ch = .ok s' ∧
      s'.val = fillL dst.val off.val len.val ch :=
  ⟨_, fill_val dst off len ch h, Slice.from_val _ _⟩

/-! ## 3. `eq_bytes` -/

theorem take_succ_eq_iff {α : Type _} {a b : List α} {i : Nat}
    (ha : i < a.length) (hb : i < b.length) :
    a.take (i + 1) = b.take (i + 1) ↔ a.take i = b.take i ∧ a[i] = b[i] := by
  rw [take_succ_of_lt ha, take_succ_of_lt hb]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp; omega)
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2]

theorem eq_bytes_eq (a b : Slice U8) :
    cbstm03a.eq_bytes a b = .ok (decide (a.val = b.val)) := by
  have ha : a.val.length ≤ Usize.max := a.property
  refine eq_ok_of_wp ?_
  unfold cbstm03a.eq_bytes
  aeneas_wp []
  by_cases hl : a.val.length = b.val.length
  · simp only [hl, not_true_eq_false, _root_.ite_false, cbstm03a.eq_bytes_loop]
    refine wp_loop (loop_shape _)
      (fun (s : Bool × Usize) => s.2.val ≤ a.val.length ∧
        s.1 = decide (a.val.take s.2.val = b.val.take s.2.val))
      (fun s => a.val.length - s.2.val) ?_ _ (by simp)
    rintro ⟨res, i⟩ ⟨hi, hres⟩
    simp only at hi hres
    aeneas_wp [rust_loop_body]
    by_cases hlt : i.val < a.val.length
    · have hltb : i.val < b.val.length := by omega
      have hov : i.val + 1 ≤ Usize.max := by omega
      by_cases heq : a.val[i.val].val = b.val[i.val].val
      · have e1 : a.val[i.val] = b.val[i.val] := UScalar.eq_of_val_eq heq
        simp only [hlt, hltb, hov, heq, not_true_eq_false, _root_.dite_true, _root_.ite_true,
          _root_.ite_false, loopCls_cont, UScalar.ofNatCore_val_eq]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        simp only [hres, take_succ_eq_iff hlt hltb, e1, and_true]
      · have e1 : ¬ a.val[i.val] = b.val[i.val] := fun e => heq (e ▸ rfl)
        simp only [hlt, hltb, hov, heq, not_false_eq_true, _root_.dite_true, _root_.ite_true,
          loopCls_cont, UScalar.ofNatCore_val_eq]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        simp only [take_succ_eq_iff hlt hltb, e1, and_false, decide_false]
    · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq]
      have hi' : i.val = a.val.length := by omega
      rw [hres, hi', List.take_length, hl, List.take_length]
  · simp only [hl, not_false_eq_true, _root_.ite_true, Except.ok.injEq]
    exact (decide_eq_false (fun (hab : a.val = b.val) => hl (hab ▸ rfl))).symm

/-! ## 4. `lat2ebc_table` and `gt_bytes` -/

theorem ebc2lat_table :
    cbstm03a.EBC2LAT.val = (List.range 256).map (fun j => lat (UInt8.ofNat j)) := by
  decide +kernel

theorem ebc2lat_at (j : Nat) (hj : j < 256) :
    cbstm03a.EBC2LAT.val[j]'(by simp; omega) = lat (UInt8.ofNat j) := by
  have h := congrArg (fun l => l[j]?) ebc2lat_table
  simp only [List.getElem?_map, List.getElem?_range hj] at h
  rw [List.getElem?_eq_getElem (by simp; omega)] at h
  exact Option.some.inj h

theorem lat2ebc_table_eq :
    ∃ tbl : Array U8 256#usize, cbstm03a.lat2ebc_table = .ok tbl ∧
      ∀ b : UInt8, tbl.val.getD (cp037Code b) 0#u8 = byteOf b.toNat := by
  refine exists_ok_of_wp ?_
  simp only [cbstm03a.lat2ebc_table, cbstm03a.lat2ebc_table_loop]
  refine wp_loop (loop_shape _)
    (fun (s : Array U8 256#usize × Usize) => s.2.val ≤ 256 ∧
      ∀ b : UInt8, b.toNat < s.2.val → (s.1.val.getD (cp037Code b) default).val = b.toNat)
    (fun s => 256 - s.2.val) ?_ _ ?_
  · rintro ⟨t, e⟩ ⟨he, ht⟩
    simp only at he ht
    have htl : t.val.length = 256 := t.property
    have hel : cbstm03a.EBC2LAT.val.length = 256 := cbstm03a.EBC2LAT.property
    aeneas_wp [rust_loop_body, array_index_usize_eq, array_update_eq, UScalar.cast_val_eq,
      htl, hel]
    by_cases hlt : e.val < 256
    · have hat := ebc2lat_at e.val hlt
      have hval : (cbstm03a.EBC2LAT.val[e.val]'(by omega)).val = cp037Code (UInt8.ofNat e.val) := by
        rw [hat, lat_val]
      have hcp : cp037Code (UInt8.ofNat e.val) < 256 := cp037Code_lt _
      have hm1 : cp037Code (UInt8.ofNat e.val) % 2 ^ UScalarTy.Usize.numBits =
          cp037Code (UInt8.ofNat e.val) := by
        apply Nat.mod_eq_of_lt
        rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.Usize_numBits_eq, h] <;> omega
      have hmax : e.val + 1 ≤ Usize.max := by have := usize_max_ge; omega
      simp only [hlt, hval, hm1, hcp, hmax, _root_.dite_true, _root_.ite_true,
        loopCls_cont, UScalar.ofNatCore_val_eq, Array.from_val]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      intro b hb
      have hcb : cp037Code b < 256 := cp037Code_lt b
      have hcb' : cp037Code b < t.val.length := by omega
      let v8 : U8 := UScalar.cast .U8 e
      have hv8 : v8.val = e.val := by
        simp [v8, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq, Nat.mod_eq_of_lt hlt]
      change ((t.val.set (cp037Code (UInt8.ofNat e.val)) v8).getD (cp037Code b) default).val = b.toNat
      have hcb_set : cp037Code b < (t.val.set (cp037Code (UInt8.ofNat e.val)) v8).length := by
        simp [htl, hcb]
      by_cases hbe : b.toNat = e.val
      · have hbeq : UInt8.ofNat e.val = b := by rw [← hbe, UInt8.ofNat_toNat]
        rw [List.getD_eq_getElem _ default hcb_set]
        simp only [hbeq, List.getElem_set_self, hv8, hbe]
      · have hblt : b.toNat < e.val := by omega
        have hne : cp037Code (UInt8.ofNat e.val) ≠ cp037Code b := by
          intro h
          have heq := cp037Code_inj h
          have := congrArg UInt8.toNat heq
          rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt] at this
          exact hbe this.symm
        rw [List.getD_eq_getElem _ default hcb_set, List.getElem_set_ne hne,
          ← List.getD_eq_getElem _ default hcb']
        exact ht b hblt
    · simp only [hlt, _root_.ite_false, loopCls_done]
      have he256 : e.val = 256 := by omega
      refine ⟨t, rfl, fun b => ?_⟩
      rw [byteOf_val _ b.toNat_lt]
      exact ht b (by rw [he256]; exact b.toNat_lt)
  · exact ⟨by simp, fun b hb => by simp at hb⟩

set_option maxRecDepth 100000 in
theorem gt_bytes_eq (a b : Slice U8) (tbl : Array U8 256#usize)
    (htbl : ∀ x : UInt8, tbl.val.getD (cp037Code x) 0#u8 = byteOf x.toNat)
    (bs1 bs2 : List UInt8) (ha : a.val = latL bs1) (hb : b.val = latL bs2)
    (hlen : bs1.length = bs2.length) :
    cbstm03a.gt_bytes a b tbl = .ok (Sem.cmpBytes bs1 bs2 == .gt) := by
  have hal : a.val.length = bs1.length := by simp [ha]
  have hbl : b.val.length = bs1.length := by simp [hb, hlen]
  have htl : tbl.val.length = 256 := tbl.property
  have hmax0 : a.val.length ≤ Usize.max := a.property
  refine eq_ok_of_wp ?_
  simp only [cbstm03a.gt_bytes, cbstm03a.gt_bytes_loop]
  refine wp_loop (loop_shape _)
    (fun (s : Bool × Bool × Usize) =>
      (s.2.1 = true ∧ s.1 = (Sem.cmpBytes bs1 bs2 == .gt)) ∨
      (s.2.1 = false ∧ s.1 = false ∧ s.2.2.val ≤ bs1.length ∧
        Sem.cmpBytes bs1 bs2 = Sem.cmpBytes (bs1.drop s.2.2.val) (bs2.drop s.2.2.val)))
    (fun s => if s.2.1 then 0 else bs1.length - s.2.2.val + 1) ?_ _ ?_
  · rintro ⟨res, decided, i⟩ hinv
    rcases hinv with ⟨hdec, hres⟩ | ⟨hdec, hres, hi, hcmp⟩
    · simp only at hdec hres
      subst hdec hres
      simp [cbstm03a.gt_bytes_loop.body, loopCls_done]
    · simp only at hdec hres hi hcmp
      subst hdec hres
      aeneas_wp [rust_loop_body, array_index_usize_eq, UScalar.cast_val_eq, hal, hbl, htl]
      by_cases hlt : i.val < bs1.length
      · have hlt2 : i.val < bs2.length := by omega
        have ha_at : (a.val[i.val]'(by omega)).val = cp037Code (bs1[i.val]) := by
          simp [ha, latL, lat_val]
        have hb_at : (b.val[i.val]'(by omega)).val = cp037Code (bs2[i.val]) := by
          simp [hb, latL, lat_val]
        have hc1 : cp037Code (bs1[i.val]) < 256 := cp037Code_lt _
        have hc2 : cp037Code (bs2[i.val]) < 256 := cp037Code_lt _
        have hm1 : cp037Code (bs1[i.val]) % 2 ^ UScalarTy.Usize.numBits = cp037Code (bs1[i.val]) := by
          apply Nat.mod_eq_of_lt
          rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.Usize_numBits_eq, h] <;> omega
        have hm2 : cp037Code (bs2[i.val]) % 2 ^ UScalarTy.Usize.numBits = cp037Code (bs2[i.val]) := by
          apply Nat.mod_eq_of_lt
          rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.Usize_numBits_eq, h] <;> omega
        have hx : (tbl.val[cp037Code (bs1[i.val])]'(by omega)).val = (bs1[i.val]).toNat := by
          have := htbl (bs1[i.val])
          rw [List.getD_eq_getElem _ 0#u8 (by omega)] at this
          rw [this, byteOf_val _ (UInt8.toNat_lt _)]
        have hy : (tbl.val[cp037Code (bs2[i.val])]'(by omega)).val = (bs2[i.val]).toNat := by
          have := htbl (bs2[i.val])
          rw [List.getD_eq_getElem _ 0#u8 (by omega)] at this
          rw [this, byteOf_val _ (UInt8.toNat_lt _)]
        have hov : i.val + 1 ≤ Usize.max := by omega
        have hdrop1 : bs1.drop i.val = bs1[i.val] :: bs1.drop (i.val + 1) :=
          List.drop_eq_getElem_cons hlt
        have hdrop2 : bs2.drop i.val = bs2[i.val] :: bs2.drop (i.val + 1) :=
          List.drop_eq_getElem_cons hlt2
        rw [hdrop1, hdrop2, Sem.cmpBytes.eq_1] at hcmp
        simp only [UInt8.lt_iff_toNat_lt] at hcmp
        simp only [hlt, ha_at, hb_at, hm1, hm2, hc1, hc2, hx, hy, hov, _root_.dite_true,
          _root_.ite_true]
        by_cases hgt : (bs2[i.val]).toNat < (bs1[i.val]).toNat
        · have hnlt : ¬ (bs1[i.val]).toNat < (bs2[i.val]).toNat := by omega
          simp only [hgt, hnlt, _root_.ite_true, _root_.ite_false, loopCls_cont] at hcmp ⊢
          exact ⟨Or.inl ⟨trivial, by rw [hcmp]; rfl⟩, by simp only [↓reduceIte, Bool.false_eq_true]; omega⟩
        · by_cases hlt' : (bs1[i.val]).toNat < (bs2[i.val]).toNat
          · simp only [hgt, hlt', _root_.ite_true, _root_.ite_false, loopCls_cont] at hcmp ⊢
            exact ⟨Or.inl ⟨trivial, by rw [hcmp]; rfl⟩, by simp only [↓reduceIte, Bool.false_eq_true]; omega⟩
          · simp only [hgt, hlt', _root_.ite_false, loopCls_cont, UScalar.ofNatCore_val_eq] at hcmp ⊢
            exact ⟨Or.inr ⟨trivial, trivial, by omega, hcmp⟩, by simp only [↓reduceIte, Bool.false_eq_true]; omega⟩
      · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq]
        have hi' : i.val = bs1.length := by omega
        have hd1 : bs1.drop i.val = [] := by simp [hi']
        have hd2 : bs2.drop i.val = [] := by simp [hi', ← hlen]
        rw [hd1, hd2, Cobol.StmCore.cmpBytes_self] at hcmp
        rw [hcmp]; rfl
  · exact Or.inr ⟨rfl, rfl, Nat.zero_le _, rfl⟩

/-! ## 5. `put_unum` and `put_snum` -/

theorem latL_digitChars (d x : Nat) :
    latL (Sem.digitChars {} d x) = zeroPad d x := by
  unfold latL Sem.digitChars zeroPad zpad
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro a ha
  simp only [Function.comp_apply, lat]
  rw [cp037Code_digitByte a (Cobol.Digits.toDigits_lt (by decide) d x a ha)]

theorem latL_encodeNum_unsigned (d : Nat) (sc : Int) (hd : 0 < d) (v : Int) :
    latL (encodeNum {} { digits := d, scale := sc, usage := .display, signed := false } v) =
      zeroPad d v.natAbs := by
  rw [latL_eq_u8Line, text_unsigned rfl rfl hd v]
  rfl

/-- The overpunched last digit of a signed DISPLAY value (`{`, `A` … `I`, `}`, `J` … `R`), as a
Latin-1 byte. -/
def overByte (v : Int) : U8 := byteOf (overpunch (decide (v < 0)) (v.natAbs % 10))

theorem overByte_val (v : Int) :
    (overByte v).val = overpunch (decide (v < 0)) (v.natAbs % 10) := by
  have := Nat.mod_lt v.natAbs (show 10 > 0 by norm_num)
  unfold overByte
  apply byteOf_val
  unfold overpunch
  split_ifs <;> omega

theorem latL_encodeNum_signed (d : Nat) (sc : Int) (v : Int) :
    latL (encodeNum {} { digits := d, scale := sc, usage := .display, signed := true } v) =
      zeroPad (d - 1) (v.natAbs / 10) ++ [overByte v] := by
  rw [latL_eq_u8Line, text_signed rfl rfl rfl rfl v]
  simp [u8Line, zeroPad, overByte]

theorem zeroPad_succ_right (m x : Nat) :
    zeroPad (m + 1) x = zeroPad m (x / 10) ++ [byteOf (48 + x % 10)] := by
  simp only [zeroPad, zpad, toDigits_succ, List.map_append, List.map_cons, List.map_nil]

theorem set_take_succ_mid {α : Type _} (dst Z R : List α) (k : Nat) (c : α)
    (hk : k < dst.length) :
    (dst.take (k + 1) ++ Z ++ R).set k c =
      dst.take k ++ ([c] ++ Z) ++ R := by
  rw [take_succ_of_lt hk, List.append_assoc, List.append_assoc,
    List.set_append_right _ _ (by simp)]
  have hl : (dst.take k).length = k := by simp; omega
  rw [hl, Nat.sub_self, List.singleton_append, List.set_cons_zero]
  simp

set_option maxHeartbeats 2000000 in
theorem put_unum_loop_spec (dst : Slice U8) (off n : Usize) (x : Nat) (m : U64)
    (h : off.val + n.val ≤ dst.val.length) (hm : m.val = x) :
    wp (cbstm03a.put_unum_loop dst off m n)
      (fun o => ∃ s' : Slice U8, o = .ok s' ∧
        s'.val = putL dst.val off.val n.val (zeroPad n.val x)) := by
  have hd : dst.val.length ≤ Usize.max := dst.property
  simp only [cbstm03a.put_unum_loop]
  refine wp_loop (loop_shape _)
    (fun (s : Slice U8 × U64 × Usize) =>
      s.2.2.val ≤ n.val ∧
      s.2.1.val = x / 10 ^ (n.val - s.2.2.val) ∧
      s.1.val = dst.val.take (off.val + s.2.2.val) ++ zeroPad (n.val - s.2.2.val) x ++
        dst.val.drop (off.val + n.val))
    (fun s => s.2.2.val) ?_ _ ?_
  · rintro ⟨cur, m', i⟩ ⟨hi, hm', hcur⟩
    simp only at hi hm' hcur
    have hcl : cur.val.length = dst.val.length := by
      rw [hcur]
      simp only [List.length_append, List.length_take, zeroPad_length, List.length_drop]
      omega
    aeneas_wp [rust_loop_body, slice_update_eq, UScalar.cast_val_eq, Slice.from_val, hcl]
    by_cases hgt : 0 < i.val
    · have hoi : off.val + (i.val - 1) < dst.val.length := by omega
      have hd10 : m'.val % 10 < 10 := Nat.mod_lt _ (by norm_num)
      have h256 : m'.val % 10 % 2 ^ 8 = m'.val % 10 := Nat.mod_eq_of_lt (by omega)
      simp only [hgt, _root_.ite_true, h256]
      split_ifs
      all_goals try (exfalso; omega)
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq, Slice.from_val]
      refine ⟨⟨by omega, ?_, ?_⟩, by omega⟩
      · rw [hm', Nat.div_div_eq_div_mul, ← Nat.pow_succ]
        congr 2; omega
      · rw [hcur, show off.val + i.val = (off.val + (i.val - 1)) + 1 by omega,
          set_take_succ_mid _ _ _ _ _ hoi,
          show n.val - (i.val - 1) = (n.val - i.val) + 1 by omega, zeroPad_succ_left]
        congr 2
        simp only [List.append_cancel_right_eq, List.cons.injEq, and_true]
        apply UScalar.eq_of_val_eq
        rw [UScalar.ofNatCore_val_eq, byteOf_val _ (by omega), hm']
    · simp only [hgt, _root_.ite_false, loopCls_done]
      have hi0 : i.val = 0 := by omega
      refine ⟨cur, rfl, ?_⟩
      rw [hcur, hi0, Nat.add_zero, Nat.sub_zero, putL_eq_of_length_eq _ _ _ _ (zeroPad_length _ _)]
  · refine ⟨le_refl _, by simp [hm], ?_⟩
    have hz : zeroPad 0 x = [] := by simp [zeroPad, zpad, toDigits]
    simp [hz]

theorem put_unum_zeroPad (dst : Slice U8) (off n : Usize) (v : I64)
    (h : off.val + n.val ≤ dst.val.length) (hmin : -9223372036854775808 < v.val) :
    ∃ s' : Slice U8, cbstm03a.put_unum dst off n v = .ok s' ∧
      s'.val = putL dst.val off.val n.val (zeroPad n.val v.val.natAbs) := by
  refine exists_ok_of_wp ?_
  unfold cbstm03a.put_unum
  by_cases hv : v.val < 0
  · have hlt : (v < 0#i64) = True := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_true]
    aeneas_wp [IScalar.cast_val_eq]
    simp (disch := omega) only [dite_eq_left]
    refine put_unum_loop_spec dst off n v.val.natAbs _ h ?_
    simp only [IScalar.hcast_val_eq, IScalar.ofInt_val_eq, UScalarTy.U64_numBits_eq, Int.reducePow]
    omega
  · have hlt : (v < 0#i64) = False := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_false, wp_bind, wp_ok]
    refine put_unum_loop_spec dst off n v.val.natAbs _ h ?_
    have := v.hBounds
    simp only [IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq, IScalarTy.I64_numBits_eq,
      Int.reducePow] at *
    omega

theorem put_unum_eq (dst : Slice U8) (off n : Usize) (v : I64) (sc : Int := 0)
    (hn : 0 < n.val) (h : off.val + n.val ≤ dst.val.length)
    (hmin : -9223372036854775808 < v.val) :
    ∃ s' : Slice U8, cbstm03a.put_unum dst off n v = .ok s' ∧
      s'.val = putL dst.val off.val n.val
        (latL (encodeNum {} { digits := n.val, scale := sc, usage := .display, signed := false } v.val)) := by
  rw [latL_encodeNum_unsigned n.val sc hn v.val]
  exact put_unum_zeroPad dst off n v h hmin

theorem put_unum_holds (dst : Slice U8) (off n : Usize) (v : I64) (sc : Int := 0)
    (hn : 0 < n.val) (hn18 : n.val ≤ 18) (h : off.val + n.val ≤ dst.val.length)
    (hholds : ({ digits := n.val, scale := sc, usage := .display, signed := false } : NumFmt).Holds {} v.val) :
    ∃ s' : Slice U8, cbstm03a.put_unum dst off n v = .ok s' ∧
      s'.val = putL dst.val off.val n.val
        (latL (encodeNum {} { digits := n.val, scale := sc, usage := .display, signed := false } v.val)) := by
  have hh := (EquivLean.Modernize.GlueKit.holds_display rfl).mp hholds
  dsimp only at hh
  have hpow : (10 : Nat) ^ n.val ≤ 10 ^ 18 := Nat.pow_le_pow_right (by norm_num) hn18
  exact put_unum_eq dst off n v sc hn h (by omega)

theorem slice_index_usize_getD {α : Type _} [Inhabited α] (s : Slice α) (i : Usize) :
    Slice.index_usize s i =
      if i.val < s.val.length then .ok (s.val.getD i.val default)
      else .fail .arrayOutOfBounds := by
  simp only [Slice.index_usize, Slice.getElem?_Usize_eq]
  by_cases h : i.val < s.val.length
  · simp [h]
  · simp [h]

theorem getD_append_cons {α : Type _} (A B : List α) (b d : α) :
    (A ++ b :: B).getD A.length d = b := by
  induction A with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem putL_zeroPad_getD (dst : List U8) (off n v : Nat)
    (hn : 0 < n) (h : off + n ≤ dst.length) :
    (putL dst off n (zeroPad n v)).getD (off + n - 1) default = byteOf (48 + v % 10) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsplit : putL dst off (m + 1) (zeroPad (m + 1) v) =
      (dst.take off ++ zeroPad m (v / 10)) ++ byteOf (48 + v % 10) :: dst.drop (off + (m + 1)) := by
    rw [putL_eq_of_length_eq _ _ _ _ (zeroPad_length _ _), zeroPad_succ_right]
    simp [List.append_assoc]
  have hpre : off + (m + 1) - 1 = (dst.take off ++ zeroPad m (v / 10)).length := by
    simp [zeroPad_length]; omega
  rw [hsplit, hpre, getD_append_cons]

theorem putL_zeroPad_set_last (dst : List U8) (off n : Nat) (v : Int) (c : U8)
    (hn : 0 < n) (h : off + n ≤ dst.length) (hc : c = overByte v) :
    (putL dst off n (zeroPad n v.natAbs)).set (off + n - 1) c =
      putL dst off n (zeroPad (n - 1) (v.natAbs / 10) ++ [overByte v]) := by
  subst hc
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsplit : putL dst off (m + 1) (zeroPad (m + 1) v.natAbs) =
      (dst.take off ++ zeroPad m (v.natAbs / 10)) ++
        byteOf (48 + v.natAbs % 10) :: dst.drop (off + (m + 1)) := by
    rw [putL_eq_of_length_eq _ _ _ _ (zeroPad_length _ _), zeroPad_succ_right]
    simp [List.append_assoc]
  have hpre : off + (m + 1) - 1 = (dst.take off ++ zeroPad m (v.natAbs / 10)).length := by
    simp [zeroPad_length]; omega
  have hlen_enc : (zeroPad m (v.natAbs / 10) ++ [overByte v]).length = m + 1 := by
    simp [zeroPad_length]
  rw [hsplit, hpre, Cobol.StmCore.set_append_cons, Nat.add_sub_cancel,
    putL_eq_of_length_eq _ _ _ _ hlen_enc]
  simp [List.append_assoc]

set_option maxHeartbeats 2000000 in
theorem put_snum_zeroPad (dst : Slice U8) (off n : Usize) (v : I64)
    (hn : 0 < n.val) (h : off.val + n.val ≤ dst.val.length)
    (hmin : -9223372036854775808 < v.val) :
    ∃ s' : Slice U8, cbstm03a.put_snum dst off n v = .ok s' ∧
      s'.val = putL dst.val off.val n.val
        (zeroPad (n.val - 1) (v.val.natAbs / 10) ++ [overByte v.val]) := by
  have hd : dst.val.length ≤ Usize.max := dst.property
  obtain ⟨dst1, hpu, hdst1⟩ := put_unum_zeroPad dst off n v h hmin
  have hd10 : v.val.natAbs % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hdst1_len : dst1.val.length = dst.val.length := by
    rw [hdst1, length_putL _ _ _ _ h]
  have hget : dst1.val.getD (off.val + n.val - 1) default = byteOf (48 + v.val.natAbs % 10) := by
    rw [hdst1]
    exact putL_zeroPad_getD dst.val off.val n.val v.val.natAbs hn h
  have hset : ∀ c : U8, c = overByte v.val →
      dst1.val.set (off.val + n.val - 1) c =
        putL dst.val off.val n.val (zeroPad (n.val - 1) (v.val.natAbs / 10) ++ [overByte v.val]) := by
    intro c hc
    rw [hdst1]
    exact putL_zeroPad_set_last dst.val off.val n.val v.val c hn h hc
  have hb : (byteOf (48 + v.val.natAbs % 10)).val = 48 + v.val.natAbs % 10 :=
    byteOf_val _ (by omega)
  have hmax1 : off.val + n.val ≤ Usize.max := by omega
  have h1le : 1 ≤ off.val + n.val := by omega
  have hlt1 : off.val + n.val - 1 < dst.val.length := by omega
  have h48 : 48 ≤ 48 + v.val.natAbs % 10 := by omega
  have h74a : 74 + v.val.natAbs % 10 ≤ 255 := by omega
  have h65a : 65 + v.val.natAbs % 10 ≤ 255 := by omega
  have h74b : 1 ≤ 74 + v.val.natAbs % 10 := by omega
  have h65b : 1 ≤ 65 + v.val.natAbs % 10 := by omega
  refine exists_ok_of_wp ?_
  simp only [cbstm03a.put_snum, hpu, wp_bind, wp_ok]
  aeneas_wp [slice_index_usize_getD, slice_update_eq, Slice.from_val, uscalar_ofNat_val,
    iscalar_ofInt_val, hdst1_len, hn, hmax1, h1le, hlt1, hget, hb, Nat.add_sub_cancel_left,
    h48, h74a, h65a, h74b, h65b]
  split_ifs with hv0 hd0 hd0
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals rw [Slice.from_val]
  all_goals apply hset
  all_goals apply UScalar.eq_of_val_eq
  all_goals rw [overByte_val]
  · have : decide (v.val < 0) = true := decide_eq_true hv0
    simp only [overpunch, this, hd0, uscalar_ofNat_val, _root_.ite_true]
  · have : decide (v.val < 0) = true := decide_eq_true hv0
    simp only [overpunch, this, hd0, UScalar.ofNatCore_val_eq, _root_.ite_true, _root_.ite_false]; omega
  · have : decide (v.val < 0) = false := decide_eq_false hv0
    simp only [overpunch, this, hd0, Bool.false_eq_true, uscalar_ofNat_val, _root_.ite_true, _root_.ite_false]
  · have : decide (v.val < 0) = false := decide_eq_false hv0
    simp only [overpunch, this, hd0, Bool.false_eq_true, UScalar.ofNatCore_val_eq, _root_.ite_false]; omega

theorem put_snum_eq (dst : Slice U8) (off n : Usize) (v : I64) (sc : Int := 0)
    (hn : 0 < n.val) (h : off.val + n.val ≤ dst.val.length)
    (hmin : -9223372036854775808 < v.val) :
    ∃ s' : Slice U8, cbstm03a.put_snum dst off n v = .ok s' ∧
      s'.val = putL dst.val off.val n.val
        (latL (encodeNum {} { digits := n.val, scale := sc, usage := .display, signed := true } v.val)) := by
  rw [latL_encodeNum_signed n.val sc v.val]
  exact put_snum_zeroPad dst off n v hn h hmin

theorem put_snum_holds (dst : Slice U8) (off n : Usize) (v : I64) (sc : Int := 0)
    (hn : 0 < n.val) (hn18 : n.val ≤ 18) (h : off.val + n.val ≤ dst.val.length)
    (hholds : ({ digits := n.val, scale := sc, usage := .display, signed := true } : NumFmt).Holds {} v.val) :
    ∃ s' : Slice U8, cbstm03a.put_snum dst off n v = .ok s' ∧
      s'.val = putL dst.val off.val n.val
        (latL (encodeNum {} { digits := n.val, scale := sc, usage := .display, signed := true } v.val)) := by
  have hh := (EquivLean.Modernize.GlueKit.holds_display rfl).mp hholds
  dsimp only at hh
  have hpow : (10 : Nat) ^ n.val ≤ 10 ^ 18 := Nat.pow_le_pow_right (by norm_num) hn18
  exact put_snum_eq dst off n v sc hn h (by omega)

/-! ## 6. `digits11`, `fmt_9_99`, and `fmt_z_99` -/

set_option maxHeartbeats 2000000 in
theorem digits11_loop_spec (x : Nat) (m : I64) (hm : m.val = (x : Int)) :
    wp (cbstm03a.digits11_loop m (Array.repeat 11#usize 48#u8) 11#usize)
      (fun o => ∃ d, o = .ok d ∧ d.val = zeroPad 11 x) := by
  simp only [cbstm03a.digits11_loop]
  refine wp_loop (loop_shape _)
    (fun s =>
      s.2.2.val ≤ 11 ∧
      s.1.val = ((x / 10 ^ (11 - s.2.2.val) : Nat) : Int) ∧
      s.2.1.val = List.replicate s.2.2.val 48#u8 ++ zeroPad (11 - s.2.2.val) x)
    (fun s => s.2.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro m' d i ⟨hi, hm', hd⟩
    have hdl : d.val.length = 11 := d.property
    aeneas_wp [rust_loop_body, array_update_eq, IScalar.hcast_val_eq, iscalar_srem_val,
      uscalar_ofNat_val, iscalar_ofInt_val, Array.from_val, hdl]
    by_cases hgt : 0 < i.val
    · let q := x / 10 ^ (11 - i.val)
      have hq : m'.val = (q : Int) := hm'
      have hm'0 : 0 ≤ m'.val := by rw [hq]; positivity
      have hd10 : q % 10 < 10 := Nat.mod_lt _ (by norm_num)
      have htmod : (m'.val.tmod 10 % 2 ^ 8).toNat = q % 10 := by
        rw [hq, Int.tmod_eq_emod_of_nonneg (by positivity)]
        omega
      have h48 : 48 + (m'.val.tmod 10 % 2 ^ 8).toNat ≤ 255 := by omega
      simp only [hgt, _root_.ite_true]
      split_ifs
      all_goals try (exfalso; omega)
      rw [loopCls_cont]
      dsimp only
      refine ⟨⟨by rw [UScalar.ofNatCore_val_eq]; omega, ?_, ?_⟩, by
        rw [UScalar.ofNatCore_val_eq]; omega⟩
      · rw [IScalar.ofInt_val_eq, hq, Int.tdiv_eq_ediv_of_nonneg (by positivity)]
        norm_cast
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
        congr 2
        rw [UScalar.ofNatCore_val_eq]; omega
      · rw [Array.from_val, UScalar.ofNatCore_val_eq (x := i.val - 1)]
        obtain ⟨k, hk⟩ : ∃ k, i.val = k + 1 := ⟨i.val - 1, by omega⟩
        rw [hd, hk, Nat.add_sub_cancel, set_replicate_end,
          show 11 - k = (11 - (k + 1)) + 1 by omega, zeroPad_succ_left, ← hk]
        simp only [List.append_assoc, List.singleton_append, List.append_cancel_left_eq,
          List.cons.injEq, and_true]
        apply UScalar.eq_of_val_eq
        rw [UScalar.ofNatCore_val_eq, byteOf_val _ (by omega), htmod]
    · simp only [hgt, _root_.ite_false, loopCls_done]
      have hi0' : i.val = 0 := by omega
      refine ⟨d, rfl, ?_⟩
      rw [hd, hi0', List.replicate_zero, List.nil_append, Nat.sub_zero]
  · refine ⟨by simp, by simp [hm], ?_⟩
    simp only [Array.repeat_val, uscalar_ofNat_val, Nat.sub_self]
    have hz : zeroPad 0 x = [] := by simp [zeroPad, zpad, toDigits]
    rw [hz, List.append_nil]

theorem digits11_eq (v : I64) (hmin : -9223372036854775808 < v.val) :
    ∃ d : Array U8 11#usize, cbstm03a.digits11 v = .ok d ∧
      d.val = latL (Sem.digitChars {} 11 (v.val.natAbs % 10 ^ 11)) := by
  rw [latL_digitChars]
  refine exists_ok_of_wp ?_
  unfold cbstm03a.digits11
  by_cases hv : v.val < 0
  · have hlt : (v < 0#i64) = True := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_true]
    aeneas_wp []
    simp (disch := omega) only [dite_eq_left, ite_eq_left]
    refine digits11_loop_spec (v.val.natAbs % 10 ^ 11) _ ?_
    rw [iscalar_srem_val, IScalar.ofInt_val_eq, iscalar_ofInt_val,
      Int.tmod_eq_emod_of_nonneg (by omega), show -v.val = (v.val.natAbs : Int) by omega]
    norm_cast
  · have hlt : (v < 0#i64) = False := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_false, wp_bind, wp_ok]
    aeneas_wp []
    simp (disch := omega) only [ite_eq_left]
    refine digits11_loop_spec (v.val.natAbs % 10 ^ 11) _ ?_
    rw [iscalar_srem_val, iscalar_ofInt_val,
      Int.tmod_eq_emod_of_nonneg (by omega), show v.val = (v.val.natAbs : Int) by omega]
    norm_cast

theorem digits11_lt_eq (v : I64) (hv : v.val.natAbs < 10 ^ 11) :
    ∃ d : Array U8 11#usize, cbstm03a.digits11 v = .ok d ∧
      d.val = latL (Sem.digitChars {} 11 v.val.natAbs) := by
  rw [← Nat.mod_eq_of_lt hv]
  exact digits11_eq v (by omega)

theorem array_index_usize_getD {α : Type _} [Inhabited α] {n : Usize} (a : Array α n) (i : Usize) :
    Array.index_usize a i =
      if i.val < a.val.length then .ok (a.val.getD i.val default)
      else .fail .arrayOutOfBounds := by
  rw [array_index_usize_eq]
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ h]
  · rfl

theorem set_after' {α : Type _} (pre : List α) (k n : Nat) (a c : α) (hn : pre.length = n) :
    (pre ++ List.replicate (k + 1) a).set n c = pre ++ c :: List.replicate k a := by
  subst hn
  rw [List.set_append_right _ _ (le_refl _), Nat.sub_self, List.replicate_succ]
  rfl

theorem set_tail4 {α : Type _} (Z : List α) (hZ : Z.length = 9) (a w x y z : α) :
    ((((Z ++ List.replicate 4 a).set 9 w).set 10 x).set 11 y).set 12 z = Z ++ [w, x, y, z] := by
  have h1 : (Z ++ List.replicate 4 a).set 9 w = (Z ++ [w]) ++ List.replicate 3 a := by
    rw [set_after' Z 3 9 a w hZ]; simp [List.append_assoc]
  have h2 : ((Z ++ [w]) ++ List.replicate 3 a).set 10 x = (Z ++ [w, x]) ++ List.replicate 2 a := by
    rw [set_after' (Z ++ [w]) 2 10 a x (by simp [hZ])]; simp [List.append_assoc]
  have h3 : ((Z ++ [w, x]) ++ List.replicate 2 a).set 11 y = (Z ++ [w, x, y]) ++ List.replicate 1 a := by
    rw [set_after' (Z ++ [w, x]) 1 11 a y (by simp [hZ])]; simp [List.append_assoc]
  have h4 : ((Z ++ [w, x, y]) ++ List.replicate 1 a).set 12 z = (Z ++ [w, x, y, z]) ++ List.replicate 0 a := by
    rw [set_after' (Z ++ [w, x, y]) 0 12 a z (by simp [hZ])]; simp [List.append_assoc]
  rw [h1, h2, h3, h4, List.replicate_zero, List.append_nil]

theorem fmt_9_99_loop_spec (d : Array U8 11#usize) :
    wp (cbstm03a.fmt_9_99_loop d (Array.repeat 13#usize 32#u8) 0#usize)
      (fun res => ∃ o1 : Array U8 13#usize, res = .ok o1 ∧
        o1.val = d.val.take 9 ++ List.replicate 4 32#u8) := by
  have hdl : d.val.length = 11 := d.property
  simp only [cbstm03a.fmt_9_99_loop]
  refine wp_loop (loop_shape _)
    (fun s => s.2.val ≤ 9 ∧ s.1.val = d.val.take s.2.val ++ List.replicate (13 - s.2.val) 32#u8)
    (fun s => 9 - s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro o i ⟨hi, ho⟩
    have hol : o.val.length = 13 := o.property
    aeneas_wp [rust_loop_body, array_index_usize_eq, array_update_eq, uscalar_ofNat_val,
      Array.from_val, hdl, hol]
    by_cases hlt : i.val < 9
    · have hti : (d.val.take i.val).length = i.val := by simp [hdl]; omega
      simp only [hlt, _root_.ite_true]
      split_ifs
      all_goals try (exfalso; omega)
      all_goals try (exfalso; scalar_tac)
      rw [loopCls_cont]
      dsimp only
      refine ⟨⟨by rw [UScalar.ofNatCore_val_eq]; omega, ?_⟩, by
        rw [UScalar.ofNatCore_val_eq]; omega⟩
      rw [Array.from_val, UScalar.ofNatCore_val_eq, ho,
        show 13 - i.val = (13 - (i.val + 1)) + 1 by omega, set_after' _ _ _ _ _ hti,
        take_succ_of_lt (by omega)]
      simp only [List.append_assoc, List.singleton_append]
    · simp only [hlt, _root_.ite_false, loopCls_done]
      have hi9 : i.val = 9 := by omega
      exact ⟨o, rfl, by rw [ho, hi9]⟩
  · simp [Array.repeat_val]

theorem zeroPad_getD_eq_lat_digitByte (n x j : Nat) (hj : j < n) :
    (zeroPad n x).getD j default = lat (({} : Config).digitByte ((toDigits 10 n x).getD j 0)) := by
  have hl : (toDigits 10 n x).length = n := Cobol.Digits.length_toDigits 10 n x
  rw [← latL_digitChars, latL, Sem.digitChars, List.map_map,
    List.getD_eq_getElem _ _ (by simp [hl, hj]), List.getElem_map,
    List.getD_eq_getElem _ _ (by simp [hl, hj])]
  rfl

theorem take9_eq_getD (l : List U8) (hl : l.length = 11) :
    l.take 9 = [l.getD 0 default, l.getD 1 default, l.getD 2 default, l.getD 3 default,
      l.getD 4 default, l.getD 5 default, l.getD 6 default, l.getD 7 default, l.getD 8 default] := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ | ⟨x8, _ | ⟨x9, _ | ⟨x10, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at hl
  rfl

theorem latL_edit9 (v : Int) :
    latL (Cobol.StmCore.edit9 v) =
      let d := zeroPad 11 (v.natAbs % 10 ^ 11)
      d.take 9 ++ [46#u8, d.getD 9 default, d.getD 10 default, if v < 0 then 45#u8 else 32#u8] := by
  dsimp only
  rw [take9_eq_getD _ (zeroPad_length 11 _)]
  unfold Cobol.StmCore.edit9 Edit.edit Edit.editOpt
  have hf : Edit.floatSym pic9 = none := by decide
  have hb : Edit.floatBeforePoint [Edit.Pos.digit none, .digit none, .digit none, .digit none,
    .digit none, .digit none, .digit none, .digit none, .digit none, .point, .digit none, .digit none,
    .fixed .minus] = true := by decide
  have ha : [Edit.Pos.digit none, .digit none, .digit none, .digit none, .digit none, .digit none,
    .digit none, .digit none, .digit none, .point, .digit none, .digit none, .fixed .minus].all
    (fun p => p != Edit.Pos.digit none) = false := by decide
  have hfn : ([Edit.Pos.digit none, .digit none, .digit none, .digit none, .digit none, .digit none,
    .digit none, .digit none, .digit none, .point, .digit none, .digit none, .fixed .minus].filter
    (fun p => match p with | .digit _ => true | _ => false)).findIdx? (· == .digit none) = some 0 := by
    decide
  have hnum : Edit.numDigitPos [Edit.Pos.digit none, .digit none, .digit none, .digit none,
    .digit none, .digit none, .digit none, .digit none, .digit none, .point, .digit none, .digit none,
    .fixed .minus] = 11 := by decide
  have hfrac : Edit.fracDigits [Edit.Pos.digit none, .digit none, .digit none, .digit none,
    .digit none, .digit none, .digit none, .digit none, .digit none, .point, .digit none, .digit none,
    .fixed .minus] = 2 := by decide
  have hdot : lat (({} : Config).chr 0x2E) = 46#u8 := by decide +kernel
  simp only [classify_pic9, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.getD_some,
    hf, hb, ha, hnum, hfrac, Nat.reduceSub, List.filter_cons, List.filter_nil,
    List.findIdx?_cons, beq_self_eq_true, Nat.zero_min, Nat.min_zero, Nat.not_lt_zero,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.false_and,
    Nat.cast_ofNat, rescale_same, Edit.editOpt.gen, Edit.symChar, Edit.fixedBytes, Edit.signChar,
    List.map_cons, List.map_append, List.map_nil, latL, hdot]
  simp (disch := omega) only [zeroPad_getD_eq_lat_digitByte]
  by_cases hv : v < 0
  · have hm : lat ({} : Config).minusChar = 45#u8 := by decide +kernel
    simp [hv, hm]
  · have hs : lat ({} : Config).space = 32#u8 := by decide +kernel
    simp [hv, hs]

set_option maxHeartbeats 2000000 in
theorem fmt_9_99_eq (v : I64) (hmin : -9223372036854775808 < v.val) :
    ∃ o : Array U8 13#usize, cbstm03a.fmt_9_99 v = .ok o ∧
      o.val = latL (Cobol.StmCore.edit9 v.val) := by
  obtain ⟨d, hd, hdv⟩ := digits11_eq v hmin
  rw [latL_digitChars] at hdv
  obtain ⟨o1, ho1, ho1v⟩ := exists_ok_of_wp (fmt_9_99_loop_spec d)
  have hdl : d.val.length = 11 := d.property
  have ho1l : o1.val.length = 13 := o1.property
  refine exists_ok_of_wp ?_
  simp only [cbstm03a.fmt_9_99, hd, ho1, wp_bind, wp_ok]
  aeneas_wp [array_index_usize_getD, array_update_eq, uscalar_ofNat_val, iscalar_ofInt_val,
    Array.from_val, List.length_set, hdl, ho1l]
  rw [latL_edit9, ← hdv]
  by_cases hv : v.val < 0
  · simp only [hv, _root_.ite_true]
    refine ⟨_, rfl, ?_⟩
    rw [Array.from_val, ho1v, set_tail4 _ (by simp [hdl])]
  · simp only [hv, _root_.ite_false]
    refine ⟨_, rfl, ?_⟩
    rw [Array.from_val, ho1v, set_tail4 _ (by simp [hdl])]

theorem findIdx?_cons_getD_length {α : Type _} (p : α → Bool) (a : α) (l : List α) :
    ((a :: l).findIdx? p).getD (a :: l).length =
      if p a then 0 else (l.findIdx? p).getD l.length + 1 := by
  simp only [List.findIdx?_cons, List.length_cons]
  cases p a
  · cases l.findIdx? p <;> rfl
  · rfl

theorem findIdx?_getD_gt_of_eq_false {α : Type _} {p : α → Bool} :
    ∀ (l : List α) (i : Nat) (hi : i < l.length), i ≤ (l.findIdx? p).getD l.length →
      p l[i] = false → i < (l.findIdx? p).getD l.length
  | a :: l, 0, _, _, hp => by
    simp only [List.getElem_cons_zero] at hp
    rw [findIdx?_cons_getD_length, hp]; simp
  | a :: l, i + 1, hi, hle, hp => by
    simp only [List.getElem_cons_succ] at hp
    rw [findIdx?_cons_getD_length] at hle ⊢
    cases hpa : p a
    · simp only [hpa, Bool.false_eq_true, ↓reduceIte] at hle ⊢
      have := findIdx?_getD_gt_of_eq_false l i (by simp at hi; omega) (by omega) hp
      omega
    · simp [hpa] at hle

theorem findIdx?_getD_le_of_eq_true {α : Type _} {p : α → Bool} :
    ∀ (l : List α) (i : Nat) (hi : i < l.length),
      p l[i] = true → (l.findIdx? p).getD l.length ≤ i
  | a :: l, 0, _, hp => by
    simp only [List.getElem_cons_zero] at hp
    rw [findIdx?_cons_getD_length, hp]; simp
  | a :: l, i + 1, hi, hp => by
    simp only [List.getElem_cons_succ] at hp
    rw [findIdx?_cons_getD_length]
    cases hpa : p a
    · have ih := findIdx?_getD_le_of_eq_true l i (by simp at hi; omega) hp
      simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · simp

theorem fmt_z_99_loop_spec (x : Nat) (d : Array U8 11#usize) (hdv : d.val = zeroPad 11 x) :
    let ds := toDigits 10 11 x
    let k0 := min 9 (min 9 ((ds.findIdx? (· != 0)).getD 11))
    wp (cbstm03a.fmt_z_99_loop d (Array.repeat 13#usize 32#u8) false 0#usize)
      (fun res => ∃ o1 : Array U8 13#usize, res = .ok o1 ∧
        o1.val = (List.range 9).map (fun j => if j < k0 then 32#u8 else d.val.getD j default) ++
          List.replicate 4 32#u8) := by
  intro ds k0
  have hdl : d.val.length = 11 := d.property
  have hdsl : ds.length = 11 := Cobol.Digits.length_toDigits 10 11 x
  have hk0_eq : k0 = min 9 ((ds.findIdx? (· != 0)).getD ds.length) := by
    simp [k0, hdsl]
  simp only [cbstm03a.fmt_z_99_loop]
  refine wp_loop (loop_shape _)
    (fun s => s.2.2.val ≤ 9 ∧
      s.2.1 = decide (k0 < s.2.2.val) ∧
      s.1.val = (List.range s.2.2.val).map (fun j => if j < k0 then 32#u8 else d.val.getD j default) ++
        List.replicate (13 - s.2.2.val) 32#u8)
    (fun s => 9 - s.2.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro o sig i ⟨hi, hsig, ho⟩
    have hol : o.val.length = 13 := o.property
    aeneas_wp [rust_loop_body, array_index_usize_getD, array_update_eq, uscalar_ofNat_val,
      Array.from_val, hdl, hol]
    by_cases hlt : i.val < 9
    · have hi11 : i.val < 11 := by omega
      have hmax : i.val + 1 ≤ Usize.max := by scalar_tac
      have hi_ds : i.val < ds.length := by omega
      have hd_lt : ds[i.val]'hi_ds < 10 :=
        Cobol.Digits.toDigits_lt (by decide) 11 x _ (List.getElem_mem hi_ds)
      have hdi_val : (d.val.getD i.val default).val = 48 + ds[i.val]'hi_ds := by
        rw [hdv, zeroPad, zpad, List.getD_eq_getElem _ _ (by simp [hi11]),
          List.getElem_map, List.getElem_map]
        exact byteOf_val (48 + ds[i.val]'hi_ds) (by omega)
      have hri : ((List.range i.val).map (fun j => if j < k0 then 32#u8 else d.val.getD j default)).length =
          i.val := by simp
      simp only [hlt, hi11, hmax, _root_.dite_true, _root_.ite_true]
      by_cases hnz : ds[i.val]'hi_ds = 0
      · have hdi48 : (d.val.getD i.val default).val = 48 := by omega
        simp only [hdi48, not_true_eq_false, _root_.ite_false]
        by_cases hki : k0 < i.val
        · have hsigt : sig = true := by rw [hsig]; exact decide_eq_true hki
          simp only [hsigt, _root_.ite_true, show i.val < 13 by omega, _root_.dite_true]
          rw [loopCls_cont]; dsimp only
          refine ⟨⟨by rw [UScalar.ofNatCore_val_eq]; omega, ?_, ?_⟩, by
            rw [UScalar.ofNatCore_val_eq]; omega⟩
          · rw [UScalar.ofNatCore_val_eq]; exact (decide_eq_true (by omega)).symm
          · rw [Array.from_val, UScalar.ofNatCore_val_eq, ho,
              show 13 - i.val = (13 - (i.val + 1)) + 1 by omega, set_after' _ _ _ _ _ hri,
              List.range_succ, List.map_append, List.map_singleton]
            simp [show ¬ i.val < k0 by omega]
        · have hsigf : sig = false := by rw [hsig]; exact decide_eq_false hki
          have hik0 : i.val < k0 := by
            have hle' : i.val ≤ (ds.findIdx? (· != 0)).getD ds.length := by omega
            have hgt := findIdx?_getD_gt_of_eq_false ds i.val hi_ds hle' (by simp [hnz])
            omega
          simp only [hsigf, Bool.false_eq_true, _root_.ite_false, show i.val < 13 by omega,
            _root_.dite_true]
          rw [loopCls_cont]; dsimp only
          refine ⟨⟨by rw [UScalar.ofNatCore_val_eq]; omega, ?_, ?_⟩, by
            rw [UScalar.ofNatCore_val_eq]; omega⟩
          · rw [UScalar.ofNatCore_val_eq]; exact (decide_eq_false (by omega)).symm
          · rw [Array.from_val, UScalar.ofNatCore_val_eq, ho,
              show 13 - i.val = (13 - (i.val + 1)) + 1 by omega, set_after' _ _ _ _ _ hri,
              List.range_succ, List.map_append, List.map_singleton]
            simp [hik0]
      · have hdi48 : ¬ (d.val.getD i.val default).val = 48 := by omega
        have hk0_le : k0 ≤ i.val := by
          have htrue : (ds[i.val]'hi_ds != 0) = true := bne_iff_ne.2 hnz
          have := findIdx?_getD_le_of_eq_true (p := (· != 0)) ds i.val hi_ds htrue
          omega
        simp only [hdi48, not_false_eq_true, _root_.ite_true, show i.val < 13 by omega,
          _root_.dite_true]
        rw [loopCls_cont]; dsimp only
        refine ⟨⟨by rw [UScalar.ofNatCore_val_eq]; omega, ?_, ?_⟩, by
          rw [UScalar.ofNatCore_val_eq]; omega⟩
        · rw [UScalar.ofNatCore_val_eq]; exact (decide_eq_true (by omega)).symm
        · rw [Array.from_val, UScalar.ofNatCore_val_eq, ho,
            show 13 - i.val = (13 - (i.val + 1)) + 1 by omega, set_after' _ _ _ _ _ hri,
            List.range_succ, List.map_append, List.map_singleton]
          simp [show ¬ i.val < k0 by omega]
    · simp only [hlt, _root_.ite_false, loopCls_done]
      have hi9 : i.val = 9 := by omega
      exact ⟨o, rfl, by rw [ho, hi9]⟩
  · dsimp only
    rw [Array.repeat_val]
    have h0 : (0#usize).val = 0 := rfl
    have h13 : (13#usize).val = 13 := rfl
    rw [h0, h13]
    simp

theorem latL_editZ (v : Int) :
    latL (Cobol.StmCore.editZ v) =
      let d := zeroPad 11 (v.natAbs % 10 ^ 11)
      let ds := toDigits 10 11 (v.natAbs % 10 ^ 11)
      let k0 := min 9 (min 9 ((ds.findIdx? (· != 0)).getD 11))
      (List.range 9).map (fun j => if j < k0 then 32#u8 else d.getD j default) ++
        [46#u8, d.getD 9 default, d.getD 10 default, if v < 0 then 45#u8 else 32#u8] := by
  dsimp only
  unfold Cobol.StmCore.editZ Edit.edit Edit.editOpt
  have hf : Edit.floatSym picZ = none := by decide
  have hb : Edit.floatBeforePoint [Edit.Pos.digit (some .z), .digit (some .z), .digit (some .z),
    .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z),
    .digit (some .z), .point, .digit none, .digit none, .fixed .minus] = true := by decide
  have ha : [Edit.Pos.digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z),
    .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z), .point,
    .digit none, .digit none, .fixed .minus].all (fun p => p != Edit.Pos.digit none) = false := by
    decide
  have hfn' : List.findIdx? (fun x => x == Edit.Pos.digit none)
      [Edit.Pos.digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z),
       .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z),
       .digit none, .digit none] = some 9 := by decide
  have hnum : Edit.numDigitPos [Edit.Pos.digit (some .z), .digit (some .z), .digit (some .z),
    .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z),
    .digit (some .z), .point, .digit none, .digit none, .fixed .minus] = 11 := by decide
  have hfrac : Edit.fracDigits [Edit.Pos.digit (some .z), .digit (some .z), .digit (some .z),
    .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z),
    .digit (some .z), .point, .digit none, .digit none, .fixed .minus] = 2 := by decide
  simp only [classify_picZ, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.getD_some,
    hf, hb, ha, hnum, hfrac, Nat.reduceSub, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Bool.and_false, Bool.false_and, Nat.cast_ofNat, rescale_same]
  have hrange9 : List.range 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] := rfl
  have hdot : lat (({} : Config).chr 0x2E) = 46#u8 := by decide +kernel
  have hsp : lat ({} : Config).space = 32#u8 := by decide +kernel
  rw [hrange9]
  simp only [Edit.editOpt.gen, Edit.symChar, Edit.fixedBytes, Edit.signChar,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    latL, apply_ite Prod.fst, apply_ite lat, hsp, hdot]
  simp (disch := omega) only [zeroPad_getD_eq_lat_digitByte]
  by_cases hv : v < 0
  · have hm : lat ({} : Config).minusChar = 45#u8 := by decide +kernel
    simp [hv, hm, hfn']
  · simp [hv, hfn']

set_option maxHeartbeats 2000000 in
theorem fmt_z_99_eq (v : I64) (hmin : -9223372036854775808 < v.val) :
    ∃ o : Array U8 13#usize, cbstm03a.fmt_z_99 v = .ok o ∧
      o.val = latL (Cobol.StmCore.editZ v.val) := by
  obtain ⟨d, hd, hdv⟩ := digits11_eq v hmin
  rw [latL_digitChars] at hdv
  obtain ⟨o1, ho1, ho1v⟩ := exists_ok_of_wp (fmt_z_99_loop_spec (v.val.natAbs % 10 ^ 11) d hdv)
  have hdl : d.val.length = 11 := d.property
  have ho1l : o1.val.length = 13 := o1.property
  refine exists_ok_of_wp ?_
  simp only [cbstm03a.fmt_z_99, hd, ho1, wp_bind, wp_ok]
  aeneas_wp [array_index_usize_getD, array_update_eq, uscalar_ofNat_val, iscalar_ofInt_val,
    Array.from_val, List.length_set, hdl, ho1l]
  rw [latL_editZ, ← hdv]
  by_cases hv : v.val < 0
  · simp only [hv, _root_.ite_true]
    refine ⟨_, rfl, ?_⟩
    rw [Array.from_val, ho1v, set_tail4 _ (by simp)]
  · simp only [hv, _root_.ite_false]
    refine ⟨_, rfl, ?_⟩
    rw [Array.from_val, ho1v, set_tail4 _ (by simp)]

/-! ## 7. `zoned` -/

theorem zoned_loop_unfold (b : Slice U8) (v : I64) (neg : Bool) (n i : Usize) :
    cbstm03a.zoned_loop b v neg n i =
      Std.bind (cbstm03a.zoned_loop.body b n v neg i) (fun r =>
        match r with
        | .cont (v1, neg1, i1) => cbstm03a.zoned_loop b v1 neg1 n i1
        | .done res => .ok res) := by
  unfold cbstm03a.zoned_loop
  rw [loop_unfold]
  dsimp only
  congr 1; funext r; cases r with
  | cont x => rcases x with ⟨v1, neg1, i1⟩; rfl
  | done res => rfl

theorem zoned_loop_done_step (b : Slice U8) (n : Usize) (v : I64) (neg : Bool) (i : Usize)
    (hi : n.val ≤ i.val) :
    cbstm03a.zoned_loop.body b n v neg i = .ok (.done (v, neg)) := by
  have hlt : ¬ i < n := by scalar_tac
  unfold cbstm03a.zoned_loop.body
  exact ite_eq_right hlt

theorem zoned_loop_done (b : Slice U8) (n : Usize) (v : I64) (neg : Bool) (i : Usize)
    (hi : n.val ≤ i.val) :
    cbstm03a.zoned_loop b v neg n i = .ok (v, neg) := by
  rw [zoned_loop_unfold, zoned_loop_done_step b n v neg i hi, bind_ok]

theorem zoned_loop_digits_step (b : Slice U8) (n : Usize) (v : I64) (neg : Bool) (i : Usize)
    (digit : Nat) (hi : i.val < n.val) (hn : n.val ≤ b.val.length) (hd : digit < 10)
    (hb : b.val.getD i.val default = byteOf (48 + digit))
    (hv0 : 0 ≤ v.val) (hv1 : v.val < 10 ^ 12) :
    ∃ (v' : I64) (i' : Usize),
      cbstm03a.zoned_loop.body b n v neg i = .ok (.cont (v', neg, i')) ∧
      v'.val = v.val * 10 + (digit : Int) ∧
      i'.val = i.val + 1 := by
  have hbl : b.val.length ≤ Usize.max := b.property
  have hilt : i < n := by scalar_tac
  have hilen : i.val < b.val.length := by omega
  have hcv : (byteOf (48 + digit)).val = 48 + digit := byteOf_val _ (by omega)
  have hc48 : byteOf (48 + digit) >= 48#u8 := by
    simp [UScalar.le_equiv, hcv]
  have hc57 : byteOf (48 + digit) <= 57#u8 := by
    simp [UScalar.le_equiv, hcv]; omega
  obtain ⟨r, hr, v', i', rfl, hv', hi'⟩ :
      ∃ r, cbstm03a.zoned_loop.body b n v neg i = .ok r ∧
        ∃ (v' : I64) (i' : Usize), r = .cont (v', neg, i') ∧
          v'.val = v.val * 10 + (digit : Int) ∧ i'.val = i.val + 1 := by
    refine exists_ok_of_wp ?_
    unfold cbstm03a.zoned_loop.body
    rw [ite_eq_left hilt, slice_index_usize_getD, ite_eq_left hilen, hb, bind_ok,
      ite_eq_left hc48, ite_eq_left hc57]
    aeneas_wp [uscalar_ofNat_val, iscalar_ofInt_val, hcv]
    have hov : i.val + 1 ≤ Usize.max := by omega
    simp (disch := omega) only [dite_eq_left, ite_eq_left]
    exact ⟨_, rfl, _, _, rfl, by rw [IScalar.ofInt_val_eq]; omega, rfl⟩
  exact ⟨v', i', hr, hv', hi'⟩

theorem zoned_loop_prefix (b : Slice U8) (n : Usize) (m y : Nat) (neg : Bool)
    (hm : m ≤ n.val) (hn : n.val ≤ b.val.length) (hm12 : m ≤ 12) (hy : y < 10 ^ m)
    (hb : ∀ (j : Nat) (hj : j < m), b.val.getD j default = byteOf (48 + (toDigits 10 m y)[j]'(by
      rw [Cobol.Digits.length_toDigits]; exact hj))) :
    ∀ (k : Nat) (v : I64) (i : Usize),
      m - i.val = k → i.val ≤ m → v.val = ((y / 10 ^ (m - i.val) : Nat) : Int) →
      ∃ (v_m : I64) (i_m : Usize),
        cbstm03a.zoned_loop b v neg n i = cbstm03a.zoned_loop b v_m neg n i_m ∧
        v_m.val = (y : Int) ∧ i_m.val = m := by
  intro k
  induction k with
  | zero =>
    intro v i hk hi hv
    have him : i.val = m := by omega
    refine ⟨v, i, rfl, ?_, him⟩
    rw [hv, him, Nat.sub_self, Nat.pow_zero, Nat.div_one]
  | succ k ih =>
    intro v i hk hi hv
    have hilt : i.val < m := by omega
    let digit := (toDigits 10 m y)[i.val]'(by rw [Cobol.Digits.length_toDigits]; exact hilt)
    have hd_lt : digit < 10 :=
      Cobol.Digits.toDigits_lt (by decide) m y digit (List.getElem_mem _)
    have hd_eq : digit = y / 10 ^ (m - 1 - i.val) % 10 :=
      toDigits_getElem m y i.val hilt
    have hv0 : 0 ≤ v.val := by rw [hv]; positivity
    have hv1 : v.val < 10 ^ 12 := by
      have h1 : y / 10 ^ (m - i.val) ≤ y := Nat.div_le_self _ _
      have h2 : (10 : Nat) ^ m ≤ 10 ^ 12 := Nat.pow_le_pow_right (by norm_num) hm12
      rw [hv]; exact_mod_cast (show y / 10 ^ (m - i.val) < 10 ^ 12 by omega)
    obtain ⟨v', i', hstep, hv', hi'⟩ :=
      zoned_loop_digits_step b n v neg i digit (by omega) hn hd_lt (hb i.val hilt) hv0 hv1
    have hstep_loop : cbstm03a.zoned_loop b v neg n i = cbstm03a.zoned_loop b v' neg n i' := by
      rw [zoned_loop_unfold, hstep, bind_ok]
    have hv'_eq : v'.val = ((y / 10 ^ (m - i'.val) : Nat) : Int) := by
      rw [hv', hv, hd_eq, hi']
      norm_cast
      have hpow : m - i.val = (m - 1 - i.val) + 1 := by omega
      rw [hpow, Nat.pow_succ, ← Nat.div_div_eq_div_mul, Nat.mul_comm _ 10, Nat.div_add_mod,
        show m - 1 - i.val = m - (i.val + 1) by omega]
    obtain ⟨v_m, i_m, h1, h2, h3⟩ := ih v' i' (by omega) (by omega) hv'_eq
    exact ⟨v_m, i_m, hstep_loop.trans h1, h2, h3⟩

theorem usize_add1_eq (i n : Usize) (h : i.val + 1 = n.val) :
    (i + 1#usize : Result Usize) = .ok n := by
  refine eq_ok_of_wp ?_
  aeneas_wp [uscalar_ofNat_val]
  have hmax : i.val + 1 ≤ Usize.max := by have := n.hBounds; scalar_tac
  simp only [hmax, _root_.dite_true, Except.ok.injEq]
  apply UScalar.eq_of_val_eq
  rw [UScalar.ofNatCore_val_eq, h]

theorem zoned_loop_overpunch_step (b : Slice U8) (n : Usize) (v : I64) (neg neg0 : Bool) (i : Usize)
    (digit : Nat) (hi1 : i.val + 1 = n.val) (hn : n.val ≤ b.val.length) (hd : digit < 10)
    (hb : b.val.getD i.val default = byteOf (overpunch neg0 digit))
    (hv0 : 0 ≤ v.val) (hv1 : v.val < 10 ^ 12) :
    ∃ (v' : I64),
      cbstm03a.zoned_loop.body b n v neg i = .ok (.cont (v', neg0 || neg, n)) ∧
      v'.val = v.val * 10 + (digit : Int) := by
  have hilt : i < n := by scalar_tac
  have hilen : i.val < b.val.length := by omega
  have hadd1 : (i + 1#usize : Result Usize) = .ok n := usize_add1_eq i n hi1
  let c := byteOf (overpunch neg0 digit)
  have hcv : c.val = overpunch neg0 digit := by
    dsimp [c]; apply byteOf_val; unfold overpunch; split_ifs <;> omega
  have hc48 : c >= 48#u8 := by
    simp only [UScalar.le_equiv, uscalar_ofNat_val, hcv, overpunch]; split_ifs <;> omega
  have hc57 : ¬ c <= 57#u8 := by
    simp only [UScalar.le_equiv, uscalar_ofNat_val, hcv, overpunch]; split_ifs <;> omega
  obtain ⟨r, hr, v', rfl, hv'⟩ :
      ∃ r, cbstm03a.zoned_loop.body b n v neg i = .ok r ∧
        ∃ v' : I64, r = .cont (v', neg0 || neg, n) ∧ v'.val = v.val * 10 + (digit : Int) := by
    refine exists_ok_of_wp ?_
    unfold cbstm03a.zoned_loop.body
    rw [ite_eq_left hilt, slice_index_usize_getD, ite_eq_left hilen, hb, bind_ok,
      ite_eq_left hc48, ite_eq_right hc57, hadd1, bind_ok, ite_eq_left rfl]
    cases neg0 <;> by_cases hd0 : digit = 0
    · subst hd0
      have hc123 : c = 123#u8 := by
        apply UScalar.eq_of_val_eq; simp [hcv, overpunch]
      rw [ite_eq_left hc123, bind_ok, Aeneas.Std.uncurry_apply_pair]
      aeneas_wp [uscalar_ofNat_val, iscalar_ofInt_val]
      simp (disch := omega) only [dite_eq_left]
      exact ⟨_, rfl, _, rfl, by rw [IScalar.ofInt_val_eq]; omega⟩
    · have hc123 : ¬ c = 123#u8 := by
        rw [UScalar.eq_equiv, hcv, uscalar_ofNat_val]; simp [overpunch, hd0]; omega
      have hc65 : c >= 65#u8 := by
        simp [UScalar.le_equiv, hcv, overpunch, hd0]; omega
      have hc73 : c <= 73#u8 := by
        simp [UScalar.le_equiv, hcv, overpunch, hd0]; omega
      rw [ite_eq_right hc123, ite_eq_left rfl, ite_eq_left hc65, ite_eq_left hc73]
      aeneas_wp [uscalar_ofNat_val, iscalar_ofInt_val, hcv]
      simp only [overpunch, Bool.false_eq_true, hd0, ↓reduceIte, Bool.false_or,
        byteOf_val (64 + digit) (by omega)]
      simp (disch := omega) only [dite_eq_left, ite_eq_left]
      exact ⟨_, rfl, _, rfl, by rw [IScalar.ofInt_val_eq]; omega⟩
    · subst hd0
      have hc123 : ¬ c = 123#u8 := by
        rw [UScalar.eq_equiv, hcv, uscalar_ofNat_val]; simp [overpunch]
      have hc65 : c >= 65#u8 := by
        simp [UScalar.le_equiv, hcv, overpunch]
      have hc73 : ¬ c <= 73#u8 := by
        simp [UScalar.le_equiv, hcv, overpunch]
      have hc125 : c = 125#u8 := by
        apply UScalar.eq_of_val_eq; simp [hcv, overpunch]
      rw [ite_eq_right hc123, ite_eq_left rfl, ite_eq_left hc65, ite_eq_right hc73,
        ite_eq_left rfl, ite_eq_left hc125, bind_ok, Aeneas.Std.uncurry_apply_pair]
      aeneas_wp [uscalar_ofNat_val, iscalar_ofInt_val]
      simp (disch := omega) only [dite_eq_left]
      exact ⟨_, rfl, _, rfl, by rw [IScalar.ofInt_val_eq]; omega⟩
    · have hc123 : ¬ c = 123#u8 := by
        rw [UScalar.eq_equiv, hcv, uscalar_ofNat_val]; simp [overpunch, hd0]; omega
      have hc65 : c >= 65#u8 := by
        simp [UScalar.le_equiv, hcv, overpunch, hd0]; omega
      have hc73 : ¬ c <= 73#u8 := by
        simp [UScalar.le_equiv, hcv, overpunch, hd0]
      have hc125 : ¬ c = 125#u8 := by
        rw [UScalar.eq_equiv, hcv, uscalar_ofNat_val]; simp [overpunch, hd0]; omega
      have hc74 : c >= 74#u8 := by
        simp [UScalar.le_equiv, hcv, overpunch, hd0]; omega
      have hc82 : c <= 82#u8 := by
        simp [UScalar.le_equiv, hcv, overpunch, hd0]; omega
      rw [ite_eq_right hc123, ite_eq_left rfl, ite_eq_left hc65, ite_eq_right hc73,
        ite_eq_left rfl, ite_eq_right hc125, ite_eq_left rfl, ite_eq_left hc74,
        ite_eq_left hc82]
      aeneas_wp [uscalar_ofNat_val, iscalar_ofInt_val, hcv]
      simp only [overpunch, hd0, ↓reduceIte, Bool.true_or,
        byteOf_val (73 + digit) (by omega)]
      simp (disch := omega) only [dite_eq_left, ite_eq_left]
      exact ⟨_, rfl, _, rfl, by rw [IScalar.ofInt_val_eq]; omega⟩
  exact ⟨v', hr, hv'⟩

theorem zoned_zeroPad_eq (s : Slice U8) (d y : Nat)
    (hd12 : d ≤ 12) (hy : y < 10 ^ d) (hs : s.val = zeroPad d y) :
    ∃ out : I64, cbstm03a.zoned s = .ok out ∧ out.val = (y : Int) := by
  have hsl : (Slice.len s).val = d := by simp [hs, zeroPad_length]
  have hb : ∀ (j : Nat) (hj : j < d), s.val.getD j default = byteOf (48 + (toDigits 10 d y)[j]'(by
      rw [Cobol.Digits.length_toDigits]; exact hj)) := by
    intro j hj
    rw [hs, zeroPad, zpad, List.getD_eq_getElem _ _ (by simp [hj]),
      List.getElem_map, List.getElem_map]
  obtain ⟨v_d, i_d, hloop, hvd, hid⟩ :=
    zoned_loop_prefix s (Slice.len s) d y false (by omega) (by simp) hd12 hy hb
      d 0#i64 0#usize (by simp) (Nat.zero_le _)
      (by simp [Nat.div_eq_of_lt hy])
  unfold cbstm03a.zoned
  dsimp only
  rw [hloop, zoned_loop_done s (Slice.len s) v_d false i_d (by omega),
    bind_ok, Aeneas.Std.uncurry_apply_pair]
  exact ⟨v_d, rfl, hvd⟩

theorem zoned_digitChars_eq (s : Slice U8) (n : Nat) (hn : n < 10 ^ 11)
    (hs : s.val = latL (Sem.digitChars {} 11 n)) :
    ∃ out : I64, cbstm03a.zoned s = .ok out ∧ out.val = (n : Int) := by
  rw [latL_digitChars] at hs
  exact zoned_zeroPad_eq s 11 n (by omega) hn hs

theorem zoned_eq (s : Slice U8) (d : Nat) (sc : Int) (sg : Bool) (v : Int)
    (hd1 : 1 ≤ d) (hd12 : d ≤ 12)
    (hholds : ({ digits := d, scale := sc, signed := sg } : NumFmt).Holds {} v)
    (hs : s.val = latL (encodeNum {} { digits := d, scale := sc, signed := sg } v)) :
    ∃ out : I64, cbstm03a.zoned s = .ok out ∧ out.val = v := by
  obtain ⟨hv_abs, hv_nonneg⟩ := (EquivLean.Modernize.GlueKit.holds_display rfl).mp hholds
  cases sg
  · have hv0 : 0 ≤ v := hv_nonneg rfl
    rw [latL_encodeNum_unsigned d sc hd1 v] at hs
    obtain ⟨out, hout, houtv⟩ := zoned_zeroPad_eq s d v.natAbs hd12 hv_abs hs
    exact ⟨out, hout, by rw [houtv]; omega⟩
  · obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    rw [latL_encodeNum_signed (m + 1) sc v, Nat.add_sub_cancel] at hs
    have hy : v.natAbs / 10 < 10 ^ m := by
      have h1 : v.natAbs < 10 ^ (m + 1) := hv_abs
      rw [Nat.pow_succ] at h1
      omega
    have hsl : (Slice.len s).val = m + 1 := by
      simp [hs, zeroPad_length]
    have hb_pre : ∀ (j : Nat) (hj : j < m), s.val.getD j default =
        byteOf (48 + (toDigits 10 m (v.natAbs / 10))[j]'(by
          rw [Cobol.Digits.length_toDigits]; exact hj)) := by
      intro j hj
      rw [hs, List.getD_eq_getElem _ _ (by simp [zeroPad_length]; omega),
        List.getElem_append_left (by simp [zeroPad_length]; exact hj)]
      simp [zeroPad, zpad]
    have hb_last : s.val.getD m default = byteOf (overpunch (decide (v < 0)) (v.natAbs % 10)) := by
      rw [hs, List.getD_eq_getElem _ _ (by simp [zeroPad_length]),
        List.getElem_append_right (by simp [zeroPad_length])]
      simp [zeroPad_length, overByte]
    obtain ⟨v_m, i_m, hloop, hvm, him⟩ :=
      zoned_loop_prefix s (Slice.len s) m (v.natAbs / 10) false (by omega) (by simp) (by omega)
        hy hb_pre m 0#i64 0#usize (by simp) (Nat.zero_le _)
        (by simp [Nat.div_eq_of_lt hy])
    have hvm0 : 0 ≤ v_m.val := by rw [hvm]; positivity
    have hvm12 : v_m.val < 10 ^ 12 := by
      have h2 : (10 : Nat) ^ m ≤ 10 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hvm]; exact_mod_cast (show v.natAbs / 10 < 10 ^ 12 by omega)
    obtain ⟨v_end, hstep, hvend⟩ :=
      zoned_loop_overpunch_step s (Slice.len s) v_m false (decide (v < 0)) i_m
        (v.natAbs % 10) (by omega) (by simp) (Nat.mod_lt _ (by norm_num))
        (by rw [him]; exact hb_last) hvm0 hvm12
    have hvend_eq : v_end.val = (v.natAbs : Int) := by
      rw [hvend, hvm]
      have : v.natAbs / 10 * 10 + v.natAbs % 10 = v.natAbs := by omega
      exact_mod_cast this
    have hloop_end : cbstm03a.zoned_loop s 0#i64 false (Slice.len s) 0#usize =
        .ok (v_end, decide (v < 0)) := by
      rw [hloop, zoned_loop_unfold, hstep, bind_ok, Bool.or_false]
      exact zoned_loop_done s (Slice.len s) v_end (decide (v < 0)) (Slice.len s) (le_refl _)
    unfold cbstm03a.zoned
    dsimp only
    rw [hloop_end, bind_ok, Aeneas.Std.uncurry_apply_pair]
    by_cases hv : v < 0
    · have hneg : decide (v < 0) = true := decide_eq_true hv
      rw [hneg, ite_eq_left rfl]
      refine exists_ok_of_wp ?_
      aeneas_wp []
      have hbd : -9223372036854775808 ≤ -v_end.val ∧ -v_end.val ≤ 9223372036854775807 := by
        have : (10 : Nat) ^ (m + 1) ≤ 10 ^ 12 := Nat.pow_le_pow_right (by norm_num) hd12
        omega
      simp only [hbd, and_self, _root_.dite_true]
      refine ⟨_, rfl, ?_⟩
      rw [IScalar.ofInt_val_eq, hvend_eq]; omega
    · have hneg : decide (v < 0) = false := decide_eq_false hv
      rw [hneg]
      exact ⟨v_end, rfl, by rw [hvend_eq]; omega⟩

/-! ## 8. `str_part` -/

/-- One step of a copy loop `a[off + p] = src[p]`. -/
theorem copy_step {α : Type _} (orig src : List α) (off p : Nat) (hp : p < src.length)
    (ho : off + p < orig.length) :
    (orig.take off ++ src.take p ++ orig.drop (off + p)).set (off + p) src[p] =
      orig.take off ++ src.take (p + 1) ++ orig.drop (off + p + 1) := by
  have h1 : (orig.take off).length = off := by simp; omega
  have h2 : (src.take p).length = p := by simp; omega
  rw [List.append_assoc, List.set_append_right _ _ (by omega), h1, Nat.add_sub_cancel_left,
    List.set_append_right _ _ (by omega), h2, Nat.sub_self, List.drop_eq_getElem_cons ho,
    List.set_cons_zero, take_succ_of_lt hp]
  simp only [List.append_assoc, List.singleton_append]

theorem ovw_eq_take_drop : ∀ (piece B : List UInt8),
    ovw piece B = piece.take B.length ++ B.drop piece.length
  | [], B => by simp [ovw]
  | _ :: _, [] => by simp [ovw]
  | b :: bs, _ :: d => by simp [ovw, ovw_eq_take_drop bs d]

theorem drop_min_length {α : Type _} (k : Nat) (l : List α) :
    l.drop (min k l.length) = l.drop k := by
  by_cases h : k ≤ l.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.drop_length, List.drop_of_length_le (by omega)]

theorem drop_append_add {α : Type _} (A B : List α) (k : Nat) :
    (A ++ B).drop (A.length + k) = B.drop k := by
  induction A with
  | nil => simp
  | cons _ A ih => simp [Nat.succ_add, ih]

theorem copy_latL_ovw (A B piece : List UInt8) :
    (latL (A ++ B)).take A.length ++
      (latL piece).take ((latL (A ++ B)).length - A.length) ++
      (latL (A ++ B)).drop (A.length + min piece.length ((latL (A ++ B)).length - A.length)) =
      latL (A ++ ovw piece B) := by
  have hlen : (latL (A ++ B)).length - A.length = B.length := by simp
  have hdrop : (latL A ++ latL B).drop (A.length + min piece.length B.length) =
      (latL B).drop (min piece.length B.length) := by
    have := drop_append_add (latL A) (latL B) (min piece.length B.length)
    simpa using this
  rw [hlen, latL_append, List.take_left' (by simp), ← latL_take, hdrop,
    ← latL_drop, drop_min_length, ovw_eq_take_drop,
    latL_append, latL_append, List.append_assoc]

theorem str_part_loop1_eq (dst : Slice U8) (ptr : Usize) (src : Slice U8) (n1 : Usize)
    (hptr : ptr.val ≤ dst.val.length) (hn1 : n1.val ≤ src.val.length) :
    let m := min n1.val (dst.val.length - ptr.val)
    ∃ (s' : Slice U8) (ptr' : Usize),
      cbstm03a.str_part_loop1 dst ptr src n1 0#usize = .ok (s', ptr') ∧
      s'.val = dst.val.take ptr.val ++ (src.val.take n1.val).take (dst.val.length - ptr.val) ++
        dst.val.drop (ptr.val + m) ∧
      ptr'.val = ptr.val + m := by
  intro m
  have hd_max : dst.val.length ≤ Usize.max := dst.property
  have hs_max : src.val.length ≤ Usize.max := src.property
  obtain ⟨⟨s', ptr'⟩, hok, hs', hptr'⟩ :
      ∃ res : Slice U8 × Usize,
        cbstm03a.str_part_loop1 dst ptr src n1 0#usize = .ok res ∧
        res.1.val = dst.val.take ptr.val ++ (src.val.take n1.val).take (dst.val.length - ptr.val) ++
          dst.val.drop (ptr.val + m) ∧
        res.2.val = ptr.val + m := by
    refine exists_ok_of_wp ?_
    simp only [cbstm03a.str_part_loop1]
    refine wp_loop (loop_shape _)
      (fun (s : Slice U8 × Usize × Usize) =>
        s.2.2.val ≤ m ∧
        s.2.1.val = ptr.val + s.2.2.val ∧
        s.1.val = dst.val.take ptr.val ++ src.val.take s.2.2.val ++ dst.val.drop (ptr.val + s.2.2.val))
      (fun s => m - s.2.2.val) ?_ _ ?_
    · rintro ⟨cur, p, k⟩ ⟨hk, hp, hcur⟩
      simp only at hk hp hcur
      have hcl : cur.val.length = dst.val.length := by
        rw [hcur]
        simp only [List.length_append, List.length_take, List.length_drop]
        omega
      aeneas_wp [rust_loop_body, slice_update_eq, uscalar_ofNat_val, Slice.from_val, hcl]
      by_cases hkm : k.val < m
      · have hkn : k.val < n1.val := by omega
        have hpd : p.val < dst.val.length := by omega
        have hks : k.val < src.val.length := by omega
        have hpmax : p.val + 1 ≤ Usize.max := by omega
        have hkmax : k.val + 1 ≤ Usize.max := by omega
        simp only [hkn, hpd, hks, hpmax, hkmax, _root_.dite_true, _root_.ite_true,
          loopCls_cont, UScalar.ofNatCore_val_eq, Slice.from_val]
        refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
        rw [hcur, hp, copy_step dst.val src.val ptr.val k.val hks (by omega),
          Nat.add_assoc]
      · have hkm_eq : k.val = m := by omega
        by_cases hkn : k.val < n1.val
        · have hpd : ¬ p.val < dst.val.length := by omega
          simp only [hkn, hpd, _root_.ite_true, _root_.ite_false, loopCls_done]
          refine ⟨(cur, p), rfl, ?_, by dsimp only; omega⟩
          dsimp only
          rw [hcur, hkm_eq, List.take_take, Nat.min_comm]
        · simp only [hkn, _root_.ite_false, loopCls_done]
          refine ⟨(cur, p), rfl, ?_, by dsimp only; omega⟩
          dsimp only
          rw [hcur, hkm_eq, List.take_take, Nat.min_comm]
    · simp
  exact ⟨s', ptr', hok, hs', hptr'⟩

theorem str_part_loop0_loop0_eq (src delim : Slice U8) (i : Usize)
    (hi : i.val + delim.val.length ≤ src.val.length) :
    cbstm03a.str_part_loop0_loop0 src delim i true 0#usize =
      .ok (decide ((src.val.drop i.val).take delim.val.length = delim.val)) := by
  have hs_max : src.val.length ≤ Usize.max := src.property
  refine eq_ok_of_wp ?_
  simp only [cbstm03a.str_part_loop0_loop0]
  refine wp_loop (loop_shape _)
    (fun (s : Bool × Usize) =>
      s.2.val ≤ delim.val.length ∧
      s.1 = decide (((src.val.drop i.val).take delim.val.length).take s.2.val = delim.val.take s.2.val))
    (fun s => delim.val.length - s.2.val) ?_ _ (by simp)
  rintro ⟨m, j⟩ ⟨hj, hm⟩
  simp only at hj hm
  aeneas_wp [rust_loop_body, uscalar_ofNat_val]
  by_cases hlt : j.val < delim.val.length
  · have hij_max : i.val + j.val ≤ Usize.max := by omega
    have hij_lt : i.val + j.val < src.val.length := by omega
    have hj_max : j.val + 1 ≤ Usize.max := by omega
    have hlt_sub : j.val < ((src.val.drop i.val).take delim.val.length).length := by simp; omega
    have hget_sub : ((src.val.drop i.val).take delim.val.length)[j.val]'hlt_sub =
        src.val[i.val + j.val]'hij_lt := by
      rw [List.getElem_take, List.getElem_drop]
    simp only [hlt, hij_max, hij_lt, hj_max, _root_.dite_true, _root_.ite_true,
      loopCls_cont, UScalar.ofNatCore_val_eq]
    by_cases heq : (src.val[i.val + j.val]'hij_lt).val = (delim.val[j.val]'hlt).val
    · have e1 : ((src.val.drop i.val).take delim.val.length)[j.val]'hlt_sub = delim.val[j.val]'hlt := by
        rw [hget_sub]; exact UScalar.eq_of_val_eq heq
      simp only [heq, not_true_eq_false, _root_.ite_false]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      simp only [hm, take_succ_eq_iff hlt_sub hlt, e1, and_true]
    · have e1 : ¬ ((src.val.drop i.val).take delim.val.length)[j.val]'hlt_sub = delim.val[j.val]'hlt := by
        rw [hget_sub]; exact fun e => heq (e ▸ rfl)
      simp only [heq, not_false_eq_true, _root_.ite_true]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      simp only [take_succ_eq_iff hlt_sub hlt, e1, and_false, decide_false]
  · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq]
    have hj_eq : j.val = delim.val.length := by omega
    rw [hm, hj_eq, List.take_of_length_le (by simp), List.take_length]

theorem str_part_loop0_spec (src delim : Slice U8) (K : Nat)
    (hd0 : 0 < delim.val.length) (hd_le : delim.val.length ≤ src.val.length)
    (hs_max : src.val.length < Usize.max)
    (hbefore : ∀ i, i < K → i + delim.val.length ≤ src.val.length →
      (src.val.drop i).take delim.val.length ≠ delim.val)
    (hat : (K + delim.val.length ≤ src.val.length ∧
      (src.val.drop K).take delim.val.length = delim.val) ∨ K = src.val.length) :
    wp (cbstm03a.str_part_loop0 src delim (Slice.len src) 0#usize false)
      (fun o => ∃ n1 : Usize, o = .ok n1 ∧ n1.val = K) := by
  simp only [cbstm03a.str_part_loop0]
  refine wp_loop (loop_shape _)
    (fun (s : Usize × Usize × Bool) =>
      (s.2.2 = true ∧ s.1.val = K) ∨
      (s.2.2 = false ∧ s.1.val = src.val.length ∧ s.2.1.val ≤ K ∧
        s.2.1.val + delim.val.length ≤ src.val.length + 1))
    (fun s => if s.2.2 then 0 else K - s.2.1.val + 1) ?_ _ ?_
  · rintro ⟨n1, i, found⟩ hinv
    rcases hinv with ⟨hf, hn1⟩ | ⟨hf, hn1, hi, hibd⟩
    · simp only at hf hn1
      subst hf
      unfold cbstm03a.str_part_loop0.body
      rw [ite_eq_left rfl, wp_ok]
      exact ⟨n1, rfl, hn1⟩
    · simp only at hf hn1 hi hibd
      subst hf
      have himax : i.val + delim.val.length ≤ Usize.max := by omega
      aeneas_wp [rust_loop_body, uscalar_ofNat_val, himax]
      by_cases hle : i.val + delim.val.length ≤ src.val.length
      · simp only [hle, _root_.ite_true, str_part_loop0_loop0_eq src delim i hle, wp_ok]
        by_cases hiK : i.val < K
        · have hne := hbefore i.val hiK hle
          have hdec : decide ((src.val.drop i.val).take delim.val.length = delim.val) = false :=
            decide_eq_false hne
          have hi1max : i.val + 1 ≤ Usize.max := by omega
          simp only [hdec, Bool.false_eq_true, _root_.ite_false, hi1max, _root_.dite_true,
            loopCls_cont, UScalar.ofNatCore_val_eq]
          exact ⟨Or.inr ⟨trivial, hn1, by omega, by omega⟩, by omega⟩
        · have hi_eq : i.val = K := by omega
          rcases hat with ⟨_, hmatch⟩ | hK_len
          · have hdec : decide ((src.val.drop i.val).take delim.val.length = delim.val) = true := by
              rw [hi_eq]; exact decide_eq_true hmatch
            simp only [hdec, _root_.ite_true, loopCls_cont]
            exact ⟨Or.inl ⟨trivial, hi_eq⟩,
              by simp only [↓reduceIte, Bool.false_eq_true]; omega⟩
          · omega
      · simp only [hle, _root_.ite_false, loopCls_done]
        rcases hat with ⟨h1, _⟩ | hK_len
        · omega
        · exact ⟨n1, rfl, by omega⟩
  · exact Or.inr ⟨rfl, by simp, Nat.zero_le _, by simp; omega⟩

/-- General specification of `str_part` for any delimiter with match position `K`. -/
theorem str_part_delim_spec (dst : Slice U8) (ptr : Usize) (src delim : Slice U8) (K : Nat)
    (hptr : ptr.val ≤ dst.val.length) (hd0 : 0 < delim.val.length)
    (hs_max : src.val.length < Usize.max) (hK : K ≤ src.val.length)
    (hbefore : ∀ i, i < K → i + delim.val.length ≤ src.val.length →
      (src.val.drop i).take delim.val.length ≠ delim.val)
    (hat : (K + delim.val.length ≤ src.val.length ∧
      (src.val.drop K).take delim.val.length = delim.val) ∨ K = src.val.length) :
    let m := min K (dst.val.length - ptr.val)
    ∃ (s' : Slice U8) (ptr' : Usize),
      cbstm03a.str_part dst ptr src delim = .ok (s', ptr') ∧
      s'.val = dst.val.take ptr.val ++ (src.val.take K).take (dst.val.length - ptr.val) ++
        dst.val.drop (ptr.val + m) ∧
      ptr'.val = ptr.val + m := by
  intro m
  have hd_gt : Slice.len delim > 0#usize := by
    simp [UScalar.lt_equiv, hd0]
  have hloop2 : cbstm03a.str_part_loop2 = cbstm03a.str_part_loop1 := rfl
  unfold cbstm03a.str_part
  dsimp only
  rw [ite_eq_left hd_gt]
  by_cases hd_le : delim.val.length ≤ src.val.length
  · have hle_usz : Slice.len delim <= Slice.len src := by
      simp [UScalar.le_equiv, hd_le]
    rw [ite_eq_left hle_usz]
    obtain ⟨n1, hn1, hn1_val⟩ :=
      exists_ok_of_wp (str_part_loop0_spec src delim K hd0 hd_le hs_max hbefore hat)
    rw [hn1, bind_ok]
    obtain ⟨s', ptr', h1, h2, h3⟩ := str_part_loop1_eq dst ptr src n1 hptr (by omega)
    exact ⟨s', ptr', h1, by simpa [hn1_val, m] using h2, by simpa [hn1_val, m] using h3⟩
  · have hle_usz : ¬ (Slice.len delim <= Slice.len src) := by
      simp [UScalar.le_equiv, hd_le]
    have hK_eq : K = src.val.length := by
      rcases hat with ⟨h1, _⟩ | h2
      · omega
      · exact h2
    rw [ite_eq_right hle_usz, hloop2]
    obtain ⟨s', ptr', h1, h2, h3⟩ := str_part_loop1_eq dst ptr src (Slice.len src) hptr (by simp)
    exact ⟨s', ptr', h1, by simpa [Slice.len_val, ← hK_eq, m] using h2,
      by simpa [Slice.len_val, ← hK_eq, m] using h3⟩

/-! ### 8.1 `str_part` with empty delimiter (`b""`) -/

theorem str_part_empty_eq (dst : Slice U8) (ptr : Usize) (src delim : Slice U8)
    (hdelim : delim.val = []) (hptr : ptr.val ≤ dst.val.length) :
    let m := min src.val.length (dst.val.length - ptr.val)
    ∃ (s' : Slice U8) (ptr' : Usize),
      cbstm03a.str_part dst ptr src delim = .ok (s', ptr') ∧
      s'.val = dst.val.take ptr.val ++ src.val.take (dst.val.length - ptr.val) ++
        dst.val.drop (ptr.val + m) ∧
      ptr'.val = ptr.val + m := by
  intro m
  have hd0 : ¬ (Slice.len delim > 0#usize) := by
    simp [UScalar.lt_equiv, hdelim]
  have hloop : cbstm03a.str_part_loop3 = cbstm03a.str_part_loop1 := rfl
  unfold cbstm03a.str_part
  dsimp only
  rw [ite_eq_right hd0, hloop]
  obtain ⟨s', ptr', h1, h2, h3⟩ := str_part_loop1_eq dst ptr src (Slice.len src) hptr (by simp)
  refine ⟨s', ptr', h1, ?_, ?_⟩
  · simpa [Slice.len_val] using h2
  · simpa [Slice.len_val, m] using h3

theorem str_part_empty_fit (dst : Slice U8) (ptr : Usize) (src delim : Slice U8)
    (pre rest : List U8) (hdelim : delim.val = [])
    (hdst : dst.val = pre ++ rest) (hptr : pre.length = ptr.val)
    (hfit : src.val.length ≤ rest.length) :
    ∃ (s' : Slice U8) (ptr' : Usize),
      cbstm03a.str_part dst ptr src delim = .ok (s', ptr') ∧
      s'.val = pre ++ src.val ++ rest.drop src.val.length ∧
      ptr'.val = ptr.val + src.val.length := by
  have hd_len : dst.val.length = ptr.val + rest.length := by simp [hdst, hptr]
  obtain ⟨s', ptr', hok, hs', hptr'⟩ :=
    str_part_empty_eq dst ptr src delim hdelim (by omega)
  have hm : min src.val.length (dst.val.length - ptr.val) = src.val.length := by
    rw [hd_len, Nat.add_sub_cancel_left]; exact Nat.min_eq_left hfit
  refine ⟨s', ptr', hok, ?_, by rw [hptr', hm]⟩
  rw [hs', hm, hdst, ← hptr, List.take_left,
    show (pre ++ rest).length - pre.length = rest.length by simp,
    List.take_of_length_le hfit, drop_append_add]

theorem str_part_empty_ovw (dst : Slice U8) (ptr : Usize) (src delim : Slice U8)
    (A B piece : List UInt8) (hdelim : delim.val = [])
    (hdst : dst.val = latL (A ++ B)) (hptr : ptr.val = A.length)
    (hsrc : src.val = latL piece) :
    ∃ (s' : Slice U8) (ptr' : Usize),
      cbstm03a.str_part dst ptr src delim = .ok (s', ptr') ∧
      s'.val = latL (A ++ ovw piece B) ∧
      ptr'.val = A.length + min piece.length B.length := by
  have hdl : dst.val.length = A.length + B.length := by simp [hdst]
  have hsl : src.val.length = piece.length := by simp [hsrc]
  obtain ⟨s', ptr', hok, hs', hptr'⟩ :=
    str_part_empty_eq dst ptr src delim hdelim (by omega)
  refine ⟨s', ptr', hok, ?_, by rw [hptr', hptr, hsl]; congr 2; omega⟩
  rw [hs', hsl, hdst, hsrc, hptr, copy_latL_ovw]

/-! ### 8.2 `str_part` with single-byte delimiter (`b" "` or `b"*"`, `tokB`) -/

theorem tokB_props (b : UInt8) :
    ∀ bs : List UInt8,
      (tokB b bs).length ≤ bs.length ∧
      bs.take (tokB b bs).length = tokB b bs ∧
      (∀ i, i < (tokB b bs).length → (bs.drop i).take 1 ≠ [b]) ∧
      (((tokB b bs).length + 1 ≤ bs.length ∧ (bs.drop (tokB b bs).length).take 1 = [b]) ∨
        (tokB b bs).length = bs.length)
  | [] => by simp [tokB_nil]
  | x :: xs => by
    rw [tokB_cons]
    by_cases hxb : x = b
    · subst hxb; simp
    · obtain ⟨h1, h2, h3, h4⟩ := tokB_props b xs
      simp only [hxb, ↓reduceIte, List.length_cons, List.take_succ_cons]
      refine ⟨by omega, congrArg (x :: ·) h2, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => simp [hxb]
        | succ i => exact h3 i (by omega)
      · rcases h4 with ⟨h4a, h4b⟩ | h4c
        · exact Or.inl ⟨by omega, h4b⟩
        · exact Or.inr (by omega)

theorem str_part_single_eq (dst : Slice U8) (ptr : Usize) (src delim : Slice U8)
    (b : UInt8) (bs : List UInt8) (hdelim : delim.val = [lat b])
    (hsrc : src.val = latL bs)
    (hptr : ptr.val ≤ dst.val.length)
    (hs_max : bs.length < Usize.max := by have := usize_max_ge; omega) :
    let m := min (tokB b bs).length (dst.val.length - ptr.val)
    ∃ (s' : Slice U8) (ptr' : Usize),
      cbstm03a.str_part dst ptr src delim = .ok (s', ptr') ∧
      s'.val = dst.val.take ptr.val ++ (latL (tokB b bs)).take (dst.val.length - ptr.val) ++
        dst.val.drop (ptr.val + m) ∧
      ptr'.val = ptr.val + m := by
  intro m
  obtain ⟨hK_le, htake, hbefore, hat⟩ := tokB_props b bs
  have hsl : src.val.length = bs.length := by simp [hsrc]
  have hdl : delim.val.length = 1 := by simp [hdelim]
  have hd1 : delim.val = latL [b] := by simp [hdelim, latL]
  have hbefore' : ∀ i, i < (tokB b bs).length → i + delim.val.length ≤ src.val.length →
      (src.val.drop i).take delim.val.length ≠ delim.val := by
    intro i hi _ h
    rw [hsrc, hdl, hd1, ← latL_drop, ← latL_take, latL_inj] at h
    exact hbefore i hi h
  have hat' : ((tokB b bs).length + delim.val.length ≤ src.val.length ∧
      (src.val.drop (tokB b bs).length).take delim.val.length = delim.val) ∨
      (tokB b bs).length = src.val.length := by
    rw [hsl, hdl, hsrc, hd1, ← latL_drop, ← latL_take, latL_inj]
    exact hat
  obtain ⟨s', ptr', h1, h2, h3⟩ :=
    str_part_delim_spec dst ptr src delim (tokB b bs).length hptr (by omega)
      (by omega) (by omega) hbefore' hat'
  refine ⟨s', ptr', h1, ?_, h3⟩
  rw [hsrc, ← latL_take, htake] at h2
  exact h2

theorem str_part_single_ovw (dst : Slice U8) (ptr : Usize) (src delim : Slice U8)
    (b : UInt8) (A B bs : List UInt8) (hdelim : delim.val = [lat b])
    (hdst : dst.val = latL (A ++ B)) (hptr : ptr.val = A.length)
    (hsrc : src.val = latL bs)
    (hs_max : bs.length < Usize.max := by have := usize_max_ge; omega) :
    ∃ (s' : Slice U8) (ptr' : Usize),
      cbstm03a.str_part dst ptr src delim = .ok (s', ptr') ∧
      s'.val = latL (A ++ ovw (tokB b bs) B) ∧
      ptr'.val = A.length + min (tokB b bs).length B.length := by
  have hdl : dst.val.length = A.length + B.length := by simp [hdst]
  obtain ⟨s', ptr', hok, hs', hptr'⟩ :=
    str_part_single_eq dst ptr src delim b bs hdelim hsrc (by omega) hs_max
  refine ⟨s', ptr', hok, ?_, by rw [hptr', hptr]; congr 2; omega⟩
  rw [hs', hdst, hptr, copy_latL_ovw]

/-! ### 8.3 `str_part` with double-space delimiter (`b"  "`, `tok2`) -/

theorem tok2_props :
    ∀ bs : List UInt8,
      (tok2 bs).length ≤ bs.length ∧
      bs.take (tok2 bs).length = tok2 bs ∧
      (∀ i, i < (tok2 bs).length → i + 2 ≤ bs.length → (bs.drop i).take 2 ≠ [64, 64]) ∧
      (((tok2 bs).length + 2 ≤ bs.length ∧ (bs.drop (tok2 bs).length).take 2 = [64, 64]) ∨
        (tok2 bs).length = bs.length)
  | [] => by simp [tok2]
  | [x] => by
    refine ⟨by simp [tok2], by simp [tok2], ?_, Or.inr (by simp [tok2])⟩
    intro i _ hi2; simp at hi2
  | x :: y :: rest => by
    rw [tok2_cons_cons]
    by_cases hxy : x = 64 ∧ y = 64
    · rcases hxy with ⟨rfl, rfl⟩
      simp
    · obtain ⟨h1, h2, h3, h4⟩ := tok2_props (y :: rest)
      simp only [hxy, ↓reduceIte, List.length_cons, List.take_succ_cons]
      refine ⟨by simp at h1 ⊢; omega, congrArg (x :: ·) h2, ?_, ?_⟩
      · intro i hi hi2
        cases i with
        | zero =>
          simp only [List.drop_zero, List.take_succ_cons, List.take_zero, ne_eq, List.cons.injEq,
            and_true]
          exact hxy
        | succ i =>
          exact h3 i (by omega) (by simp at hi2 ⊢; omega)
      · rcases h4 with ⟨h4a, h4b⟩ | h4c
        · exact Or.inl ⟨by simp at h4a ⊢; omega, h4b⟩
        · exact Or.inr (by simp at h4c ⊢; omega)

theorem str_part_double_eq (dst : Slice U8) (ptr : Usize) (src delim : Slice U8)
    (bs : List UInt8) (hdelim : delim.val = [32#u8, 32#u8])
    (hsrc : src.val = latL bs)
    (hptr : ptr.val ≤ dst.val.length)
    (hs_max : bs.length < Usize.max := by have := usize_max_ge; omega) :
    let m := min (tok2 bs).length (dst.val.length - ptr.val)
    ∃ (s' : Slice U8) (ptr' : Usize),
      cbstm03a.str_part dst ptr src delim = .ok (s', ptr') ∧
      s'.val = dst.val.take ptr.val ++ (latL (tok2 bs)).take (dst.val.length - ptr.val) ++
        dst.val.drop (ptr.val + m) ∧
      ptr'.val = ptr.val + m := by
  intro m
  obtain ⟨hK_le, htake, hbefore, hat⟩ := tok2_props bs
  have hsl : src.val.length = bs.length := by simp [hsrc]
  have hdl : delim.val.length = 2 := by simp [hdelim]
  have hd2 : delim.val = latL [64, 64] := by simp [hdelim, latL, lat_space]
  have hbefore' : ∀ i, i < (tok2 bs).length → i + delim.val.length ≤ src.val.length →
      (src.val.drop i).take delim.val.length ≠ delim.val := by
    intro i hi hle h
    rw [hsrc, hdl, hd2, ← latL_drop, ← latL_take, latL_inj] at h
    exact hbefore i hi (by omega) h
  have hat' : ((tok2 bs).length + delim.val.length ≤ src.val.length ∧
      (src.val.drop (tok2 bs).length).take delim.val.length = delim.val) ∨
      (tok2 bs).length = src.val.length := by
    rw [hsl, hdl, hsrc, hd2, ← latL_drop, ← latL_take, latL_inj]
    exact hat
  obtain ⟨s', ptr', h1, h2, h3⟩ :=
    str_part_delim_spec dst ptr src delim (tok2 bs).length hptr (by omega)
      (by omega) (by omega) hbefore' hat'
  refine ⟨s', ptr', h1, ?_, h3⟩
  rw [hsrc, ← latL_take, htake] at h2
  exact h2

theorem str_part_double_ovw (dst : Slice U8) (ptr : Usize) (src delim : Slice U8)
    (A B bs : List UInt8) (hdelim : delim.val = [32#u8, 32#u8])
    (hdst : dst.val = latL (A ++ B)) (hptr : ptr.val = A.length)
    (hsrc : src.val = latL bs)
    (hs_max : bs.length < Usize.max := by have := usize_max_ge; omega) :
    ∃ (s' : Slice U8) (ptr' : Usize),
      cbstm03a.str_part dst ptr src delim = .ok (s', ptr') ∧
      s'.val = latL (A ++ ovw (tok2 bs) B) ∧
      ptr'.val = A.length + min (tok2 bs).length B.length := by
  have hdl : dst.val.length = A.length + B.length := by simp [hdst]
  obtain ⟨s', ptr', hok, hs', hptr'⟩ :=
    str_part_double_eq dst ptr src delim bs hdelim hsrc (by omega) hs_max
  refine ⟨s', ptr', hok, ?_, by rw [hptr', hptr]; congr 2; omega⟩
  rw [hs', hdst, hptr, copy_latL_ovw]

/-! ## 9. `add1` and `add_trunc11` -/

theorem add1_eq (x : I64) (h0 : 0 ≤ x.val) (h1 : x.val < 9999) :
    ∃ y : I64, cbstm03a.add1 x = .ok y ∧ y.val = x.val + 1 := by
  refine exists_ok_of_wp ?_
  unfold cbstm03a.add1
  aeneas_wp []
  simp (disch := omega) only [dite_eq_left, ite_eq_left]
  refine ⟨_, rfl, ?_⟩
  rw [iscalar_srem_val, IScalar.ofInt_val_eq, iscalar_ofInt_val,
    Int.tmod_eq_of_lt (by omega) (by omega)]

theorem add_trunc11_eq (a b : I64) (ha : a.val.natAbs < 10 ^ 11) (hb : b.val.natAbs < 10 ^ 11) :
    ∃ y : I64, cbstm03a.add_trunc11 a b = .ok y ∧
      y.val = (Sem.fitNum {} { digits := 11, scale := 2, signed := true, usage := .packed }
        (a.val + b.val)).2 := by
  have hfit : (Sem.fitNum {} { digits := 11, scale := 2, signed := true, usage := .packed }
      (a.val + b.val)).2 = Int.tmod (a.val + b.val) 100000000000 := by
    have hfb : ({ digits := 11, scale := 2, signed := true, usage := .packed } : NumFmt).fullBinary {} =
        false := rfl
    simp only [Sem.fitNum, ↓reduceIte, hfb, Bool.false_eq_true]
    exact EquivLean.Modernize.GlueKit.fitDec_eq 11 (a.val + b.val)
  rw [hfit]
  refine exists_ok_of_wp ?_
  unfold cbstm03a.add_trunc11
  aeneas_wp []
  by_cases hs : a.val + b.val < 0
  · simp only [hs, _root_.ite_true]
    have hrem : (-(a.val + b.val)).tmod 100000000000 = (-(a.val + b.val)) % 100000000000 :=
      Int.tmod_eq_emod_of_nonneg (by omega)
    have hrem_bd : 0 ≤ (-(a.val + b.val)) % 100000000000 ∧
        (-(a.val + b.val)) % 100000000000 < 100000000000 :=
      ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
    simp (disch := omega) only [dite_eq_left, ite_eq_left, iscalar_srem_val, IScalar.ofInt_val_eq,
      hrem]
    refine ⟨_, rfl, ?_⟩
    rw [IScalar.ofInt_val_eq, ← hrem, ← EquivLean.Modernize.GlueKit.tmod_neg_of_neg hs]
  · simp only [hs, _root_.ite_false]
    simp (disch := omega) only [dite_eq_left, ite_eq_left]
    refine ⟨_, rfl, ?_⟩
    rw [iscalar_srem_val, IScalar.ofInt_val_eq, iscalar_ofInt_val]

#print axioms vb_eq
#print axioms app_eq
#print axioms put_eq
#print axioms fill_eq
#print axioms eq_bytes_eq
#print axioms lat2ebc_table_eq
#print axioms gt_bytes_eq
#print axioms put_unum_eq
#print axioms put_snum_eq
#print axioms digits11_eq
#print axioms fmt_9_99_eq
#print axioms fmt_z_99_eq
#print axioms zoned_eq
#print axioms zoned_digitChars_eq
#print axioms str_part_empty_eq
#print axioms str_part_empty_fit
#print axioms str_part_empty_ovw
#print axioms str_part_single_eq
#print axioms str_part_single_ovw
#print axioms str_part_double_eq
#print axioms str_part_double_ovw
#print axioms add1_eq
#print axioms add_trunc11_eq

end EquivLean.Modernize.Cbstm03a.Rust
