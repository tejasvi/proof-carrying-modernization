import EquivLean.Modernize.Cbstm03a.RustDefs

open Aeneas Aeneas.Std Result ControlFlow Error EquivLean EquivLean.Aeneas
open Cobol Cobol.StmCore EquivLean.Cobol.Rec
open EquivLean.Modernize.Cbstm03a.StmBridge EquivLean.Modernize.Cbstm03a.Model

set_option maxRecDepth 20000

namespace EquivLean.Modernize.Cbstm03a.Rust

/-! ## 1. Mathematical model of `cbstm03a.Mem` -/

/-- Total byte length of a list of writes `ws`. -/
def wsBytesLen (ws : List (Int × List U8)) : Nat :=
  (ws.map (fun w => w.2.length)).sum

@[simp] theorem wsBytesLen_nil : wsBytesLen [] = 0 := rfl

@[simp] theorem wsBytesLen_append (ws1 ws2 : List (Int × List U8)) :
    wsBytesLen (ws1 ++ ws2) = wsBytesLen ws1 + wsBytesLen ws2 := by
  simp [wsBytesLen, List.map_append, List.sum_append]

@[simp] theorem wsBytesLen_singleton (o : Int) (bs : List U8) :
    wsBytesLen [(o, bs)] = bs.length := by
  simp [wsBytesLen]

/-- Well-formedness of `cbstm03a.Mem` representing the sequence of writes `ws`. -/
def MemWF (mem : cbstm03a.Mem) (ws : List (Int × List U8)) : Prop :=
  mem.offs.val.length = ws.length ∧
  mem.starts.val.length = ws.length ∧
  mem.lens.val.length = ws.length ∧
  mem.bytes.val.length = wsBytesLen ws ∧
  (∀ w ∈ ws, 0 ≤ w.1 ∧ w.1 + (w.2.length : Int) ≤ 200000) ∧
  (∀ k, k < ws.length →
    (mem.offs.val.getD k 0#i64).val = (ws.getD k (0, [])).1 ∧
    (mem.lens.val.getD k 0#usize).val = (ws.getD k (0, [])).2.length ∧
    (mem.starts.val.getD k 0#usize).val + (ws.getD k (0, [])).2.length ≤ mem.bytes.val.length ∧
    (mem.bytes.val.drop (mem.starts.val.getD k 0#usize).val).take (ws.getD k (0, [])).2.length =
      (ws.getD k (0, [])).2)

/-- The initial empty `Mem`. -/
@[reducible] def emptyMem : cbstm03a.Mem :=
  { offs := alloc.vec.Vec.new Std.I64
    starts := alloc.vec.Vec.new Std.Usize
    lens := alloc.vec.Vec.new Std.Usize
    bytes := alloc.vec.Vec.new Std.U8 }

theorem memWF_empty : MemWF emptyMem [] := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro w hw; simp at hw
  · intro k hk; simp at hk

theorem mem_default_eq (p : Std.I64) :
    cbstm03a.mem_default p =
      .ok (if 0 ≤ p.val ∧ p.val < 171156 then 32#u8 else 0#u8) := by
  have htsz : cbstm03a.TABLE_SZ.val = 171156 := by simp [cbstm03a.TABLE_SZ]
  refine eq_ok_of_wp ?_
  unfold cbstm03a.mem_default
  aeneas_wp [htsz]
  split_ifs <;> simp_all

theorem mem_write_loop_spec (v : alloc.vec.Vec Std.U8) (src : Slice Std.U8)
    (hmax : v.val.length + src.val.length ≤ Usize.max) :
    ∃ v', cbstm03a.mem_write_loop v src 0#usize = .ok v' ∧
      v'.val = v.val ++ src.val := by
  refine exists_ok_of_wp ?_
  unfold cbstm03a.mem_write_loop
  refine wp_loop (loop_shape _)
    (fun (s : alloc.vec.Vec Std.U8 × Std.Usize) =>
      s.2.val ≤ src.val.length ∧ s.1.val = v.val ++ src.val.take s.2.val)
    (fun s => src.val.length - s.2.val) ?_ _ ?_
  · rintro ⟨v1, i⟩ ⟨hi, hv1⟩
    simp only at hi hv1
    by_cases hlt : i.val < src.val.length
    · have hvlen : v1.val.length < Usize.max := by
        rw [hv1, List.length_append, List.length_take]; omega
      have himax : i.val + 1 ≤ Usize.max := by
        have := src.property; omega
      aeneas_wp [rust_loop_body, hlt, hvlen, himax]
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq, alloc.vec.Vec.from_val]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hv1, take_succ_of_lt hlt, List.append_assoc]
    · aeneas_wp [rust_loop_body, hlt]
      simp only [loopCls_done]
      have hieq : i.val = src.val.length := by omega
      refine ⟨v1, rfl, ?_⟩
      rw [hv1, hieq, List.take_length]
  · simp

theorem drop_take_append_of_le {α : Type _} (l1 l2 : List α) (st ln : Nat)
    (h : st + ln ≤ l1.length) :
    ((l1 ++ l2).drop st).take ln = (l1.drop st).take ln := by
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp [List.length_drop]; omega)]

theorem mem_write_spec (mem : cbstm03a.Mem) (ws : List (Int × List U8))
    (off : Std.I64) (src : Slice Std.U8)
    (hwf : MemWF mem ws)
    (hlen1 : ws.length < Usize.max)
    (hlen2 : wsBytesLen ws + src.val.length ≤ Usize.max)
    (hoff0 : 0 ≤ off.val)
    (hoff1 : off.val + (src.val.length : Int) ≤ 200000) :
    ∃ mem', cbstm03a.mem_write mem off src = .ok mem' ∧
      MemWF mem' (ws ++ [(off.val, src.val)]) := by
  obtain ⟨hoL, hsL, hlL, hbL, hwB, hkP⟩ := hwf
  obtain ⟨v3, hv3, hv3val⟩ := mem_write_loop_spec mem.bytes src (by omega)
  have ho_lt : mem.offs.val.length < Usize.max := by omega
  have hs_lt : mem.starts.val.length < Usize.max := by omega
  have hl_lt : mem.lens.val.length < Usize.max := by omega
  refine exists_ok_of_wp ?_
  unfold cbstm03a.mem_write
  aeneas_wp [ho_lt, hs_lt, hl_lt, hv3]
  refine ⟨_, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hoL]
  · simp [hsL]
  · simp [hlL]
  · simp [hv3val, hbL]
  · intro w hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact hwB w hw
    · exact ⟨hoff0, hoff1⟩
  · intro k hk
    simp only [List.length_append, List.length_singleton] at hk
    simp only [alloc.vec.Vec.from_val, hv3val]
    by_cases hlt : k < ws.length
    · obtain ⟨hk1, hk2, hk3, hk4⟩ := hkP k hlt
      rw [getD_snoc_lt _ _ _ _ (by omega : k < mem.offs.val.length),
        getD_snoc_lt _ _ _ _ (by omega : k < mem.lens.val.length),
        getD_snoc_lt _ _ _ _ (by omega : k < mem.starts.val.length),
        getD_snoc_lt _ _ _ _ hlt]
      refine ⟨hk1, hk2, by rw [List.length_append]; omega, ?_⟩
      rw [drop_take_append_of_le _ _ _ _ hk3]
      exact hk4
    · have hkeq : k = ws.length := by omega
      subst hkeq
      rw [← hoL, getD_snoc_eq, hoL,
        ← hlL, getD_snoc_eq, hlL,
        ← hsL, getD_snoc_eq, hsL,
        getD_snoc_eq]
      refine ⟨by simp, by simp, by simp, ?_⟩
      simp only [alloc.vec.Vec.len_val]
      rw [List.drop_left, List.take_length]

theorem hcast_i64_of_le (x : Std.Usize) (h : x.val ≤ 200000) :
    (UScalar.hcast .I64 x).val = (x.val : Int) := by
  rw [UScalar.hcast_val_eq]
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' _ _ (by decide)
  · simp [IScalarTy.I64_numBits_eq]
  · simp [IScalarTy.I64_numBits_eq]; omega

theorem hcast_usize_of_nonneg (x : Std.I64) (h0 : 0 ≤ x.val) (h1 : x.val ≤ 200000) :
    (IScalar.hcast .Usize x).val = x.val.toNat := by
  have hb : x.val < 2 ^ UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp only [UScalarTy.numBits, h] <;> omega
  rw [IScalar.hcast_val_eq, Int.emod_eq_of_lt h0 hb]

/-- Every write in `ws` is either disjoint from `[off, off + bs.length)` or equal to `(off, bs)`,
and `(off, bs)` has been written at least once. -/
def HasWrite (ws : List (Int × List U8)) (off : Int) (bs : List U8) : Prop :=
  (off, bs) ∈ ws ∧
  ∀ w ∈ ws, (w.1 + (w.2.length : Int) ≤ off ∨ off + (bs.length : Int) ≤ w.1) ∨ w = (off, bs)

theorem mem_get_loop0_spec (off : Std.I64) (dst : Slice Std.U8)
    (hoff0 : 0 ≤ off.val) (hoff1 : off.val + (dst.val.length : Int) ≤ 200000) :
    ∃ dst1, cbstm03a.mem_get_loop0 off dst 0#usize = .ok dst1 ∧
      dst1.val.length = dst.val.length := by
  refine exists_ok_of_wp ?_
  unfold cbstm03a.mem_get_loop0
  refine wp_loop (loop_shape _)
    (fun (s : Slice Std.U8 × Std.Usize) =>
      s.2.val ≤ dst.val.length ∧ s.1.val.length = dst.val.length)
    (fun s => dst.val.length - s.2.val) ?_ _ ?_
  · rintro ⟨dst1, i⟩ ⟨hi, hlen⟩
    simp only at hi hlen
    by_cases hlt : i.val < dst.val.length
    · have hlt' : i.val < dst1.val.length := by omega
      have himax : i.val + 1 ≤ Usize.max := by have := dst.property; omega
      have hcast : (UScalar.hcast .I64 i).val = (i.val : Int) :=
        hcast_i64_of_le i (by omega)
      have hadd : -9223372036854775808 ≤ off.val + (UScalar.hcast .I64 i).val ∧
          off.val + (UScalar.hcast .I64 i).val ≤ 9223372036854775807 := by omega
      aeneas_wp [rust_loop_body, mem_default_eq, slice_update_eq, hlt, hlt', himax, hadd]
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq, Slice.from_val, List.length_set]
      exact ⟨⟨by omega, hlen⟩, by omega⟩
    · have hlt' : ¬ i.val < dst1.val.length := by omega
      aeneas_wp [rust_loop_body, hlt']
      simp only [loopCls_done]
      exact ⟨dst1, rfl, hlen⟩
  · simp

theorem mem_get_loop1_loop0_disjoint (v : alloc.vec.Vec Std.U8) (off : Std.I64)
    (dst : Slice Std.U8) (o : Std.I64) (start : Std.Usize) (s e : Std.I64)
    (hdisj : e.val ≤ s.val) :
    cbstm03a.mem_get_loop1_loop0 v off dst o start s e = .ok dst := by
  unfold cbstm03a.mem_get_loop1_loop0
  rw [loop_unfold]
  have hlt : ¬ (s < e) := by scalar_tac
  simp [cbstm03a.mem_get_loop1_loop0.body, hlt]

theorem getElem_of_drop_take_eq {α : Type _} {l bs : List α} {st j : Nat}
    (hst : st + bs.length ≤ l.length) (hdt : (l.drop st).take bs.length = bs)
    (hj : j < bs.length) :
    l[st + j]'(by omega) = bs[j]'hj := by
  have h1 : bs[j]'hj = ((l.drop st).take bs.length)[j]'(by rw [hdt]; exact hj) := by
    congr 1; exact hdt.symm
  rw [h1, List.getElem_take, List.getElem_drop]

theorem set_take_append_drop {α : Type _} (bs dst : List α) (j : Nat)
    (hlen : dst.length = bs.length) (hj : j < bs.length) :
    (bs.take j ++ dst.drop j).set j (bs[j]'hj) = bs.take (j + 1) ++ dst.drop (j + 1) := by
  have htl : (bs.take j).length = j := by simp; omega
  rw [List.set_append_right _ _ (by omega)]
  simp only [htl, Nat.sub_self]
  rw [set_drop_zero dst j _ (by omega), take_succ_of_lt hj, List.append_assoc, List.singleton_append]

theorem mem_get_loop1_loop0_exact (v : alloc.vec.Vec Std.U8) (off : Std.I64)
    (dst : Slice Std.U8) (start : Std.Usize) (e : Std.I64) (bs : List U8)
    (hoff0 : 0 ≤ off.val) (hoff1 : off.val + (bs.length : Int) ≤ 200000)
    (hdst : dst.val.length = bs.length)
    (he : e.val = off.val + (bs.length : Int))
    (hst : start.val + bs.length ≤ v.val.length)
    (hdt : (v.val.drop start.val).take bs.length = bs) :
    ∃ dst', cbstm03a.mem_get_loop1_loop0 v off dst off start off e = .ok dst' ∧
      dst'.val = bs := by
  refine exists_ok_of_wp ?_
  unfold cbstm03a.mem_get_loop1_loop0
  refine wp_loop (loop_shape _)
    (fun (st : Slice Std.U8 × Std.I64) =>
      off.val ≤ st.2.val ∧ st.2.val ≤ e.val ∧
      st.1.val = bs.take (st.2.val - off.val).toNat ++ dst.val.drop (st.2.val - off.val).toNat)
    (fun st => (e.val - st.2.val).toNat) ?_ _ ?_
  · rintro ⟨dst1, s⟩ ⟨hs0, hs1, hdst1⟩
    simp only at hs0 hs1 hdst1
    by_cases hlt : s.val < e.val
    · set j : Nat := (s.val - off.val).toNat
      have hj_eq : (j : Int) = s.val - off.val := Int.toNat_of_nonneg (by omega)
      have hj_lt : j < bs.length := by omega
      have hsub : -9223372036854775808 ≤ s.val - off.val ∧
          s.val - off.val ≤ 9223372036854775807 := by omega
      have hs_add : -9223372036854775808 ≤ s.val + 1 ∧
          s.val + 1 ≤ 9223372036854775807 := by omega
      have hvmax : v.val.length ≤ Usize.max := v.property
      have hdst1_len : dst1.val.length = bs.length := by
        rw [hdst1, List.length_append, List.length_take, List.length_drop, hdst]; omega
      aeneas_wp [rust_loop_body, slice_update_eq, hlt, hsub, hs_add]
      have hcast_i : (IScalar.hcast .Usize (IScalar.ofIntCore (ty := .I64) (s.val - off.val)
          ⟨by simp [IScalarTy.I64_numBits_eq]; omega,
           by simp [IScalarTy.I64_numBits_eq]; omega⟩)).val = j := by
        rw [hcast_usize_of_nonneg _ (by rw [IScalar.ofInt_val_eq]; omega)
          (by rw [IScalar.ofInt_val_eq]; omega), IScalar.ofInt_val_eq]
      have hst_add : start.val + j ≤ Usize.max := by omega
      have hsrc_lt : start.val + j < v.val.length := by omega
      have hdst_lt : j < dst1.val.length := by omega
      simp only [hcast_i, hst_add, hsrc_lt, hdst_lt, ↓reduceDIte, loopCls_cont,
        IScalar.ofInt_val_eq, Slice.from_val]
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      have hj1 : (s.val + 1 - off.val).toNat = j + 1 := by omega
      rw [hj1, hdst1, getElem_of_drop_take_eq hst hdt hj_lt,
        set_take_append_drop bs dst.val j hdst hj_lt]
    · aeneas_wp [rust_loop_body, hlt]
      simp only [loopCls_done]
      have hseq : (s.val - off.val).toNat = bs.length := by omega
      refine ⟨dst1, rfl, ?_⟩
      rw [hdst1, hseq, List.take_length, ← hdst, List.drop_length, List.append_nil]
  · simp [he]

theorem mem_get_loop1_spec (mem : cbstm03a.Mem) (ws : List (Int × List U8))
    (off : Std.I64) (dst1 : Slice Std.U8) (dl : Std.I64) (bs : List U8)
    (hwf : MemWF mem ws)
    (hhas : HasWrite ws off.val bs)
    (hbs_pos : 0 < bs.length)
    (hdst1 : dst1.val.length = bs.length)
    (hdl : dl.val = (bs.length : Int)) :
    ∃ dst', cbstm03a.mem_get_loop1 mem off dst1 dl 0#usize = .ok dst' ∧
      dst'.val = bs := by
  obtain ⟨hoL, hsL, hlL, hbL, hwB, hkP⟩ := hwf
  obtain ⟨hmem_ws, hdisj_or_eq⟩ := hhas
  obtain ⟨hoff0, hoff1⟩ := hwB (off.val, bs) hmem_ws
  simp only at hoff0 hoff1
  refine exists_ok_of_wp ?_
  unfold cbstm03a.mem_get_loop1
  refine wp_loop (loop_shape _)
    (fun (st : Slice Std.U8 × Std.Usize) =>
      st.2.val ≤ ws.length ∧
      st.1.val.length = bs.length ∧
      ((off.val, bs) ∈ ws.take st.2.val → st.1.val = bs))
    (fun st => ws.length - st.2.val) ?_ _ ?_
  · rintro ⟨dst, w⟩ ⟨hw_le, hdst_len, himp⟩
    simp only at hw_le hdst_len himp
    by_cases hlt : w.val < ws.length
    · have ho_lt : w.val < mem.offs.val.length := by omega
      have hs_lt : w.val < mem.starts.val.length := by omega
      have hl_lt : w.val < mem.lens.val.length := by omega
      have hw_max : w.val + 1 ≤ Usize.max := by have := mem.offs.property; omega
      obtain ⟨hk_off, hk_len, hk_st, hk_dt⟩ := hkP w.val hlt
      rw [List.getD_eq_getElem _ _ ho_lt] at hk_off
      rw [List.getD_eq_getElem _ _ hl_lt] at hk_len
      rw [List.getD_eq_getElem _ _ hs_lt] at hk_st hk_dt
      have hwk_mem : ws.getD w.val (0, []) ∈ ws := getD_mem_of_lt hlt
      obtain ⟨hwk0, hwk1⟩ := hwB _ hwk_mem
      have hcast_n : (UScalar.hcast .I64 (mem.lens.val[w.val]'hl_lt)).val =
          ((ws.getD w.val (0, [])).2.length : Int) := by
        rw [hcast_i64_of_le _ (by omega), hk_len]
      have he1_bnd : -9223372036854775808 ≤
            (mem.offs.val[w.val]'ho_lt).val + (UScalar.hcast .I64 (mem.lens.val[w.val]'hl_lt)).val ∧
          (mem.offs.val[w.val]'ho_lt).val + (UScalar.hcast .I64 (mem.lens.val[w.val]'hl_lt)).val ≤
            9223372036854775807 := by omega
      have he2_bnd : -9223372036854775808 ≤ off.val + dl.val ∧
          off.val + dl.val ≤ 9223372036854775807 := by omega
      rcases hdisj_or_eq _ hwk_mem with hdisj | heq_wk
      · aeneas_wp [rust_loop_body, ho_lt, hs_lt, hl_lt, hw_max, he1_bnd, he2_bnd]
        split_ifs with h1 h2
        all_goals
          rw [mem_get_loop1_loop0_disjoint _ _ _ _ _ _ _ (by simp only [IScalar.ofInt_val_eq]; omega)]
          aeneas_wp [hw_max]
          simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
          refine ⟨⟨by omega, hdst_len, ?_⟩, by omega⟩
          intro hmem_next
          rw [take_succ_of_lt hlt, List.mem_append, List.mem_singleton] at hmem_next
          rcases hmem_next with hmem_prev | h_eq
          · exact himp hmem_prev
          · have hgetD : ws.getD w.val (0, []) = ws[w.val]'hlt :=
              List.getD_eq_getElem _ (0, []) hlt
            rw [← hgetD] at h_eq
            have h1_eq : off.val = (ws.getD w.val (0, [])).1 := congrArg Prod.fst h_eq
            have h2_eq : bs = (ws.getD w.val (0, [])).2 := congrArg Prod.snd h_eq
            subst h2_eq
            omega
      · have ho_eq : mem.offs.val[w.val]'ho_lt = off := by
          apply IScalar.eq_of_val_eq
          rw [hk_off, heq_wk]
        have hnot_gt : ¬ (off.val < (mem.offs.val[w.val]'ho_lt).val) := by
          rw [ho_eq]; exact Int.lt_irrefl _
        have hnot_e : ¬ ((mem.offs.val[w.val]'ho_lt).val +
            (UScalar.hcast .I64 (mem.lens.val[w.val]'hl_lt)).val < off.val + dl.val) := by
          rw [ho_eq, hcast_n, heq_wk, hdl]; exact Int.lt_irrefl _
        set e2 : Std.I64 := IScalar.ofIntCore (off.val + dl.val)
          ⟨by simp [IScalarTy.I64_numBits_eq]; omega,
           by simp [IScalarTy.I64_numBits_eq]; omega⟩
        have hst_bs : (mem.starts.val[w.val]'hs_lt).val + bs.length ≤ mem.bytes.val.length := by
          rw [heq_wk] at hk_st; exact hk_st
        have hdt_bs : (mem.bytes.val.drop (mem.starts.val[w.val]'hs_lt).val).take bs.length = bs := by
          rw [heq_wk] at hk_dt; exact hk_dt
        obtain ⟨dst', hloop0, hdst'_val⟩ := mem_get_loop1_loop0_exact mem.bytes off dst
          (mem.starts.val[w.val]'hs_lt) e2 bs hoff0 hoff1 hdst_len
          (by simp [e2, IScalar.ofInt_val_eq, hdl]) hst_bs hdt_bs
        aeneas_wp [rust_loop_body, ho_lt, hs_lt, hl_lt, hw_max, he1_bnd, he2_bnd, hnot_gt, hnot_e]
        rw [ho_eq, hloop0]
        aeneas_wp [hw_max]
        simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
        refine ⟨⟨by omega, by rw [hdst'_val], fun _ => hdst'_val⟩, by omega⟩
    · have hlt' : ¬ w.val < mem.offs.val.length := by omega
      aeneas_wp [rust_loop_body, hlt']
      simp only [loopCls_done]
      have hweq : w.val = ws.length := by omega
      rw [hweq, List.take_length] at himp
      exact ⟨dst, rfl, himp hmem_ws⟩
  · simp [hdst1]

theorem mem_get_spec (mem : cbstm03a.Mem) (ws : List (Int × List U8))
    (off : Std.I64) (dst : Slice Std.U8) (bs : List U8)
    (hwf : MemWF mem ws)
    (hhas : HasWrite ws off.val bs)
    (hbs_pos : 0 < bs.length)
    (hdst : dst.val.length = bs.length) :
    ∃ s', cbstm03a.mem_get mem off dst = .ok s' ∧ s'.val = bs := by
  obtain ⟨hoff0, hoff1⟩ := hwf.2.2.2.2.1 (off.val, bs) hhas.1
  simp only at hoff0 hoff1
  obtain ⟨dst1, hloop0, hdst1_len⟩ := mem_get_loop0_spec off dst hoff0 (by omega)
  have hcast_dl : (UScalar.hcast .I64 (Slice.len dst)).val = (bs.length : Int) := by
    rw [hcast_i64_of_le _ (by simp; omega), Slice.len_val]
    exact_mod_cast hdst
  obtain ⟨dst', hloop1, hdst'_val⟩ := mem_get_loop1_spec mem ws off dst1
    (UScalar.hcast .I64 (Slice.len dst)) bs hwf hhas hbs_pos (by omega) hcast_dl
  refine exists_ok_of_wp ?_
  unfold cbstm03a.mem_get
  aeneas_wp [hloop0, hloop1]
  exact ⟨dst', rfl, hdst'_val⟩

/-! ## 2. Offset helpers and `write_trct` / `read_trct` -/

theorem card_off_spec (c : Std.I64) (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 50) :
    ∃ off : Std.I64, cbstm03a.card_off c = .ok off ∧ off.val = (c.val - 1) * 3356 := by
  have hcsz : cbstm03a.CARD_SZ.val = 3356 := by simp [cbstm03a.CARD_SZ]
  have hsub : -9223372036854775808 ≤ c.val - 1 ∧ c.val - 1 ≤ 9223372036854775807 := by omega
  have hmul : -9223372036854775808 ≤ (c.val - 1) * cbstm03a.CARD_SZ.val ∧
      (c.val - 1) * cbstm03a.CARD_SZ.val ≤ 9223372036854775807 := by rw [hcsz]; omega
  refine exists_ok_of_wp ?_
  unfold cbstm03a.card_off
  aeneas_wp [hsub, hmul]
  exact ⟨_, rfl, by simp [IScalar.ofInt_val_eq, hcsz]⟩

theorem tran_off_spec (c t : Std.I64) (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 50)
    (ht1 : 1 ≤ t.val) (ht2 : t.val ≤ 10) :
    ∃ off : Std.I64, cbstm03a.tran_off c t = .ok off ∧
      off.val = (c.val - 1) * 3356 + 16 + (t.val - 1) * 334 := by
  have hcsz : cbstm03a.CARD_SZ.val = 3356 := by simp [cbstm03a.CARD_SZ]
  have htsz : cbstm03a.TRAN_SZ.val = 334 := by simp [cbstm03a.TRAN_SZ]
  have hb1 : -9223372036854775808 ≤ c.val - 1 ∧ c.val - 1 ≤ 9223372036854775807 := by omega
  have hb2 : -9223372036854775808 ≤ (c.val - 1) * cbstm03a.CARD_SZ.val ∧
      (c.val - 1) * cbstm03a.CARD_SZ.val ≤ 9223372036854775807 := by rw [hcsz]; omega
  have hb3 : -9223372036854775808 ≤ (c.val - 1) * cbstm03a.CARD_SZ.val + 16 ∧
      (c.val - 1) * cbstm03a.CARD_SZ.val + 16 ≤ 9223372036854775807 := by rw [hcsz]; omega
  have hb4 : -9223372036854775808 ≤ t.val - 1 ∧ t.val - 1 ≤ 9223372036854775807 := by omega
  have hb5 : -9223372036854775808 ≤ (t.val - 1) * cbstm03a.TRAN_SZ.val ∧
      (t.val - 1) * cbstm03a.TRAN_SZ.val ≤ 9223372036854775807 := by rw [htsz]; omega
  have hb6 : -9223372036854775808 ≤
        (c.val - 1) * cbstm03a.CARD_SZ.val + 16 + (t.val - 1) * cbstm03a.TRAN_SZ.val ∧
      (c.val - 1) * cbstm03a.CARD_SZ.val + 16 + (t.val - 1) * cbstm03a.TRAN_SZ.val ≤
        9223372036854775807 := by rw [hcsz, htsz]; omega
  refine exists_ok_of_wp ?_
  unfold cbstm03a.tran_off
  aeneas_wp [hb1, hb2, hb3, hb4, hb5, hb6]
  exact ⟨_, rfl, by simp [IScalar.ofInt_val_eq, hcsz, htsz]⟩

theorem trct_off_spec (c : Std.I64) (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 50) :
    ∃ off : Std.I64, cbstm03a.trct_off c = .ok off ∧ off.val = 171160 + (c.val - 1) * 2 := by
  have hbase : cbstm03a.CNTR_BASE.val = 171160 := by simp [cbstm03a.CNTR_BASE]
  have hb1 : -9223372036854775808 ≤ c.val - 1 ∧ c.val - 1 ≤ 9223372036854775807 := by omega
  have hb2 : -9223372036854775808 ≤ (c.val - 1) * 2 ∧ (c.val - 1) * 2 ≤ 9223372036854775807 := by omega
  have hb3 : -9223372036854775808 ≤ cbstm03a.CNTR_BASE.val + (c.val - 1) * 2 ∧
      cbstm03a.CNTR_BASE.val + (c.val - 1) * 2 ≤ 9223372036854775807 := by rw [hbase]; omega
  refine exists_ok_of_wp ?_
  unfold cbstm03a.trct_off
  aeneas_wp [hb1, hb2, hb3]
  exact ⟨_, rfl, by simp [IScalar.ofInt_val_eq, hbase]⟩

/-- The 2-byte big-endian representation of a transaction count `n ≤ 10`. -/
def trctBytes (n : Nat) : List U8 := [0#u8, byteOf n]

@[simp] theorem length_trctBytes (n : Nat) : (trctBytes n).length = 2 := rfl

theorem write_trct_bytes (v : Std.I64) (hv0 : 0 ≤ v.val) (hv1 : v.val ≤ 10) :
    ∃ i : Std.I64, ((v &&& 65535#i64) >>> 8#i32) = .ok i ∧
      IScalar.hcast .U8 (i &&& 255#i64) = 0#u8 ∧
      IScalar.hcast .U8 ((v &&& 65535#i64) &&& 255#i64) = byteOf v.val.toNat := by
  have h : v.val.toNat = 0 ∨ v.val.toNat = 1 ∨ v.val.toNat = 2 ∨ v.val.toNat = 3 ∨
      v.val.toNat = 4 ∨ v.val.toNat = 5 ∨ v.val.toNat = 6 ∨ v.val.toNat = 7 ∨
      v.val.toNat = 8 ∨ v.val.toNat = 9 ∨ v.val.toNat = 10 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · have hv : v = 0#i64 := IScalar.eq_of_val_eq (by simp; omega)
    subst hv; exact ⟨0#i64, rfl, by decide +kernel, by decide +kernel⟩
  · have hv : v = 1#i64 := IScalar.eq_of_val_eq (by simp; omega)
    subst hv; exact ⟨0#i64, rfl, by decide +kernel, by decide +kernel⟩
  · have hv : v = 2#i64 := IScalar.eq_of_val_eq (by simp; omega)
    subst hv; exact ⟨0#i64, rfl, by decide +kernel, by decide +kernel⟩
  · have hv : v = 3#i64 := IScalar.eq_of_val_eq (by simp; omega)
    subst hv; exact ⟨0#i64, rfl, by decide +kernel, by decide +kernel⟩
  · have hv : v = 4#i64 := IScalar.eq_of_val_eq (by simp; omega)
    subst hv; exact ⟨0#i64, rfl, by decide +kernel, by decide +kernel⟩
  · have hv : v = 5#i64 := IScalar.eq_of_val_eq (by simp; omega)
    subst hv; exact ⟨0#i64, rfl, by decide +kernel, by decide +kernel⟩
  · have hv : v = 6#i64 := IScalar.eq_of_val_eq (by simp; omega)
    subst hv; exact ⟨0#i64, rfl, by decide +kernel, by decide +kernel⟩
  · have hv : v = 7#i64 := IScalar.eq_of_val_eq (by simp; omega)
    subst hv; exact ⟨0#i64, rfl, by decide +kernel, by decide +kernel⟩
  · have hv : v = 8#i64 := IScalar.eq_of_val_eq (by simp; omega)
    subst hv; exact ⟨0#i64, rfl, by decide +kernel, by decide +kernel⟩
  · have hv : v = 9#i64 := IScalar.eq_of_val_eq (by simp; omega)
    subst hv; exact ⟨0#i64, rfl, by decide +kernel, by decide +kernel⟩
  · have hv : v = 10#i64 := IScalar.eq_of_val_eq (by simp; omega)
    subst hv; exact ⟨0#i64, rfl, by decide +kernel, by decide +kernel⟩

theorem write_trct_spec (mem : cbstm03a.Mem) (ws : List (Int × List U8))
    (c v : Std.I64)
    (hwf : MemWF mem ws)
    (hlen1 : ws.length < Usize.max)
    (hlen2 : wsBytesLen ws + 2 ≤ Usize.max)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 50)
    (hv0 : 0 ≤ v.val) (hv1 : v.val ≤ 10) :
    ∃ mem', cbstm03a.write_trct mem c v = .ok mem' ∧
      MemWF mem' (ws ++ [(171160 + (c.val - 1) * 2, trctBytes v.val.toNat)]) := by
  obtain ⟨i, hshr, hb0, hb1⟩ := write_trct_bytes v hv0 hv1
  obtain ⟨off, hoff_eq, hoff_val⟩ := trct_off_spec c hc1 hc2
  set s := Array.to_slice (Array.make 2#usize
    [IScalar.hcast .U8 (i &&& 255#i64), IScalar.hcast .U8 ((v &&& 65535#i64) &&& 255#i64)])
  have hs_val : s.val = trctBytes v.val.toNat := by
    simp [s, hb0, hb1, trctBytes]
  obtain ⟨mem', hmw, hwf'⟩ := mem_write_spec mem ws off s hwf hlen1
    (by rw [hs_val]; exact hlen2) (by omega) (by rw [hs_val]; simp; omega)
  refine ⟨mem', ?_, ?_⟩
  · unfold cbstm03a.write_trct
    simp only [lift, bind_ok, hshr, hoff_eq]
    exact hmw
  · rwa [hoff_val, hs_val] at hwf'

theorem read_trct_spec (mem : cbstm03a.Mem) (ws : List (Int × List U8))
    (c : Std.I64) (n : Nat)
    (hwf : MemWF mem ws)
    (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ 50)
    (hn : n ≤ 10)
    (hhas : HasWrite ws (171160 + (c.val - 1) * 2) (trctBytes n)) :
    ∃ cnt : Std.I64, cbstm03a.read_trct mem c = .ok cnt ∧ cnt.val = (n : Int) := by
  obtain ⟨off, hoff_eq, hoff_val⟩ := trct_off_spec c hc1 hc2
  let b := Array.repeat 2#usize 0#u8
  let s := Array.to_slice b
  have hs_len : s.val.length = 2 := by
    simp [s, b, Array.to_slice, Array.repeat_val]
  have hhas' : HasWrite ws off.val (trctBytes n) := by rwa [hoff_val]
  obtain ⟨s1, hmg, hs1_val⟩ := mem_get_spec mem ws off s (trctBytes n) hwf hhas'
    (by simp [trctBytes]) hs_len
  let b1 := Array.from_slice b s1
  have hb1_val : b1.val = [0#u8, byteOf n] := by
    simp [b1, Array.from_slice, hs1_val, trctBytes]
  have hi0 : Array.index_usize b1 0#usize = .ok 0#u8 := by
    rw [array_index_usize_eq, dite_eq_left (by simp [hb1_val])]
    simp [hb1_val]
  have hi1 : Array.index_usize b1 1#usize = .ok (byteOf n) := by
    rw [array_index_usize_eq, dite_eq_left (by simp [hb1_val])]
    simp [hb1_val]
  dsimp only [s, b] at hmg
  dsimp only [b1, b] at hi0 hi1
  have h1 : (0#u8).val = 0 := rfl
  have h2 : (byteOf n).val = n := byteOf_val n (by omega)
  refine exists_ok_of_wp ?_
  unfold cbstm03a.read_trct
  aeneas_wp [Array.to_slice_mut, hoff_eq, hmg, hi0, hi1, h1, h2]
  split_ifs <;> try omega
  exact ⟨_, rfl, by simp [IScalar.ofInt_val_eq]⟩

/-! ## 3. Group invariants and `TableWrites` -/

/-- Well-formedness of a group list `gs` produced by `grp`. -/
def GroupsWF (gs : List (List (List UInt8))) : Prop :=
  gs.length ≤ 50 ∧
  ∀ g ∈ gs, 1 ≤ g.length ∧ g.length ≤ 10 ∧ ∀ r ∈ g, r.length = 350

theorem getLastD_mem_of_ne_nil {α : Type _} {l : List α} (d : α) (h : l ≠ []) :
    l.getLastD d ∈ l := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]
  exact List.getLast_mem h

theorem length_tCard_of_eq {r : List UInt8} (hr : r.length = 350) :
    (tCard r).length = 16 := by
  simp [tCard, hr]

theorem length_tId_of_eq {r : List UInt8} (hr : r.length = 350) :
    (tId r).length = 16 := by
  simp [tId, hr]

theorem length_tRest_of_eq {r : List UInt8} (hr : r.length = 350) :
    (tRest r).length = 318 := by
  simp [tRest, hr]

theorem length_gCard_of_wf {gs : List (List (List UInt8))} (hgs : GroupsWF gs)
    {k : Nat} (hk1 : 1 ≤ k) (hk2 : k ≤ gs.length) :
    (gCard (gs.getD (k - 1) [])).length = 16 := by
  have hmem : gs.getD (k - 1) [] ∈ gs := getD_mem_of_lt (by omega)
  obtain ⟨hg1, _, hgr⟩ := hgs.2 _ hmem
  have hne : gs.getD (k - 1) [] ≠ [] := by
    intro h; rw [h] at hg1; simp at hg1
  have hlast_mem : (gs.getD (k - 1) []).getLastD [] ∈ gs.getD (k - 1) [] :=
    getLastD_mem_of_ne_nil [] hne
  exact length_tCard_of_eq (hgr _ hlast_mem)

theorem length_tId_of_wf {gs : List (List (List UInt8))} (hgs : GroupsWF gs)
    {k j : Nat} (hk1 : 1 ≤ k) (hk2 : k ≤ gs.length)
    (hj1 : 1 ≤ j) (hj2 : j ≤ (gs.getD (k - 1) []).length) :
    (tId ((gs.getD (k - 1) []).getD (j - 1) [])).length = 16 := by
  have hmem : gs.getD (k - 1) [] ∈ gs := getD_mem_of_lt (by omega)
  obtain ⟨_, _, hgr⟩ := hgs.2 _ hmem
  have hrmem : (gs.getD (k - 1) []).getD (j - 1) [] ∈ gs.getD (k - 1) [] :=
    getD_mem_of_lt (by omega)
  exact length_tId_of_eq (hgr _ hrmem)

theorem length_tRest_of_wf {gs : List (List (List UInt8))} (hgs : GroupsWF gs)
    {k j : Nat} (hk1 : 1 ≤ k) (hk2 : k ≤ gs.length)
    (hj1 : 1 ≤ j) (hj2 : j ≤ (gs.getD (k - 1) []).length) :
    (tRest ((gs.getD (k - 1) []).getD (j - 1) [])).length = 318 := by
  have hmem : gs.getD (k - 1) [] ∈ gs := getD_mem_of_lt (by omega)
  obtain ⟨_, _, hgr⟩ := hgs.2 _ hmem
  have hrmem : (gs.getD (k - 1) []).getD (j - 1) [] ∈ gs.getD (k - 1) [] :=
    getD_mem_of_lt (by omega)
  exact length_tRest_of_eq (hgr _ hrmem)

/-- A write `w` is one of the card, transaction ID, transaction rest, or counter writes of `gs`. -/
def WriteValid (gs : List (List (List UInt8))) (nTrct : Nat) (w : Int × List U8) : Prop :=
  (∃ k, 1 ≤ k ∧ k ≤ gs.length ∧
    w = (((k : Int) - 1) * 3356, latL (gCard (gs.getD (k - 1) [])))) ∨
  (∃ k j, 1 ≤ k ∧ k ≤ gs.length ∧ 1 ≤ j ∧ j ≤ (gs.getD (k - 1) []).length ∧
    w = (((k : Int) - 1) * 3356 + 16 + ((j : Int) - 1) * 334,
      latL (tId ((gs.getD (k - 1) []).getD (j - 1) [])))) ∨
  (∃ k j, 1 ≤ k ∧ k ≤ gs.length ∧ 1 ≤ j ∧ j ≤ (gs.getD (k - 1) []).length ∧
    w = (((k : Int) - 1) * 3356 + 16 + ((j : Int) - 1) * 334 + 16,
      latL (tRest ((gs.getD (k - 1) []).getD (j - 1) [])))) ∨
  (∃ k, 1 ≤ k ∧ k ≤ nTrct ∧
    w = (171160 + ((k : Int) - 1) * 2, trctBytes (gs.getD (k - 1) []).length))

/-- Every valid write is either disjoint from or equal to a given card slot. -/
theorem writeValid_disj_card {gs : List (List (List UInt8))} {nTrct : Nat} {w : Int × List U8}
    (hgs : GroupsWF gs) (hnt : nTrct ≤ gs.length) (hw : WriteValid gs nTrct w)
    {c : Nat} (hc1 : 1 ≤ c) (hc2 : c ≤ gs.length) :
    let off := ((c : Int) - 1) * 3356
    let bs := latL (gCard (gs.getD (c - 1) []))
    (w.1 + (w.2.length : Int) ≤ off ∨ off + (bs.length : Int) ≤ w.1) ∨ w = (off, bs) := by
  have hgsl : gs.length ≤ 50 := hgs.1
  have hbs_len : (latL (gCard (gs.getD (c - 1) []))).length = 16 := by
    rw [length_latL, length_gCard_of_wf hgs hc1 hc2]
  dsimp only
  rw [hbs_len]
  rcases hw with ⟨k, hk1, hk2, rfl⟩ | ⟨k, j, hk1, hk2, hj1, hj2, rfl⟩ |
      ⟨k, j, hk1, hk2, hj1, hj2, rfl⟩ | ⟨k, hk1, hk2, rfl⟩
  · by_cases hkc : k = c
    · subst hkc; exact Or.inr rfl
    · left
      have hlen : (latL (gCard (gs.getD (k - 1) []))).length = 16 := by
        rw [length_latL, length_gCard_of_wf hgs hk1 hk2]
      simp only [hlen]; omega
  · left
    have hmem : gs.getD (k - 1) [] ∈ gs := getD_mem_of_lt (by omega)
    have hgl : (gs.getD (k - 1) []).length ≤ 10 := (hgs.2 _ hmem).2.1
    have hlen : (latL (tId ((gs.getD (k - 1) []).getD (j - 1) []))).length = 16 := by
      rw [length_latL, length_tId_of_wf hgs hk1 hk2 hj1 hj2]
    simp only [hlen]
    rcases Nat.lt_trichotomy k c with _ | rfl | _ <;> omega
  · left
    have hmem : gs.getD (k - 1) [] ∈ gs := getD_mem_of_lt (by omega)
    have hgl : (gs.getD (k - 1) []).length ≤ 10 := (hgs.2 _ hmem).2.1
    have hlen : (latL (tRest ((gs.getD (k - 1) []).getD (j - 1) []))).length = 318 := by
      rw [length_latL, length_tRest_of_wf hgs hk1 hk2 hj1 hj2]
    simp only [hlen]
    rcases Nat.lt_trichotomy k c with _ | rfl | _ <;> omega
  · left
    simp only [length_trctBytes]; omega

/-- Every valid write is either disjoint from or equal to a given transaction-id slot. -/
theorem writeValid_disj_tId {gs : List (List (List UInt8))} {nTrct : Nat} {w : Int × List U8}
    (hgs : GroupsWF gs) (hnt : nTrct ≤ gs.length) (hw : WriteValid gs nTrct w)
    {c t : Nat} (hc1 : 1 ≤ c) (hc2 : c ≤ gs.length)
    (ht1 : 1 ≤ t) (ht2 : t ≤ (gs.getD (c - 1) []).length) :
    let off := ((c : Int) - 1) * 3356 + 16 + ((t : Int) - 1) * 334
    let bs := latL (tId ((gs.getD (c - 1) []).getD (t - 1) []))
    (w.1 + (w.2.length : Int) ≤ off ∨ off + (bs.length : Int) ≤ w.1) ∨ w = (off, bs) := by
  have hgsl : gs.length ≤ 50 := hgs.1
  have hcmem : gs.getD (c - 1) [] ∈ gs := getD_mem_of_lt (by omega)
  have hcgl : (gs.getD (c - 1) []).length ≤ 10 := (hgs.2 _ hcmem).2.1
  have hbs_len : (latL (tId ((gs.getD (c - 1) []).getD (t - 1) []))).length = 16 := by
    rw [length_latL, length_tId_of_wf hgs hc1 hc2 ht1 ht2]
  dsimp only
  rw [hbs_len]
  rcases hw with ⟨k, hk1, hk2, rfl⟩ | ⟨k, j, hk1, hk2, hj1, hj2, rfl⟩ |
      ⟨k, j, hk1, hk2, hj1, hj2, rfl⟩ | ⟨k, hk1, hk2, rfl⟩
  · left
    have hlen : (latL (gCard (gs.getD (k - 1) []))).length = 16 := by
      rw [length_latL, length_gCard_of_wf hgs hk1 hk2]
    simp only [hlen]
    rcases Nat.lt_trichotomy k c with _ | rfl | _ <;> omega
  · by_cases hkc : k = c ∧ j = t
    · obtain ⟨rfl, rfl⟩ := hkc; exact Or.inr rfl
    · left
      have hmem : gs.getD (k - 1) [] ∈ gs := getD_mem_of_lt (by omega)
      have hgl : (gs.getD (k - 1) []).length ≤ 10 := (hgs.2 _ hmem).2.1
      have hlen : (latL (tId ((gs.getD (k - 1) []).getD (j - 1) []))).length = 16 := by
        rw [length_latL, length_tId_of_wf hgs hk1 hk2 hj1 hj2]
      simp only [hlen]
      rcases Nat.lt_trichotomy k c with _ | rfl | _ <;> omega
  · left
    have hmem : gs.getD (k - 1) [] ∈ gs := getD_mem_of_lt (by omega)
    have hgl : (gs.getD (k - 1) []).length ≤ 10 := (hgs.2 _ hmem).2.1
    have hlen : (latL (tRest ((gs.getD (k - 1) []).getD (j - 1) []))).length = 318 := by
      rw [length_latL, length_tRest_of_wf hgs hk1 hk2 hj1 hj2]
    simp only [hlen]
    rcases Nat.lt_trichotomy k c with _ | rfl | _ <;>
      rcases Nat.lt_trichotomy j t with _ | rfl | _ <;> omega
  · left
    simp only [length_trctBytes]; omega

/-- Every valid write is either disjoint from or equal to a given transaction-rest slot. -/
theorem writeValid_disj_tRest {gs : List (List (List UInt8))} {nTrct : Nat} {w : Int × List U8}
    (hgs : GroupsWF gs) (hnt : nTrct ≤ gs.length) (hw : WriteValid gs nTrct w)
    {c t : Nat} (hc1 : 1 ≤ c) (hc2 : c ≤ gs.length)
    (ht1 : 1 ≤ t) (ht2 : t ≤ (gs.getD (c - 1) []).length) :
    let off := ((c : Int) - 1) * 3356 + 16 + ((t : Int) - 1) * 334 + 16
    let bs := latL (tRest ((gs.getD (c - 1) []).getD (t - 1) []))
    (w.1 + (w.2.length : Int) ≤ off ∨ off + (bs.length : Int) ≤ w.1) ∨ w = (off, bs) := by
  have hgsl : gs.length ≤ 50 := hgs.1
  have hcmem : gs.getD (c - 1) [] ∈ gs := getD_mem_of_lt (by omega)
  have hcgl : (gs.getD (c - 1) []).length ≤ 10 := (hgs.2 _ hcmem).2.1
  have hbs_len : (latL (tRest ((gs.getD (c - 1) []).getD (t - 1) []))).length = 318 := by
    rw [length_latL, length_tRest_of_wf hgs hc1 hc2 ht1 ht2]
  dsimp only
  rw [hbs_len]
  rcases hw with ⟨k, hk1, hk2, rfl⟩ | ⟨k, j, hk1, hk2, hj1, hj2, rfl⟩ |
      ⟨k, j, hk1, hk2, hj1, hj2, rfl⟩ | ⟨k, hk1, hk2, rfl⟩
  · left
    have hlen : (latL (gCard (gs.getD (k - 1) []))).length = 16 := by
      rw [length_latL, length_gCard_of_wf hgs hk1 hk2]
    simp only [hlen]
    rcases Nat.lt_trichotomy k c with _ | rfl | _ <;> omega
  · left
    have hmem : gs.getD (k - 1) [] ∈ gs := getD_mem_of_lt (by omega)
    have hgl : (gs.getD (k - 1) []).length ≤ 10 := (hgs.2 _ hmem).2.1
    have hlen : (latL (tId ((gs.getD (k - 1) []).getD (j - 1) []))).length = 16 := by
      rw [length_latL, length_tId_of_wf hgs hk1 hk2 hj1 hj2]
    simp only [hlen]
    rcases Nat.lt_trichotomy k c with _ | rfl | _ <;>
      rcases Nat.lt_trichotomy j t with _ | rfl | _ <;> omega
  · by_cases hkc : k = c ∧ j = t
    · obtain ⟨rfl, rfl⟩ := hkc; exact Or.inr rfl
    · left
      have hmem : gs.getD (k - 1) [] ∈ gs := getD_mem_of_lt (by omega)
      have hgl : (gs.getD (k - 1) []).length ≤ 10 := (hgs.2 _ hmem).2.1
      have hlen : (latL (tRest ((gs.getD (k - 1) []).getD (j - 1) []))).length = 318 := by
        rw [length_latL, length_tRest_of_wf hgs hk1 hk2 hj1 hj2]
      simp only [hlen]
      rcases Nat.lt_trichotomy k c with _ | rfl | _ <;> omega
  · left
    simp only [length_trctBytes]; omega

/-- Every valid write is either disjoint from or equal to a given transaction-count slot. -/
theorem writeValid_disj_trct {gs : List (List (List UInt8))} {nTrct : Nat} {w : Int × List U8}
    (hgs : GroupsWF gs) (hnt : nTrct ≤ gs.length) (hw : WriteValid gs nTrct w)
    {c : Nat} (hc1 : 1 ≤ c) (hc2 : c ≤ nTrct) :
    let off := 171160 + ((c : Int) - 1) * 2
    let bs := trctBytes (gs.getD (c - 1) []).length
    (w.1 + (w.2.length : Int) ≤ off ∨ off + (bs.length : Int) ≤ w.1) ∨ w = (off, bs) := by
  have hgsl : gs.length ≤ 50 := hgs.1
  dsimp only
  rw [length_trctBytes]
  rcases hw with ⟨k, hk1, hk2, rfl⟩ | ⟨k, j, hk1, hk2, hj1, hj2, rfl⟩ |
      ⟨k, j, hk1, hk2, hj1, hj2, rfl⟩ | ⟨k, hk1, hk2, rfl⟩
  · left
    have hlen : (latL (gCard (gs.getD (k - 1) []))).length = 16 := by
      rw [length_latL, length_gCard_of_wf hgs hk1 hk2]
    simp only [hlen]; omega
  · left
    have hmem : gs.getD (k - 1) [] ∈ gs := getD_mem_of_lt (by omega)
    have hgl : (gs.getD (k - 1) []).length ≤ 10 := (hgs.2 _ hmem).2.1
    have hlen : (latL (tId ((gs.getD (k - 1) []).getD (j - 1) []))).length = 16 := by
      rw [length_latL, length_tId_of_wf hgs hk1 hk2 hj1 hj2]
    simp only [hlen]; omega
  · left
    have hmem : gs.getD (k - 1) [] ∈ gs := getD_mem_of_lt (by omega)
    have hgl : (gs.getD (k - 1) []).length ≤ 10 := (hgs.2 _ hmem).2.1
    have hlen : (latL (tRest ((gs.getD (k - 1) []).getD (j - 1) []))).length = 318 := by
      rw [length_latL, length_tRest_of_wf hgs hk1 hk2 hj1 hj2]
    simp only [hlen]; omega
  · by_cases hkc : k = c
    · subst hkc; exact Or.inr rfl
    · left; simp only [length_trctBytes]; omega

/-- Complete write-list invariant for `gs` with `nTrct` group counts written. -/
def TableWrites (ws : List (Int × List U8)) (gs : List (List (List UInt8))) (nTrct : Nat) : Prop :=
  GroupsWF gs ∧
  nTrct ≤ gs.length ∧
  (∀ w ∈ ws, WriteValid gs nTrct w) ∧
  (∀ k, 1 ≤ k → k ≤ gs.length →
    (((k : Int) - 1) * 3356, latL (gCard (gs.getD (k - 1) []))) ∈ ws ∧
    ∀ j, 1 ≤ j → j ≤ (gs.getD (k - 1) []).length →
      (((k : Int) - 1) * 3356 + 16 + ((j : Int) - 1) * 334,
        latL (tId ((gs.getD (k - 1) []).getD (j - 1) []))) ∈ ws ∧
      (((k : Int) - 1) * 3356 + 16 + ((j : Int) - 1) * 334 + 16,
        latL (tRest ((gs.getD (k - 1) []).getD (j - 1) []))) ∈ ws) ∧
  (∀ k, 1 ≤ k → k ≤ nTrct →
    (171160 + ((k : Int) - 1) * 2, trctBytes (gs.getD (k - 1) []).length) ∈ ws)

theorem tableWrites_nil : TableWrites [] [] 0 := by
  refine ⟨⟨by decide, fun g hg => by simp at hg⟩, by decide,
    fun w hw => by simp at hw,
    fun k hk1 hk2 => by simp at hk2; omega,
    fun k hk1 hk2 => by omega⟩

theorem tableWrites_hasWrite_card {ws : List (Int × List U8)} {gs : List (List (List UInt8))}
    {nTrct c : Nat} (htw : TableWrites ws gs nTrct) (hc1 : 1 ≤ c) (hc2 : c ≤ gs.length) :
    HasWrite ws (((c : Int) - 1) * 3356) (latL (gCard (gs.getD (c - 1) []))) :=
  ⟨(htw.2.2.2.1 c hc1 hc2).1, fun _ hw => writeValid_disj_card htw.1 htw.2.1 (htw.2.2.1 _ hw) hc1 hc2⟩

theorem tableWrites_hasWrite_tId {ws : List (Int × List U8)} {gs : List (List (List UInt8))}
    {nTrct c t : Nat} (htw : TableWrites ws gs nTrct) (hc1 : 1 ≤ c) (hc2 : c ≤ gs.length)
    (ht1 : 1 ≤ t) (ht2 : t ≤ (gs.getD (c - 1) []).length) :
    HasWrite ws (((c : Int) - 1) * 3356 + 16 + ((t : Int) - 1) * 334)
      (latL (tId ((gs.getD (c - 1) []).getD (t - 1) []))) :=
  ⟨((htw.2.2.2.1 c hc1 hc2).2 t ht1 ht2).1,
   fun _ hw => writeValid_disj_tId htw.1 htw.2.1 (htw.2.2.1 _ hw) hc1 hc2 ht1 ht2⟩

theorem tableWrites_hasWrite_tRest {ws : List (Int × List U8)} {gs : List (List (List UInt8))}
    {nTrct c t : Nat} (htw : TableWrites ws gs nTrct) (hc1 : 1 ≤ c) (hc2 : c ≤ gs.length)
    (ht1 : 1 ≤ t) (ht2 : t ≤ (gs.getD (c - 1) []).length) :
    HasWrite ws (((c : Int) - 1) * 3356 + 16 + ((t : Int) - 1) * 334 + 16)
      (latL (tRest ((gs.getD (c - 1) []).getD (t - 1) []))) :=
  ⟨((htw.2.2.2.1 c hc1 hc2).2 t ht1 ht2).2,
   fun _ hw => writeValid_disj_tRest htw.1 htw.2.1 (htw.2.2.1 _ hw) hc1 hc2 ht1 ht2⟩

theorem tableWrites_hasWrite_trct {ws : List (Int × List U8)} {gs : List (List (List UInt8))}
    {nTrct c : Nat} (htw : TableWrites ws gs nTrct) (hc1 : 1 ≤ c) (hc2 : c ≤ nTrct) :
    HasWrite ws (171160 + ((c : Int) - 1) * 2) (trctBytes (gs.getD (c - 1) []).length) :=
  ⟨htw.2.2.2.2 c hc1 hc2, fun _ hw => writeValid_disj_trct htw.1 htw.2.1 (htw.2.2.1 _ hw) hc1 hc2⟩

/-- The three writes performed for record `cur` at card `c`, transaction `t`. -/
def recWrites (c t : Nat) (cur : List UInt8) : List (Int × List U8) :=
  [(((c : Int) - 1) * 3356, latL (tCard cur)),
   (((c : Int) - 1) * 3356 + 16 + ((t : Int) - 1) * 334, latL (tId cur)),
   (((c : Int) - 1) * 3356 + 16 + ((t : Int) - 1) * 334 + 16, latL (tRest cur))]

theorem tableWrites_first {cur : List UInt8} (hcur : cur.length = 350) :
    TableWrites (recWrites 1 1 cur) [[cur]] 0 := by
  have hgwf : GroupsWF [[cur]] := by
    refine ⟨by simp, fun g hg => ?_⟩
    simp only [List.mem_singleton] at hg; subst hg
    exact ⟨by simp, by simp, fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hcur⟩
  refine ⟨hgwf, by simp, ?_, ?_, fun k hk1 hk2 => by omega⟩
  · intro w hw
    simp only [recWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact Or.inl ⟨1, by decide, by simp, by simp [gCard]⟩
    · exact Or.inr (Or.inl ⟨1, 1, by decide, by simp, by decide, by simp, by simp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨1, 1, by decide, by simp, by decide, by simp, by simp⟩))
  · intro k hk1 hk2
    simp only [List.length_singleton] at hk2
    obtain rfl : k = 1 := by omega
    refine ⟨by simp [recWrites, gCard], fun j hj1 hj2 => ?_⟩
    simp only [Nat.sub_self, List.getD_cons_zero, List.length_singleton] at hj2 ⊢
    obtain rfl : j = 1 := by omega
    simp [recWrites]

theorem writeValid_mono_same {gs0 : List (List (List UInt8))} {g : List (List UInt8)}
    {cur : List UInt8} {w : Int × List U8}
    (hsame : gCard g = tCard cur)
    (hw : WriteValid (gs0 ++ [g]) gs0.length w) :
    WriteValid (gs0 ++ [g ++ [cur]]) gs0.length w := by
  have hgc : gCard (g ++ [cur]) = gCard g := by
    rw [gCard, getLastD_snoc, hsame]
  rcases hw with ⟨k, hk1, hk2, rfl⟩ | ⟨k, j, hk1, hk2, hj1, hj2, rfl⟩ |
      ⟨k, j, hk1, hk2, hj1, hj2, rfl⟩ | ⟨k, hk1, hk2, rfl⟩
  · left
    refine ⟨k, hk1, by simp at hk2 ⊢; exact hk2, ?_⟩
    by_cases hlt : k - 1 < gs0.length
    · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ hlt]
    · have hkeq : k - 1 = gs0.length := by simp at hk2; omega
      rw [hkeq, getD_snoc_eq, getD_snoc_eq, hgc]
  · right; left
    by_cases hlt : k - 1 < gs0.length
    · refine ⟨k, j, hk1, by simp at hk2 ⊢; exact hk2, hj1, ?_, ?_⟩
      · rw [getD_snoc_lt _ _ _ _ hlt] at hj2 ⊢; exact hj2
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ hlt]
    · have hkeq : k - 1 = gs0.length := by simp at hk2; omega
      rw [hkeq, getD_snoc_eq] at hj2
      have hjlt : j - 1 < g.length := by omega
      refine ⟨k, j, hk1, by simp at hk2 ⊢; exact hk2, hj1, ?_, ?_⟩
      · rw [hkeq, getD_snoc_eq, List.length_append, List.length_singleton]; omega
      · rw [hkeq, getD_snoc_eq, getD_snoc_eq, getD_snoc_lt _ _ _ _ hjlt]
  · right; right; left
    by_cases hlt : k - 1 < gs0.length
    · refine ⟨k, j, hk1, by simp at hk2 ⊢; exact hk2, hj1, ?_, ?_⟩
      · rw [getD_snoc_lt _ _ _ _ hlt] at hj2 ⊢; exact hj2
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ hlt]
    · have hkeq : k - 1 = gs0.length := by simp at hk2; omega
      rw [hkeq, getD_snoc_eq] at hj2
      have hjlt : j - 1 < g.length := by omega
      refine ⟨k, j, hk1, by simp at hk2 ⊢; exact hk2, hj1, ?_, ?_⟩
      · rw [hkeq, getD_snoc_eq, List.length_append, List.length_singleton]; omega
      · rw [hkeq, getD_snoc_eq, getD_snoc_eq, getD_snoc_lt _ _ _ _ hjlt]
  · right; right; right
    have hlt : k - 1 < gs0.length := by omega
    refine ⟨k, hk1, hk2, ?_⟩
    rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ hlt]

theorem tableWrites_same {ws : List (Int × List U8)} {gs0 : List (List (List UInt8))}
    {g : List (List UInt8)} {cur : List UInt8}
    (htw : TableWrites ws (gs0 ++ [g]) gs0.length)
    (hsame : gCard g = tCard cur)
    (hgl : g.length + 1 ≤ 10)
    (hcur : cur.length = 350) :
    TableWrites (ws ++ recWrites (gs0.length + 1) (g.length + 1) cur)
      (gs0 ++ [g ++ [cur]]) gs0.length := by
  obtain ⟨hgwf, hnt, hvalid, hpres, htrct⟩ := htw
  have hgc : gCard (g ++ [cur]) = tCard cur := by simp [gCard]
  have hgwf' : GroupsWF (gs0 ++ [g ++ [cur]]) := by
    refine ⟨by simpa using hgwf.1, fun x hx => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hgwf.2 x (by simp [hx])
    · obtain ⟨_, _, hgr⟩ := hgwf.2 g (by simp)
      refine ⟨by simp, by simpa using hgl, fun r hr => ?_⟩
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hgr r hr
      · exact hcur
  refine ⟨hgwf', by simp, ?_, ?_, ?_⟩
  · intro w hw
    simp only [List.mem_append] at hw
    rcases hw with hw | hw
    · exact writeValid_mono_same hsame (hvalid w hw)
    · simp only [recWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
      have hk1 : 1 ≤ gs0.length + 1 := by omega
      have hk2 : gs0.length + 1 ≤ (gs0 ++ [g ++ [cur]]).length := by simp
      have hj1 : 1 ≤ g.length + 1 := by omega
      have hj2 : g.length + 1 ≤ ((gs0 ++ [g ++ [cur]]).getD gs0.length []).length := by
        rw [getD_snoc_eq]; simp
      rcases hw with rfl | rfl | rfl
      · exact Or.inl ⟨gs0.length + 1, hk1, hk2, by rw [Nat.add_sub_cancel, getD_snoc_eq, hgc]⟩
      · exact Or.inr (Or.inl ⟨gs0.length + 1, g.length + 1, hk1, hk2, hj1,
          by simp,
          by simp only [Nat.add_sub_cancel]; rw [getD_snoc_eq, getD_snoc_eq]⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨gs0.length + 1, g.length + 1, hk1, hk2, hj1,
          by simp,
          by simp only [Nat.add_sub_cancel]; rw [getD_snoc_eq, getD_snoc_eq]⟩))
  · intro k hk1 hk2
    simp only [List.length_append, List.length_singleton] at hk2
    by_cases hlt : k - 1 < gs0.length
    · obtain ⟨hc, htr⟩ := hpres k hk1 (by simp; omega)
      rw [getD_snoc_lt _ _ _ _ hlt] at hc htr ⊢
      refine ⟨List.mem_append_left _ hc, fun j hj1 hj2 => ?_⟩
      obtain ⟨ht1, ht2⟩ := htr j hj1 hj2
      exact ⟨List.mem_append_left _ ht1, List.mem_append_left _ ht2⟩
    · have hkeq : k = gs0.length + 1 := by omega
      subst hkeq
      simp only [Nat.add_sub_cancel, getD_snoc_eq]
      refine ⟨?_, fun j hj1 hj2 => ?_⟩
      · rw [hgc]; exact List.mem_append_right _ (by simp [recWrites])
      · simp only [List.length_append, List.length_singleton] at hj2
        by_cases hjlt : j - 1 < g.length
        · obtain ⟨_, htr⟩ := hpres (gs0.length + 1) (by omega) (by simp)
          simp only [Nat.add_sub_cancel, getD_snoc_eq] at htr
          obtain ⟨ht1, ht2⟩ := htr j hj1 (by omega)
          rw [getD_snoc_lt _ _ _ _ hjlt]
          exact ⟨List.mem_append_left _ ht1, List.mem_append_left _ ht2⟩
        · have hjeq : j = g.length + 1 := by omega
          subst hjeq
          simp only [Nat.add_sub_cancel, getD_snoc_eq]
          exact ⟨List.mem_append_right _ (by simp [recWrites]),
            List.mem_append_right _ (by simp [recWrites])⟩
  · intro k hk1 hk2
    have hlt : k - 1 < gs0.length := by omega
    rw [getD_snoc_lt _ _ _ _ hlt]
    have hm := htrct k hk1 hk2
    rw [getD_snoc_lt _ _ _ _ hlt] at hm
    exact List.mem_append_left _ hm

theorem writeValid_mono_diff {gs : List (List (List UInt8))} {nTrct : Nat}
    {cur : List UInt8} {w : Int × List U8}
    (hnt : nTrct ≤ gs.length)
    (hw : WriteValid gs nTrct w) :
    WriteValid (gs ++ [[cur]]) (nTrct + 1) w := by
  rcases hw with ⟨k, hk1, hk2, rfl⟩ | ⟨k, j, hk1, hk2, hj1, hj2, rfl⟩ |
      ⟨k, j, hk1, hk2, hj1, hj2, rfl⟩ | ⟨k, hk1, hk2, rfl⟩
  · left
    have hlt : k - 1 < gs.length := by omega
    refine ⟨k, hk1, by simp; omega, ?_⟩
    rw [getD_snoc_lt _ _ _ _ hlt]
  · right; left
    have hlt : k - 1 < gs.length := by omega
    refine ⟨k, j, hk1, by simp; omega, hj1, by rw [getD_snoc_lt _ _ _ _ hlt]; exact hj2, ?_⟩
    rw [getD_snoc_lt _ _ _ _ hlt]
  · right; right; left
    have hlt : k - 1 < gs.length := by omega
    refine ⟨k, j, hk1, by simp; omega, hj1, by rw [getD_snoc_lt _ _ _ _ hlt]; exact hj2, ?_⟩
    rw [getD_snoc_lt _ _ _ _ hlt]
  · right; right; right
    have hlt : k - 1 < gs.length := by omega
    refine ⟨k, hk1, by omega, ?_⟩
    rw [getD_snoc_lt _ _ _ _ hlt]

theorem tableWrites_diff {ws : List (Int × List U8)} {gs0 : List (List (List UInt8))}
    {g : List (List UInt8)} {cur : List UInt8}
    (htw : TableWrites ws (gs0 ++ [g]) gs0.length)
    (hG : (gs0 ++ [g]).length + 1 ≤ 50)
    (hcur : cur.length = 350) :
    TableWrites
      ((ws ++ [(171160 + (((gs0.length + 1 : Nat) : Int) - 1) * 2, trctBytes g.length)]) ++
        recWrites (gs0.length + 2) 1 cur)
      ((gs0 ++ [g]) ++ [[cur]]) (gs0.length + 1) := by
  obtain ⟨hgwf, hnt, hvalid, hpres, htrct⟩ := htw
  have hlen_gs : (gs0 ++ [g]).length = gs0.length + 1 := by simp
  have hgwf' : GroupsWF ((gs0 ++ [g]) ++ [[cur]]) := by
    refine ⟨by simp; omega, fun x hx => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hgwf.2 x (by simpa using hx)
    · exact ⟨by simp, by simp, fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hcur⟩
  refine ⟨hgwf', by simp, ?_, ?_, ?_⟩
  · intro w hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with (hw | rfl) | hw
    · exact writeValid_mono_diff hnt (hvalid w hw)
    · right; right; right
      refine ⟨gs0.length + 1, by omega, by omega, ?_⟩
      simp only [Nat.add_sub_cancel]
      rw [getD_snoc_lt _ _ _ _ (by simp : gs0.length < (gs0 ++ [g]).length), getD_snoc_eq]
    · simp only [recWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
      have hk1 : 1 ≤ gs0.length + 2 := by omega
      have hk2 : gs0.length + 2 ≤ ((gs0 ++ [g]) ++ [[cur]]).length := by simp
      have hkeq : gs0.length + 2 - 1 = (gs0 ++ [g]).length := by simp
      rcases hw with rfl | rfl | rfl
      · exact Or.inl ⟨gs0.length + 2, hk1, hk2, by rw [hkeq, getD_snoc_eq]; simp [gCard]⟩
      · exact Or.inr (Or.inl ⟨gs0.length + 2, 1, hk1, hk2, by decide,
          by rw [hkeq, getD_snoc_eq]; simp,
          by rw [hkeq, getD_snoc_eq]; simp⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨gs0.length + 2, 1, hk1, hk2, by decide,
          by rw [hkeq, getD_snoc_eq]; simp,
          by rw [hkeq, getD_snoc_eq]; simp⟩))
  · intro k hk1 hk2
    simp only [List.length_append, List.length_singleton] at hk2
    by_cases hlt : k - 1 < (gs0 ++ [g]).length
    · obtain ⟨hc, htr⟩ := hpres k hk1 (by omega)
      rw [getD_snoc_lt _ _ _ _ hlt]
      refine ⟨List.mem_append_left _ (List.mem_append_left _ hc), fun j hj1 hj2 => ?_⟩
      obtain ⟨ht1, ht2⟩ := htr j hj1 hj2
      exact ⟨List.mem_append_left _ (List.mem_append_left _ ht1),
        List.mem_append_left _ (List.mem_append_left _ ht2)⟩
    · have hkeq : k = gs0.length + 2 := by omega
      subst hkeq
      have hkeq' : gs0.length + 2 - 1 = (gs0 ++ [g]).length := by simp
      rw [hkeq', getD_snoc_eq]
      refine ⟨List.mem_append_right _ (by simp [recWrites, gCard]), fun j hj1 hj2 => ?_⟩
      simp only [List.length_singleton] at hj2
      obtain rfl : j = 1 := by omega
      exact ⟨List.mem_append_right _ (by simp [recWrites]),
        List.mem_append_right _ (by simp [recWrites])⟩
  · intro k hk1 hk2
    have hlt : k - 1 < (gs0 ++ [g]).length := by simp; omega
    rw [getD_snoc_lt _ _ _ _ hlt]
    by_cases hklt : k ≤ gs0.length
    · exact List.mem_append_left _ (List.mem_append_left _ (htrct k hk1 hklt))
    · have hkeq : k = gs0.length + 1 := by omega
      subst hkeq
      simp only [Nat.add_sub_cancel, getD_snoc_eq]
      exact List.mem_append_left _ (List.mem_append_right _ (by simp))

theorem tableWrites_finish {ws : List (Int × List U8)} {gs0 : List (List (List UInt8))}
    {g : List (List UInt8)}
    (htw : TableWrites ws (gs0 ++ [g]) gs0.length) :
    TableWrites (ws ++ [(171160 + (((gs0.length + 1 : Nat) : Int) - 1) * 2, trctBytes g.length)])
      (gs0 ++ [g]) (gs0 ++ [g]).length := by
  obtain ⟨hgwf, hnt, hvalid, hpres, htrct⟩ := htw
  refine ⟨hgwf, Nat.le_refl _, ?_, ?_, ?_⟩
  · intro w hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · rcases hvalid w hw with h1 | h2 | h3 | ⟨k, hk1, hk2, rfl⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inr (Or.inr (Or.inr ⟨k, hk1, by simp; omega, rfl⟩))
    · right; right; right
      refine ⟨gs0.length + 1, by omega, by simp, ?_⟩
      simp only [Nat.add_sub_cancel, getD_snoc_eq]
  · intro k hk1 hk2
    obtain ⟨hc, htr⟩ := hpres k hk1 hk2
    refine ⟨List.mem_append_left _ hc, fun j hj1 hj2 => ?_⟩
    obtain ⟨ht1, ht2⟩ := htr j hj1 hj2
    exact ⟨List.mem_append_left _ ht1, List.mem_append_left _ ht2⟩
  · intro k hk1 hk2
    simp only [List.length_append, List.length_singleton] at hk2
    by_cases hklt : k ≤ gs0.length
    · exact List.mem_append_left _ (htrct k hk1 hklt)
    · have hkeq : k = gs0.length + 1 := by omega
      subst hkeq
      simp only [Nat.add_sub_cancel, getD_snoc_eq]
      exact List.mem_append_right _ (by simp)

/-- `MemWF` and a completed `TableWrites` (`nTrct = gs.length`) imply `MemLoaded`. -/
theorem memLoaded_of_tableWrites {mem : cbstm03a.Mem} {ws : List (Int × List U8)}
    {gs : List (List (List UInt8))}
    (hwf : MemWF mem ws) (htw : TableWrites ws gs gs.length) :
    MemLoaded mem gs := by
  refine ⟨htw.1.1, htw.1.2, fun c hc1 hc2 => ?_⟩
  set ck : Nat := c.val.toNat
  have hck_val : (ck : Int) = c.val := Int.toNat_of_nonneg (by omega)
  have hck1 : 1 ≤ ck := by omega
  have hck2 : ck ≤ gs.length := by omega
  have hg_mem : gs.getD (ck - 1) [] ∈ gs := getD_mem_of_lt (by omega)
  have hgl : (gs.getD (ck - 1) []).length ≤ 10 := (htw.1.2 _ hg_mem).2.1
  have hts_len : gs.length ≤ 50 := htw.1.1
  refine ⟨?_, ?_, ?_⟩
  · intro off dst hoff hdst
    have hhas := tableWrites_hasWrite_card htw hck1 hck2
    rw [hck_val, ← hoff] at hhas
    have hbs_len : (latL (gCard (gs.getD (ck - 1) []))).length = 16 := by
      rw [length_latL, length_gCard_of_wf htw.1 hck1 hck2]
    exact mem_get_spec mem ws off dst _ hwf hhas (by omega) (by omega)
  · have hhas := tableWrites_hasWrite_trct htw hck1 hck2
    rw [hck_val] at hhas
    exact read_trct_spec mem ws c (gs.getD (ck - 1) []).length hwf hc1 (by omega) hgl hhas
  · intro t ht1 ht2
    set tj : Nat := t.val.toNat
    have htj_val : (tj : Int) = t.val := Int.toNat_of_nonneg (by omega)
    have htj1 : 1 ≤ tj := by omega
    have htj2 : tj ≤ (gs.getD (ck - 1) []).length := by omega
    refine ⟨?_, ?_⟩
    · intro off dst hoff hdst
      have hhas := tableWrites_hasWrite_tId htw hck1 hck2 htj1 htj2
      rw [hck_val, htj_val, ← hoff] at hhas
      have hbs_len : (latL (tId ((gs.getD (ck - 1) []).getD (tj - 1) []))).length = 16 := by
        rw [length_latL, length_tId_of_wf htw.1 hck1 hck2 htj1 htj2]
      exact mem_get_spec mem ws off dst _ hwf hhas (by omega) (by omega)
    · intro off dst hoff hdst
      have hhas := tableWrites_hasWrite_tRest htw hck1 hck2 htj1 htj2
      rw [hck_val, htj_val, ← hoff] at hhas
      have hbs_len : (latL (tRest ((gs.getD (ck - 1) []).getD (tj - 1) []))).length = 318 := by
        rw [length_latL, length_tRest_of_wf htw.1 hck1 hck2 htj1 htj2]
      exact mem_get_spec mem ws off dst _ hwf hhas (by omega) (by omega)

/-! ## 4. Local helpers for `put`, `eq_bytes`, `add1`, `set_dd`, `call_m03b` -/

private theorem usize_max_ge : 4294967295 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max_eq, U64.max_eq] <;> omega

private theorem ite_true_of {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

private theorem array_index_range {n : Usize} (a : Array U8 n) (j k : Usize)
    (hjk : j.val ≤ k.val) (hk : k.val ≤ n.val) :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      a { start := j, «end» := k } =
      .ok (Slice.from ((a.val.drop j.val).take (k.val - j.val)) (by simp; scalar_tac)) := by
  simp only [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice, core.slice.index.SliceIndexRangeUsizeSlice.index]
  have hl : a.to_slice.length = n.val := by simp [Array.to_slice]
  rw [ite_true_of ⟨by simpa [UScalar.le_equiv] using hjk, by rw [hl]; exact hk⟩]
  congr 1
  rw [Slice.eq_iff]
  simp [List.slice, Array.to_slice]

private theorem putL_zero (dst : List U8) (off : Nat) (src : List U8) :
    putL dst off 0 src = dst := by
  simp [putL]

private theorem putL_step (dst : List U8) (off i : Nat) (src : List U8)
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

private theorem put_val (dst : Slice U8) (off len : Usize) (src : Slice U8)
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

private theorem take_succ_eq_iff {α : Type _} {a b : List α} {i : Nat}
    (ha : i < a.length) (hb : i < b.length) :
    a.take (i + 1) = b.take (i + 1) ↔ a.take i = b.take i ∧ a[i] = b[i] := by
  rw [take_succ_of_lt ha, take_succ_of_lt hb]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp; omega)
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2]

private theorem eq_bytes_eq (a b : Slice U8) :
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

private theorem add1_eq (x : I64) (h0 : 0 ≤ x.val) (h1 : x.val < 9999) :
    ∃ y : I64, cbstm03a.add1 x = .ok y ∧ y.val = x.val + 1 := by
  refine exists_ok_of_wp ?_
  unfold cbstm03a.add1
  aeneas_wp []
  simp (disch := omega) only [dite_eq_left, ite_eq_left]
  refine ⟨_, rfl, ?_⟩
  rw [iscalar_srem_val, IScalar.ofInt_val_eq, iscalar_ofInt_val,
    Int.tmod_eq_of_lt (by omega) (by omega)]

private def ddTrnxArr : Array U8 8#usize :=
  Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8]

private theorem putL_full (dst src : List U8) (n : Nat) (hd : dst.length = n) (hs : src.length = n) :
    putL dst 0 n src = src := by
  simp [putL, hd, hs]

private theorem take_putL_zero (dst src : List U8) (k : Nat) (hs : src.length = k) :
    (putL dst 0 k src).take k = src := by
  subst hs
  simp [putL]

private theorem set_dd_eq (c : cbstm03a.Ctx) (dd : Array U8 8#usize) :
    cbstm03a.set_dd c dd.to_slice = .ok { c with m_dd := dd } := by
  unfold cbstm03a.set_dd
  simp only [lift, bind_ok, Array.to_slice_mut, Aeneas.Std.uncurry_apply_pair]
  rw [put_val _ _ _ _ (by simp [Array.to_slice, c.m_dd.property]), bind_ok]
  congr 2
  rw [Array.eq_iff]
  simp [Array.from_slice, Array.to_slice, putL_full _ _ 8 c.m_dd.property dd.property]

private theorem m03b_trnx_some
    {trnx_file : Slice cbstm03a.TrnxRecord}
    {xref_file : Slice cbstm03a.CardXrefRecord}
    {cust_file : Slice cbstm03a.CustomerRecord}
    {acct_file : Slice cbstm03a.AccountRecord}
    {vals1 : List (List FVal)}
    (htrnx : trnx_file.val.map TrnxRecord.vals = vals1)
    (hv1 : ∀ v ∈ vals1, TrnxRecord.Valid v)
    (hser : ∀ r : cbstm03a.TrnxRecord,
      ∃ b : Array U8 350#usize, cbstm03a.ser_trnx r = .ok b ∧
        b.val = latL (TrnxRecord.encode (TrnxRecord.vals r)))
    (c : cbstm03a.Ctx) (idx : Nat)
    (hdd : c.m_dd = ddTrnxArr) (hop : c.m_oper = 82#u8) (heof : c.trnx_eof = false)
    (hpos : c.trnx_pos.val = idx) (hlt : idx < vals1.length) :
    ∃ c' : cbstm03a.Ctx,
      cbstm03a.call_m03b c trnx_file xref_file cust_file acct_file = .ok c' ∧
      c'.m_rc = Array.make 2#usize [48#u8, 48#u8] ∧
      c'.trnx_pos.val = idx + 1 ∧ c'.trnx_eof = false ∧
      (c'.m_fldt.val.drop 0).take 350 =
        latL (TrnxRecord.encode (vals1.getD idx [])) ∧
      c'.xref_pos = c.xref_pos ∧ c'.xref_eof = c.xref_eof ∧
      c'.xref_status = c.xref_status ∧ c'.cust_status = c.cust_status ∧
      c'.acct_status = c.acct_status ∧
      c'.displays = c.displays ∧ c'.stmt = c.stmt ∧ c'.html = c.html ∧
      c'.abended = c.abended := by
  have htlen : trnx_file.val.length = vals1.length := by
    rw [← htrnx, List.length_map]
  have hpos_lt : c.trnx_pos.val < trnx_file.val.length := by omega
  have hpos_max : c.trnx_pos.val + 1 ≤ Usize.max := by
    have := trnx_file.property; omega
  obtain ⟨img, himg, himg_val⟩ := hser (trnx_file.val[c.trnx_pos.val]'hpos_lt)
  have hr_vals : TrnxRecord.vals (trnx_file.val[c.trnx_pos.val]'hpos_lt) = vals1.getD idx [] := by
    rw [← htrnx, List.getD_eq_getElem _ _ (by simp [htlen, hlt]), List.getElem_map]
    simp [hpos]
  have hr_valid : TrnxRecord.Valid (vals1.getD idx []) :=
    hv1 _ (getD_mem_of_lt hlt)
  have henc_len : (TrnxRecord.encode (vals1.getD idx [])).length = 350 :=
    trnx_length hr_valid
  have hput_b : (0#usize).val + (350#usize).val ≤ (Array.repeat 1000#usize 32#u8).to_slice.val.length := by
    simp [Array.to_slice, Array.repeat_val]
  have hp := put_val (Array.repeat 1000#usize 32#u8).to_slice 0#usize 350#usize img.to_slice hput_b
  refine exists_ok_of_wp ?_
  unfold cbstm03a.call_m03b
  have hdd_eq : cbstm03a.eq_bytes c.m_dd.to_slice ddTrnxArr.to_slice = .ok true := by
    rw [eq_bytes_eq, hdd]; rfl
  rw [show Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddTrnxArr from rfl]
  aeneas_wp [Array.to_slice_mut, hdd_eq, hop, heof, hpos_lt, hpos_max, himg, hp]
  refine ⟨_, rfl, rfl, by simp [UScalar.ofNatCore_val_eq, hpos], rfl, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [Array.from_slice_val _ _ (by simp [Slice.from_val, length_putL, Array.to_slice, Array.repeat_val])]
  simp only [Slice.from_val, Array.to_slice, himg_val, hr_vals, List.drop_zero]
  exact take_putL_zero _ _ 350 (by rw [length_latL, henc_len])

private theorem m03b_trnx_eof
    {trnx_file : Slice cbstm03a.TrnxRecord}
    {xref_file : Slice cbstm03a.CardXrefRecord}
    {cust_file : Slice cbstm03a.CustomerRecord}
    {acct_file : Slice cbstm03a.AccountRecord}
    {vals1 : List (List FVal)}
    (htrnx : trnx_file.val.map TrnxRecord.vals = vals1)
    (c : cbstm03a.Ctx)
    (hdd : c.m_dd = ddTrnxArr) (hop : c.m_oper = 82#u8) (heof : c.trnx_eof = false)
    (hpos : c.trnx_pos.val = vals1.length) :
    ∃ c' : cbstm03a.Ctx,
      cbstm03a.call_m03b c trnx_file xref_file cust_file acct_file = .ok c' ∧
      c'.m_rc = Array.make 2#usize [49#u8, 48#u8] ∧
      c'.trnx_pos.val = vals1.length ∧ c'.trnx_eof = true ∧
      c'.xref_pos = c.xref_pos ∧ c'.xref_eof = c.xref_eof ∧
      c'.xref_status = c.xref_status ∧ c'.cust_status = c.cust_status ∧
      c'.acct_status = c.acct_status ∧
      c'.displays = c.displays ∧ c'.stmt = c.stmt ∧ c'.html = c.html ∧
      c'.abended = c.abended := by
  have htlen : trnx_file.val.length = vals1.length := by
    rw [← htrnx, List.length_map]
  have hpos_nlt : ¬ (c.trnx_pos.val < trnx_file.val.length) := by omega
  refine exists_ok_of_wp ?_
  unfold cbstm03a.call_m03b
  have hdd_eq : cbstm03a.eq_bytes c.m_dd.to_slice ddTrnxArr.to_slice = .ok true := by
    rw [eq_bytes_eq, hdd]; rfl
  rw [show Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddTrnxArr from rfl]
  aeneas_wp [hdd_eq, hop, heof, hpos_nlt]
  exact ⟨_, rfl, rfl, hpos, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 5. `8500-READTRNX-READ` (`run_loop0`) and `MemLoaded` -/

theorem run_loop0_done (trnx_file : Slice cbstm03a.TrnxRecord)
    (xref_file : Slice cbstm03a.CardXrefRecord) (cust_file : Slice cbstm03a.CustomerRecord)
    (acct_file : Slice cbstm03a.AccountRecord)
    (c : cbstm03a.Ctx) (mem : cbstm03a.Mem) (trnx_rec : Array U8 350#usize)
    (save_card : Array U8 16#usize) (cr_cnt tr_cnt : Std.I64) (ok1 : Bool) :
    cbstm03a.run_loop0 trnx_file xref_file cust_file acct_file
      c mem trnx_rec save_card cr_cnt tr_cnt false ok1 =
    .ok (c, mem, trnx_rec, cr_cnt, tr_cnt, ok1) := by
  rw [cbstm03a.run_loop0, loop_unfold]
  simp [cbstm03a.run_loop0.body]

theorem run_loop0_step
    {trnx_file : Slice cbstm03a.TrnxRecord}
    {xref_file : Slice cbstm03a.CardXrefRecord}
    {cust_file : Slice cbstm03a.CustomerRecord}
    {acct_file : Slice cbstm03a.AccountRecord}
    {c c' : cbstm03a.Ctx} {mem mem' : cbstm03a.Mem}
    {trnx_rec trnx_rec' : Array U8 350#usize}
    {save_card save_card' : Array U8 16#usize}
    {cr_cnt cr_cnt' tr_cnt tr_cnt' : Std.I64}
    {reading reading' ok1 ok1' : Bool}
    (hbody : cbstm03a.run_loop0.body trnx_file xref_file cust_file acct_file
      c mem trnx_rec save_card cr_cnt tr_cnt reading ok1 =
      .ok (.cont (c', mem', trnx_rec', save_card', cr_cnt', tr_cnt', reading', ok1'))) :
    cbstm03a.run_loop0 trnx_file xref_file cust_file acct_file
      c mem trnx_rec save_card cr_cnt tr_cnt reading ok1 =
    cbstm03a.run_loop0 trnx_file xref_file cust_file acct_file
      c' mem' trnx_rec' save_card' cr_cnt' tr_cnt' reading' ok1' := by
  rw [cbstm03a.run_loop0, loop_unfold]
  dsimp only
  rw [hbody, bind_ok]
  rfl

@[simp] theorem length_recWrites (c t : Nat) (cur : List UInt8) :
    (recWrites c t cur).length = 3 := rfl

theorem wsBytesLen_recWrites (c t : Nat) {cur : List UInt8} (hcur : cur.length = 350) :
    wsBytesLen (recWrites c t cur) = 350 := by
  simp [recWrites, wsBytesLen, length_tCard_of_eq hcur, length_tId_of_eq hcur, length_tRest_of_eq hcur]

theorem mem_write_rec_spec
    {mem1 : cbstm03a.Mem} {ws1 : List (Int × List U8)}
    {cr_cnt1 tr_cnt1 : Std.I64} {c t : Nat}
    {trnx_rec : Array U8 350#usize} {cur : List UInt8} {s1 : Slice U8}
    (hwf1 : MemWF mem1 ws1)
    (hlen1 : ws1.length + 3 ≤ Usize.max)
    (hlen2 : wsBytesLen ws1 + 350 ≤ Usize.max)
    (hcr : cr_cnt1.val = (c : Int)) (htr : tr_cnt1.val = (t : Int))
    (hc1 : 1 ≤ c) (hc2 : c ≤ 50) (ht1 : 1 ≤ t) (ht2 : t ≤ 10)
    (hcur : cur.length = 350)
    (htrec : trnx_rec.val = latL cur)
    (hs1 : s1.val = latL (tCard cur)) :
    ∃ (i : Std.I64) (mem2 : cbstm03a.Mem) (i1 : Std.I64) (s2 : Slice U8)
      (mem3 : cbstm03a.Mem) (i2 : Std.I64) (s3 : Slice U8) (mem4 : cbstm03a.Mem),
      cbstm03a.card_off cr_cnt1 = .ok i ∧
      cbstm03a.mem_write mem1 i s1 = .ok mem2 ∧
      cbstm03a.tran_off cr_cnt1 tr_cnt1 = .ok i1 ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) trnx_rec
        { start := 16#usize, «end» := 32#usize } = .ok s2 ∧
      cbstm03a.mem_write mem2 i1 s2 = .ok mem3 ∧
      (i1 + 16#i64 : Result Std.I64) = .ok i2 ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) trnx_rec
        { start := 32#usize, «end» := 350#usize } = .ok s3 ∧
      cbstm03a.mem_write mem3 i2 s3 = .ok mem4 ∧
      MemWF mem4 (ws1 ++ recWrites c t cur) := by
  obtain ⟨i, hi_eq, hi_val⟩ := card_off_spec cr_cnt1 (by omega) (by omega)
  have hs1_len : s1.val.length = 16 := by rw [hs1, length_latL, length_tCard_of_eq hcur]
  obtain ⟨mem2, hmw1, hwf2⟩ := mem_write_spec mem1 ws1 i s1 hwf1
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨i1, hi1_eq, hi1_val⟩ := tran_off_spec cr_cnt1 tr_cnt1
    (by omega) (by omega) (by omega) (by omega)
  have hrng2 := array_index_range trnx_rec 16#usize 32#usize (by decide) (by decide)
  set s2 := Slice.from ((trnx_rec.val.drop (16#usize).val).take ((32#usize).val - (16#usize).val))
    (by simp; scalar_tac)
  have hs2_val : s2.val = latL (tId cur) := by
    simp [s2, htrec, ← latL_drop, ← latL_take, tId]
  have hs2_len : s2.val.length = 16 := by rw [hs2_val, length_latL, length_tId_of_eq hcur]
  obtain ⟨mem3, hmw2, hwf3⟩ := mem_write_spec mem2 (ws1 ++ [(i.val, s1.val)]) i1 s2 hwf2
    (by simp; omega) (by simp [hs1_len, hs2_len]; omega) (by omega) (by omega)
  have hi2_bnd : -9223372036854775808 ≤ i1.val + 16 ∧
      i1.val + 16 ≤ 9223372036854775807 := by omega
  obtain ⟨i2, hi2_eq, hi2_val⟩ : ∃ i2 : Std.I64,
      (i1 + 16#i64 : Result Std.I64) = .ok i2 ∧ i2.val = i1.val + 16 := by
    refine exists_ok_of_wp ?_
    aeneas_wp [hi2_bnd]
    exact ⟨_, rfl, by simp [IScalar.ofInt_val_eq]⟩
  have hrng3 := array_index_range trnx_rec 32#usize 350#usize (by decide) (by decide)
  set s3 := Slice.from ((trnx_rec.val.drop (32#usize).val).take ((350#usize).val - (32#usize).val))
    (by simp; scalar_tac)
  have hs3_val : s3.val = latL (tRest cur) := by
    simp [s3, htrec, ← latL_drop, ← latL_take, tRest,
      List.take_of_length_le (by simp [hcur] : (cur.drop 32).length ≤ 318)]
  have hs3_len : s3.val.length = 318 := by rw [hs3_val, length_latL, length_tRest_of_eq hcur]
  obtain ⟨mem4, hmw3, hwf4⟩ := mem_write_spec mem3
    ((ws1 ++ [(i.val, s1.val)]) ++ [(i1.val, s2.val)]) i2 s3 hwf3
    (by simp; omega)
    (by rw [wsBytesLen_append, wsBytesLen_append, wsBytesLen_singleton, wsBytesLen_singleton,
          hs1_len, hs2_len, hs3_len]; omega)
    (by omega) (by omega)
  refine ⟨i, mem2, i1, s2, mem3, i2, s3, mem4,
    hi_eq, hmw1, hi1_eq, hrng2, hmw2, hi2_eq, hrng3, hmw3, ?_⟩
  rw [hi_val, hcr, hs1, hi1_val, hcr, htr, hs2_val, hi2_val, hi1_val, hcr, htr, hs3_val] at hwf4
  simpa [recWrites, List.append_assoc] using hwf4

theorem tableWrites_nil_eq {ws : List (Int × List U8)} (htw : TableWrites ws [] 0) :
    ws = [] := by
  cases ws with
  | nil => rfl
  | cons w ws =>
    exfalso
    rcases htw.2.2.1 w (List.mem_cons_self ..) with
      ⟨k, hk1, hk2, _⟩ | ⟨k, _, hk1, hk2, _⟩ | ⟨k, _, hk1, hk2, _⟩ | ⟨k, hk1, hk2, _⟩ <;>
      (simp at hk2; omega)

theorem branch_trct_spec
    {done : List (List UInt8)} {cur : List UInt8}
    {mem : cbstm03a.Mem} {ws : List (Int × List U8)}
    {save_card : Array U8 16#usize} {s1 : Slice U8}
    {cr_cnt tr_cnt : Std.I64}
    (hcur : cur.length = 350)
    (hG : (grp (done ++ [cur])).length ≤ 50)
    (hT : ∀ g ∈ grp (done ++ [cur]), g.length ≤ 10)
    (hwf : MemWF mem ws)
    (htw : TableWrites ws (grp done) ((grp done).length - 1))
    (hlen1 : ws.length + 4 ≤ Usize.max)
    (hlen2 : wsBytesLen ws + 352 ≤ Usize.max)
    (hsave : save_card.val = latL (tCard (done.getLastD cur)))
    (hs1 : s1.val = latL (tCard cur))
    (hcr : cr_cnt.val = ((max 1 (grp done).length : Nat) : Int))
    (htr : tr_cnt.val = (((grp done).getLastD []).length : Int)) :
    ∃ (b : Bool) (mem1 : cbstm03a.Mem) (cr_cnt1 tr_cnt1 : Std.I64) (ws1 : List (Int × List U8)),
      cbstm03a.eq_bytes save_card.to_slice s1 = .ok b ∧
      ((b = true ∧ cbstm03a.add1 tr_cnt = .ok tr_cnt1 ∧ mem1 = mem ∧ cr_cnt1 = cr_cnt) ∨
       (b = false ∧ ∃ mem2, cbstm03a.write_trct mem cr_cnt tr_cnt = .ok mem2 ∧
          cbstm03a.add1 cr_cnt = .ok cr_cnt1 ∧ mem1 = mem2 ∧ tr_cnt1 = 1#i64)) ∧
      MemWF mem1 ws1 ∧
      ws1.length ≤ ws.length + 1 ∧
      wsBytesLen ws1 ≤ wsBytesLen ws + 2 ∧
      cr_cnt1.val = ((grp (done ++ [cur])).length : Int) ∧
      tr_cnt1.val = (((grp (done ++ [cur])).getLastD []).length : Int) ∧
      1 ≤ (grp (done ++ [cur])).length ∧
      (grp (done ++ [cur])).length ≤ 50 ∧
      1 ≤ ((grp (done ++ [cur])).getLastD []).length ∧
      ((grp (done ++ [cur])).getLastD []).length ≤ 10 ∧
      TableWrites
        (ws1 ++ recWrites (grp (done ++ [cur])).length ((grp (done ++ [cur])).getLastD []).length cur)
        (grp (done ++ [cur]))
        ((grp (done ++ [cur])).length - 1) := by
  by_cases hd : done = []
  · subst hd
    simp only [grp_nil, List.nil_append, List.length_nil, List.getLastD_nil] at htw hsave hcr htr hG hT ⊢
    have hws_nil : ws = [] := tableWrites_nil_eq htw
    subst hws_nil
    have hgrp1 : grp [cur] = [[cur]] := rfl
    have heq : cbstm03a.eq_bytes save_card.to_slice s1 = .ok true := by
      rw [eq_bytes_eq, Array.to_slice, Slice.from_val, hsave, hs1]; simp
    obtain ⟨tr_cnt2, hadd, htr2_val⟩ := add1_eq tr_cnt (by omega) (by omega)
    refine ⟨true, mem, cr_cnt, tr_cnt2, [], heq, Or.inl ⟨rfl, hadd, rfl, rfl⟩, hwf, by simp, by simp,
      by rw [hgrp1]; simp [hcr], by rw [hgrp1, htr2_val, htr]; rfl,
      by rw [hgrp1]; simp, by rw [hgrp1]; simp,
      by rw [hgrp1]; simp, by rw [hgrp1]; simp, ?_⟩
    rw [hgrp1, List.nil_append]
    exact tableWrites_first hcur
  · obtain ⟨gs0, g, hgs, hgc⟩ := grp_snoc_form done hd
    have hsave' : save_card.val = latL (gCard g) := by
      rw [hsave, hgc, getLastD_ne_nil done hd cur []]
    rw [hgs] at htw hcr htr
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel, getLastD_snoc] at htw hcr htr
    have hg_mem : g ∈ gs0 ++ [g] := by simp
    obtain ⟨hg1, hg10, _⟩ := htw.1.2 g hg_mem
    have hgs0_len : (gs0 ++ [g]).length ≤ 50 := htw.1.1
    have hmax_eq : max 1 (gs0.length + 1) = gs0.length + 1 := by omega
    rw [hmax_eq] at hcr
    by_cases hsame : gCard g = tCard cur
    · have hgs' := grp_snoc_same done cur gs0 g hgs hsame
      rw [hgs'] at hG hT ⊢
      have hgl1 : g.length + 1 ≤ 10 := by
        have := hT (g ++ [cur]) (by simp); simpa using this
      have heq : cbstm03a.eq_bytes save_card.to_slice s1 = .ok true := by
        rw [eq_bytes_eq, Array.to_slice, Slice.from_val, hsave', hs1, hsame]; simp
      obtain ⟨tr_cnt2, hadd, htr2_val⟩ := add1_eq tr_cnt (by omega) (by omega)
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel, getLastD_snoc]
      refine ⟨true, mem, cr_cnt, tr_cnt2, ws, heq, Or.inl ⟨rfl, hadd, rfl, rfl⟩, hwf, by omega, by omega,
        by omega, by omega, by omega, by simp at hG; omega, by omega, hgl1, ?_⟩
      exact tableWrites_same htw hsame hgl1 hcur
    · have hgs' := grp_snoc_diff done cur gs0 g hgs hsame
      rw [hgs'] at hG hT ⊢
      have heq : cbstm03a.eq_bytes save_card.to_slice s1 = .ok false := by
        rw [eq_bytes_eq, Array.to_slice, Slice.from_val, hsave', hs1]
        simp [latL_inj, hsame]
      obtain ⟨mem2, hwt, hwf2⟩ := write_trct_spec mem ws cr_cnt tr_cnt hwf
        (by omega) (by omega) (by omega) (by simp at hgs0_len; omega) (by omega) (by omega)
      have htr_toNat : tr_cnt.val.toNat = g.length := by omega
      rw [hcr, htr_toNat] at hwf2
      obtain ⟨cr_cnt2, hadd, hcr2_val⟩ := add1_eq cr_cnt (by omega) (by simp at hgs0_len; omega)
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel, getLastD_snoc]
      refine ⟨false, mem2, cr_cnt2, 1#i64,
        ws ++ [(171160 + (((gs0.length + 1 : Nat) : Int) - 1) * 2, trctBytes g.length)],
        heq, Or.inr ⟨rfl, mem2, hwt, hadd, rfl, rfl⟩, hwf2, by simp, by simp,
        by omega, rfl, by omega, by simp at hG; omega, by decide, by decide, ?_⟩
      exact tableWrites_diff htw (by simp at hG ⊢; omega) hcur

theorem length_flatten_le_10 {α : Type} : ∀ {gs : List (List α)},
    (∀ g ∈ gs, g.length ≤ 10) → gs.flatten.length ≤ 10 * gs.length
  | [], _ => by simp
  | g :: gs, h => by
    have hg := h g (List.mem_cons_self ..)
    have hgs := length_flatten_le_10 (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem trs_length_le_500 {vals1 : List (List FVal)}
    (hG : (grp (vals1.map TrnxRecord.encode)).length ≤ 50)
    (hT : ∀ g ∈ grp (vals1.map TrnxRecord.encode), g.length ≤ 10) :
    vals1.length ≤ 500 := by
  have hf := (grp_props (vals1.map TrnxRecord.encode)).1
  have hlen : (vals1.map TrnxRecord.encode).length = vals1.length := List.length_map _
  have hfl := length_flatten_le_10 hT
  rw [hf, hlen] at hfl
  omega

theorem run_loop0_aux
    {trnx_file : Slice cbstm03a.TrnxRecord}
    {xref_file : Slice cbstm03a.CardXrefRecord}
    {cust_file : Slice cbstm03a.CustomerRecord}
    {acct_file : Slice cbstm03a.AccountRecord}
    {vals1 : List (List FVal)}
    (htrnx : trnx_file.val.map TrnxRecord.vals = vals1)
    (hv1 : ∀ v ∈ vals1, TrnxRecord.Valid v)
    (hser : ∀ r : cbstm03a.TrnxRecord,
      ∃ b : Array U8 350#usize, cbstm03a.ser_trnx r = .ok b ∧
        b.val = latL (TrnxRecord.encode (TrnxRecord.vals r)))
    (hG : (grp (vals1.map TrnxRecord.encode)).length ≤ 50)
    (hT : ∀ g ∈ grp (vals1.map TrnxRecord.encode), g.length ≤ 10)
    (rest : List (List UInt8)) :
    ∀ (done : List (List UInt8)) (cur : List UInt8),
      vals1.map TrnxRecord.encode = done ++ cur :: rest →
      ∀ (c : cbstm03a.Ctx) (mem : cbstm03a.Mem) (ws : List (Int × List U8))
        (trnx_rec : Array U8 350#usize) (save_card : Array U8 16#usize)
        (cr_cnt tr_cnt : Std.I64),
        c.trnx_pos.val = done.length + 1 →
        c.trnx_eof = false →
        MemWF mem ws →
        TableWrites ws (grp done) ((grp done).length - 1) →
        ws.length ≤ 4 * done.length →
        wsBytesLen ws ≤ 352 * done.length →
        trnx_rec.val = latL cur →
        save_card.val = latL (tCard (done.getLastD cur)) →
        cr_cnt.val = ((max 1 (grp done).length : Nat) : Int) →
        tr_cnt.val = (((grp done).getLastD []).length : Int) →
        ∃ c' mem' trnx_rec' cr_cnt' tr_cnt' ws',
          cbstm03a.run_loop0 trnx_file xref_file cust_file acct_file
            c mem trnx_rec save_card cr_cnt tr_cnt true true =
            .ok (c', mem', trnx_rec', cr_cnt', tr_cnt', true) ∧
          MemWF mem' ws' ∧
          TableWrites ws' (grp (vals1.map TrnxRecord.encode))
            ((grp (vals1.map TrnxRecord.encode)).length - 1) ∧
          ws'.length ≤ 4 * vals1.length ∧
          wsBytesLen ws' ≤ 352 * vals1.length ∧
          cr_cnt'.val = ((grp (vals1.map TrnxRecord.encode)).length : Int) ∧
          tr_cnt'.val = (((grp (vals1.map TrnxRecord.encode)).getLastD []).length : Int) ∧
          c'.trnx_pos.val = vals1.length ∧
          c'.trnx_eof = true ∧
          c'.xref_pos = c.xref_pos ∧ c'.xref_eof = c.xref_eof ∧
          c'.xref_status = c.xref_status ∧ c'.cust_status = c.cust_status ∧
          c'.acct_status = c.acct_status ∧
          c'.displays = c.displays ∧ c'.stmt = c.stmt ∧ c'.html = c.html ∧
          c'.abended = c.abended := by
  have h500 := trs_length_le_500 hG hT
  induction rest with
  | nil =>
    intro done cur htrs c mem ws trnx_rec save_card cr_cnt tr_cnt
      hpos heof hwf htw hlen1 hlen2 htrec hsave hcr htr
    have hcur_mem : cur ∈ vals1.map TrnxRecord.encode := by simp [htrs]
    obtain ⟨vcur, hvcur_mem, hvcur_enc⟩ := List.mem_map.mp hcur_mem
    have hcur_len : cur.length = 350 := by
      rw [← hvcur_enc]; exact trnx_length (hv1 vcur hvcur_mem)
    have htrs' : vals1.map TrnxRecord.encode = done ++ [cur] := by simpa using htrs
    have hdone_len : done.length + 1 = vals1.length := by
      have := congrArg List.length htrs'
      simp only [List.length_map, List.length_append, List.length_singleton] at this
      omega
    have hmax := usize_max_ge
    have hrng1 := array_index_range trnx_rec 0#usize 16#usize (by decide) (by decide)
    set s1 := Slice.from ((trnx_rec.val.drop (0#usize).val).take ((16#usize).val - (0#usize).val))
      (by simp; scalar_tac)
    have hs1_val : s1.val = latL (tCard cur) := by
      simp [s1, htrec, ← latL_take, tCard]
    obtain ⟨b, mem1, cr_cnt1, tr_cnt1, ws1, heq, hbr, hwf1, hws1_l, hws1_b,
        hcr1, htr1, hc1, hc2, ht1, ht2, htw'⟩ :=
      branch_trct_spec hcur_len (by rw [← htrs']; exact hG) (by rw [← htrs']; exact hT)
        hwf htw (by omega) (by omega) hsave hs1_val hcr htr
    obtain ⟨i, mem2, i1, s2, mem3, i2, s3, mem4,
        hi_eq, hmw1, hi1_eq, hrng2, hmw2, hi2_eq, hrng3, hmw3, hwf4⟩ :=
      mem_write_rec_spec hwf1 (by omega) (by omega) hcr1 htr1 hc1 hc2 ht1 ht2 hcur_len htrec hs1_val
    have hput5 := put_val save_card.to_slice 0#usize 16#usize s1
      (by simp [Array.to_slice, save_card.property])
    set s5 := Slice.from (putL save_card.to_slice.val (0#usize).val (16#usize).val s1.val)
      (by rw [length_putL _ _ _ _ (by simp [Array.to_slice, save_card.property])]; exact save_card.to_slice.property)
    have hset := set_dd_eq c ddTrnxArr
    obtain ⟨c2, hm03b, hrc2, hpos2, heof2, hxp, hxe, hxs, hcs, has, hd, hs, hh, ha⟩ :=
      @m03b_trnx_eof trnx_file xref_file cust_file acct_file vals1 htrnx
        { c with m_dd := ddTrnxArr, m_oper := 82#u8, m_fldt := Array.repeat 1000#usize 32#u8 }
        rfl rfl heof (by simp [hpos, hdone_len])
    have heq00 : cbstm03a.eq_bytes c2.m_rc.to_slice (Array.make 2#usize [48#u8, 48#u8]).to_slice = .ok false := by
      rw [eq_bytes_eq, hrc2]; simp [Array.to_slice, Array.make_val]
    have heq10 : cbstm03a.eq_bytes c2.m_rc.to_slice (Array.make 2#usize [49#u8, 48#u8]).to_slice = .ok true := by
      rw [eq_bytes_eq, hrc2]; rfl
    have hbody : cbstm03a.run_loop0.body trnx_file xref_file cust_file acct_file
        c mem trnx_rec save_card cr_cnt tr_cnt true true =
        .ok (.cont (c2, mem4, trnx_rec, save_card.from_slice s5, cr_cnt1, tr_cnt1, false, true)) := by
      unfold cbstm03a.run_loop0.body
      rw [show Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddTrnxArr from rfl]
      rcases hbr with ⟨rfl, hadd, rfl, rfl⟩ | ⟨rfl, mem2_, hwt, hadd, rfl, rfl⟩
      · simp only [↓reduceIte, lift, bind_ok, Array.to_slice_mut, Aeneas.Std.uncurry_apply_pair,
          hrng1, heq, hadd, hi_eq, hmw1, hi1_eq, hrng2, hmw2, hi2_eq, hrng3, hmw3, hput5, hset, hm03b,
          heq00, heq10, Bool.false_eq_true]
      · simp only [↓reduceIte, lift, bind_ok, Array.to_slice_mut, Aeneas.Std.uncurry_apply_pair,
          hrng1, heq, hwt, hadd, hi_eq, hmw1, hi1_eq, hrng2, hmw2, hi2_eq, hrng3, hmw3, hput5, hset, hm03b,
          heq00, heq10, Bool.false_eq_true]
    rw [run_loop0_step hbody, run_loop0_done]
    refine ⟨c2, mem4, trnx_rec, cr_cnt1, tr_cnt1,
      ws1 ++ recWrites (grp (done ++ [cur])).length ((grp (done ++ [cur])).getLastD []).length cur,
      rfl, hwf4, by rwa [htrs'], ?_, ?_, by rwa [htrs'], by rwa [htrs'],
      hpos2, heof2, hxp, hxe, hxs, hcs, has, hd, hs, hh, ha⟩
    · simp only [List.length_append, length_recWrites]; omega
    · rw [wsBytesLen_append, wsBytesLen_recWrites _ _ hcur_len]; omega
  | cons next rest' ih =>
    intro done cur htrs c mem ws trnx_rec save_card cr_cnt tr_cnt
      hpos heof hwf htw hlen1 hlen2 htrec hsave hcr htr
    have hcur_mem : cur ∈ vals1.map TrnxRecord.encode := by simp [htrs]
    obtain ⟨vcur, hvcur_mem, hvcur_enc⟩ := List.mem_map.mp hcur_mem
    have hcur_len : cur.length = 350 := by
      rw [← hvcur_enc]; exact trnx_length (hv1 vcur hvcur_mem)
    have hnext_mem : next ∈ vals1.map TrnxRecord.encode := by simp [htrs]
    obtain ⟨vnext, hvnext_mem, hvnext_enc⟩ := List.mem_map.mp hnext_mem
    have hnext_len : next.length = 350 := by
      rw [← hvnext_enc]; exact trnx_length (hv1 vnext hvnext_mem)
    have htrs' : vals1.map TrnxRecord.encode = (done ++ [cur]) ++ next :: rest' := by simp [htrs]
    obtain ⟨hG_pre, hT_pre⟩ := grp_bounds (done ++ [cur]) (next :: rest')
      (by rw [← htrs']; exact hG)
      (by rw [← htrs']; exact hT)
    have hT_pre' : ∀ g ∈ grp (done ++ [cur]), g.length ≤ 10 := by
      intro g hg
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hg
      have := hT_pre idx hidx
      rwa [List.getD_eq_getElem _ _ hidx] at this
    have hdone_lt : done.length + 1 < vals1.length := by
      have := congrArg List.length htrs'
      simp only [List.length_map, List.length_append, List.length_cons] at this
      omega
    have hnext_getD : TrnxRecord.encode (vals1.getD (done.length + 1) []) = next := by
      have h1 : (vals1.map TrnxRecord.encode).getD (done.length + 1) [] =
          TrnxRecord.encode (vals1.getD (done.length + 1) []) := by
        rw [List.getD_eq_getElem _ _ (by simp [hdone_lt]), List.getD_eq_getElem _ _ hdone_lt,
          List.getElem_map]
      rw [← h1, htrs', getD_append_right' _ _ _ _ (by simp)]
      simp
    have hmax := usize_max_ge
    have hrng1 := array_index_range trnx_rec 0#usize 16#usize (by decide) (by decide)
    set s1 := Slice.from ((trnx_rec.val.drop (0#usize).val).take ((16#usize).val - (0#usize).val))
      (by simp; scalar_tac)
    have hs1_val : s1.val = latL (tCard cur) := by
      simp [s1, htrec, ← latL_take, tCard]
    obtain ⟨b, mem1, cr_cnt1, tr_cnt1, ws1, heq, hbr, hwf1, hws1_l, hws1_b,
        hcr1, htr1, hc1, hc2, ht1, ht2, htw'⟩ :=
      branch_trct_spec hcur_len hG_pre hT_pre' hwf htw (by omega) (by omega) hsave hs1_val hcr htr
    obtain ⟨i, mem2, i1, s2, mem3, i2, s3, mem4,
        hi_eq, hmw1, hi1_eq, hrng2, hmw2, hi2_eq, hrng3, hmw3, hwf4⟩ :=
      mem_write_rec_spec hwf1 (by omega) (by omega) hcr1 htr1 hc1 hc2 ht1 ht2 hcur_len htrec hs1_val
    have hput5 := put_val save_card.to_slice 0#usize 16#usize s1
      (by simp [Array.to_slice, save_card.property])
    set s5 := Slice.from (putL save_card.to_slice.val (0#usize).val (16#usize).val s1.val)
      (by rw [length_putL _ _ _ _ (by simp [Array.to_slice, save_card.property])]; exact save_card.to_slice.property)
    have hset := set_dd_eq c ddTrnxArr
    obtain ⟨c2, hm03b, hrc2, hpos2, heof2, hfldt2, hxp, hxe, hxs, hcs, has, hd, hs, hh, ha⟩ :=
      @m03b_trnx_some trnx_file xref_file cust_file acct_file vals1 htrnx hv1 hser
        { c with m_dd := ddTrnxArr, m_oper := 82#u8, m_fldt := Array.repeat 1000#usize 32#u8 }
        (done.length + 1) rfl rfl heof hpos hdone_lt
    rw [hnext_getD] at hfldt2
    have heq00 : cbstm03a.eq_bytes c2.m_rc.to_slice (Array.make 2#usize [48#u8, 48#u8]).to_slice = .ok true := by
      rw [eq_bytes_eq, hrc2]; rfl
    have hrng10 := array_index_range c2.m_fldt 0#usize 350#usize (by decide) (by decide)
    set s10 := Slice.from ((c2.m_fldt.val.drop (0#usize).val).take ((350#usize).val - (0#usize).val))
      (by simp; scalar_tac)
    have hs10_val : s10.val = latL next := by
      simpa [s10] using hfldt2
    have hput11 := put_val trnx_rec.to_slice 0#usize 350#usize s10
      (by simp [Array.to_slice, trnx_rec.property])
    set s11 := Slice.from (putL trnx_rec.to_slice.val (0#usize).val (350#usize).val s10.val)
      (by rw [length_putL _ _ _ _ (by simp [Array.to_slice, trnx_rec.property])]; exact trnx_rec.to_slice.property)
    have hbody : cbstm03a.run_loop0.body trnx_file xref_file cust_file acct_file
        c mem trnx_rec save_card cr_cnt tr_cnt true true =
        .ok (.cont (c2, mem4, trnx_rec.from_slice s11, save_card.from_slice s5,
          cr_cnt1, tr_cnt1, true, true)) := by
      unfold cbstm03a.run_loop0.body
      rw [show Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddTrnxArr from rfl]
      rcases hbr with ⟨rfl, hadd, rfl, rfl⟩ | ⟨rfl, mem2_, hwt, hadd, rfl, rfl⟩
      · simp only [↓reduceIte, lift, bind_ok, Array.to_slice_mut, Aeneas.Std.uncurry_apply_pair,
          hrng1, heq, hadd, hi_eq, hmw1, hi1_eq, hrng2, hmw2, hi2_eq, hrng3, hmw3, hput5, hset, hm03b,
          heq00, hrng10, hput11]
      · simp only [↓reduceIte, lift, bind_ok, Array.to_slice_mut, Aeneas.Std.uncurry_apply_pair,
          hrng1, heq, hwt, hadd, hi_eq, hmw1, hi1_eq, hrng2, hmw2, hi2_eq, hrng3, hmw3, hput5, hset, hm03b,
          heq00, hrng10, hput11, Bool.false_eq_true]
    rw [run_loop0_step hbody]
    have htrec1 : (trnx_rec.from_slice s11).val = latL next := by
      rw [Array.from_slice_val _ _ (by simp [s11, Slice.from_val, length_putL, Array.to_slice, trnx_rec.property])]
      simp only [s11, Slice.from_val, Array.to_slice, hs10_val, uscalar_ofNat_val]
      exact putL_full _ _ 350 trnx_rec.property (by rw [length_latL, hnext_len])
    have hsave1 : (save_card.from_slice s5).val = latL (tCard ((done ++ [cur]).getLastD next)) := by
      rw [Array.from_slice_val _ _ (by simp [s5, Slice.from_val, length_putL, Array.to_slice, save_card.property])]
      simp only [s5, Slice.from_val, Array.to_slice, hs1_val, uscalar_ofNat_val, getLastD_snoc]
      exact putL_full _ _ 16 save_card.property (by rw [length_latL, length_tCard_of_eq hcur_len])
    have hcr1' : cr_cnt1.val = ((max 1 (grp (done ++ [cur])).length : Nat) : Int) := by
      rw [hcr1]; congr 1; omega
    obtain ⟨c', mem', trnx_rec', cr_cnt', tr_cnt', ws',
        hres, hwf', htw_fin, hws'_l, hws'_b, hcr', htr',
        hpos', heof', hxp', hxe', hxs', hcs', has', hd', hs', hh', ha'⟩ :=
      ih (done ++ [cur]) next htrs' c2 mem4
        (ws1 ++ recWrites (grp (done ++ [cur])).length ((grp (done ++ [cur])).getLastD []).length cur)
        (trnx_rec.from_slice s11) (save_card.from_slice s5) cr_cnt1 tr_cnt1
        (by simp [hpos2]) heof2 hwf4 htw'
        (by simp only [List.length_append, length_recWrites, List.length_singleton]; omega)
        (by rw [wsBytesLen_append, wsBytesLen_recWrites _ _ hcur_len, List.length_append, List.length_singleton]; omega)
        htrec1 hsave1 hcr1' htr1
    exact ⟨c', mem', trnx_rec', cr_cnt', tr_cnt', ws',
      hres, hwf', htw_fin, hws'_l, hws'_b, hcr', htr',
      hpos', heof',
      by rw [hxp', hxp], by rw [hxe', hxe], by rw [hxs', hxs],
      by rw [hcs', hcs], by rw [has', has],
      by rw [hd', hd], by rw [hs', hs], by rw [hh', hh], by rw [ha', ha]⟩

/-! ## 6. Private `ser_trnx` helper and top-level `run_loop0_spec` -/

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

set_option maxHeartbeats 1000000 in
private theorem put_unum_loop_spec (dst : Slice U8) (off n : Usize) (x : Nat) (m : U64)
    (h : off.val + n.val ≤ dst.val.length) (hm : m.val = x) :
    wp (cbstm03a.put_unum_loop dst off m n)
      (fun o => o = .ok (Slice.from (putL dst.val off.val n.val (zeroPad n.val x))
        (by rw [length_putL _ _ _ _ h]; exact dst.property))) := by
  have hd : dst.val.length ≤ Usize.max := dst.property
  simp only [cbstm03a.put_unum_loop]
  refine wp_loop (loop_shape _)
    (fun (s : Slice U8 × U64 × Usize) =>
      s.2.2.val ≤ n.val ∧
      s.2.1.val = x / 10 ^ (n.val - s.2.2.val) ∧
      s.1.val = dst.val.take (off.val + s.2.2.val) ++ zeroPad (n.val - s.2.2.val) x ++
        dst.val.drop (off.val + n.val))
    (fun s => s.2.2.val) ?_ _ ?_
  · rintro ⟨cur, w, i⟩ ⟨hi, hw, hcur⟩
    simp only at hi hw hcur
    have hcl : cur.val.length = dst.val.length := by
      rw [hcur, List.length_append, List.length_append, List.length_take, zeroPad_length,
        List.length_drop]; omega
    aeneas_wp [rust_loop_body, slice_update_eq, UScalar.cast_val_eq, hcl]
    by_cases h0 : 0 < i.val
    · obtain ⟨k, hk⟩ : ∃ k, i.val = k + 1 := ⟨i.val - 1, by omega⟩
      have hd10 : w.val % 10 < 10 := Nat.mod_lt _ (by norm_num)
      have h256 : w.val % 10 % 2 ^ 8 = w.val % 10 := Nat.mod_eq_of_lt (by omega)
      have hoi : off.val + (i.val - 1) < dst.val.length := by omega
      have hmax1 : off.val + (i.val - 1) ≤ Usize.max := by omega
      simp only [h0, hoi, hmax1, h256, show 1 ≤ i.val by omega, show ¬ (10 = 0) by norm_num,
        not_false_eq_true, show 48 + w.val % 10 ≤ 255 by omega, _root_.dite_true, _root_.ite_true,
        loopCls_cont, UScalar.ofNatCore_val_eq, Slice.from_val]
      refine ⟨⟨by omega, ?_, ?_⟩, by omega⟩
      · rw [hw, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
        congr 2; omega
      · rw [hcur, hk, Nat.add_sub_cancel]
        refine set_take_zeroPad dst.val off.val n.val k x _ (by omega) h ?_
        apply UScalar.eq_of_val_eq
        rw [UScalar.ofNatCore_val_eq, byteOf_val _ (by omega), hw, hk]
    · simp only [h0, _root_.ite_false, loopCls_done, Except.ok.injEq, Slice.eq_iff, Slice.from_val]
      have hi0 : i.val = 0 := by omega
      rw [hcur, hi0, Nat.add_zero, Nat.sub_zero, putL_of_len_eq _ _ _ _ (zeroPad_length _ _)]
  · refine ⟨le_refl _, by simp [hm], ?_⟩
    have hz : zeroPad 0 x = [] := by simp [zeroPad, zpad, Cobol.Digits.toDigits]
    rw [Nat.sub_self, hz, List.append_nil, List.take_append_drop]

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
    refine wp_mono (put_unum_loop_spec dst off n v.val.natAbs _ h ?_) ?_
    · simp only [IScalar.hcast_val_eq, IScalar.ofInt_val_eq, UScalarTy.U64_numBits_eq, Int.reducePow]
      omega
    · intro _ ho; exact ⟨_, ho, Slice.from_val _ _⟩
  · have hlt : (v < 0#i64) = False := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_false, wp_bind, wp_ok]
    refine wp_mono (put_unum_loop_spec dst off n v.val.natAbs _ h ?_) ?_
    · simp only [IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq, Int.reducePow]
      omega
    · intro _ ho; exact ⟨_, ho, Slice.from_val _ _⟩

private def sdigs (n : Nat) (v : Int) : List U8 :=
  zeroPad (n - 1) (v.natAbs / 10) ++ [byteOf (overpunch (decide (v < 0)) (v.natAbs % 10))]

private theorem length_sdigs (n : Nat) (v : Int) (hn : 0 < n) :
    (sdigs n v).length = n := by
  simp only [sdigs, List.length_append, zeroPad_length, List.length_singleton]; omega

private theorem zeroPad_succ_right (m x : Nat) :
    zeroPad (m + 1) x = zeroPad m (x / 10) ++ [byteOf (48 + x % 10)] := by
  simp only [zeroPad, zpad, toDigits_succ, List.map_append, List.map_cons, List.map_nil]

private theorem overpunch_lt (neg : Bool) (d : Nat) (hd : d < 10) : overpunch neg d < 256 := by
  unfold overpunch; split_ifs <;> omega

private theorem slice_index_usize_getD {α : Type _} [Inhabited α] (s : Slice α) (i : Usize) :
    Slice.index_usize s i =
      if i.val < s.val.length then .ok (s.val.getD i.val default)
      else .fail .arrayOutOfBounds := by
  simp only [Slice.index_usize, Slice.getElem?_Usize_eq]
  by_cases h : i.val < s.val.length
  · simp [h]
  · simp [h]

private theorem putL_zeroPad_getD (dst : List U8) (off n v : Nat)
    (hn : 0 < n) (_h : off + n ≤ dst.length) :
    (putL dst off n (zeroPad n v)).getD (off + n - 1) default = byteOf (48 + v % 10) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsplit : putL dst off (m + 1) (zeroPad (m + 1) v) =
      (dst.take off ++ zeroPad m (v / 10)) ++ byteOf (48 + v % 10) :: dst.drop (off + (m + 1)) := by
    rw [putL_of_len_eq _ _ _ _ (zeroPad_length _ _), zeroPad_succ_right]
    simp [List.append_assoc]
  have hpre : off + (m + 1) - 1 = (dst.take off ++ zeroPad m (v / 10)).length := by
    simp [zeroPad_length]; omega
  rw [hsplit, hpre]
  simp [List.getD_eq_getElem?_getD]

private theorem putL_zeroPad_set_last (dst : List U8) (off n : Nat) (v : Int) (c : U8)
    (hn : 0 < n) (_h : off + n ≤ dst.length)
    (hc : c = byteOf (overpunch (decide (v < 0)) (v.natAbs % 10))) :
    (putL dst off n (zeroPad n v.natAbs)).set (off + n - 1) c =
      putL dst off n (sdigs n v) := by
  subst hc
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsplit : putL dst off (m + 1) (zeroPad (m + 1) v.natAbs) =
      (dst.take off ++ zeroPad m (v.natAbs / 10)) ++
        byteOf (48 + v.natAbs % 10) :: dst.drop (off + (m + 1)) := by
    rw [putL_of_len_eq _ _ _ _ (zeroPad_length _ _), zeroPad_succ_right]
    simp [List.append_assoc]
  have hpre : off + (m + 1) - 1 = (dst.take off ++ zeroPad m (v.natAbs / 10)).length := by
    simp [zeroPad_length]; omega
  have hlen_enc : (sdigs (m + 1) v).length = m + 1 := length_sdigs (m + 1) v (by omega)
  rw [hsplit, hpre, Cobol.StmCore.set_append_cons,
    putL_of_len_eq _ _ _ _ hlen_enc]
  simp [sdigs, List.append_assoc]

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
  have hset : ∀ c : U8, c = byteOf (overpunch (decide (v.val < 0)) (v.val.natAbs % 10)) →
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
  all_goals rw [byteOf_val _ (overpunch_lt _ _ hmod)]
  · have : decide (v.val < 0) = true := decide_eq_true hv
    simp only [overpunch, this, hd0, uscalar_ofNat_val, _root_.ite_true]
  · have : decide (v.val < 0) = true := decide_eq_true hv
    simp only [overpunch, this, hd0, UScalar.ofNatCore_val_eq, _root_.ite_true, _root_.ite_false]; omega
  · have : decide (v.val < 0) = false := decide_eq_false hv
    simp only [overpunch, this, hd0, uscalar_ofNat_val, Bool.false_eq_true, _root_.ite_true, _root_.ite_false]
  · have : decide (v.val < 0) = false := decide_eq_false hv
    simp only [overpunch, this, hd0, UScalar.ofNatCore_val_eq, Bool.false_eq_true, _root_.ite_false]; omega

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

private theorem latL_map_ebc (l : List U8) :
    latL (l.map fun u => ebcdicOfLatin1 u.val) = l := by
  induction l with
  | nil => rfl
  | cons u us ih =>
    simp only [latL, List.map_cons]
    refine congrArg₂ List.cons ?_ ih
    apply UScalar.eq_of_val_eq
    rw [lat_val, cp037_roundtrip ⟨u.val, by have := u.hBounds; simpa using this⟩]

private theorem latL_encodeNum_unsigned {fmt : NumFmt}
    (hu : fmt.usage = .display) (hs : fmt.signed = false) (hd : 0 < fmt.digits) (v : Int) :
    latL (encodeNum {} fmt v) = zeroPad fmt.digits v.natAbs := by
  rw [latL_eq_u8Line, text_unsigned hu hs hd, u8Line, zeroPad]

private theorem latL_encodeNum_signed {fmt : NumFmt}
    (hu : fmt.usage = .display) (hs : fmt.signed = true)
    (hsep : fmt.signSep = false) (hlead : fmt.signLead = false) (v : Int) :
    latL (encodeNum {} fmt v) = sdigs fmt.digits v := by
  rw [latL_eq_u8Line, text_signed hu hs hsep hlead, u8Line, List.map_append,
    List.map_singleton, sdigs, zeroPad]

private theorem ser_trnx_val (r : cbstm03a.TrnxRecord) :
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
  simp (disch := decide) only [latL_encodeNum_unsigned, latL_encodeNum_signed]
  simp only [uscalar_ofNat_val]

/-- **Specification of `8500-READTRNX-READ` (`run_loop0`) followed by the final `write_trct`.** -/
theorem run_loop0_spec
    {trnx_file : Slice cbstm03a.TrnxRecord}
    {xref_file : Slice cbstm03a.CardXrefRecord}
    {cust_file : Slice cbstm03a.CustomerRecord}
    {acct_file : Slice cbstm03a.AccountRecord}
    {vals1 : List (List FVal)}
    (htrnx : trnx_file.val.map TrnxRecord.vals = vals1)
    (hv1 : ∀ v ∈ vals1, TrnxRecord.Valid v)
    (hne : vals1 ≠ [])
    (hG : (grp (vals1.map TrnxRecord.encode)).length ≤ 50)
    (hT : ∀ g ∈ grp (vals1.map TrnxRecord.encode), g.length ≤ 10)
    (c : cbstm03a.Ctx)
    (trnx_rec : Array U8 350#usize)
    (save_card : Array U8 16#usize)
    (hpos : c.trnx_pos.val = 1)
    (heof : c.trnx_eof = false)
    (htrec : trnx_rec.val = latL ((vals1.map TrnxRecord.encode).getD 0 []))
    (hsave : save_card.val = latL (tCard ((vals1.map TrnxRecord.encode).getD 0 []))) :
    ∃ c' mem' trnx_rec' cr_cnt' tr_cnt' mem1,
      cbstm03a.run_loop0 trnx_file xref_file cust_file acct_file
        c emptyMem trnx_rec save_card 1#i64 0#i64 true true =
        .ok (c', mem', trnx_rec', cr_cnt', tr_cnt', true) ∧
      cbstm03a.write_trct mem' cr_cnt' tr_cnt' = .ok mem1 ∧
      MemLoaded mem1 (grp (vals1.map TrnxRecord.encode)) ∧
      cr_cnt'.val = ((grp (vals1.map TrnxRecord.encode)).length : Int) ∧
      tr_cnt'.val = (((grp (vals1.map TrnxRecord.encode)).getLastD []).length : Int) ∧
      c'.trnx_pos.val = vals1.length ∧
      c'.trnx_eof = true ∧
      c'.xref_pos = c.xref_pos ∧ c'.xref_eof = c.xref_eof ∧
      c'.xref_status = c.xref_status ∧ c'.cust_status = c.cust_status ∧
      c'.acct_status = c.acct_status ∧
      c'.displays = c.displays ∧ c'.stmt = c.stmt ∧ c'.html = c.html ∧
      c'.abended = c.abended := by
  have h500 := trs_length_le_500 hG hT
  have hmax := usize_max_ge
  have htrs_ne : vals1.map TrnxRecord.encode ≠ [] := by simp [hne]
  obtain ⟨cur, rest, htrs_eq⟩ := List.exists_cons_of_ne_nil htrs_ne
  have hcur0 : (vals1.map TrnxRecord.encode).getD 0 [] = cur := by simp [htrs_eq]
  rw [hcur0] at htrec hsave
  obtain ⟨c', mem', trnx_rec', cr_cnt', tr_cnt', ws',
      hloop, hwf', htw', hws'_l, hws'_b, hcr', htr',
      hpos', heof', hxp, hxe, hxs, hcs, has, hd, hs, hh, ha⟩ :=
    @run_loop0_aux trnx_file xref_file cust_file acct_file vals1 htrnx hv1 ser_trnx_val hG hT
      rest [] cur (by simpa using htrs_eq) c emptyMem [] trnx_rec save_card 1#i64 0#i64
      hpos heof memWF_empty tableWrites_nil (by simp) (by simp) htrec hsave rfl rfl
  obtain ⟨gs0, g, hgs, _⟩ := grp_snoc_form (vals1.map TrnxRecord.encode) htrs_ne
  rw [hgs] at htw' hcr' htr' hG
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel, getLastD_snoc] at htw' hcr' htr' hG
  have hg_mem : g ∈ gs0 ++ [g] := by simp
  obtain ⟨hg1, hg10, _⟩ := htw'.1.2 g hg_mem
  obtain ⟨mem1, hwt, hwf1⟩ := write_trct_spec mem' ws' cr_cnt' tr_cnt' hwf'
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have htr_toNat : tr_cnt'.val.toNat = g.length := by omega
  rw [hcr', htr_toNat] at hwf1
  have htw1 := tableWrites_finish htw'
  have hloaded : MemLoaded mem1 (grp (vals1.map TrnxRecord.encode)) := by
    rw [hgs]
    exact memLoaded_of_tableWrites hwf1 htw1
  refine ⟨c', mem', trnx_rec', cr_cnt', tr_cnt', mem1,
    hloop, hwt, hloaded, ?_, ?_, hpos', heof', hxp, hxe, hxs, hcs, has, hd, hs, hh, ha⟩
  · rw [hgs, List.length_append, List.length_singleton]; exact hcr'
  · rw [hgs, getLastD_snoc]; exact htr'

/-- Combined specification from the initial `call_m03b` read through `run_loop0` and `write_trct`,
matching the hypotheses of `RustRun5.run_eq_of_parts`. -/
theorem run_load_phase_spec
    {trnx_file : Slice cbstm03a.TrnxRecord}
    {xref_file : Slice cbstm03a.CardXrefRecord}
    {cust_file : Slice cbstm03a.CustomerRecord}
    {acct_file : Slice cbstm03a.AccountRecord}
    {vals1 vals2 vals3 vals4 : List (List FVal)}
    (htrnx : trnx_file.val.map TrnxRecord.vals = vals1)
    (hv1 : ∀ v ∈ vals1, TrnxRecord.Valid v)
    (hD : EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4)
    (c : cbstm03a.Ctx)
    (hdd : c.m_dd = Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8])
    (hpos : c.trnx_pos = 0#usize)
    (heof : c.trnx_eof = false) :
    ∃ (c1 c2 : cbstm03a.Ctx) (s4 s7 : Slice U8) (mem mem1 : cbstm03a.Mem)
      (trnx_rec2 : Array U8 350#usize) (cr_cnt tr_cnt : Std.I64),
      cbstm03a.call_m03b { c with m_oper := 82#u8, m_fldt := Array.repeat 1000#usize 32#u8 }
        trnx_file xref_file cust_file acct_file = .ok c1 ∧
      cbstm03a.rc_ok c1 = .ok true ∧
      (∀ s : Slice U8, s.val = (c1.m_fldt.val.drop 0).take 350 →
        cbstm03a.put (Array.repeat 350#usize 32#u8).to_slice 0#usize 350#usize s = .ok s4) ∧
      (∀ s : Slice U8, s.val = (((Array.repeat 350#usize 32#u8).from_slice s4).val.drop 0).take 16 →
        cbstm03a.put (Array.repeat 16#usize 32#u8).to_slice 0#usize 16#usize s = .ok s7) ∧
      cbstm03a.run_loop0 trnx_file xref_file cust_file acct_file c1 emptyMem
        ((Array.repeat 350#usize 32#u8).from_slice s4)
        ((Array.repeat 16#usize 32#u8).from_slice s7) 1#i64 0#i64 true true =
        .ok (c2, mem, trnx_rec2, cr_cnt, tr_cnt, true) ∧
      cbstm03a.write_trct mem cr_cnt tr_cnt = .ok mem1 ∧
      MemLoaded mem1 (grp (vals1.map TrnxRecord.encode)) ∧
      cr_cnt.val = ((grp (vals1.map TrnxRecord.encode)).length : Int) ∧
      tr_cnt.val = (((grp (vals1.map TrnxRecord.encode)).getLastD []).length : Int) ∧
      c2.trnx_pos.val = vals1.length ∧
      c2.trnx_eof = true ∧
      c2.xref_pos = c.xref_pos ∧ c2.xref_eof = c.xref_eof ∧
      c2.displays = c.displays ∧ c2.stmt = c.stmt ∧ c2.html = c.html ∧
      c2.abended = c.abended := by
  obtain ⟨hne, _, hG, hT, _⟩ := hD
  have hlen_pos : 0 < vals1.length := List.length_pos_iff.mpr hne
  obtain ⟨c1, hm0, hrc1_arr, hpos1, heof1, hfldt1,
      hxp1, hxe1, hxs1, hcs1, has1, hd1, hs1, hh1, ha1⟩ :=
    @m03b_trnx_some trnx_file xref_file cust_file acct_file vals1 htrnx hv1 ser_trnx_val
      { c with m_oper := 82#u8, m_fldt := Array.repeat 1000#usize 32#u8 }
      0 hdd rfl heof (by simp [hpos]) hlen_pos
  have hrc1 : cbstm03a.rc_ok c1 = .ok true := by
    unfold cbstm03a.rc_ok
    simp [lift, bind_ok, eq_bytes_eq, hrc1_arr]
  have htr0_eq : (vals1.map TrnxRecord.encode).getD 0 [] = TrnxRecord.encode (vals1.getD 0 []) := by
    rw [List.getD_eq_getElem _ _ (by simp [hlen_pos]), List.getD_eq_getElem _ _ hlen_pos,
      List.getElem_map]
  have htr0_len : ((vals1.map TrnxRecord.encode).getD 0 []).length = 350 := by
    rw [htr0_eq]
    exact trnx_length (hv1 _ (getD_mem_of_lt hlen_pos))
  rw [← htr0_eq] at hfldt1
  set r0 := (vals1.map TrnxRecord.encode).getD 0 []
  let s4 : Slice U8 := Slice.from (putL (Array.repeat 350#usize 32#u8).to_slice.val 0 350 (latL r0))
    (by simp [length_putL, Array.to_slice, Array.repeat_val]; scalar_tac)
  have hp350 : ∀ s : Slice U8, s.val = (c1.m_fldt.val.drop 0).take 350 →
      cbstm03a.put (Array.repeat 350#usize 32#u8).to_slice 0#usize 350#usize s = .ok s4 := by
    intro s hs_val
    rw [put_val _ _ _ _ (by simp [Array.to_slice, Array.repeat_val])]
    congr 1
    rw [Slice.eq_iff, Slice.from_val, hs_val, hfldt1]
    simp [s4]
  have htrec1 : ((Array.repeat 350#usize 32#u8).from_slice s4).val = latL r0 := by
    rw [Array.from_slice_val _ _ (by simp [s4, Slice.from_val, length_putL, Array.to_slice, Array.repeat_val])]
    simp only [s4, Slice.from_val, Array.to_slice]
    exact putL_full _ _ 350 (by simp [Array.repeat_val]) (by rw [length_latL, htr0_len])
  let s7 : Slice U8 := Slice.from (putL (Array.repeat 16#usize 32#u8).to_slice.val 0 16 (latL (tCard r0)))
    (by simp [length_putL, Array.to_slice, Array.repeat_val]; scalar_tac)
  have hp16 : ∀ s : Slice U8, s.val = (((Array.repeat 350#usize 32#u8).from_slice s4).val.drop 0).take 16 →
      cbstm03a.put (Array.repeat 16#usize 32#u8).to_slice 0#usize 16#usize s = .ok s7 := by
    intro s hs_val
    rw [put_val _ _ _ _ (by simp [Array.to_slice, Array.repeat_val])]
    congr 1
    rw [Slice.eq_iff]
    simp [s7, hs_val, htrec1, ← latL_take, tCard]
  have hsave1 : ((Array.repeat 16#usize 32#u8).from_slice s7).val = latL (tCard r0) := by
    rw [Array.from_slice_val _ _ (by simp [s7, Slice.from_val, length_putL, Array.to_slice, Array.repeat_val])]
    simp only [s7, Slice.from_val, Array.to_slice]
    exact putL_full _ _ 16 (by simp [Array.repeat_val]) (by rw [length_latL, length_tCard_of_eq htr0_len])
  obtain ⟨c2, mem, trnx_rec2, cr_cnt, tr_cnt, mem1,
      hl0, hwtrct, hloaded, hcr, htr, hpos2, heof2,
      hxp2, hxe2, _, _, _, hd2, hs2, hh2, ha2⟩ :=
    @run_loop0_spec trnx_file xref_file cust_file acct_file vals1 htrnx hv1 hne hG hT
      c1 ((Array.repeat 350#usize 32#u8).from_slice s4)
      ((Array.repeat 16#usize 32#u8).from_slice s7)
      hpos1 heof1 htrec1 hsave1
  exact ⟨c1, c2, s4, s7, mem, mem1, trnx_rec2, cr_cnt, tr_cnt,
    hm0, hrc1, hp350, hp16, hl0, hwtrct, hloaded, hcr, htr, hpos2, heof2,
    by rw [hxp2, hxp1], by rw [hxe2, hxe1],
    by rw [hd2, hd1], by rw [hs2, hs1], by rw [hh2, hh1], by rw [ha2, ha1]⟩

end EquivLean.Modernize.Cbstm03a.Rust
