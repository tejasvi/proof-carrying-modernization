import EquivLean.Modernize.Cbstm03a.RustRun1
import EquivLean.Modernize.Cbstm03a.RustRun3
import EquivLean.Modernize.Cbstm03a.Glue

open Aeneas Aeneas.Std Result EquivLean EquivLean.Aeneas
open Cobol Cobol.StmCore EquivLean.Cobol.Rec
open EquivLean.Modernize.Cbstm03a.StmBridge EquivLean.Modernize.Cbstm03a.Model
open EquivLean.Modernize.Cbstm03a.Glue

set_option maxRecDepth 100000

namespace EquivLean.Modernize.Cbstm03a.Rust

/-! ## 1. Statement and HTML output helpers for `write_trans` and `trnx_get` -/

/-- `c'` extends `c` by appending `stmts` (EBCDIC lines, converted via `cp037Code`) to `stmt`
and `htmls` to `html`, preserving all other context fields. -/
def CtxExt (c c' : cbstm03a.Ctx) (stmts htmls : List (List UInt8)) : Prop :=
  c'.stmt.val.map (fun l => l.val.map (·.val)) =
    c.stmt.val.map (fun l => l.val.map (·.val)) ++ stmts.map (·.map cp037Code) ∧
  c'.stmt.val.length = c.stmt.val.length + stmts.length ∧
  c'.html.val.map (fun l => l.val.map (·.val)) =
    c.html.val.map (fun l => l.val.map (·.val)) ++ htmls.map (·.map cp037Code) ∧
  c'.html.val.length = c.html.val.length + htmls.length ∧
  c'.displays = c.displays ∧ c'.abended = c.abended ∧
  c'.xref_pos = c.xref_pos ∧ c'.xref_eof = c.xref_eof

theorem CtxExt_refl (c : cbstm03a.Ctx) : CtxExt c c [] [] := by
  simp [CtxExt]

theorem CtxExt_trans {c1 c2 c3 : cbstm03a.Ctx} {s1 s2 h1 h2 : List (List UInt8)}
    (H1 : CtxExt c1 c2 s1 h1) (H2 : CtxExt c2 c3 s2 h2) :
    CtxExt c1 c3 (s1 ++ s2) (h1 ++ h2) := by
  obtain ⟨hs1, hsl1, hh1, hhl1, hd1, ha1, hxp1, hxe1⟩ := H1
  obtain ⟨hs2, hsl2, hh2, hhl2, hd2, ha2, hxp2, hxe2⟩ := H2
  refine ⟨?_, by simp [hsl1, hsl2]; omega, ?_, by simp [hhl1, hhl2]; omega,
    hd2.trans hd1, ha2.trans ha1, hxp2.trans hxp1, hxe2.trans hxe1⟩
  · rw [hs2, hs1, List.map_append, List.append_assoc]
  · rw [hh2, hh1, List.map_append, List.append_assoc]

private theorem CtxExt_cons_html {c0 c1 c2 : cbstm03a.Ctx} {ss hs : List (List UInt8)} {b : List UInt8}
    (H1 : CtxExt c0 c1 [] [b]) (H2 : CtxExt c1 c2 ss hs) :
    CtxExt c0 c2 ss (b :: hs) := by
  simpa only [List.nil_append, List.singleton_append] using CtxExt_trans H1 H2

private theorem CtxExt_cons_stmt {c0 c1 c2 : cbstm03a.Ctx} {ss hs : List (List UInt8)} {b : List UInt8}
    (H1 : CtxExt c0 c1 [b] []) (H2 : CtxExt c1 c2 ss hs) :
    CtxExt c0 c2 (b :: ss) hs := by
  simpa only [List.nil_append, List.singleton_append] using CtxExt_trans H1 H2

private theorem array_from_slice_eq {α : Type _} [Inhabited α] {n : Usize}
    (a : Array α n) (s : Slice α) :
    a.from_slice s = if h : s.val.length = n.val then Array.from s.val h else a := by
  simp [Array.from_slice]

private theorem sw_eq (c : cbstm03a.Ctx) (line : Array U8 80#usize)
    (hcap : c.stmt.val.length + 1 ≤ Usize.max) :
    cbstm03a.sw c line = .ok { c with stmt :=
      (alloc.vec.Vec.from (c.stmt.val ++ [alloc.vec.Vec.from line.val (by scalar_tac)])
        (by simp; omega)) } := by
  refine eq_ok_of_wp ?_
  unfold cbstm03a.sw
  aeneas_wp [vb_eq, Array.to_slice, hcap]
  rw [dite_eq_left (by omega)]
  trivial

private theorem hw_eq (c : cbstm03a.Ctx) (lit : Slice U8)
    (hcap : c.html.val.length + 1 ≤ Usize.max) :
    cbstm03a.hw c lit = .ok { c with html :=
      (alloc.vec.Vec.from (c.html.val ++ [alloc.vec.Vec.from
        (putL (List.replicate 100 32#u8) 0 100 lit.val)
        (by
          rw [length_putL _ _ _ _ (by simp)]
          have h2 := usize_max_ge
          simp; omega)]) (by simp; omega)) } := by
  refine eq_ok_of_wp ?_
  unfold cbstm03a.hw
  simp only [lift, bind_ok, Array.to_slice_mut, Aeneas.Std.uncurry_apply_pair]
  rw [put_val _ _ _ _ (by simp [Array.to_slice, Array.repeat_val]), bind_ok]
  aeneas_wp [vb_eq, Array.to_slice, Array.repeat_val,
    Array.from_val, array_from_slice_eq, Slice.from_val, length_putL, List.length_replicate,
    uscalar_ofNat_val, Nat.reduceAdd, Nat.reduceLeDiff, ↓reduceDIte, hcap]
  rw [dite_eq_left (by omega)]
  trivial

private theorem sw_ext (c : cbstm03a.Ctx) (line : Array U8 80#usize) (bs : List UInt8)
    (hl : line.val = latL bs) (hcap : c.stmt.val.length + 1 ≤ Usize.max) :
    ∃ c', cbstm03a.sw c line = .ok c' ∧ CtxExt c c' [bs] [] := by
  refine ⟨_, sw_eq c line hcap, ?_⟩
  simp [CtxExt, hl, latL_val]

private theorem hw_ext (c : cbstm03a.Ctx) (lit : Slice U8) (bs : List UInt8)
    (hlit : putL (List.replicate 100 32#u8) 0 100 lit.val = latL bs)
    (hcap : c.html.val.length + 1 ≤ Usize.max) :
    ∃ c', cbstm03a.hw c lit = .ok c' ∧ CtxExt c c' [] [bs] := by
  refine ⟨_, hw_eq c lit hcap, ?_⟩
  simp only [CtxExt, alloc.vec.Vec.from_val, List.map_append, List.map_cons,
    List.map_nil, List.length_append, List.length_singleton, List.length_nil, List.append_nil,
    Nat.add_zero, hlit, latL_val, and_self]

private theorem step_hw {α : Type} {f : cbstm03a.Ctx → α}
    {c : cbstm03a.Ctx} {ss hs : List (List UInt8)} {n : Nat}
    (hcap : c.html.val.length + (n + 1) ≤ Usize.max)
    (lit : Slice U8) (bs : List UInt8)
    (hlit : putL (List.replicate 100 32#u8) 0 100 lit.val = latL bs)
    {k : cbstm03a.Ctx → Std.Result α}
    (hk : ∀ c1, c1.stmt.val.length = c.stmt.val.length →
      c1.html.val.length + n ≤ Usize.max →
      ∃ res, k c1 = .ok (f res) ∧ CtxExt c1 res ss hs) :
    ∃ res, Std.bind (cbstm03a.hw c lit) k = .ok (f res) ∧ CtxExt c res ss (bs :: hs) := by
  obtain ⟨c1, h1, he1⟩ := hw_ext c lit bs hlit (by omega)
  rw [h1, bind_ok]
  have hs1 : c1.stmt.val.length = c.stmt.val.length := by
    have := he1.2.1; simpa only [List.length_nil, Nat.add_zero] using this
  have hcap1 : c1.html.val.length + n ≤ Usize.max := by
    have := he1.2.2.2.1; simp only [List.length_singleton] at this; omega
  obtain ⟨res, hres, he2⟩ := hk c1 hs1 hcap1
  exact ⟨res, hres, CtxExt_cons_html he1 he2⟩

private theorem last_hw_map {α : Type} (f : cbstm03a.Ctx → α)
    {c : cbstm03a.Ctx} (hcap : c.html.val.length + 1 ≤ Usize.max)
    (lit : Slice U8) (bs : List UInt8)
    (hlit : putL (List.replicate 100 32#u8) 0 100 lit.val = latL bs) :
    ∃ c1, Std.bind (cbstm03a.hw c lit) (fun c1 => Result.ok (f c1)) = .ok (f c1) ∧
      CtxExt c c1 [] [bs] := by
  obtain ⟨c1, h1, he1⟩ := hw_ext c lit bs hlit hcap
  rw [h1, bind_ok]
  exact ⟨c1, rfl, he1⟩

private theorem step_sw {α : Type} {f : cbstm03a.Ctx → α}
    {c : cbstm03a.Ctx} {ss hs : List (List UInt8)} {ns : Nat}
    (hcaps : c.stmt.val.length + (ns + 1) ≤ Usize.max)
    (line : Array U8 80#usize) (bs : List UInt8) (hl : line.val = latL bs)
    {k : cbstm03a.Ctx → Std.Result α}
    (hk : ∀ c1, c1.stmt.val.length + ns ≤ Usize.max →
      c1.html.val.length = c.html.val.length →
      ∃ res, k c1 = .ok (f res) ∧ CtxExt c1 res ss hs) :
    ∃ res, Std.bind (cbstm03a.sw c line) k = .ok (f res) ∧ CtxExt c res (bs :: ss) hs := by
  obtain ⟨c1, h1, he1⟩ := sw_ext c line bs hl (by omega)
  rw [h1, bind_ok]
  have hcaps1 : c1.stmt.val.length + ns ≤ Usize.max := by
    have := he1.2.1; simp only [List.length_singleton] at this; omega
  have hh1 : c1.html.val.length = c.html.val.length := by
    have := he1.2.2.2.1; simpa only [List.length_nil, Nat.add_zero] using this
  obtain ⟨res, hres, he2⟩ := hk c1 hcaps1 hh1
  exact ⟨res, hres, CtxExt_cons_stmt he1 he2⟩

private theorem hw_LTRS : putL (List.replicate 100 32#u8) 0 100 cbstm03a.LTRS.val = latL hLTRS := by decide +kernel
private theorem hw_LTRE : putL (List.replicate 100 32#u8) 0 100 cbstm03a.LTRE.val = latL hLTRE := by decide +kernel
private theorem hw_LTDE : putL (List.replicate 100 32#u8) 0 100 cbstm03a.LTDE.val = latL hLTDE := by decide +kernel
private theorem hw_L10 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L10.val = latL hL10 := by decide +kernel
private theorem hw_L58 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L58.val = latL hL58 := by decide +kernel
private theorem hw_L61 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L61.val = latL hL61 := by decide +kernel
private theorem hw_L64 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L64.val = latL hL64 := by decide +kernel
private theorem hw_L75 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L75.val = latL hL75 := by decide +kernel
private theorem hw_L78 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L78.val = latL hL78 := by decide +kernel
private theorem hw_L79 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L79.val = latL hL79 := by decide +kernel
private theorem hw_L80 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L80.val = latL hL80 := by decide +kernel

private theorem latL_tP : [60#u8, 112#u8, 62#u8] = latL tP := by decide +kernel
private theorem tokB_92_tP : tokB 92 tP = tP := by decide +kernel
private theorem length_tP : tP.length = 3 := by decide +kernel
private theorem latL_tEndP : [60#u8, 47#u8, 112#u8, 62#u8] = latL tEndP := by decide +kernel
private theorem tokB_92_tEndP : tokB 92 tEndP = tEndP := by decide +kernel
private theorem length_tEndP : tEndP.length = 4 := by decide +kernel

private theorem ovw_sp_split (piece : List UInt8) (n : Nat) (h : piece.length ≤ n) :
    ovw piece (sp n) = piece ++ sp (n - piece.length) := by
  rw [ovw_eq_take_drop, List.take_of_length_le (by simp [sp, h])]
  simp [sp, List.drop_replicate]

private theorem html_p_line_tP_star_ext
    (c : cbstm03a.Ctx) (pre data delim : Slice U8) (bs : List UInt8)
    (hpre : pre.val = [60#u8, 112#u8, 62#u8])
    (hdata : data.val = latL bs) (hbs_len : bs.length ≤ 80)
    (hdelim : delim.val = [42#u8])
    (hcap : c.html.val.length + 1 ≤ Usize.max) :
    ∃ c', cbstm03a.html_p_line c pre data delim false = .ok c' ∧
      CtxExt c c' [] [hfield tP (tokB 92 bs) tEndP] := by
  have hmax := usize_max_ge
  let r := Array.repeat 100#usize 32#u8
  let s1 := (Array.make 1#usize [42#u8]).to_slice
  have hs1 : s1.val = [lat 92] := by decide +kernel
  have hr_val : r.to_slice.val = latL ([] ++ sp 100) := by decide +kernel
  obtain ⟨s2, p, hsp1, hs2_val, hp_val⟩ :=
    str_part_single_ovw r.to_slice 0#usize pre s1 92 [] (sp 100) tP hs1 hr_val rfl
      (by rw [hpre, latL_tP]) (by rw [length_tP]; omega)
  rw [tokB_92_tP, List.nil_append, ovw_sp_split tP 100 (by rw [length_tP]; omega)] at hs2_val
  rw [tokB_92_tP, length_tP] at hp_val
  simp only [List.length_nil, sp, List.length_replicate, Nat.zero_add] at hp_val
  let r1 := r.from_slice s2
  have hr1_val : r1.to_slice.val = latL (tP ++ sp 97) := by
    rw [Array.to_slice, Slice.from_val,
      Array.from_slice_val _ _ (by rw [hs2_val, length_latL]; simp [length_tP, sp])]
    exact hs2_val
  have htok_le : (tokB 92 bs).length ≤ bs.length := (tokB_props 92 bs).1
  obtain ⟨s4, p1, hsp2, hs4_val, hp1_val⟩ :=
    str_part_single_ovw r1.to_slice p data delim 92 tP (sp 97) bs
      (by rw [hdelim]; decide +kernel) hr1_val (by rw [length_tP]; exact hp_val) hdata (by omega)
  rw [ovw_sp_split (tokB 92 bs) 97 (by omega), ← List.append_assoc] at hs4_val
  let r2 := r1.from_slice s4
  have hr2_val : r2.to_slice.val = latL ((tP ++ tokB 92 bs) ++ sp (97 - (tokB 92 bs).length)) := by
    rw [Array.to_slice, Slice.from_val,
      Array.from_slice_val _ _ (by rw [hs4_val, length_latL]; simp [length_tP, sp]; omega)]
    exact hs4_val
  have hp1_len : p1.val = (tP ++ tokB 92 bs).length := by
    rw [hp1_val, List.length_append, length_tP]
    have hsp97 : (sp 97).length = 97 := by simp [sp]
    rw [hsp97]; omega
  let s6 := (Array.make 4#usize [60#u8, 47#u8, 112#u8, 62#u8]).to_slice
  obtain ⟨s8, p3, hsp3, hs8_val, _⟩ :=
    str_part_single_ovw r2.to_slice p1 s6 s1 92 (tP ++ tokB 92 bs) (sp (97 - (tokB 92 bs).length))
      tEndP hs1 hr2_val hp1_len (by simp [s6, Array.to_slice, latL_tEndP]) (by rw [length_tEndP]; omega)
  rw [tokB_92_tEndP] at hs8_val
  have hovw_end : (tP ++ tokB 92 bs) ++ ovw tEndP (sp (97 - (tokB 92 bs).length)) =
      hfield tP (tokB 92 bs) tEndP := by
    unfold hfield
    rw [ovw_sp_split (tP ++ tokB 92 bs ++ tEndP) 100
      (by simp only [List.length_append, length_tP, length_tEndP]; omega),
      ovw_sp_split tEndP (97 - (tokB 92 bs).length)
      (by rw [length_tEndP]; omega)]
    simp only [List.append_assoc, List.length_append, length_tP, length_tEndP]
    have hsub : 100 - (3 + ((tokB 92 bs).length + 4)) = 97 - (tokB 92 bs).length - 4 := by omega
    rw [hsub]
  rw [hovw_end] at hs8_val
  let r3 := r2.from_slice s8
  have hr3_val : r3.val = latL (hfield tP (tokB 92 bs) tEndP) := by
    rw [Array.from_slice_val _ _ (by rw [hs8_val, length_latL]; simp [hfield, length_ovw, sp])]
    exact hs8_val
  have hvb := vb_eq r3.to_slice
  dsimp only [r, s1, r1, r2, s6, r3] at hsp1 hsp2 hsp3 hvb
  have hcap_lt : c.html.val.length < Usize.max := by omega
  have hpush_ok : ∃ c' : cbstm03a.Ctx, cbstm03a.html_p_line c pre data delim false = .ok c' ∧
      c'.stmt = c.stmt ∧ c'.displays = c.displays ∧ c'.abended = c.abended ∧
      c'.xref_pos = c.xref_pos ∧ c'.xref_eof = c.xref_eof ∧
      c'.html.val = c.html.val ++ [alloc.vec.Vec.from r3.to_slice.val (by scalar_tac)] := by
    refine exists_ok_of_wp ?_
    unfold cbstm03a.html_p_line
    aeneas_wp [Array.to_slice_mut, hsp1, hsp2, Bool.false_eq_true, hsp3, hvb, hcap_lt]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, by simp [r, r1, r2, r3]⟩
  obtain ⟨c', hc', hst_c, hd_c, ha_c, hxp_c, hxe_c, hhtml_c⟩ := hpush_ok
  refine ⟨c', hc', ?_⟩
  simp [CtxExt, hst_c, hd_c, ha_c, hxp_c, hxe_c, hhtml_c, Array.to_slice, hr3_val, latL_val]

private theorem step_tP_star {α : Type} {f : cbstm03a.Ctx → α}
    {c : cbstm03a.Ctx} {ss hs : List (List UInt8)} {m : Usize} {cap : Nat}
    (hcap : c.html.val.length + (cap + 1) ≤ Usize.max)
    (arr : Array U8 m) (bs : List UInt8) (hbs : arr.val = latL bs) (hbs_len : bs.length ≤ 80)
    {k : cbstm03a.Ctx → Std.Result α}
    (hk : ∀ c1, c1.stmt.val.length = c.stmt.val.length →
      c1.html.val.length + cap ≤ Usize.max →
      ∃ res, k c1 = .ok (f res) ∧ CtxExt c1 res ss hs) :
    ∃ res,
      Std.bind (lift (Array.to_slice (Array.make 3#usize [ 60#u8, 112#u8, 62#u8 ]))) (fun s7 =>
        Std.bind (lift (Array.to_slice arr)) (fun s8 =>
          Std.bind (lift (Array.to_slice (Array.make 1#usize [ 42#u8 ]))) (fun s9 =>
            Std.bind (cbstm03a.html_p_line c s7 s8 s9 false) k))) = .ok (f res) ∧
      CtxExt c res ss (hfield tP (tokB 92 bs) tEndP :: hs) := by
  simp only [lift, bind_ok]
  obtain ⟨c1, h1, he1⟩ := html_p_line_tP_star_ext c
    (Array.make 3#usize [60#u8, 112#u8, 62#u8]).to_slice arr.to_slice
    (Array.make 1#usize [42#u8]).to_slice bs rfl
    (by simp [Array.to_slice, hbs]) hbs_len rfl (by omega)
  rw [h1, bind_ok]
  have hs1 : c1.stmt.val.length = c.stmt.val.length := by
    have := he1.2.1; simpa only [List.length_nil, Nat.add_zero] using this
  have hcap1 : c1.html.val.length + cap ≤ Usize.max := by
    have := he1.2.2.2.1; simp only [List.length_singleton] at this; omega
  obtain ⟨res, hres, he2⟩ := hk c1 hs1 hcap1
  exact ⟨res, hres, CtxExt_cons_html he1 he2⟩

/-! ## 2. `st_line` on lines 12, 14, 140, 15 -/

private theorem prod_casesOn_mk {α β : Type _} {γ : α × β → Sort _}
    (a : α) (b : β) (f : (x : α) → (y : β) → γ (x, y)) :
    Prod.casesOn (motive := γ) (a, b) f = f a b := rfl

private theorem ok_array_from_eq {n : Usize} {a b : List U8} {ha : a.length = n.val} {hb : b.length = n.val}
    (h : a = b) :
    (Except.ok (Array.from a ha) : Except Error (Array U8 n)) = Except.ok (Array.from b hb) := by
  subst h; rfl

private theorem putL_exact (pre src post : List U8) (off len : Nat)
    (hpre : pre.length = off) (hsrc : src.length = len) :
    putL (pre ++ post) off len src = pre ++ src ++ post.drop len := by
  unfold putL
  rw [List.take_left' hpre, List.take_of_length_le (by rw [hsrc]), hsrc, Nat.sub_self,
    List.replicate_zero, List.append_nil, ← hpre, ← List.drop_drop, List.drop_left]

private theorem putL_zero_exact (src post : List U8) (len : Nat) (hsrc : src.length = len) :
    putL post 0 len src = src ++ post.drop len := by
  have := putL_exact [] src post 0 len rfl hsrc
  simpa using this

private theorem take_putL_zero (dst src : List U8) (k : Nat) (hs : src.length = k) :
    (putL dst 0 k src).take k = src := by
  subst hs
  simp [putL]

private theorem st_line_12_eq (st : cbstm03a.St) :
    cbstm03a.st_line 12#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← cbstm03a.fill s 0#usize 80#usize 45#u8
      Result.ok (to_slice_mut_back s1)) := rfl

private theorem st_line_14_eq (st : cbstm03a.St) :
    cbstm03a.st_line 14#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← lift (Array.to_slice st.tranid)
      let s2 ← cbstm03a.put s 0#usize 16#usize s1
      let l1 := to_slice_mut_back s2
      let l2 ← Array.update l1 16#usize 32#u8
      let (s3, to_slice_mut_back1) ← lift (Array.to_slice_mut l2)
      let s4 ← lift (Array.to_slice st.trandt)
      let s5 ← cbstm03a.put s3 17#usize 49#usize s4
      let l3 := to_slice_mut_back1 s5
      let l4 ← Array.update l3 66#usize 36#u8
      let (s6, to_slice_mut_back2) ← lift (Array.to_slice_mut l4)
      let s7 ← lift (Array.to_slice st.tranamt)
      let s8 ← cbstm03a.put s6 67#usize 13#usize s7
      Result.ok (to_slice_mut_back2 s8)) := rfl

private theorem st_line_140_eq (st : cbstm03a.St) :
    cbstm03a.st_line 140#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← lift (Array.to_slice (Array.make 10#usize [
        84#u8, 111#u8, 116#u8, 97#u8, 108#u8, 32#u8, 69#u8, 88#u8, 80#u8, 58#u8 ]))
      let s2 ← cbstm03a.put s 0#usize 10#usize s1
      let l1 := to_slice_mut_back s2
      let l2 ← Array.update l1 66#usize 36#u8
      let (s3, to_slice_mut_back1) ← lift (Array.to_slice_mut l2)
      let s4 ← lift (Array.to_slice st.total_tramt)
      let s5 ← cbstm03a.put s3 67#usize 13#usize s4
      Result.ok (to_slice_mut_back1 s5)) := rfl

private theorem st_line_15_eq (st : cbstm03a.St) :
    cbstm03a.st_line 15#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← cbstm03a.fill s 0#usize 32#usize 42#u8
      let l1 := to_slice_mut_back s1
      let (s2, to_slice_mut_back1) ← lift (Array.to_slice_mut l1)
      let s3 ← lift (Array.to_slice (Array.make 16#usize [
        69#u8, 78#u8, 68#u8, 32#u8, 79#u8, 70#u8, 32#u8, 83#u8, 84#u8, 65#u8,
        84#u8, 69#u8, 77#u8, 69#u8, 78#u8, 84#u8 ]))
      let s4 ← cbstm03a.put s2 32#usize 16#usize s3
      let l2 := to_slice_mut_back1 s4
      let (s5, to_slice_mut_back2) ← lift (Array.to_slice_mut l2)
      let s6 ← cbstm03a.fill s5 48#usize 32#usize 42#u8
      Result.ok (to_slice_mut_back2 s6)) := rfl

macro "st_line_wp" : tactic =>
  `(tactic| aeneas_wp [fill_val, put_val, Array.to_slice, Array.to_slice_mut, Array.repeat_val,
    Array.make_val, Array.from_val, array_from_slice_eq, array_update_eq, Slice.from_val,
    length_putL, length_fillL, List.length_replicate, List.length_set, uscalar_ofNat_val,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, ↓reduceDIte])

private theorem st_line_12 (st : cbstm03a.St) :
    cbstm03a.st_line 12#u32 st = .ok (Array.from (latL c3430) (by decide)) := by
  rw [st_line_12_eq]; refine eq_ok_of_wp ?_; st_line_wp
  apply ok_array_from_eq; decide +kernel

private theorem st_line_15 (st : cbstm03a.St) :
    cbstm03a.st_line 15#u32 st = .ok (Array.from (latL c3750) (by decide)) := by
  rw [st_line_15_eq]; refine eq_ok_of_wp ?_; st_line_wp
  apply ok_array_from_eq; decide +kernel

set_option maxHeartbeats 2000000 in
private theorem st_line_140 (st : cbstm03a.St)
    (totT : List UInt8) (htot : st.total_tramt.val = latL totT) (htotl : totT.length = 13) :
    cbstm03a.st_line 140#u32 st =
      .ok (Array.from (latL (c3670 ++ totT)) (by simp [htotl]; decide)) := by
  rw [st_line_140_eq]; refine eq_ok_of_wp ?_; st_line_wp
  apply ok_array_from_eq
  rw [htot]
  have htl : (latL totT).length = 13 := by simp [htotl]
  have hs1 : (putL (List.replicate 80 32#u8) 0 10
      [84#u8, 111#u8, 116#u8, 97#u8, 108#u8, 32#u8, 69#u8, 88#u8, 80#u8, 58#u8]).set 66 36#u8 =
      latL c3670 ++ List.replicate 13 32#u8 := by decide +kernel
  have hd : (List.replicate 13 32#u8).drop 13 = [] := by decide +kernel
  rw [hs1, putL_exact (latL c3670) (latL totT) (List.replicate 13 32#u8) 67 13 (by decide) htl,
    hd, List.append_nil, latL_append]

set_option maxHeartbeats 2000000 in
private theorem st_line_14 (st : cbstm03a.St)
    (tid dt amtT : List UInt8)
    (htid : st.tranid.val = latL tid) (htidl : tid.length = 16)
    (hdt : st.trandt.val = latL dt) (hdtl : dt.length = 49)
    (hamt : st.tranamt.val = latL amtT) (hamtl : amtT.length = 13) :
    cbstm03a.st_line 14#u32 st =
      .ok (Array.from (latL (tid ++ c3606 ++ dt ++ c3656 ++ amtT))
        (by simp [htidl, hdtl, hamtl]; decide)) := by
  rw [st_line_14_eq]; refine eq_ok_of_wp ?_; st_line_wp
  apply ok_array_from_eq
  rw [htid, hdt, hamt]
  have htl : (latL tid).length = 16 := by simp [htidl]
  have hdl : (latL dt).length = 49 := by simp [hdtl]
  have hal : (latL amtT).length = 13 := by simp [hamtl]
  rw [putL_zero_exact (latL tid) _ 16 htl,
    show (List.replicate 80 32#u8).drop 16 = 32#u8 :: List.replicate 63 32#u8 by decide +kernel,
    List.set_append_right _ _ (by omega), htl, Nat.sub_self, List.set_cons_zero,
    show latL tid ++ 32#u8 :: List.replicate 63 32#u8 = (latL tid ++ [32#u8]) ++ List.replicate 63 32#u8 by simp,
    putL_exact (latL tid ++ [32#u8]) (latL dt) (List.replicate 63 32#u8) 17 49 (by simp [htl]) hdl,
    show (List.replicate 63 32#u8).drop 49 = 32#u8 :: List.replicate 13 32#u8 by decide +kernel,
    List.set_append_right _ _ (by simp [htl, hdl]), show 66 - (latL tid ++ [32#u8] ++ latL dt).length = 0 by simp [htl, hdl],
    List.set_cons_zero,
    show (latL tid ++ [32#u8] ++ latL dt) ++ 36#u8 :: List.replicate 13 32#u8 =
      (latL tid ++ [32#u8] ++ latL dt ++ [36#u8]) ++ List.replicate 13 32#u8 by simp,
    putL_exact (latL tid ++ [32#u8] ++ latL dt ++ [36#u8]) (latL amtT) (List.replicate 13 32#u8) 67 13
      (by simp [htl, hdl]) hal]
  have hd : (List.replicate 13 32#u8).drop 13 = [] := by decide +kernel
  have hc1 : [32#u8] = latL c3606 := by decide +kernel
  have hc2 : [36#u8] = latL c3656 := by decide +kernel
  rw [hd, List.append_nil, hc1, hc2]
  simp [latL_append, List.append_assoc]

/-! ## 3. `6000-WRITE-TRANS` (`write_trans_spec`) -/

private theorem ite_true_of {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

private theorem array_index_range {n : Usize} (a : Array U8 n) (j k : Usize)
    (j0 k0 : Nat) (hj : j.val = j0) (hk0 : k.val = k0)
    (hjk : j0 ≤ k0) (hk : k0 ≤ n.val) :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      a { start := j, «end» := k } =
      .ok (Slice.from ((a.val.drop j0).take (k0 - j0))
        (by have := a.property; have := n.hBounds; simp; scalar_tac)) := by
  simp only [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice, core.slice.index.SliceIndexRangeUsizeSlice.index]
  have hl : a.to_slice.length = n.val := by simp [Array.to_slice]
  rw [ite_true_of ⟨by simp [UScalar.le_equiv, hj, hk0, hjk], by rw [hl, hk0]; exact hk⟩]
  congr 1
  rw [Slice.eq_iff]
  simp [List.slice, Array.to_slice, hj, hk0]

theorem zoned_trnx_amt {s : Slice U8} {rval : List FVal} (hr : TrnxRecord.Valid rval)
    (hs : s.val = latL (((TrnxRecord.encode rval).drop 148).take 11)) :
    ∃ v : I64, cbstm03a.zoned s = .ok v ∧
      v.val = tAmt (TrnxRecord.encode rval) ∧
      v.val.natAbs < 10 ^ 11 := by
  have h6 := field_num_decode trnxRecord_contig hr 6 148 11
    { digits := 11, scale := 2, signed := true } (by decide) rfl rfl rfl
  have hta := (trnx_fields hr).2.2.2.2.2.2.1
  obtain ⟨v, hv, hval⟩ := zoned_eq s 11 2 true (numOf (rval.getD 6 default))
    (by decide) (by decide) h6.2.2 (by rw [hs, h6.1])
  have hh := (EquivLean.Modernize.GlueKit.holds_display rfl).mp h6.2.2
  exact ⟨v, hv, by rw [hval, hta], by rw [hval]; exact hh.1⟩

set_option maxHeartbeats 2000000 in
/-- **Specification of `cbstm03a.write_trans` (`6000-WRITE-TRANS`).** -/
theorem write_trans_spec
    (c : cbstm03a.Ctx) (st : cbstm03a.St) (trnx : Array U8 350#usize)
    (rval : List FVal) (hr : TrnxRecord.Valid rval)
    (htrnx : trnx.val = latL (TrnxRecord.encode rval))
    (hcaps : c.stmt.val.length + 1 ≤ Usize.max)
    (hcaph : c.html.val.length + 11 ≤ Usize.max) :
    let r := TrnxRecord.encode rval
    ∃ (c' : cbstm03a.Ctx) (st' : cbstm03a.St),
      cbstm03a.write_trans c st trnx = .ok (c', st') ∧
      CtxExt c c' [tranStmtR r] (tranHtmlR r) := by
  intro r
  have hmax := usize_max_ge
  have hrl : r.length = 350 := trnx_length hr
  have hrng1 := array_index_range trnx 16#usize 32#usize 16 32 rfl rfl (by decide) (by decide)
  let s1 := Slice.from ((trnx.val.drop 16).take (32 - 16))
    (by simp; omega)
  have hs1 : s1.val = latL (tId r) := by
    simp [s1, htrnx, r, ← latL_drop, ← latL_take, tId]
  have hp1 := put_val st.tranid.to_slice 0#usize 16#usize s1 (by simp [Array.to_slice, st.tranid.property])
  let s2 := Slice.from (putL st.tranid.to_slice.val (0#usize).val (16#usize).val s1.val)
    (by rw [length_putL _ _ _ _ (by simp [Array.to_slice, st.tranid.property])]; exact st.tranid.to_slice.property)
  let a1 := st.tranid.from_slice s2
  have htid_len : (tId r).length = 16 := by simp [tId, hrl]
  have ha1 : a1.val = latL (tId r) := by
    rw [Array.from_slice_val _ _ (by simp [s2, Slice.from_val, length_putL, Array.to_slice, st.tranid.property])]
    simp only [s2, Slice.from_val, Array.to_slice, hs1, uscalar_ofNat_val]
    rw [putL_zero_exact _ _ 16 (by rw [length_latL, htid_len]),
      List.drop_of_length_le (by rw [st.tranid.property]; decide), List.append_nil]
  have hrng2 := array_index_range trnx 48#usize 148#usize 48 148 rfl rfl (by decide) (by decide)
  let s4 := Slice.from ((trnx.val.drop 48).take (148 - 48))
    (by simp; omega)
  have hs4 : s4.val = latL (tDesc r) := by
    simp [s4, htrnx, r, ← latL_drop, ← latL_take, tDesc, tRest, List.drop_drop]
  have hp2 := put_val st.trandt.to_slice 0#usize 49#usize s4 (by simp [Array.to_slice, st.trandt.property])
  let s5 := Slice.from (putL st.trandt.to_slice.val (0#usize).val (49#usize).val s4.val)
    (by rw [length_putL _ _ _ _ (by simp [Array.to_slice, st.trandt.property])]; exact st.trandt.to_slice.property)
  let a2 := st.trandt.from_slice s5
  have hdesc_len : (tDesc r).length = 100 := by simp [tDesc, tRest, hrl]
  have hdt_len : ((tDesc r).take 49).length = 49 := by simp [hdesc_len]
  have ha2 : a2.val = latL ((tDesc r).take 49) := by
    rw [Array.from_slice_val _ _ (by simp [s5, Slice.from_val, length_putL, Array.to_slice, st.trandt.property])]
    simp only [s5, Slice.from_val, Array.to_slice, hs4, uscalar_ofNat_val, putL, List.take_zero,
      List.nil_append, latL_take, length_latL, hdesc_len,
      show 49 - 100 = 0 by rfl, List.replicate_zero, List.append_nil]
    have h49 : st.trandt.val.length ≤ 49 := by rw [st.trandt.property]; decide
    rw [List.drop_of_length_le h49, List.append_nil]
  have hrng3 := array_index_range trnx 148#usize 159#usize 148 159 rfl rfl (by decide) (by decide)
  let s6 := Slice.from ((trnx.val.drop 148).take (159 - 148))
    (by simp; omega)
  obtain ⟨i, hzoned, hi_val, hi_abs⟩ := zoned_trnx_amt hr
    (s := s6) (by simp [s6, htrnx, ← latL_drop, ← latL_take])
  obtain ⟨a, hfmt, ha_val⟩ := fmt_z_99_eq i (by omega)
  rw [hi_val] at ha_val
  have hamt_len : (editZ (tAmt r)).length = 13 := length_editZ _
  let st' : cbstm03a.St := { st with tranid := a1, trandt := a2, tranamt := a }
  have hst14 := st_line_14 st' (tId r) ((tDesc r).take 49) (editZ (tAmt r))
    ha1 htid_len ha2 hdt_len ha_val hamt_len
  suffices hchain : ∃ c12,
      cbstm03a.write_trans c st trnx = .ok (c12, st') ∧
      CtxExt c c12 [tranStmtR r] (tranHtmlR r) by
    obtain ⟨c12, hc12, hext⟩ := hchain
    exact ⟨c12, st', hc12, hext⟩
  unfold cbstm03a.write_trans
  rw [show lift (Array.to_slice_mut st.tranid) = Result.ok (st.tranid.to_slice, st.tranid.from_slice) from rfl,
    bind_ok, Aeneas.Std.uncurry_apply_pair, hrng1, bind_ok, hp1, bind_ok,
    show lift (Array.to_slice_mut st.trandt) = Result.ok (st.trandt.to_slice, st.trandt.from_slice) from rfl,
    bind_ok, Aeneas.Std.uncurry_apply_pair, hrng2, bind_ok, hp2, bind_ok,
    hrng3, bind_ok, hzoned, bind_ok, hfmt, bind_ok]
  dsimp only
  rw [hst14, bind_ok]
  unfold tranStmtR tranStmt tranHtmlR tranHtml
  refine step_sw (f := (·, st')) hcaps _ _ (Array.from_val _ _) (fun c1 _ hh1 => ?_)
  have hcaph1 : c1.html.val.length + 11 ≤ Usize.max := by omega
  refine step_hw hcaph1 _ _ hw_LTRS (fun c2 _ hcaph2 => ?_)
  refine step_hw hcaph2 _ _ hw_L58 (fun c3 _ hcaph3 => ?_)
  refine step_tP_star hcaph3 a1 (tId r) ha1 (by omega) (fun c4 _ hcaph4 => ?_)
  refine step_hw hcaph4 _ _ hw_LTDE (fun c5 _ hcaph5 => ?_)
  refine step_hw hcaph5 _ _ hw_L61 (fun c6 _ hcaph6 => ?_)
  refine step_tP_star hcaph6 a2 ((tDesc r).take 49) ha2 (by omega) (fun c7 _ hcaph7 => ?_)
  refine step_hw hcaph7 _ _ hw_LTDE (fun c8 _ hcaph8 => ?_)
  refine step_hw hcaph8 _ _ hw_L64 (fun c9 _ hcaph9 => ?_)
  refine step_tP_star hcaph9 a (editZ (tAmt r)) ha_val (by omega) (fun c10 _ hcaph10 => ?_)
  refine step_hw hcaph10 _ _ hw_LTDE (fun c11 _ hcaph11 => ?_)
  exact last_hw_map (·, st') hcaph11 _ _ hw_LTRE

/-! ## 4. Inner transaction loop `trnx_get_loop0_loop0` -/

theorem trnx_get_loop0_loop0_done
    (c : cbstm03a.Ctx) (st : cbstm03a.St) (mem : cbstm03a.Mem)
    (trnx_rec : Array U8 350#usize) (total cr_jmp tr_jmp : Std.I64) :
    cbstm03a.trnx_get_loop0_loop0 c st mem trnx_rec total cr_jmp tr_jmp true =
      .ok (c, st, trnx_rec, total) := by
  rw [cbstm03a.trnx_get_loop0_loop0, loop_unfold]
  simp [cbstm03a.trnx_get_loop0_loop0.body]

theorem trnx_get_loop0_loop0_step
    {c c' : cbstm03a.Ctx} {st st' : cbstm03a.St} {mem : cbstm03a.Mem}
    {trnx_rec trnx_rec' : Array U8 350#usize}
    {total total' cr_jmp tr_jmp tr_jmp' : Std.I64} {tdone tdone' : Bool}
    (hbody : cbstm03a.trnx_get_loop0_loop0.body mem cr_jmp c st trnx_rec total tr_jmp tdone =
      .ok (.cont (c', st', trnx_rec', total', tr_jmp', tdone'))) :
    cbstm03a.trnx_get_loop0_loop0 c st mem trnx_rec total cr_jmp tr_jmp tdone =
    cbstm03a.trnx_get_loop0_loop0 c' st' mem trnx_rec' total' cr_jmp tr_jmp' tdone' := by
  rw [cbstm03a.trnx_get_loop0_loop0, loop_unfold]
  dsimp only
  rw [hbody, bind_ok]
  rfl

private theorem put_trnx_id_rest
    (trnx_rec : Array U8 350#usize) (r : List UInt8) (hrl : r.length = 350)
    (hcard : trnx_rec.val.take 16 = latL (tCard r))
    {s1 s3 : Slice U8} (hs1 : s1.val = latL (tId r)) (hs3 : s3.val = latL (tRest r)) :
    ∃ (s6 s9 : Slice U8),
      cbstm03a.put trnx_rec.to_slice 16#usize 16#usize
        ((Array.repeat 16#usize 32#u8).from_slice s1).to_slice = .ok s6 ∧
      cbstm03a.put (trnx_rec.from_slice s6).to_slice 32#usize 318#usize
        ((Array.repeat 318#usize 32#u8).from_slice s3).to_slice = .ok s9 ∧
      ((trnx_rec.from_slice s6).from_slice s9).val = latL r ∧
      ((trnx_rec.from_slice s6).from_slice s9).val.take 16 = latL (tCard r) := by
  obtain ⟨s6, hp6, hs6⟩ := put_eq trnx_rec.to_slice 16#usize 16#usize
    ((Array.repeat 16#usize 32#u8).from_slice s1).to_slice
    (by simp [Array.to_slice, trnx_rec.property])
  obtain ⟨s9, hp9, hs9⟩ := put_eq (trnx_rec.from_slice s6).to_slice 32#usize 318#usize
    ((Array.repeat 318#usize 32#u8).from_slice s3).to_slice
    (by simp [Array.to_slice, (trnx_rec.from_slice s6).property])
  have htid_l : (latL (tId r)).length = 16 := by simp [tId, hrl]
  have htrest_l : (latL (tRest r)).length = 318 := by simp [tRest, hrl]
  have hs1_arr : ((Array.repeat 16#usize 32#u8).from_slice s1).to_slice.val = latL (tId r) := by
    rw [Array.to_slice, Slice.from_val,
      Array.from_slice_val _ _ (by rw [hs1]; exact htid_l), hs1]
  have hs3_arr : ((Array.repeat 318#usize 32#u8).from_slice s3).to_slice.val = latL (tRest r) := by
    rw [Array.to_slice, Slice.from_val,
      Array.from_slice_val _ _ (by rw [hs3]; exact htrest_l), hs3]
  have hrec1 : (trnx_rec.from_slice s6).val =
      latL (tCard r) ++ latL (tId r) ++ trnx_rec.val.drop 32 := by
    rw [Array.from_slice_val _ _ (by rw [hs6, length_putL _ _ _ _ (by simp [Array.to_slice, trnx_rec.property])]; simp [Array.to_slice, trnx_rec.property]),
      hs6, hs1_arr, Array.to_slice, Slice.from_val]
    unfold putL
    simp only [uscalar_ofNat_val, hcard, htid_l, List.take_of_length_le (by rw [htid_l]),
      Nat.sub_self, List.replicate_zero, List.append_nil, Nat.reduceAdd]
  have hrec2 : ((trnx_rec.from_slice s6).from_slice s9).val = latL r := by
    rw [Array.from_slice_val _ _ (by rw [hs9, length_putL _ _ _ _ (by simp [Array.to_slice, (trnx_rec.from_slice s6).property])]; simp [Array.to_slice, (trnx_rec.from_slice s6).property]),
      hs9, hs3_arr, Array.to_slice, Slice.from_val, hrec1]
    simp only [uscalar_ofNat_val]
    have hpre32 : (latL (tCard r) ++ latL (tId r)).length = 32 := by
      simp [tCard, tId, hrl]
    rw [putL_exact (latL (tCard r) ++ latL (tId r)) (latL (tRest r)) (trnx_rec.val.drop 32)
      32 318 hpre32 htrest_l]
    have hdrop : (trnx_rec.val.drop 32).drop 318 = [] := by
      rw [List.drop_drop, List.drop_of_length_le (by rw [trnx_rec.property]; decide)]
    rw [hdrop, List.append_nil, ← latL_append, ← latL_append]
    congr 1
    unfold tCard tId tRest
    rw [List.append_assoc, show List.drop 32 r = List.drop 16 (List.drop 16 r) by simp [List.drop_drop],
      List.take_append_drop, List.take_append_drop]
  refine ⟨s6, s9, hp6, hp9, hrec2, ?_⟩
  rw [hrec2, ← latL_take, tCard]

set_option maxHeartbeats 2000000 in
theorem trnx_get_loop0_loop0_spec
    {mem : cbstm03a.Mem} {gs : List (List (List UInt8))}
    (hmem : MemLoaded mem gs)
    {cr_jmp : Std.I64} (hc1 : 1 ≤ cr_jmp.val) (hc2 : cr_jmp.val ≤ gs.length)
    (hvalid_g : ∀ r ∈ gs.getD (cr_jmp.val.toNat - 1) [],
      ∃ rval, TrnxRecord.Valid rval ∧ TrnxRecord.encode rval = r ∧
        tCard r = gCard (gs.getD (cr_jmp.val.toNat - 1) []))
    (rest : List (List UInt8)) :
    ∀ (done : List (List UInt8)),
      gs.getD (cr_jmp.val.toNat - 1) [] = done ++ rest →
      ∀ (c : cbstm03a.Ctx) (st : cbstm03a.St) (trnx_rec : Array U8 350#usize)
        (total tr_jmp : Std.I64),
        tr_jmp.val = (done.length : Int) + 1 →
        total.val.natAbs < 10 ^ 11 →
        trnx_rec.val.take 16 = latL (gCard (gs.getD (cr_jmp.val.toNat - 1) [])) →
        c.stmt.val.length + rest.length ≤ Usize.max →
        c.html.val.length + 11 * rest.length ≤ Usize.max →
        ∃ c' st' trnx_rec' total',
          cbstm03a.trnx_get_loop0_loop0 c st mem trnx_rec total cr_jmp tr_jmp false =
            .ok (c', st', trnx_rec', total') ∧
          CtxExt c c' (rest.map tranStmtR) (rest.flatMap tranHtmlR) ∧
          total'.val = rest.foldl addAmt total.val ∧
          total'.val.natAbs < 10 ^ 11 := by
  obtain ⟨hgs_le, hgs_wf, hmem_c⟩ := hmem
  obtain ⟨_, ⟨cnt, hcnt_eq, hcnt_val⟩, hmem_t⟩ := hmem_c cr_jmp hc1 hc2
  dsimp only at hcnt_val hmem_t
  set g := gs.getD (cr_jmp.val.toNat - 1) []
  have hg_mem : g ∈ gs := getD_mem_of_lt (by omega)
  obtain ⟨hg1, hg10, hgr⟩ := hgs_wf g hg_mem
  induction rest with
  | nil =>
    intro done hdone c st trnx_rec total tr_jmp htr htot hcard hcaps hcaph
    simp only [List.append_nil] at hdone
    have hgt : tr_jmp > cnt := by
      simp [IScalar.lt_equiv, htr, hcnt_val, ← hdone]
    have hbody : cbstm03a.trnx_get_loop0_loop0.body mem cr_jmp c st trnx_rec total tr_jmp false =
        .ok (.cont (c, st, trnx_rec, total, tr_jmp, true)) := by
      unfold cbstm03a.trnx_get_loop0_loop0.body
      simp only [Bool.false_eq_true, ↓reduceIte, hcnt_eq, bind_ok, hgt]
    rw [trnx_get_loop0_loop0_step hbody, trnx_get_loop0_loop0_done]
    exact ⟨c, st, trnx_rec, total, rfl, CtxExt_refl c, rfl, htot⟩
  | cons r rest' ih =>
    intro done hdone c st trnx_rec total tr_jmp htr htot hcard hcaps hcaph
    have hr_mem : r ∈ g := by rw [hdone]; simp
    obtain ⟨rval, hrval, henc, hrcard⟩ := hvalid_g r hr_mem
    have hrl : r.length = 350 := hgr r hr_mem
    have hdone_lt : done.length < g.length := by
      have := congrArg List.length hdone; simp at this; omega
    have hnot_gt : ¬ (tr_jmp > cnt) := by
      rw [gt_iff_lt, IScalar.lt_equiv, htr, hcnt_val]; omega
    have ht1 : 1 ≤ tr_jmp.val := by omega
    have ht2 : tr_jmp.val ≤ g.length := by omega
    have hr_getD : g.getD (tr_jmp.val.toNat - 1) [] = r := by
      have hidx : tr_jmp.val.toNat - 1 = done.length := by omega
      rw [hidx, hdone, getD_append_right' _ _ _ _ (Nat.le_refl _)]
      simp
    obtain ⟨hget_id, hget_rest⟩ := hmem_t tr_jmp ht1 ht2
    rw [hr_getD] at hget_id hget_rest
    obtain ⟨i1, hi1_eq, hi1_val⟩ := tran_off_spec cr_jmp tr_jmp hc1 (by omega) ht1 (by omega)
    let tid := Array.repeat 16#usize 32#u8
    obtain ⟨s1, hs1_eq, hs1_val⟩ := hget_id i1 tid.to_slice hi1_val
      (by simp [tid, Array.to_slice, Array.repeat_val])
    have hi2_bnd : -9223372036854775808 ≤ i1.val + 16 ∧ i1.val + 16 ≤ 9223372036854775807 := by omega
    obtain ⟨i2, hi2_eq, hi2_val⟩ : ∃ i2 : Std.I64,
        (i1 + 16#i64 : Result Std.I64) = .ok i2 ∧ i2.val = i1.val + 16 := by
      refine exists_ok_of_wp ?_
      aeneas_wp [hi2_bnd]
      exact ⟨_, rfl, by simp [IScalar.ofInt_val_eq]⟩
    let rest_arr := Array.repeat 318#usize 32#u8
    obtain ⟨s3, hs3_eq, hs3_val⟩ := hget_rest i2 rest_arr.to_slice (by omega)
      (by simp [rest_arr, Array.to_slice, Array.repeat_val])
    obtain ⟨s6, s9, hp6, hp9, htrec2_val, htrec2_card⟩ :=
      put_trnx_id_rest trnx_rec r hrl (by rw [hcard, hrcard]) hs1_val hs3_val
    let trnx_rec1 := trnx_rec.from_slice s6
    let trnx_rec2 := trnx_rec1.from_slice s9
    obtain ⟨c1, st1, hwt, hext1⟩ := write_trans_spec c st trnx_rec2 rval hrval
      (by rw [htrec2_val, henc]) (by simp at hcaps; omega) (by simp at hcaph; omega)
    rw [henc] at hext1
    have hmax := usize_max_ge
    have hrng10 := array_index_range trnx_rec2 148#usize 159#usize 148 159 rfl rfl (by decide) (by decide)
    let s10 := Slice.from ((trnx_rec2.val.drop 148).take (159 - 148))
      (by simp; omega)
    have htrec2_val' : trnx_rec2.val = latL r := htrec2_val
    obtain ⟨i3, hzoned, hi3_val, hi3_abs⟩ := zoned_trnx_amt hrval
      (s := s10) (by simp [s10, htrec2_val', henc, ← latL_drop, ← latL_take])
    rw [henc] at hi3_val
    obtain ⟨total1, htrunc, htot1_val⟩ := add_trunc11_eq total i3 htot hi3_abs
    rw [hi3_val] at htot1_val
    have htot1_eq : total1.val = addAmt total.val r := htot1_val
    have htot1_abs : total1.val.natAbs < 10 ^ 11 := by
      rw [htot1_eq]; exact addAmt_lt total.val r
    obtain ⟨tr_jmp1, hadd1, htr1_val⟩ := add1_eq tr_jmp (by omega) (by omega)
    dsimp only [tid, rest_arr, trnx_rec1, trnx_rec2, s10] at hs1_eq hs3_eq hp6 hp9 hwt hrng10 hzoned
    have hbody : cbstm03a.trnx_get_loop0_loop0.body mem cr_jmp c st trnx_rec total tr_jmp false =
        .ok (.cont (c1, st1, trnx_rec2, total1, tr_jmp1, false)) := by
      unfold cbstm03a.trnx_get_loop0_loop0.body
      simp only [Bool.false_eq_true, ↓reduceIte, hcnt_eq, bind_ok, hnot_gt,
        hi1_eq, lift, Array.to_slice_mut, Aeneas.Std.uncurry_apply_pair,
        hs1_eq, hi2_eq, hs3_eq, hp6, hp9, hwt, hrng10, hzoned, htrunc, hadd1]
      rfl
    rw [trnx_get_loop0_loop0_step hbody]
    have hcaps1 : c1.stmt.val.length + rest'.length ≤ Usize.max := by
      have := hext1.2.1; simp at this hcaps; omega
    have hcaph1 : c1.html.val.length + 11 * rest'.length ≤ Usize.max := by
      have := hext1.2.2.2.1
      have hlen11 : (tranHtmlR r).length = 11 := rfl
      rw [hlen11] at this
      simp [Nat.left_distrib] at hcaph; omega
    obtain ⟨c', st', trnx_rec', total', hloop, hext2, htot_fin, htot_abs_fin⟩ :=
      ih (done ++ [r]) (by simp [hdone]) c1 st1 trnx_rec2 total1 tr_jmp1
        (by simp [htr1_val, htr]) htot1_abs
        (by rw [htrec2_card, hrcard]) hcaps1 hcaph1
    refine ⟨c', st', trnx_rec', total', hloop, ?_, ?_, htot_abs_fin⟩
    · simpa only [List.map_cons, List.flatMap_cons, List.singleton_append] using CtxExt_trans hext1 hext2
    · simp only [List.foldl_cons, ← htot1_eq, htot_fin]

/-! ## 5. Outer card-scan loop `trnx_get_loop0` and `trnx_get_spec` -/

theorem trnx_get_loop0_done
    (c : cbstm03a.Ctx) (st : cbstm03a.St) (mem : cbstm03a.Mem)
    (cr_cnt : Std.I64) (trnx_rec : Array U8 350#usize) (tbl : Array U8 256#usize)
    (total : Std.I64) (xref_card : Array U8 16#usize) (cr_jmp : Std.I64) :
    cbstm03a.trnx_get_loop0 c st mem cr_cnt trnx_rec tbl total xref_card cr_jmp true =
      .ok (c, st, trnx_rec, total) := by
  rw [cbstm03a.trnx_get_loop0, loop_unfold]
  simp [cbstm03a.trnx_get_loop0.body]

theorem trnx_get_loop0_step
    {c c' : cbstm03a.Ctx} {st st' : cbstm03a.St} {mem : cbstm03a.Mem}
    {cr_cnt : Std.I64} {trnx_rec trnx_rec' : Array U8 350#usize}
    {tbl : Array U8 256#usize} {total total' : Std.I64}
    {xref_card : Array U8 16#usize} {cr_jmp cr_jmp' : Std.I64} {done1 done1' : Bool}
    (hbody : cbstm03a.trnx_get_loop0.body mem cr_cnt tbl xref_card c st trnx_rec total cr_jmp done1 =
      .ok (.cont (c', st', trnx_rec', total', cr_jmp', done1'))) :
    cbstm03a.trnx_get_loop0 c st mem cr_cnt trnx_rec tbl total xref_card cr_jmp done1 =
    cbstm03a.trnx_get_loop0 c' st' mem cr_cnt trnx_rec' tbl total' xref_card cr_jmp' done1' := by
  rw [cbstm03a.trnx_get_loop0, loop_unfold]
  dsimp only
  rw [hbody, bind_ok]
  rfl

private theorem length_gCard_of_loaded {mem : cbstm03a.Mem} {gs : List (List (List UInt8))}
    (hmem : MemLoaded mem gs) {k : Nat} (hk : k < gs.length) :
    (gCard (gs.getD k [])).length = 16 := by
  have hg_mem : gs.getD k [] ∈ gs := getD_mem_of_lt hk
  obtain ⟨hg1, _, hgr⟩ := hmem.2.1 _ hg_mem
  have hne : gs.getD k [] ≠ [] := by intro h; rw [h] at hg1; simp at hg1
  have hlast : (gs.getD k []).getLastD [] ∈ gs.getD k [] := getLastD_mem_of_ne_nil [] hne
  exact length_tCard_of_eq (hgr _ hlast)

set_option maxHeartbeats 2000000 in
theorem trnx_get_loop0_spec
    {mem : cbstm03a.Mem} {gs : List (List (List UInt8))}
    (hmem : MemLoaded mem gs)
    (hvalid : ∀ g ∈ gs, ∀ r ∈ g, ∃ rval, TrnxRecord.Valid rval ∧ TrnxRecord.encode rval = r ∧
      tCard r = gCard g)
    {cr_cnt : Std.I64} (hcr_cnt : cr_cnt.val = (gs.length : Int))
    {tbl : Array U8 256#usize}
    (htbl : ∀ x : UInt8, tbl.val.getD (cp037Code x) 0#u8 = byteOf x.toNat)
    {X : List UInt8} (hXl : X.length = 16)
    {xref_card : Array U8 16#usize} (hxref : xref_card.val = latL X)
    (rest : List (List (List UInt8))) :
    ∀ (doneG : List (List (List UInt8))),
      vis X gs = doneG ++ rest →
      ∀ (c : cbstm03a.Ctx) (st : cbstm03a.St) (trnx_rec : Array U8 350#usize)
        (total cr_jmp : Std.I64),
        cr_jmp.val = (doneG.length : Int) + 1 →
        total.val.natAbs < 10 ^ 11 →
        c.stmt.val.length + 10 * rest.length ≤ Usize.max →
        c.html.val.length + 110 * rest.length ≤ Usize.max →
        ∃ c' st' trnx_rec' total',
          cbstm03a.trnx_get_loop0 c st mem cr_cnt trnx_rec tbl total xref_card cr_jmp false =
            .ok (c', st', trnx_rec', total') ∧
          CtxExt c c' (rest.flatMap (matchStmt X)) (rest.flatMap (matchHtml X)) ∧
          total'.val = rest.foldl (accStep X) total.val ∧
          total'.val.natAbs < 10 ^ 11 := by
  obtain ⟨hgs_le, hgs_wf, hmem_c⟩ := hmem
  induction rest with
  | nil =>
    intro doneG hdoneG c st trnx_rec total cr_jmp hcr htot hcaps hcaph
    simp only [List.append_nil] at hdoneG
    rcases vis_end X gs with hlen_eq | ⟨hlt_gs, hcmp_gt⟩
    · rw [hdoneG] at hlen_eq
      have hgt : cr_jmp > cr_cnt := by
        simp [IScalar.lt_equiv, hcr, hcr_cnt, hlen_eq]
      have hbody : cbstm03a.trnx_get_loop0.body mem cr_cnt tbl xref_card c st trnx_rec total cr_jmp false =
          .ok (.cont (c, st, trnx_rec, total, cr_jmp, true)) := by
        unfold cbstm03a.trnx_get_loop0.body
        simp only [Bool.false_eq_true, ↓reduceIte, hgt]
      rw [trnx_get_loop0_step hbody, trnx_get_loop0_done]
      exact ⟨c, st, trnx_rec, total, rfl, CtxExt_refl c, rfl, htot⟩
    · rw [hdoneG] at hlt_gs hcmp_gt
      have hnot_gt : ¬ (cr_jmp > cr_cnt) := by
        rw [gt_iff_lt, IScalar.lt_equiv, hcr, hcr_cnt]; omega
      have hc1 : 1 ≤ cr_jmp.val := by omega
      have hc2 : cr_jmp.val ≤ gs.length := by omega
      have hidx : cr_jmp.val.toNat - 1 = doneG.length := by omega
      obtain ⟨hget_card, _, _⟩ := hmem_c cr_jmp hc1 hc2
      rw [hidx] at hget_card
      obtain ⟨i, hi_eq, hi_val⟩ := card_off_spec cr_jmp hc1 (by omega)
      let wcard := Array.repeat 16#usize 32#u8
      obtain ⟨s1, hs1_eq, hs1_val⟩ := hget_card i wcard.to_slice hi_val
        (by simp [wcard, Array.to_slice, Array.repeat_val])
      have hgcard_len : (gCard (gs.getD doneG.length [])).length = 16 :=
        length_gCard_of_loaded ⟨hgs_le, hgs_wf, hmem_c⟩ hlt_gs
      let wcard1 := wcard.from_slice s1
      have hwcard1_val : wcard1.to_slice.val = latL (gCard (gs.getD doneG.length [])) := by
        rw [Array.to_slice, Slice.from_val,
          Array.from_slice_val _ _ (by rw [hs1_val, length_latL, hgcard_len]; rfl), hs1_val]
      have hgt_b := gt_bytes_eq wcard1.to_slice xref_card.to_slice tbl htbl
        (gCard (gs.getD doneG.length [])) X hwcard1_val
        (by rw [Array.to_slice, Slice.from_val, hxref])
        (by rw [hgcard_len, hXl])
      rw [hcmp_gt] at hgt_b
      dsimp only [wcard, wcard1] at hs1_eq hgt_b
      have hbody : cbstm03a.trnx_get_loop0.body mem cr_cnt tbl xref_card c st trnx_rec total cr_jmp false =
          .ok (.cont (c, st, trnx_rec, total, cr_jmp, true)) := by
        unfold cbstm03a.trnx_get_loop0.body
        simp only [Bool.false_eq_true, ↓reduceIte, hnot_gt, hi_eq, bind_ok,
          lift, Array.to_slice_mut, Aeneas.Std.uncurry_apply_pair, hs1_eq, hgt_b, beq_self_eq_true]
      rw [trnx_get_loop0_step hbody, trnx_get_loop0_done]
      exact ⟨c, st, trnx_rec, total, rfl, CtxExt_refl c, rfl, htot⟩
  | cons g rest' ih =>
    intro doneG hdoneG c st trnx_rec total cr_jmp hcr htot hcaps hcaph
    obtain ⟨hgd, hcmp_ne_gt, hlt_gs⟩ := vis_cons X gs doneG g rest' hdoneG
    have hnot_gt : ¬ (cr_jmp > cr_cnt) := by
      rw [gt_iff_lt, IScalar.lt_equiv, hcr, hcr_cnt]; omega
    have hc1 : 1 ≤ cr_jmp.val := by omega
    have hc2 : cr_jmp.val ≤ gs.length := by omega
    have hidx : cr_jmp.val.toNat - 1 = doneG.length := by omega
    obtain ⟨hget_card, _, _⟩ := hmem_c cr_jmp hc1 hc2
    rw [hidx, hgd] at hget_card
    obtain ⟨i, hi_eq, hi_val⟩ := card_off_spec cr_jmp hc1 (by omega)
    let wcard := Array.repeat 16#usize 32#u8
    obtain ⟨s1, hs1_eq, hs1_val⟩ := hget_card i wcard.to_slice hi_val
      (by simp [wcard, Array.to_slice, Array.repeat_val])
    have hgcard_len : (gCard g).length = 16 := by
      rw [← hgd]; exact length_gCard_of_loaded ⟨hgs_le, hgs_wf, hmem_c⟩ hlt_gs
    let wcard1 := wcard.from_slice s1
    have hwcard1_val : wcard1.to_slice.val = latL (gCard g) := by
      rw [Array.to_slice, Slice.from_val,
        Array.from_slice_val _ _ (by rw [hs1_val, length_latL, hgcard_len]; rfl), hs1_val]
    have hgt_b := gt_bytes_eq wcard1.to_slice xref_card.to_slice tbl htbl
      (gCard g) X hwcard1_val
      (by rw [Array.to_slice, Slice.from_val, hxref])
      (by rw [hgcard_len, hXl])
    have hcmp_false : (Sem.cmpBytes (gCard g) X == .gt) = false :=
      beq_false_of_ne hcmp_ne_gt
    rw [hcmp_false] at hgt_b
    have heq_b : cbstm03a.eq_bytes xref_card.to_slice wcard1.to_slice =
        .ok (decide (latL X = latL (gCard g))) := by
      rw [eq_bytes_eq, hwcard1_val, Array.to_slice, Slice.from_val, hxref]
    obtain ⟨cr_jmp1, hadd1, hcr1_val⟩ := add1_eq cr_jmp (by omega) (by omega)
    have hg_mem : g ∈ gs := by rw [← hgd]; exact getD_mem_of_lt hlt_gs
    obtain ⟨hg1, hg10, _⟩ := hgs_wf g hg_mem
    by_cases hmatch : gCard g = X
    · have hdec_true : decide (latL X = latL (gCard g)) = true :=
        decide_eq_true (by rw [hmatch])
      rw [hdec_true] at heq_b
      obtain ⟨s8, hp8, hs8_val⟩ := put_eq trnx_rec.to_slice 0#usize 16#usize wcard1.to_slice
        (by simp [Array.to_slice, trnx_rec.property])
      let trnx_rec1 := trnx_rec.from_slice s8
      have htrec1_card : trnx_rec1.val.take 16 = latL (gCard (gs.getD (cr_jmp.val.toNat - 1) [])) := by
        rw [hidx, hgd, Array.from_slice_val _ _ (by rw [hs8_val, length_putL _ _ _ _ (by simp [Array.to_slice, trnx_rec.property])]; simp [Array.to_slice, trnx_rec.property]),
          hs8_val, hwcard1_val]
        exact take_putL_zero _ _ 16 (by rw [length_latL, hgcard_len])
      have hvalid_g : ∀ r ∈ gs.getD (cr_jmp.val.toNat - 1) [],
          ∃ rval, TrnxRecord.Valid rval ∧ TrnxRecord.encode rval = r ∧
            tCard r = gCard (gs.getD (cr_jmp.val.toNat - 1) []) := by
        rw [hidx, hgd]; exact hvalid g hg_mem
      obtain ⟨c1, st1, trnx_rec2, total1, hinner, hext1, htot1_val, htot1_abs⟩ :=
        trnx_get_loop0_loop0_spec ⟨hgs_le, hgs_wf, hmem_c⟩ hc1 hc2 hvalid_g g []
          (by rw [hidx, hgd, List.nil_append]) c st trnx_rec1 total 1#i64
          rfl htot htrec1_card
          (by simp at hcaps; omega) (by simp [Nat.left_distrib] at hcaph; omega)
      dsimp only [wcard, wcard1, trnx_rec1] at hs1_eq hgt_b heq_b hp8 hinner
      have hbody : cbstm03a.trnx_get_loop0.body mem cr_cnt tbl xref_card c st trnx_rec total cr_jmp false =
          .ok (.cont (c1, st1, trnx_rec2, total1, cr_jmp1, false)) := by
        unfold cbstm03a.trnx_get_loop0.body
        simp only [Bool.false_eq_true, ↓reduceIte, hnot_gt, hi_eq, bind_ok,
          lift, Array.to_slice_mut, Aeneas.Std.uncurry_apply_pair,
          hs1_eq, hgt_b, heq_b, hp8, hinner, hadd1]
      rw [trnx_get_loop0_step hbody]
      have hcaps1 : c1.stmt.val.length + 10 * rest'.length ≤ Usize.max := by
        have := hext1.2.1; simp at this hcaps; omega
      have hcaph1 : c1.html.val.length + 110 * rest'.length ≤ Usize.max := by
        have := hext1.2.2.2.1
        have hfl11 : (g.flatMap tranHtmlR).length = 11 * g.length := by
          clear * -
          induction g with
          | nil => rfl
          | cons r rs ih =>
            have h11 : (tranHtmlR r).length = 11 := rfl
            simp only [List.flatMap_cons, List.length_append, h11, ih, List.length_cons]
            omega
        rw [hfl11] at this
        simp [Nat.left_distrib] at hcaph; omega
      obtain ⟨c', st', trnx_rec', total', hloop, hext2, htot_fin, htot_abs_fin⟩ :=
        ih (doneG ++ [g]) (by simp [hdoneG]) c1 st1 trnx_rec2 total1 cr_jmp1
          (by simp [hcr1_val, hcr]) htot1_abs hcaps1 hcaph1
      refine ⟨c', st', trnx_rec', total', hloop, ?_, ?_, htot_abs_fin⟩
      · simp only [List.flatMap_cons, matchStmt, matchHtml, hmatch, ↓reduceIte]
        exact CtxExt_trans hext1 hext2
      · simp only [List.foldl_cons, accStep, hmatch, ↓reduceIte, ← htot1_val, htot_fin]
    · have hdec_false : decide (latL X = latL (gCard g)) = false :=
        decide_eq_false (fun h => hmatch (latL_inj.mp h).symm)
      rw [hdec_false] at heq_b
      dsimp only [wcard, wcard1] at hs1_eq hgt_b heq_b
      have hbody : cbstm03a.trnx_get_loop0.body mem cr_cnt tbl xref_card c st trnx_rec total cr_jmp false =
          .ok (.cont (c, st, trnx_rec, total, cr_jmp1, false)) := by
        unfold cbstm03a.trnx_get_loop0.body
        simp only [Bool.false_eq_true, ↓reduceIte, hnot_gt, hi_eq, bind_ok,
          lift, Array.to_slice_mut, Aeneas.Std.uncurry_apply_pair,
          hs1_eq, hgt_b, heq_b, hadd1]
      rw [trnx_get_loop0_step hbody]
      obtain ⟨c', st', trnx_rec', total', hloop, hext2, htot_fin, htot_abs_fin⟩ :=
        ih (doneG ++ [g]) (by simp [hdoneG]) c st trnx_rec total cr_jmp1
          (by simp [hcr1_val, hcr]) htot
          (by simp [Nat.left_distrib] at hcaps; omega)
          (by simp [Nat.left_distrib] at hcaph; omega)
      refine ⟨c', st', trnx_rec', total', hloop, ?_, ?_, htot_abs_fin⟩
      · simpa only [List.flatMap_cons, matchStmt, matchHtml, hmatch, ↓reduceIte, List.nil_append] using hext2
      · simpa only [List.foldl_cons, accStep, hmatch, ↓reduceIte] using htot_fin

private theorem length_flatMap_matchStmt (X : List UInt8) :
    ∀ {gs : List (List (List UInt8))}, (∀ g ∈ gs, g.length ≤ 10) →
      (gs.flatMap (matchStmt X)).length ≤ 10 * gs.length
  | [], _ => by simp
  | g :: gs, h => by
    have hg := h g (List.mem_cons_self ..)
    have hgs := length_flatMap_matchStmt X (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, matchStmt]
    split <;> (simp only [List.length_map, List.length_nil]; omega)

private theorem length_flatMap_tranHtmlR : ∀ (g : List (List UInt8)),
    (g.flatMap tranHtmlR).length = 11 * g.length
  | [] => rfl
  | r :: rs => by
    have h11 : (tranHtmlR r).length = 11 := rfl
    simp only [List.flatMap_cons, List.length_append, h11, length_flatMap_tranHtmlR rs, List.length_cons]
    omega

private theorem length_flatMap_matchHtml (X : List UInt8) :
    ∀ {gs : List (List (List UInt8))}, (∀ g ∈ gs, g.length ≤ 10) →
      (gs.flatMap (matchHtml X)).length ≤ 110 * gs.length
  | [], _ => by simp
  | g :: gs, h => by
    have hg := h g (List.mem_cons_self ..)
    have hgs := length_flatMap_matchHtml X (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, matchHtml]
    split
    · rw [length_flatMap_tranHtmlR]; omega
    · simp only [List.length_nil]; omega

private theorem length_vis_le (X : List UInt8) (gs : List (List (List UInt8))) :
    (vis X gs).length ≤ gs.length := by
  have hsplit : gs = vis X gs ++ gs.dropWhile (fun g => Sem.cmpBytes (gCard g) X != .gt) :=
    (List.takeWhile_append_dropWhile).symm
  conv => rhs; rw [hsplit]
  simp

private theorem mem_of_mem_vis {X : List UInt8} {gs : List (List (List UInt8))} {g : List (List UInt8)}
    (hg : g ∈ vis X gs) : g ∈ gs := by
  have hsplit : gs = vis X gs ++ gs.dropWhile (fun g => Sem.cmpBytes (gCard g) X != .gt) :=
    (List.takeWhile_append_dropWhile).symm
  rw [hsplit]
  exact List.mem_append_left _ hg

set_option maxHeartbeats 2000000 in
/-- **Specification of `cbstm03a.trnx_get` (`4000-TRNXFILE-GET`).** -/
theorem trnx_get_spec
    {vals1 vals2 vals3 vals4 : List (List FVal)}
    (hv1 : ∀ v ∈ vals1, TrnxRecord.Valid v)
    (hD : EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4)
    {mem : cbstm03a.Mem}
    (hmem : MemLoaded mem (grp (vals1.map TrnxRecord.encode)))
    {cr_cnt : Std.I64}
    (hcr_cnt : cr_cnt.val = ((grp (vals1.map TrnxRecord.encode)).length : Int))
    {tbl : Array U8 256#usize}
    (htbl : ∀ x : UInt8, tbl.val.getD (cp037Code x) 0#u8 = byteOf x.toNat)
    (c : cbstm03a.Ctx) (st : cbstm03a.St)
    (xref_rec : Array U8 50#usize) (trnx_rec : Array U8 350#usize)
    (xval : List FVal) (hx : CardXrefRecord.Valid xval)
    (hxref : xref_rec.val = latL (CardXrefRecord.encode xval))
    (hcaps : c.stmt.val.length + 503 ≤ Usize.max)
    (hcaph : c.html.val.length + 5508 ≤ Usize.max) :
    let card := strOf (xval.getD 0 default)
    let ts := ofCardF card vals1
    ∃ c' st' trnx_rec',
      cbstm03a.trnx_get c st mem cr_cnt xref_rec trnx_rec tbl = .ok (c', st', trnx_rec') ∧
      c'.stmt.val.map (fun l => l.val.map (·.val)) =
        c.stmt.val.map (fun l => l.val.map (·.val)) ++
          (ts.map modelTranStmt ++ modelTailStmt (ts.foldl modelAddAmt 0)) ∧
      c'.html.val.map (fun l => l.val.map (·.val)) =
        c.html.val.map (fun l => l.val.map (·.val)) ++
          (ts.flatMap modelTranHtml ++ modelTailHtml) ∧
      c'.displays = c.displays ∧ c'.abended = c.abended ∧
      c'.xref_pos = c.xref_pos ∧ c'.xref_eof = c.xref_eof := by
  intro card ts
  obtain ⟨_, hsorted, hG, hT, _⟩ := hD
  have hmax := usize_max_ge
  set trs := vals1.map TrnxRecord.encode
  set gs := grp trs
  have hxf := xref_fields hx
  have hcard_len : card.length = 16 := hxf.2.1
  have hxcard_eq : (CardXrefRecord.encode xval).take 16 = card := hxf.1
  have hrng0 := array_index_range xref_rec 0#usize 16#usize 0 16 rfl rfl (by decide) (by decide)
  let s1 := Slice.from ((xref_rec.val.drop 0).take (16 - 0)) (by simp; omega)
  have hs1_val : s1.val = latL card := by
    simp [s1, hxref, ← latL_take, hxcard_eq]
  let xref_card := Array.repeat 16#usize 32#u8
  obtain ⟨s2, hp2, hs2_val⟩ := put_eq xref_card.to_slice 0#usize 16#usize s1
    (by simp [xref_card, Array.to_slice, Array.repeat_val])
  let xref_card1 := xref_card.from_slice s2
  have hxref1_val : xref_card1.val = latL card := by
    rw [Array.from_slice_val _ _ (by rw [hs2_val, length_putL _ _ _ _ (by simp [xref_card, Array.to_slice, Array.repeat_val])]; simp [xref_card, Array.to_slice, Array.repeat_val]),
      hs2_val, hs1_val]
    simp only [xref_card, Array.to_slice, Slice.from_val, Array.repeat_val, uscalar_ofNat_val]
    rw [putL_zero_exact _ _ 16 (by rw [length_latL, hcard_len]),
      List.drop_of_length_le (by simp), List.append_nil]
  obtain ⟨hflat, _, hgcard_prop⟩ := grp_props trs
  have hvalid : ∀ g ∈ gs, ∀ r ∈ g, ∃ rval, TrnxRecord.Valid rval ∧ TrnxRecord.encode rval = r ∧
      tCard r = gCard g := by
    intro g hg r hr
    have hr_trs : r ∈ trs := by
      rw [← hflat]; exact List.mem_flatten.mpr ⟨g, hg, hr⟩
    obtain ⟨rval, hrval_mem, hrval_enc⟩ := List.mem_map.mp hr_trs
    exact ⟨rval, hv1 rval hrval_mem, hrval_enc, hgcard_prop g hg r hr⟩
  have hvis_len : (vis card gs).length ≤ 50 :=
    Nat.le_trans (length_vis_le card gs) hG
  have hvis_T : ∀ g ∈ vis card gs, g.length ≤ 10 :=
    fun g hg => hT g (mem_of_mem_vis hg)
  obtain ⟨c1, st1, trnx_rec1, ws_trn_amt, hloop0, hext1, htot_val, htot_abs⟩ :=
    trnx_get_loop0_spec hmem hvalid hcr_cnt htbl hcard_len hxref1_val
      (vis card gs) [] (by simp) c st trnx_rec 0#i64 1#i64
      rfl (by decide) (by omega) (by omega)
  obtain ⟨a, hfmt, ha_val⟩ := fmt_z_99_eq ws_trn_amt (by omega)
  have ha_len : (editZ ws_trn_amt.val).length = 13 := length_editZ _
  let st1' : cbstm03a.St := { st1 with total_tramt := a }
  have hst12 := st_line_12 st1'
  have hst140 := st_line_140 st1' (editZ ws_trn_amt.val) ha_val ha_len
  have hst15 := st_line_15 st1'
  have hms_le := length_flatMap_matchStmt card hvis_T
  have hmh_le := length_flatMap_matchHtml card hvis_T
  have hcaps1 : c1.stmt.val.length + 3 ≤ Usize.max := by
    have := hext1.2.1; omega
  have hcaph1 : c1.html.val.length + 8 ≤ Usize.max := by
    have := hext1.2.2.2.1; omega
  have htail : ∃ c12,
      Std.bind (cbstm03a.st_line 12#u32 st1') (fun l12 =>
      Std.bind (cbstm03a.sw c1 l12) (fun c2 =>
      Std.bind (cbstm03a.st_line 140#u32 st1') (fun l14a =>
      Std.bind (cbstm03a.sw c2 l14a) (fun c3 =>
      Std.bind (cbstm03a.st_line 15#u32 st1') (fun l15 =>
      Std.bind (cbstm03a.sw c3 l15) (fun c4 =>
      Std.bind (cbstm03a.hw c4 cbstm03a.LTRS) (fun c5 =>
      Std.bind (cbstm03a.hw c5 cbstm03a.L10) (fun c6 =>
      Std.bind (cbstm03a.hw c6 cbstm03a.L75) (fun c7 =>
      Std.bind (cbstm03a.hw c7 cbstm03a.LTDE) (fun c8 =>
      Std.bind (cbstm03a.hw c8 cbstm03a.LTRE) (fun c9 =>
      Std.bind (cbstm03a.hw c9 cbstm03a.L78) (fun c10 =>
      Std.bind (cbstm03a.hw c10 cbstm03a.L79) (fun c11 =>
      Std.bind (cbstm03a.hw c11 cbstm03a.L80) (fun c12 =>
        Result.ok (c12, st1', trnx_rec1))))))))))))))) = .ok (c12, st1', trnx_rec1) ∧
      CtxExt c1 c12 (tailStmt ws_trn_amt.val) tailHtml := by
    rw [hst12, bind_ok]
    unfold tailStmt tailHtml
    refine step_sw (f := fun x => (x, st1', trnx_rec1)) hcaps1 _ _ (Array.from_val _ _) (fun c2 hcaps2 hh2 => ?_)
    rw [hst140, bind_ok]
    refine step_sw hcaps2 _ _ (Array.from_val _ _) (fun c3 hcaps3 hh3 => ?_)
    rw [hst15, bind_ok]
    refine step_sw hcaps3 _ _ (Array.from_val _ _) (fun c4 _ hh4 => ?_)
    have hcaph4 : c4.html.val.length + 8 ≤ Usize.max := by omega
    refine step_hw hcaph4 _ _ hw_LTRS (fun c5 _ hcaph5 => ?_)
    refine step_hw hcaph5 _ _ hw_L10 (fun c6 _ hcaph6 => ?_)
    refine step_hw hcaph6 _ _ hw_L75 (fun c7 _ hcaph7 => ?_)
    refine step_hw hcaph7 _ _ hw_LTDE (fun c8 _ hcaph8 => ?_)
    refine step_hw hcaph8 _ _ hw_LTRE (fun c9 _ hcaph9 => ?_)
    refine step_hw hcaph9 _ _ hw_L78 (fun c10 _ hcaph10 => ?_)
    refine step_hw hcaph10 _ _ hw_L79 (fun c11 _ hcaph11 => ?_)
    exact last_hw_map (fun x => (x, st1', trnx_rec1)) hcaph11 _ _ hw_L80
  obtain ⟨c12, htail_eq, hext2⟩ := htail
  change ws_trn_amt.val = (vis card gs).foldl (accStep card) 0 at htot_val
  have hext_all : CtxExt c c12 (trnxStmt card gs) (trnxHtml card gs) := by
    unfold trnxStmt trnxHtml
    rw [← htot_val]
    exact CtxExt_trans hext1 hext2
  dsimp only [xref_card, s1, xref_card1] at hp2 hloop0
  have htrnx_get_eq : cbstm03a.trnx_get c st mem cr_cnt xref_rec trnx_rec tbl =
      .ok (c12, st1', trnx_rec1) := by
    unfold cbstm03a.trnx_get
    simp only [lift, Array.to_slice_mut, Aeneas.Std.uncurry_apply_pair, bind_ok,
      hrng0, hp2, hloop0, hfmt]
    exact htail_eq
  have hts_valid : ∀ r ∈ ts, TrnxRecord.Valid r := ofCardF_valid hv1 card
  have hstmt_sorted : (trnxStmt card gs).map (·.map cp037Code) =
      ts.map modelTranStmt ++ modelTailStmt (ts.foldl modelAddAmt 0) := by
    rw [trnxStmt_sorted trs hsorted card, List.map_append,
      ofCard_encode hv1 card, map_tranStmtR_encode hts_valid,
      foldl_addAmt_encode hts_valid, modelTailStmt]
  have hhtml_sorted : (trnxHtml card gs).map (·.map cp037Code) =
      ts.flatMap modelTranHtml ++ modelTailHtml := by
    rw [trnxHtml_sorted trs hsorted card, List.map_append,
      ofCard_encode hv1 card, flatMap_tranHtmlR_encode hts_valid, modelTailHtml]
  obtain ⟨hs_all, _, hh_all, _, hd_all, ha_all, hxp_all, hxe_all⟩ := hext_all
  rw [hstmt_sorted] at hs_all
  rw [hhtml_sorted] at hh_all
  exact ⟨c12, st1', trnx_rec1, htrnx_get_eq, hs_all, hh_all, hd_all, ha_all, hxp_all, hxe_all⟩

end EquivLean.Modernize.Cbstm03a.Rust
