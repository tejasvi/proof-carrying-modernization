import EquivLean.Modernize.Cbstm03a.RustRun1

/-!
# CBSTM03A → Rust, part 4: `st_line`, `html_header`, `html_p_line`, `html_nmadbs`, `create_statement`
-/

open Aeneas Aeneas.Std Result ControlFlow Error EquivLean EquivLean.Aeneas
open Cobol Cobol.StmCore EquivLean.Cobol.Rec EquivLean.Modernize.GlueKit
open EquivLean.Modernize.Cbstm03a.StmBridge EquivLean.Modernize.Cbstm03a.Model

namespace EquivLean.Modernize.Cbstm03a.Rust.CS

/-! ## 1. `strPartL`, `tokBL`, `tok2L` and `Helpers1` -/

/-- Pure-Lean model of `str_part`: writes `piece` into `dst` starting at `ptr` (up to `dst.length`),
and returns the updated slice and the new pointer `ptr + min piece.length (dst.length - ptr)`. -/
def strPartL (dst : List U8) (ptr : Nat) (piece : List U8) : List U8 × Nat :=
  (dst.take ptr ++ piece.take (min piece.length (dst.length - ptr)) ++
    dst.drop (ptr + min piece.length (dst.length - ptr)),
   ptr + min piece.length (dst.length - ptr))

@[simp] theorem length_strPartL (dst : List U8) (ptr : Nat) (piece : List U8)
    (h : ptr ≤ dst.length) : (strPartL dst ptr piece).1.length = dst.length := by
  simp [strPartL]; omega

@[simp] theorem snd_strPartL_le (dst : List U8) (ptr : Nat) (piece : List U8)
    (h : ptr ≤ dst.length) : (strPartL dst ptr piece).2 ≤ dst.length := by
  simp [strPartL]; omega

theorem latL_ovw (J dst : List UInt8) :
    latL (ovw J dst) =
      let k := min J.length dst.length
      (latL J).take k ++ (latL dst).drop k := by
  induction J generalizing dst with
  | nil => simp [ovw, latL]
  | cons b bs ih =>
    cases dst with
    | nil => simp [ovw, latL]
    | cons d ds =>
      simp only [ovw, latL, List.map_cons, List.length_cons, Nat.add_min_add_right,
        List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      exact congrArg (lat b :: ·) (ih ds)

theorem ovw_eq_take_drop_min (J dst : List UInt8) :
    ovw J dst = J.take (min J.length dst.length) ++ dst.drop (min J.length dst.length) := by
  rw [← latL_inj, latL_ovw, latL_append, latL_take, latL_drop]

theorem strPartL_zero (n : Nat) (piece : List UInt8) :
    (strPartL (List.replicate n 32#u8) 0 (latL piece)).1 = latL (ovw piece (sp n)) ∧
    (strPartL (List.replicate n 32#u8) 0 (latL piece)).2 = min piece.length n := by
  rw [latL_ovw]
  simp [strPartL, sp, latL_replicate]

theorem strPartL_chain (n : Nat) (pre piece : List UInt8) (hpre : pre.length ≤ n) :
    (strPartL (latL (ovw pre (sp n))) pre.length (latL piece)).1 =
      latL (ovw (pre ++ piece) (sp n)) ∧
    (strPartL (latL (ovw pre (sp n))) pre.length (latL piece)).2 =
      min (pre ++ piece).length n := by
  have hovw1 : ovw pre (sp n) = pre ++ sp (n - pre.length) := by
    rw [ovw_eq_append_drop pre (sp n) (by simp [sp, hpre])]
    simp [sp, List.drop_replicate]
  have hovw2 : ovw (pre ++ piece) (sp n) =
      pre ++ piece.take (min piece.length (n - pre.length)) ++
        sp (n - pre.length - min piece.length (n - pre.length)) := by
    rw [ovw_append pre piece (sp n) (by simp [sp, hpre])]
    have hd : (sp n).drop pre.length = sp (n - pre.length) := by simp [sp, List.drop_replicate]
    rw [hd, ovw_eq_take_drop_min]
    simp [sp, List.drop_replicate, List.append_assoc]
  have hlen1 : (latL (ovw pre (sp n))).length = n := by
    rw [length_latL, length_ovw]; simp [sp]
  have htake1 : (latL (ovw pre (sp n))).take pre.length = latL pre := by
    rw [hovw1, latL_append, List.take_left' (by simp)]
  have hdrop1 : (latL (ovw pre (sp n))).drop (pre.length + min piece.length (n - pre.length)) =
      latL (sp (n - pre.length - min piece.length (n - pre.length))) := by
    rw [hovw1, latL_append, ← List.drop_drop, List.drop_left' (by simp)]
    simp [sp, latL_replicate, List.drop_replicate]
  constructor
  · dsimp only [strPartL]
    rw [hlen1, length_latL, htake1, hdrop1, ← latL_take, hovw2, latL_append, latL_append]
  · dsimp only [strPartL]
    rw [hlen1, length_latL, List.length_append]
    omega

theorem strPartL_chain_any (n : Nat) (pre piece : List UInt8) :
    strPartL (latL (ovw pre (sp n))) (min pre.length n) (latL piece) =
      (latL (ovw (pre ++ piece) (sp n)), min (pre ++ piece).length n) := by
  by_cases hpre : pre.length ≤ n
  · rw [Nat.min_eq_left hpre]
    exact Prod.ext (strPartL_chain n pre piece hpre).1 (strPartL_chain n pre piece hpre).2
  · have hlen1 : (latL (ovw pre (sp n))).length = n := by
      rw [length_latL, length_ovw]; simp [sp]
    have hmin1 : min pre.length n = n := by omega
    have hmin2 : min (pre ++ piece).length n = n := by simp; omega
    have hovw : ovw (pre ++ piece) (sp n) = ovw pre (sp n) := by
      rw [ovw_eq_take_drop_min, ovw_eq_take_drop_min]
      simp only [sp, List.length_replicate, hmin1, hmin2, List.drop_replicate, Nat.sub_self,
        List.replicate_zero, List.append_nil]
      exact List.take_append_of_le_length (by omega)
    rw [hmin1, hmin2, hovw]
    apply Prod.ext
    · dsimp only [strPartL]
      simp [hlen1, List.take_of_length_le (by rw [hlen1])]
    · dsimp only [strPartL]
      simp [hlen1]

@[simp] theorem strPartL_zero_fst (n : Nat) (piece : List UInt8) :
    (strPartL (List.replicate n 32#u8) 0 (latL piece)).1 = latL (ovw piece (sp n)) :=
  (strPartL_zero n piece).1

@[simp] theorem strPartL_zero_snd (n : Nat) (piece : List UInt8) :
    (strPartL (List.replicate n 32#u8) 0 (latL piece)).2 = min piece.length n :=
  (strPartL_zero n piece).2

@[simp] theorem strPartL_chain_fst (n : Nat) (pre piece : List UInt8) :
    (strPartL (latL (ovw pre (sp n))) (min pre.length n) (latL piece)).1 =
      latL (ovw (pre ++ piece) (sp n)) :=
  congrArg Prod.fst (strPartL_chain_any n pre piece)

@[simp] theorem strPartL_chain_snd (n : Nat) (pre piece : List UInt8) :
    (strPartL (latL (ovw pre (sp n))) (min pre.length n) (latL piece)).2 =
      min (pre ++ piece).length n :=
  congrArg Prod.snd (strPartL_chain_any n pre piece)

def tokBL (d : U8) (src : List U8) : List U8 := src.takeWhile (· != d)

def tok2L : List U8 → List U8
  | x :: y :: rest => if x = 32#u8 ∧ y = 32#u8 then [] else x :: tok2L (y :: rest)
  | l => l

theorem tokBL_cons (b x : U8) (xs : List U8) :
    tokBL b (x :: xs) = if x = b then [] else x :: tokBL b xs := by
  by_cases h : x = b <;> simp [tokBL, h]

theorem tokBL_latL (d : UInt8) (bs : List UInt8) :
    tokBL (lat d) (latL bs) = latL (tokB d bs) := by
  induction bs with
  | nil => rfl
  | cons x xs ih =>
    have hx : (lat x = lat d) ↔ (x = d) := ⟨lat_inj, fun h => h ▸ rfl⟩
    simp only [latL, List.map_cons, tokBL_cons, tokB_cons, hx]
    split
    · rfl
    · exact congrArg (lat x :: ·) ih

attribute [simp] tokBL_latL

@[simp] theorem tokBL_space_latL (bs : List UInt8) :
    tokBL 32#u8 (latL bs) = latL (tokB 64 bs) := by
  rw [← lat_space, tokBL_latL]

@[simp] theorem tokBL_star_latL (bs : List UInt8) :
    tokBL 42#u8 (latL bs) = latL (tokB 92 bs) := by
  rw [← lat_star, tokBL_latL]

@[simp] theorem tok2L_latL : ∀ bs : List UInt8, tok2L (latL bs) = latL (tok2 bs)
  | [] => rfl
  | [x] => rfl
  | x :: y :: rest => by
    have hx : (lat x = 32#u8) ↔ (x = 64) := by
      rw [← lat_space]; exact ⟨lat_inj, fun h => h ▸ rfl⟩
    have hy : (lat y = 32#u8) ↔ (y = 64) := by
      rw [← lat_space]; exact ⟨lat_inj, fun h => h ▸ rfl⟩
    simp only [latL, List.map_cons, tok2L, tok2, hx, hy]
    split
    · rfl
    · simp only [List.map_cons, List.cons.injEq, true_and]
      exact tok2L_latL (y :: rest)

/-- Hypotheses from `RustRun1` used by `RustRun4`. -/
structure Helpers1 (tbl : Array U8 256#usize) : Prop where
  vb_eq : ∀ (s : Slice U8), cbstm03a.vb s = .ok (alloc.vec.Vec.from s.val s.property)
  put_eq : ∀ (dst : Slice U8) (off len : Usize) (src : Slice U8)
    (h : off.val + len.val ≤ dst.val.length),
    cbstm03a.put dst off len src =
      .ok (Slice.from (putL dst.val off.val len.val src.val)
        (by rw [length_putL _ _ _ _ h]; exact dst.property))
  fill_eq : ∀ (dst : Slice U8) (off len : Usize) (ch : U8)
    (h : off.val + len.val ≤ dst.val.length),
    cbstm03a.fill dst off len ch =
      .ok (Slice.from (fillL dst.val off.val len.val ch)
        (by rw [length_fillL _ _ _ _ h]; exact dst.property))
  fmt_9_99_eq : ∀ (v : I64), v.val.natAbs < 10 ^ 12 →
    cbstm03a.fmt_9_99 v =
      .ok (Array.from (latL (edit9 v.val)) (by rw [length_latL, length_edit9]; rfl))
  fmt_z_99_eq : ∀ (v : I64), v.val.natAbs < 10 ^ 12 →
    cbstm03a.fmt_z_99 v =
      .ok (Array.from (latL (editZ v.val)) (by rw [length_latL, length_editZ]; rfl))
  zoned_acct_bal : ∀ (s : Slice U8) (a : List FVal), AccountRecord.Valid a →
    s.val = latL (((AccountRecord.encode a).drop 12).take 12) →
    ∃ v : I64, cbstm03a.zoned s = .ok v ∧ v.val = numOf (a.getD 2 default) ∧ v.val.natAbs < 10 ^ 12
  str_part_space : ∀ (dst : Slice U8) (ptr : Usize) (src delim : Slice U8),
    delim.val = [32#u8] → (h : ptr.val ≤ dst.val.length) → src.val.length ≤ 500 →
    cbstm03a.str_part dst ptr src delim =
      .ok (Slice.from (strPartL dst.val ptr.val (tokBL 32#u8 src.val)).1
            (by rw [length_strPartL _ _ _ h]; exact dst.property),
          UScalar.ofNatCore (strPartL dst.val ptr.val (tokBL 32#u8 src.val)).2
            (by have := snd_strPartL_le dst.val ptr.val (tokBL 32#u8 src.val) h; have := dst.property; scalar_tac))
  str_part_star : ∀ (dst : Slice U8) (ptr : Usize) (src delim : Slice U8),
    delim.val = [42#u8] → (h : ptr.val ≤ dst.val.length) → src.val.length ≤ 500 →
    cbstm03a.str_part dst ptr src delim =
      .ok (Slice.from (strPartL dst.val ptr.val (tokBL 42#u8 src.val)).1
            (by rw [length_strPartL _ _ _ h]; exact dst.property),
          UScalar.ofNatCore (strPartL dst.val ptr.val (tokBL 42#u8 src.val)).2
            (by have := snd_strPartL_le dst.val ptr.val (tokBL 42#u8 src.val) h; have := dst.property; scalar_tac))
  str_part_two_space : ∀ (dst : Slice U8) (ptr : Usize) (src delim : Slice U8),
    delim.val = [32#u8, 32#u8] → (h : ptr.val ≤ dst.val.length) → src.val.length ≤ 500 →
    cbstm03a.str_part dst ptr src delim =
      .ok (Slice.from (strPartL dst.val ptr.val (tok2L src.val)).1
            (by rw [length_strPartL _ _ _ h]; exact dst.property),
          UScalar.ofNatCore (strPartL dst.val ptr.val (tok2L src.val)).2
            (by have := snd_strPartL_le dst.val ptr.val (tok2L src.val) h; have := dst.property; scalar_tac))
  str_part_empty : ∀ (dst : Slice U8) (ptr : Usize) (src delim : Slice U8),
    delim.val = [] → (h : ptr.val ≤ dst.val.length) →
    cbstm03a.str_part dst ptr src delim =
      .ok (Slice.from (strPartL dst.val ptr.val src.val).1
            (by rw [length_strPartL _ _ _ h]; exact dst.property),
          UScalar.ofNatCore (strPartL dst.val ptr.val src.val).2
            (by have := snd_strPartL_le dst.val ptr.val src.val h; have := dst.property; scalar_tac))

theorem array_from_slice_eq {α : Type _} [Inhabited α] {n : Usize}
    (a : Array α n) (s : Slice α) :
    a.from_slice s = if h : s.val.length = n.val then Array.from s.val h else a := by
  simp [Array.from_slice]

def linesOfVec (v : alloc.vec.Vec (alloc.vec.Vec U8)) : List (List Nat) :=
  v.val.map (fun l => l.val.map (·.val))

def CtxExt (c c' : cbstm03a.Ctx) (stmts htmls : List (List UInt8)) : Prop :=
  linesOfVec c'.stmt = linesOfVec c.stmt ++ stmts.map (·.map cp037Code) ∧
  c'.stmt.val.length = c.stmt.val.length + stmts.length ∧
  linesOfVec c'.html = linesOfVec c.html ++ htmls.map (·.map cp037Code) ∧
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

theorem CtxExt_cons_html {c0 c1 c2 : cbstm03a.Ctx} {ss hs : List (List UInt8)} {b : List UInt8}
    (H1 : CtxExt c0 c1 [] [b]) (H2 : CtxExt c1 c2 ss hs) :
    CtxExt c0 c2 ss (b :: hs) := by
  have H12 := CtxExt_trans H1 H2
  simpa only [List.nil_append, List.singleton_append] using H12

theorem CtxExt_cons_stmt {c0 c1 c2 : cbstm03a.Ctx} {ss hs : List (List UInt8)} {b : List UInt8}
    (H1 : CtxExt c0 c1 [b] []) (H2 : CtxExt c1 c2 ss hs) :
    CtxExt c0 c2 (b :: ss) hs := by
  have H12 := CtxExt_trans H1 H2
  simpa only [List.nil_append, List.singleton_append] using H12

theorem sw_eq {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    (c : cbstm03a.Ctx) (line : Array U8 80#usize)
    (hcap : c.stmt.val.length + 1 ≤ Usize.max) :
    cbstm03a.sw c line = .ok { c with stmt :=
      (alloc.vec.Vec.from (c.stmt.val ++ [alloc.vec.Vec.from line.val (by scalar_tac)])
        (by simp; omega)) } := by
  refine eq_ok_of_wp ?_
  unfold cbstm03a.sw
  aeneas_wp [H.vb_eq, Array.to_slice, hcap]
  rw [dite_eq_left (by omega)]
  trivial

theorem hw_eq {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    (c : cbstm03a.Ctx) (lit : Slice U8)
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
  aeneas_wp [H.put_eq, H.vb_eq, Array.to_slice, Array.to_slice_mut, Array.repeat_val,
    Array.from_val, array_from_slice_eq, Slice.from_val, length_putL, List.length_replicate,
    uscalar_ofNat_val, Nat.reduceAdd, Nat.reduceLeDiff, ↓reduceDIte, hcap]
  rw [dite_eq_left (by omega)]
  trivial

theorem sw_ext {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    (c : cbstm03a.Ctx) (line : Array U8 80#usize) (bs : List UInt8)
    (hl : line.val = latL bs) (hcap : c.stmt.val.length + 1 ≤ Usize.max) :
    ∃ c', cbstm03a.sw c line = .ok c' ∧ CtxExt c c' [bs] [] := by
  refine ⟨_, sw_eq H c line hcap, ?_⟩
  simp [CtxExt, linesOfVec, hl, latL_val]

theorem hw_ext {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    (c : cbstm03a.Ctx) (lit : Slice U8) (bs : List UInt8)
    (hlit : putL (List.replicate 100 32#u8) 0 100 lit.val = latL bs)
    (hcap : c.html.val.length + 1 ≤ Usize.max) :
    ∃ c', cbstm03a.hw c lit = .ok c' ∧ CtxExt c c' [] [bs] := by
  refine ⟨_, hw_eq H c lit hcap, ?_⟩
  simp only [CtxExt, linesOfVec, alloc.vec.Vec.from_val, List.map_append, List.map_cons,
    List.map_nil, List.length_append, List.length_singleton, List.length_nil, List.append_nil,
    Nat.add_zero, hlit, latL_val, and_self]

/-! ## 2. `st_line` on all 16 line indices -/

theorem st_line_0_eq (st : cbstm03a.St) :
    cbstm03a.st_line 0#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← cbstm03a.fill s 0#usize 31#usize 42#u8
      let l1 := to_slice_mut_back s1
      let (s2, to_slice_mut_back1) ← lift (Array.to_slice_mut l1)
      let s3 ← lift (Array.to_slice (Array.make 18#usize [
        83#u8, 84#u8, 65#u8, 82#u8, 84#u8, 32#u8, 79#u8, 70#u8, 32#u8, 83#u8,
        84#u8, 65#u8, 84#u8, 69#u8, 77#u8, 69#u8, 78#u8, 84#u8 ]))
      let s4 ← cbstm03a.put s2 31#usize 18#usize s3
      let l2 := to_slice_mut_back1 s4
      let (s5, to_slice_mut_back2) ← lift (Array.to_slice_mut l2)
      let s6 ← cbstm03a.fill s5 49#usize 31#usize 42#u8
      Result.ok (to_slice_mut_back2 s6)) := rfl

theorem st_line_1_eq (st : cbstm03a.St) :
    cbstm03a.st_line 1#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← lift (Array.to_slice st.name)
      let s2 ← cbstm03a.put s 0#usize 75#usize s1
      Result.ok (to_slice_mut_back s2)) := rfl

theorem st_line_2_eq (st : cbstm03a.St) :
    cbstm03a.st_line 2#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← lift (Array.to_slice st.add1)
      let s2 ← cbstm03a.put s 0#usize 50#usize s1
      Result.ok (to_slice_mut_back s2)) := rfl

theorem st_line_3_eq (st : cbstm03a.St) :
    cbstm03a.st_line 3#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← lift (Array.to_slice st.add2)
      let s2 ← cbstm03a.put s 0#usize 50#usize s1
      Result.ok (to_slice_mut_back s2)) := rfl

theorem st_line_4_eq (st : cbstm03a.St) :
    cbstm03a.st_line 4#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← lift (Array.to_slice st.add3)
      let s2 ← cbstm03a.put s 0#usize 80#usize s1
      Result.ok (to_slice_mut_back s2)) := rfl

theorem st_line_5_eq (st : cbstm03a.St) :
    cbstm03a.st_line 5#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← cbstm03a.fill s 0#usize 80#usize 45#u8
      Result.ok (to_slice_mut_back s1)) := rfl

theorem st_line_6_eq (st : cbstm03a.St) :
    cbstm03a.st_line 6#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← lift (Array.to_slice (Array.make 13#usize [
        66#u8, 97#u8, 115#u8, 105#u8, 99#u8, 32#u8, 68#u8, 101#u8, 116#u8,
        97#u8, 105#u8, 108#u8, 115#u8 ]))
      let s2 ← cbstm03a.put s 33#usize 14#usize s1
      Result.ok (to_slice_mut_back s2)) := rfl

theorem st_line_7_eq (st : cbstm03a.St) :
    cbstm03a.st_line 7#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← lift (Array.to_slice (Array.make 20#usize [
        65#u8, 99#u8, 99#u8, 111#u8, 117#u8, 110#u8, 116#u8, 32#u8, 73#u8,
        68#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8 ]))
      let s2 ← cbstm03a.put s 0#usize 20#usize s1
      let l1 := to_slice_mut_back s2
      let (s3, to_slice_mut_back1) ← lift (Array.to_slice_mut l1)
      let s4 ← lift (Array.to_slice st.acct_id)
      let s5 ← cbstm03a.put s3 20#usize 20#usize s4
      Result.ok (to_slice_mut_back1 s5)) := rfl

theorem st_line_8_eq (st : cbstm03a.St) :
    cbstm03a.st_line 8#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← lift (Array.to_slice (Array.make 20#usize [
        67#u8, 117#u8, 114#u8, 114#u8, 101#u8, 110#u8, 116#u8, 32#u8, 66#u8,
        97#u8, 108#u8, 97#u8, 110#u8, 99#u8, 101#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8 ]))
      let s2 ← cbstm03a.put s 0#usize 20#usize s1
      let l1 := to_slice_mut_back s2
      let (s3, to_slice_mut_back1) ← lift (Array.to_slice_mut l1)
      let s4 ← lift (Array.to_slice st.curr_bal)
      let s5 ← cbstm03a.put s3 20#usize 13#usize s4
      Result.ok (to_slice_mut_back1 s5)) := rfl

theorem st_line_9_eq (st : cbstm03a.St) :
    cbstm03a.st_line 9#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← lift (Array.to_slice (Array.make 20#usize [
        70#u8, 73#u8, 67#u8, 79#u8, 32#u8, 83#u8, 99#u8, 111#u8, 114#u8,
        101#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8 ]))
      let s2 ← cbstm03a.put s 0#usize 20#usize s1
      let l1 := to_slice_mut_back s2
      let (s3, to_slice_mut_back1) ← lift (Array.to_slice_mut l1)
      let s4 ← lift (Array.to_slice st.fico)
      let s5 ← cbstm03a.put s3 20#usize 20#usize s4
      Result.ok (to_slice_mut_back1 s5)) := rfl

theorem st_line_10_eq (st : cbstm03a.St) :
    cbstm03a.st_line 10#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← cbstm03a.fill s 0#usize 80#usize 45#u8
      Result.ok (to_slice_mut_back s1)) := rfl

theorem st_line_11_eq (st : cbstm03a.St) :
    cbstm03a.st_line 11#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← lift (Array.to_slice (Array.make 20#usize [
        84#u8, 82#u8, 65#u8, 78#u8, 83#u8, 65#u8, 67#u8, 84#u8, 73#u8, 79#u8,
        78#u8, 32#u8, 83#u8, 85#u8, 77#u8, 77#u8, 65#u8, 82#u8, 89#u8, 32#u8 ]))
      let s2 ← cbstm03a.put s 30#usize 20#usize s1
      Result.ok (to_slice_mut_back s2)) := rfl

theorem st_line_12_eq (st : cbstm03a.St) :
    cbstm03a.st_line 12#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← cbstm03a.fill s 0#usize 80#usize 45#u8
      Result.ok (to_slice_mut_back s1)) := rfl

theorem st_line_13_eq (st : cbstm03a.St) :
    cbstm03a.st_line 13#u32 st = (do
      let l := Array.repeat 80#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l)
      let s1 ← lift (Array.to_slice (Array.make 16#usize [
        84#u8, 114#u8, 97#u8, 110#u8, 32#u8, 73#u8, 68#u8, 32#u8, 32#u8,
        32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8 ]))
      let s2 ← cbstm03a.put s 0#usize 16#usize s1
      let l1 := to_slice_mut_back s2
      let (s3, to_slice_mut_back1) ← lift (Array.to_slice_mut l1)
      let s4 ← lift (Array.to_slice (Array.make 16#usize [
        84#u8, 114#u8, 97#u8, 110#u8, 32#u8, 68#u8, 101#u8, 116#u8, 97#u8,
        105#u8, 108#u8, 115#u8, 32#u8, 32#u8, 32#u8, 32#u8 ]))
      let s5 ← cbstm03a.put s3 16#usize 51#usize s4
      let l2 := to_slice_mut_back1 s5
      let (s6, to_slice_mut_back2) ← lift (Array.to_slice_mut l2)
      let s7 ← lift (Array.to_slice (Array.make 13#usize [
        32#u8, 32#u8, 84#u8, 114#u8, 97#u8, 110#u8, 32#u8, 65#u8, 109#u8,
        111#u8, 117#u8, 110#u8, 116#u8 ]))
      let s8 ← cbstm03a.put s6 67#usize 13#usize s7
      Result.ok (to_slice_mut_back2 s8)) := rfl

theorem st_line_14_eq (st : cbstm03a.St) :
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

theorem st_line_140_eq (st : cbstm03a.St) :
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

theorem st_line_15_eq (st : cbstm03a.St) :
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

macro "st_line_wp" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| aeneas_wp [$xs,*, Array.to_slice, Array.to_slice_mut, Array.repeat_val,
    Array.make_val, Array.from_val, array_from_slice_eq, array_update_eq, Slice.from_val,
    length_putL, length_fillL, List.length_replicate, List.length_set, uscalar_ofNat_val,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, ↓reduceDIte])

theorem ok_array_from_eq {n : Usize} {a b : List U8} {ha : a.length = n.val} {hb : b.length = n.val}
    (h : a = b) :
    (Except.ok (Array.from a ha) : Except Error (Array U8 n)) = Except.ok (Array.from b hb) := by
  subst h; rfl

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem putL_exact (pre src post : List U8) (off len : Nat)
    (hpre : pre.length = off) (hsrc : src.length = len) :
    putL (pre ++ post) off len src = pre ++ src ++ post.drop len := by
  unfold putL
  rw [List.take_left' hpre, List.take_of_length_le (by rw [hsrc]), hsrc, Nat.sub_self,
    List.replicate_zero, List.append_nil, ← hpre, ← List.drop_drop, List.drop_left]

theorem putL_zero_exact (src post : List U8) (len : Nat) (hsrc : src.length = len) :
    putL post 0 len src = src ++ post.drop len := by
  have := putL_exact [] src post 0 len rfl hsrc
  simpa using this

theorem putL_pad (pre src post : List U8) (off len : Nat)
    (hpre : pre.length = off) (hsrc : src.length ≤ len) :
    putL (pre ++ post) off len src =
      pre ++ (src ++ List.replicate (len - src.length) 32#u8) ++ post.drop len := by
  unfold putL
  rw [List.take_left' hpre, List.take_of_length_le hsrc, ← hpre, ← List.drop_drop, List.drop_left]

theorem putL_zero_pad (src : List U8) (len : Nat) (hsrc : src.length ≤ len) :
    putL (List.replicate len 32#u8) 0 len src =
      src ++ List.replicate (len - src.length) 32#u8 := by
  have := putL_pad [] src (List.replicate len 32#u8) 0 len rfl hsrc
  simpa using this

theorem st_line_0 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St) :
    cbstm03a.st_line 0#u32 st = .ok (Array.from (latL c2470) (by rw [length_latL, c2470_lit]; rfl)) := by
  rw [st_line_0_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq; decide +kernel

theorem st_line_1 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St)
    (nm : List UInt8) (hnm : st.name.val = latL nm) (hnml : nm.length = 75) :
    cbstm03a.st_line 1#u32 st = .ok (Array.from (latL (nm ++ c2625)) (by simp [hnml, c2625_lit])) := by
  rw [st_line_1_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq
  have hc : (List.replicate 80 32#u8).drop 75 = latL c2625 := by decide +kernel
  rw [hnm, putL_zero_exact (latL nm) _ 75 (by simp [hnml]), hc, latL_append]

theorem st_line_2 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St)
    (a1 : List UInt8) (ha1 : st.add1.val = latL a1) (ha1l : a1.length = 50) :
    cbstm03a.st_line 2#u32 st = .ok (Array.from (latL (a1 ++ c2680)) (by simp [ha1l, c2680_lit])) := by
  rw [st_line_2_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq
  have hc : (List.replicate 80 32#u8).drop 50 = latL c2680 := by decide +kernel
  rw [ha1, putL_zero_exact (latL a1) _ 50 (by simp [ha1l]), hc, latL_append]

theorem st_line_3 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St)
    (a2 : List UInt8) (ha2 : st.add2.val = latL a2) (ha2l : a2.length = 50) :
    cbstm03a.st_line 3#u32 st = .ok (Array.from (latL (a2 ++ c2760)) (by simp [ha2l, c2760_lit])) := by
  rw [st_line_3_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq
  have hc : (List.replicate 80 32#u8).drop 50 = latL c2760 := by decide +kernel
  rw [ha2, putL_zero_exact (latL a2) _ 50 (by simp [ha2l]), hc, latL_append]

theorem st_line_4 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St)
    (a3 : List UInt8) (ha3 : st.add3.val = latL a3) (ha3l : a3.length = 80) :
    cbstm03a.st_line 4#u32 st = .ok (Array.from (latL a3) (by simp [ha3l])) := by
  rw [st_line_4_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq
  rw [ha3, putL_zero_exact (latL a3) _ 80 (by simp [ha3l])]
  have hd : (List.replicate 80 32#u8).drop 80 = [] := by decide +kernel
  rw [hd, List.append_nil]

theorem st_line_5 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St) :
    cbstm03a.st_line 5#u32 st = .ok (Array.from (latL c2870) (by rw [length_latL, c2870_lit]; rfl)) := by
  rw [st_line_5_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq; decide +kernel

theorem st_line_6 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St) :
    cbstm03a.st_line 6#u32 st = .ok (Array.from (latL c2950) (by rw [length_latL, c2950_lit]; rfl)) := by
  rw [st_line_6_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq; decide +kernel

theorem st_line_7 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St)
    (aidT : List UInt8) (haid : st.acct_id.val = latL aidT) (haidl : aidT.length = 20) :
    cbstm03a.st_line 7#u32 st =
      .ok (Array.from (latL (c3030 ++ aidT ++ c3070)) (by simp [haidl, c3030_lit, c3070_lit])) := by
  rw [st_line_7_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq
  have hp1 : putL (List.replicate 80 32#u8) 0 20
      [65#u8, 99#u8, 99#u8, 111#u8, 117#u8, 110#u8, 116#u8, 32#u8, 73#u8,
       68#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8] =
      latL c3030 ++ List.replicate 60 32#u8 := by decide +kernel
  rw [hp1, haid, putL_exact (latL c3030) (latL aidT) (List.replicate 60 32#u8) 20 20
    (by decide) (by simp [haidl])]
  have hc2 : (List.replicate 60 32#u8).drop 20 = latL c3070 := by decide +kernel
  rw [hc2, latL_append, latL_append]

theorem st_line_8 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St)
    (balT : List UInt8) (hbal : st.curr_bal.val = latL balT) (hball : balT.length = 13) :
    cbstm03a.st_line 8#u32 st =
      .ok (Array.from (latL (c3110 ++ balT ++ c3143)) (by simp [hball, c3110_lit, c3143_lit])) := by
  rw [st_line_8_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq
  have hp1 : putL (List.replicate 80 32#u8) 0 20
      [67#u8, 117#u8, 114#u8, 114#u8, 101#u8, 110#u8, 116#u8, 32#u8, 66#u8,
       97#u8, 108#u8, 97#u8, 110#u8, 99#u8, 101#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8] =
      latL c3110 ++ List.replicate 60 32#u8 := by decide +kernel
  rw [hp1, hbal, putL_exact (latL c3110) (latL balT) (List.replicate 60 32#u8) 20 13
    (by decide) (by simp [hball])]
  have hc2 : (List.replicate 60 32#u8).drop 13 = latL c3143 := by decide +kernel
  rw [hc2, latL_append, latL_append]

theorem st_line_9 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St)
    (ficoT : List UInt8) (hfico : st.fico.val = latL ficoT) (hficol : ficoT.length = 20) :
    cbstm03a.st_line 9#u32 st =
      .ok (Array.from (latL (c3190 ++ ficoT ++ c3230)) (by simp [hficol, c3190_lit, c3230_lit])) := by
  rw [st_line_9_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq
  have hp1 : putL (List.replicate 80 32#u8) 0 20
      [70#u8, 73#u8, 67#u8, 79#u8, 32#u8, 83#u8, 99#u8, 111#u8, 114#u8,
       101#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8] =
      latL c3190 ++ List.replicate 60 32#u8 := by decide +kernel
  rw [hp1, hfico, putL_exact (latL c3190) (latL ficoT) (List.replicate 60 32#u8) 20 20
    (by decide) (by simp [hficol])]
  have hc2 : (List.replicate 60 32#u8).drop 20 = latL c3230 := by decide +kernel
  rw [hc2, latL_append, latL_append]

theorem st_line_10 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St) :
    cbstm03a.st_line 10#u32 st = .ok (Array.from (latL c3270) (by rw [length_latL, c3270_lit]; rfl)) := by
  rw [st_line_10_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq; decide +kernel

theorem st_line_11 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St) :
    cbstm03a.st_line 11#u32 st = .ok (Array.from (latL c3350) (by rw [length_latL, c3350_lit]; rfl)) := by
  rw [st_line_11_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq; decide +kernel

theorem st_line_12 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St) :
    cbstm03a.st_line 12#u32 st = .ok (Array.from (latL c3430) (by rw [length_latL, c3430_lit]; rfl)) := by
  rw [st_line_12_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq; decide +kernel

theorem st_line_13 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St) :
    cbstm03a.st_line 13#u32 st = .ok (Array.from (latL c3510) (by rw [length_latL, c3510_lit]; rfl)) := by
  rw [st_line_13_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq; decide +kernel

theorem st_line_14 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St)
    (tid dt amtT : List UInt8)
    (htid : st.tranid.val = latL tid) (htidl : tid.length = 16)
    (hdt : st.trandt.val = latL dt) (hdtl : dt.length = 49)
    (hamt : st.tranamt.val = latL amtT) (hamtl : amtT.length = 13) :
    cbstm03a.st_line 14#u32 st =
      .ok (Array.from (latL (tid ++ c3606 ++ dt ++ c3656 ++ amtT))
        (by simp [htidl, hdtl, hamtl, c3606_lit, c3656_lit])) := by
  rw [st_line_14_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
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

theorem st_line_140 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St)
    (totT : List UInt8) (htot : st.total_tramt.val = latL totT) (htotl : totT.length = 13) :
    cbstm03a.st_line 140#u32 st =
      .ok (Array.from (latL (c3670 ++ totT)) (by simp [htotl, c3670_lit])) := by
  rw [st_line_140_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq
  rw [htot]
  have htl : (latL totT).length = 13 := by simp [htotl]
  have hs1 : (putL (List.replicate 80 32#u8) 0 10
      [84#u8, 111#u8, 116#u8, 97#u8, 108#u8, 32#u8, 69#u8, 88#u8, 80#u8, 58#u8]).set 66 36#u8 =
      latL c3670 ++ List.replicate 13 32#u8 := by decide +kernel
  have hd : (List.replicate 13 32#u8).drop 13 = [] := by decide +kernel
  rw [hs1, putL_exact (latL c3670) (latL totT) (List.replicate 13 32#u8) 67 13 (by decide) htl,
    hd, List.append_nil, latL_append]

theorem st_line_15 {tbl : Array U8 256#usize} (H : Helpers1 tbl) (st : cbstm03a.St) :
    cbstm03a.st_line 15#u32 st = .ok (Array.from (latL c3750) (by rw [length_latL, c3750_lit]; rfl)) := by
  rw [st_line_15_eq]; refine eq_ok_of_wp ?_; st_line_wp [H.fill_eq, H.put_eq]
  apply ok_array_from_eq; decide +kernel

/-! ## 3. `html_p_line`, `html_header`, and `html_nmadbs` -/

theorem latL_64 : [32#u8] = latL [64] := by decide +kernel
theorem latL_64_64 : [32#u8, 32#u8] = latL [64, 64] := by decide +kernel
theorem latL_tEndP : [60#u8, 47#u8, 112#u8, 62#u8] = latL tEndP := by decide +kernel
@[simp] theorem tokB_92_tEndP : tokB 92 tEndP = tEndP := by decide +kernel
@[simp] theorem length_sp (n : Nat) : (sp n).length = n := by simp [sp]

theorem html_p_line_two_space_ext {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    (c : cbstm03a.Ctx) (pre data delim : Slice U8) (p bs : List UInt8)
    (hpre : pre.val = latL p) (htokp : tokB 92 p = p) (hplen : p.length ≤ 500)
    (hdata : data.val = latL bs) (hbslen : bs.length ≤ 500) (hdelim : delim.val = [32#u8, 32#u8])
    (hcap : c.html.val.length + 1 ≤ Usize.max) :
    ∃ c', cbstm03a.html_p_line c pre data delim true = .ok c' ∧
      CtxExt c c' [] [hfield p (tok2 bs ++ [64, 64]) tEndP] := by
  have heq : cbstm03a.html_p_line c pre data delim true = .ok { c with html :=
      (alloc.vec.Vec.from (c.html.val ++ [alloc.vec.Vec.from
        (latL (hfield p (tok2 bs ++ [64, 64]) tEndP))
        (by
          have := usize_max_ge
          simp [hfield, length_ovw, sp]; omega)])
      (by simp; omega)) } := by
    have htendp_len : tEndP.length ≤ 500 := by decide
    refine eq_ok_of_wp ?_
    unfold cbstm03a.html_p_line
    aeneas_wp [H.str_part_star, H.str_part_two_space, H.str_part_empty, H.vb_eq,
      Array.to_slice, Array.to_slice_mut, Array.repeat_val, Array.make_val, Std.Array.empty,
      Array.from_val, array_from_slice_eq, Slice.from_val, UScalar.ofNatCore_val_eq,
      hpre, htokp, hplen, hdata, hbslen, hdelim, latL_64_64, latL_tEndP, htendp_len,
      tokBL_star_latL, tok2L_latL, tokB_92_tEndP,
      strPartL_zero_fst, strPartL_zero_snd, strPartL_chain_fst, strPartL_chain_snd,
      length_latL, length_ovw, length_sp, List.length_replicate, uscalar_ofNat_val,
      Nat.min_le_right, Nat.zero_le, ↓reduceDIte, ↓reduceIte, hcap]
    rw [dite_eq_left (by omega)]
    simp only [hfield, List.append_assoc]
  refine ⟨_, heq, ?_⟩
  simp [CtxExt, linesOfVec, latL_val]

theorem html_p_line_star_ext {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    (c : cbstm03a.Ctx) (pre data delim : Slice U8) (p bs : List UInt8)
    (hpre : pre.val = latL p) (htokp : tokB 92 p = p) (hplen : p.length ≤ 500)
    (hdata : data.val = latL bs) (hbslen : bs.length ≤ 500) (hdelim : delim.val = [42#u8])
    (hcap : c.html.val.length + 1 ≤ Usize.max) :
    ∃ c', cbstm03a.html_p_line c pre data delim false = .ok c' ∧
      CtxExt c c' [] [hfield p (tokB 92 bs) tEndP] := by
  have heq : cbstm03a.html_p_line c pre data delim false = .ok { c with html :=
      (alloc.vec.Vec.from (c.html.val ++ [alloc.vec.Vec.from
        (latL (hfield p (tokB 92 bs) tEndP))
        (by
          have := usize_max_ge
          simp [hfield, length_ovw, sp]; omega)])
      (by simp; omega)) } := by
    have htendp_len : tEndP.length ≤ 500 := by decide
    refine eq_ok_of_wp ?_
    unfold cbstm03a.html_p_line
    aeneas_wp [H.str_part_star, H.vb_eq,
      Array.to_slice, Array.to_slice_mut, Array.repeat_val, Array.make_val,
      Array.from_val, array_from_slice_eq, Slice.from_val, UScalar.ofNatCore_val_eq,
      hpre, htokp, hplen, hdata, hbslen, hdelim, latL_tEndP, htendp_len,
      tokBL_star_latL, tokB_92_tEndP,
      strPartL_zero_fst, strPartL_zero_snd, strPartL_chain_fst, strPartL_chain_snd,
      length_latL, length_ovw, length_sp, List.length_replicate, uscalar_ofNat_val,
      Nat.min_le_right, Nat.zero_le, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte, hcap]
    rw [dite_eq_left (by omega)]
    simp only [hfield, List.append_assoc]
  refine ⟨_, heq, ?_⟩
  simp [CtxExt, linesOfVec, latL_val]

theorem step_hw {α : Type _} {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    {c : cbstm03a.Ctx} {ss hs : List (List UInt8)} {n : Nat}
    (hcap : c.html.val.length + (n + 1) ≤ Usize.max)
    (lit : Slice U8) (bs : List UInt8)
    (hlit : putL (List.replicate 100 32#u8) 0 100 lit.val = latL bs)
    {k : cbstm03a.Ctx → Std.Result α} {f : α → cbstm03a.Ctx}
    (hk : ∀ c1, c1.stmt.val.length = c.stmt.val.length →
      c1.html.val.length + n ≤ Usize.max →
      ∃ res, k c1 = .ok res ∧ CtxExt c1 (f res) ss hs) :
    ∃ res, (do let c1 ← cbstm03a.hw c lit; k c1) = .ok res ∧ CtxExt c (f res) ss (bs :: hs) := by
  obtain ⟨c1, h1, he1⟩ := hw_ext H c lit bs hlit (by omega)
  rw [h1, bind_tc_ok]
  have hs1 : c1.stmt.val.length = c.stmt.val.length := by
    have := he1.2.1; simpa only [List.length_nil, Nat.add_zero] using this
  have hcap1 : c1.html.val.length + n ≤ Usize.max := by
    have := he1.2.2.2.1; simp only [List.length_singleton] at this; omega
  obtain ⟨res, hres, he2⟩ := hk c1 hs1 hcap1
  exact ⟨res, hres, CtxExt_cons_html he1 he2⟩

theorem last_hw {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    {c : cbstm03a.Ctx} (hcap : c.html.val.length + 1 ≤ Usize.max)
    (lit : Slice U8) (bs : List UInt8)
    (hlit : putL (List.replicate 100 32#u8) 0 100 lit.val = latL bs) :
    ∃ c1, cbstm03a.hw c lit = .ok c1 ∧ CtxExt c c1 [] [bs] :=
  hw_ext H c lit bs hlit hcap

theorem step_p2 {α : Type _} {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    {c : cbstm03a.Ctx} {ss hs : List (List UInt8)} {n : Nat}
    (hcap : c.html.val.length + (n + 1) ≤ Usize.max)
    (pre data delim : Slice U8) (p bs : List UInt8)
    (hpre : pre.val = latL p) (htokp : tokB 92 p = p) (hplen : p.length ≤ 500)
    (hdata : data.val = latL bs) (hbslen : bs.length ≤ 500) (hdelim : delim.val = [32#u8, 32#u8])
    {k : cbstm03a.Ctx → Std.Result α} {f : α → cbstm03a.Ctx}
    (hk : ∀ c1, c1.stmt.val.length = c.stmt.val.length →
      c1.html.val.length + n ≤ Usize.max →
      ∃ res, k c1 = .ok res ∧ CtxExt c1 (f res) ss hs) :
    ∃ res, (do let c1 ← cbstm03a.html_p_line c pre data delim true; k c1) = .ok res ∧
      CtxExt c (f res) ss (hfield p (tok2 bs ++ [64, 64]) tEndP :: hs) := by
  obtain ⟨c1, h1, he1⟩ := html_p_line_two_space_ext H c pre data delim p bs hpre htokp hplen hdata hbslen hdelim (by omega)
  rw [h1, bind_tc_ok]
  have hs1 : c1.stmt.val.length = c.stmt.val.length := by
    have := he1.2.1; simpa only [List.length_nil, Nat.add_zero] using this
  have hcap1 : c1.html.val.length + n ≤ Usize.max := by
    have := he1.2.2.2.1; simp only [List.length_singleton] at this; omega
  obtain ⟨res, hres, he2⟩ := hk c1 hs1 hcap1
  exact ⟨res, hres, CtxExt_cons_html he1 he2⟩

theorem step_pstar {α : Type _} {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    {c : cbstm03a.Ctx} {ss hs : List (List UInt8)} {n : Nat}
    (hcap : c.html.val.length + (n + 1) ≤ Usize.max)
    (pre data delim : Slice U8) (p bs : List UInt8)
    (hpre : pre.val = latL p) (htokp : tokB 92 p = p) (hplen : p.length ≤ 500)
    (hdata : data.val = latL bs) (hbslen : bs.length ≤ 500) (hdelim : delim.val = [42#u8])
    {k : cbstm03a.Ctx → Std.Result α} {f : α → cbstm03a.Ctx}
    (hk : ∀ c1, c1.stmt.val.length = c.stmt.val.length →
      c1.html.val.length + n ≤ Usize.max →
      ∃ res, k c1 = .ok res ∧ CtxExt c1 (f res) ss hs) :
    ∃ res, (do let c1 ← cbstm03a.html_p_line c pre data delim false; k c1) = .ok res ∧
      CtxExt c (f res) ss (hfield p (tokB 92 bs) tEndP :: hs) := by
  obtain ⟨c1, h1, he1⟩ := html_p_line_star_ext H c pre data delim p bs hpre htokp hplen hdata hbslen hdelim (by omega)
  rw [h1, bind_tc_ok]
  have hs1 : c1.stmt.val.length = c.stmt.val.length := by
    have := he1.2.1; simpa only [List.length_nil, Nat.add_zero] using this
  have hcap1 : c1.html.val.length + n ≤ Usize.max := by
    have := he1.2.2.2.1; simp only [List.length_singleton] at this; omega
  obtain ⟨res, hres, he2⟩ := hk c1 hs1 hcap1
  exact ⟨res, hres, CtxExt_cons_html he1 he2⟩

theorem ite_true_of {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem array_to_slice_val {α : Type} {n : Usize} (a : Array α n) :
    a.to_slice.val = a.val := by simp [Array.to_slice]

theorem step_st_sw {α : Type} {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    {c : cbstm03a.Ctx} {ss hs : List (List UInt8)} {n : Nat}
    (hcaps : c.stmt.val.length + (n + 1) ≤ Usize.max)
    {idx : U32} {st : cbstm03a.St} (bs : List UInt8) {hbs : (latL bs).length = (80#usize).val}
    (hst : cbstm03a.st_line idx st = .ok (Array.from (latL bs) hbs))
    {k : cbstm03a.Ctx → Std.Result α} {f : α → cbstm03a.Ctx}
    (hk : ∀ c1, c1.stmt.val.length + n ≤ Usize.max →
      c1.html.val.length = c.html.val.length →
      ∃ res, k c1 = .ok res ∧ CtxExt c1 (f res) ss hs) :
    ∃ res, (do let l ← cbstm03a.st_line idx st; let c1 ← cbstm03a.sw c l; k c1) = .ok res ∧
      CtxExt c (f res) (bs :: ss) hs := by
  rw [hst, bind_tc_ok]
  obtain ⟨c1, h1, he1⟩ := sw_ext H c (Array.from (latL bs) hbs) bs (Array.from_val _ _) (by omega)
  rw [h1, bind_tc_ok]
  have hcaps1 : c1.stmt.val.length + n ≤ Usize.max := by
    have := he1.2.1; simp only [List.length_singleton] at this; omega
  have hh1 : c1.html.val.length = c.html.val.length := by
    have := he1.2.2.2.1; simpa only [List.length_nil, Nat.add_zero] using this
  obtain ⟨res, hres, he2⟩ := hk c1 hcaps1 hh1
  exact ⟨res, hres, CtxExt_cons_stmt he1 he2⟩

theorem array_index_range {n : Usize} (a : Array U8 n) (j k : Usize)
    (hjk : j.val ≤ k.val) (hk : k.val ≤ n.val) :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      a { start := j, «end» := k } =
      .ok (Slice.from ((a.val.drop j.val).take (k.val - j.val))
        (by have := List.length_take_le (k.val - j.val) (a.val.drop j.val); scalar_tac)) := by
  simp only [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice, core.slice.index.SliceIndexRangeUsizeSlice.index]
  have hl : a.to_slice.length = n.val := by simp [Array.to_slice]
  rw [ite_true_of ⟨by simpa [UScalar.le_equiv] using hjk, by rw [hl]; exact hk⟩]
  congr 1
  rw [Slice.eq_iff]
  simp [List.slice, Array.to_slice]

theorem array_index_range_nat {n : Usize} (a : Array U8 n) (j k : Usize) (jN lenN : Nat)
    (hj : j.val = jN) (hlen : k.val - j.val = lenN)
    (hjk : j.val ≤ k.val) (hk : k.val ≤ n.val) :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      a { start := j, «end» := k } =
      .ok (Slice.from ((a.val.drop jN).take lenN)
        (by have := List.length_take_le lenN (a.val.drop jN); scalar_tac)) := by
  subst hj hlen
  exact array_index_range a j k hjk hk

theorem hw_L01 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L01.val = latL hL01 := by decide +kernel
theorem hw_L02 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L02.val = latL hL02 := by decide +kernel
theorem hw_L03 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L03.val = latL hL03 := by decide +kernel
theorem hw_L04 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L04.val = latL hL04 := by decide +kernel
theorem hw_L05 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L05.val = latL hL05 := by decide +kernel
theorem hw_L06 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L06.val = latL hL06 := by decide +kernel
theorem hw_L07 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L07.val = latL hL07 := by decide +kernel
theorem hw_L08 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L08.val = latL hL08 := by decide +kernel
theorem hw_LTRS : putL (List.replicate 100 32#u8) 0 100 cbstm03a.LTRS.val = latL hLTRS := by decide +kernel
theorem hw_LTRE : putL (List.replicate 100 32#u8) 0 100 cbstm03a.LTRE.val = latL hLTRE := by decide +kernel
theorem hw_LTDE : putL (List.replicate 100 32#u8) 0 100 cbstm03a.LTDE.val = latL hLTDE := by decide +kernel
theorem hw_L10 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L10.val = latL hL10 := by decide +kernel
theorem hw_L15 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L15.val = latL hL15 := by decide +kernel
theorem hw_L16 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L16.val = latL hL16 := by decide +kernel
theorem hw_L17 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L17.val = latL hL17 := by decide +kernel
theorem hw_L18 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L18.val = latL hL18 := by decide +kernel
theorem hw_L22_35 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L22_35.val = latL hL22_35 := by decide +kernel
theorem hw_L30_42 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L30_42.val = latL hL30_42 := by decide +kernel
theorem hw_L31 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L31.val = latL hL31 := by decide +kernel
theorem hw_L43 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L43.val = latL hL43 := by decide +kernel
theorem hw_L47 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L47.val = latL hL47 := by decide +kernel
theorem hw_L48 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L48.val = latL hL48 := by decide +kernel
theorem hw_L50 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L50.val = latL hL50 := by decide +kernel
theorem hw_L51 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L51.val = latL hL51 := by decide +kernel
theorem hw_L53 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L53.val = latL hL53 := by decide +kernel
theorem hw_L54 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L54.val = latL hL54 := by decide +kernel
theorem hw_L58 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L58.val = latL hL58 := by decide +kernel
theorem hw_L61 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L61.val = latL hL61 := by decide +kernel
theorem hw_L64 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L64.val = latL hL64 := by decide +kernel
theorem hw_L75 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L75.val = latL hL75 := by decide +kernel
theorem hw_L78 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L78.val = latL hL78 := by decide +kernel
theorem hw_L79 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L79.val = latL hL79 := by decide +kernel
theorem hw_L80 : putL (List.replicate 100 32#u8) 0 100 cbstm03a.L80.val = latL hL80 := by decide +kernel

theorem putL_html_l11 (s4 : List U8) (d11 : List UInt8)
    (hs4 : s4 = latL d11) (hd11l : d11.length = 11) :
    putL (List.replicate 100 32#u8) 0 100
      (putL (putL (putL (List.replicate 59 32#u8) 0 34
        [60#u8, 104#u8, 51#u8, 62#u8, 83#u8, 116#u8, 97#u8, 116#u8, 101#u8,
         109#u8, 101#u8, 110#u8, 116#u8, 32#u8, 102#u8, 111#u8, 114#u8, 32#u8,
         65#u8, 99#u8, 99#u8, 111#u8, 117#u8, 110#u8, 116#u8, 32#u8, 78#u8,
         117#u8, 109#u8, 98#u8, 101#u8, 114#u8, 58#u8, 32#u8]) 34 20 s4) 54 5
        [60#u8, 47#u8, 104#u8, 51#u8, 62#u8]) =
    latL (c3930 ++ (d11 ++ sp 9) ++ c3984 ++ sp 41) := by
  rw [hs4]
  have hp1 : putL (List.replicate 59 32#u8) 0 34
      [60#u8, 104#u8, 51#u8, 62#u8, 83#u8, 116#u8, 97#u8, 116#u8, 101#u8,
       109#u8, 101#u8, 110#u8, 116#u8, 32#u8, 102#u8, 111#u8, 114#u8, 32#u8,
       65#u8, 99#u8, 99#u8, 111#u8, 117#u8, 110#u8, 116#u8, 32#u8, 78#u8,
       117#u8, 109#u8, 98#u8, 101#u8, 114#u8, 58#u8, 32#u8] =
      latL c3930 ++ List.replicate 25 32#u8 := by decide +kernel
  have hdl : (latL d11).length = 11 := by simp [hd11l]
  rw [hp1, putL_pad (latL c3930) (latL d11) (List.replicate 25 32#u8) 34 20 (by decide) (by omega),
    hdl, show 20 - 11 = 9 by rfl,
    show (List.replicate 25 32#u8).drop 20 = List.replicate 5 32#u8 by decide +kernel,
    putL_exact (latL c3930 ++ (latL d11 ++ List.replicate 9 32#u8))
      [60#u8, 47#u8, 104#u8, 51#u8, 62#u8] (List.replicate 5 32#u8) 54 5
      (by simp [hdl]; decide) (by decide),
    show (List.replicate 5 32#u8).drop 5 = [] by decide +kernel, List.append_nil,
    putL_zero_pad _ 100 (by simp [hdl]; decide)]
  have hlen59 : (latL c3930 ++ (latL d11 ++ List.replicate 9 32#u8) ++
      [60#u8, 47#u8, 104#u8, 51#u8, 62#u8]).length = 59 := by simp [hdl]; decide
  have hc3984 : [60#u8, 47#u8, 104#u8, 51#u8, 62#u8] = latL c3984 := by decide +kernel
  have hsp9 : List.replicate 9 32#u8 = latL (sp 9) := by decide +kernel
  have hsp41 : List.replicate 41 32#u8 = latL (sp 41) := by decide +kernel
  rw [hlen59, show 100 - 59 = 41 by rfl, hc3984, hsp9, hsp41]
  simp [latL_append, List.append_assoc]

theorem lift_eq {α : Type} (x : α) : lift x = .ok x := rfl
theorem bind_ok_tc {α β : Type} (x : α) (f : α → Std.Result β) :
    (do let y ← Result.ok x; f y) = f x := bind_tc_ok x f

theorem step_html_l11 {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    {c : cbstm03a.Ctx} {ss hs : List (List UInt8)} {n : Nat}
    (hcap : c.html.val.length + (n + 1) ≤ Usize.max)
    (acct : Array U8 300#usize) (d11 : List UInt8)
    (hd11 : (acct.val.drop 0).take 11 = latL d11) (hd11l : d11.length = 11)
    {k : cbstm03a.Ctx → Std.Result cbstm03a.Ctx}
    (hk : ∀ c1, c1.stmt.val.length = c.stmt.val.length →
      c1.html.val.length + n ≤ Usize.max →
      ∃ res, k c1 = .ok res ∧ CtxExt c1 res ss hs) :
    ∃ res, (do
      let l11 := Array.repeat 59#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l11)
      let s1 ←
        lift (Array.to_slice
          (Array.make 34#usize [
            60#u8, 104#u8, 51#u8, 62#u8, 83#u8, 116#u8, 97#u8, 116#u8, 101#u8,
            109#u8, 101#u8, 110#u8, 116#u8, 32#u8, 102#u8, 111#u8, 114#u8, 32#u8,
            65#u8, 99#u8, 99#u8, 111#u8, 117#u8, 110#u8, 116#u8, 32#u8, 78#u8,
            117#u8, 109#u8, 98#u8, 101#u8, 114#u8, 58#u8, 32#u8
          ]))
      let s2 ← cbstm03a.put s 0#usize 34#usize s1
      let l111 := to_slice_mut_back s2
      let (s3, to_slice_mut_back1) ← lift (Array.to_slice_mut l111)
      let s4 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) acct
          { start := 0#usize, «end» := 11#usize }
      let s5 ← cbstm03a.put s3 34#usize 20#usize s4
      let l112 := to_slice_mut_back1 s5
      let (s6, to_slice_mut_back2) ← lift (Array.to_slice_mut l112)
      let s7 ←
        lift (Array.to_slice
          (Array.make 5#usize [ 60#u8, 47#u8, 104#u8, 51#u8, 62#u8 ]))
      let s8 ← cbstm03a.put s6 54#usize 5#usize s7
      let l113 := to_slice_mut_back2 s8
      let s9 ← lift (Array.to_slice l113)
      let c11 ← cbstm03a.hw c s9
      k c11) = .ok res ∧
      CtxExt c res ss ((c3930 ++ (d11 ++ sp 9) ++ c3984 ++ sp 41) :: hs) := by
  simp only [lift_eq, bind_tc_ok,
    array_index_range acct 0#usize 11#usize (by decide) (by decide),
    H.put_eq, Array.to_slice, Array.to_slice_mut, Array.repeat_val, Array.make_val,
    Array.from_val, array_from_slice_eq, Slice.from_val, length_putL, List.length_replicate,
    UScalar.ofNatCore_val_eq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, ↓reduceDIte]
  refine step_hw H hcap _ (c3930 ++ (d11 ++ sp 9) ++ c3984 ++ sp 41) ?_ hk
  rw [Slice.from_val]
  exact putL_html_l11 _ d11 hd11 hd11l

theorem html_header_ext {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    (c : cbstm03a.Ctx) (acct : Array U8 300#usize) (d11 : List UInt8)
    (hd11 : (acct.val.drop 0).take 11 = latL d11) (hd11l : d11.length = 11)
    (hcap : c.html.val.length + 22 ≤ Usize.max) :
    ∃ c', cbstm03a.html_header c acct = .ok c' ∧
      CtxExt c c' []
        [hL01, hL02, hL03, hL04, hL05, hL06, hL07, hL08, hLTRS, hL10,
         c3930 ++ (d11 ++ sp 9) ++ c3984 ++ sp 41,
         hLTDE, hLTRE, hLTRS, hL15, hL16, hL17, hL18, hLTDE, hLTRE, hLTRS, hL22_35] := by
  unfold cbstm03a.html_header
  refine step_hw (f := id) H hcap _ _ hw_L01 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L02 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L03 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L04 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L05 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L06 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L07 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L08 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTRS (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L10 (fun c _ hcap => ?_)
  refine step_html_l11 H hcap acct d11 hd11 hd11l (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTDE (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTRE (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTRS (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L15 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L16 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L17 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L18 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTDE (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTRE (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTRS (fun c _ hcap => ?_)
  exact last_hw H hcap _ _ hw_L22_35

theorem putL_take_50 (nm : List UInt8) (hnml : nm.length = 75) :
    putL (List.replicate 50 32#u8) 0 50 (latL nm) = latL (nm.take 50) := by
  unfold putL
  have h : (latL nm).length = 75 := by simp [hnml]
  simp [h, latL_take]

theorem latL_tPStyle :
    (Array.make 26#usize [
      60#u8, 112#u8, 32#u8, 115#u8, 116#u8, 121#u8, 108#u8, 101#u8, 61#u8,
      34#u8, 102#u8, 111#u8, 110#u8, 116#u8, 45#u8, 115#u8, 105#u8, 122#u8,
      101#u8, 58#u8, 49#u8, 54#u8, 112#u8, 120#u8, 34#u8, 62#u8 ]).val = latL tPStyle := by
  decide +kernel

theorem tokB_92_tPStyle : tokB 92 tPStyle = tPStyle := by decide +kernel

theorem latL_tP : [60#u8, 112#u8, 62#u8] = latL tP := by decide +kernel
theorem tokB_92_tP : tokB 92 tP = tP := by decide +kernel

theorem latL_tAcct :
    (Array.make 24#usize [
      60#u8, 112#u8, 62#u8, 65#u8, 99#u8, 99#u8, 111#u8, 117#u8, 110#u8,
      116#u8, 32#u8, 73#u8, 68#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8,
      32#u8, 32#u8, 32#u8, 58#u8, 32#u8 ]).val = latL tAcct := by
  decide +kernel

theorem tokB_92_tAcct : tokB 92 tAcct = tAcct := by decide +kernel

theorem latL_tBal :
    (Array.make 24#usize [
      60#u8, 112#u8, 62#u8, 67#u8, 117#u8, 114#u8, 114#u8, 101#u8, 110#u8,
      116#u8, 32#u8, 66#u8, 97#u8, 108#u8, 97#u8, 110#u8, 99#u8, 101#u8,
      32#u8, 32#u8, 32#u8, 32#u8, 58#u8, 32#u8 ]).val = latL tBal := by
  decide +kernel

theorem tokB_92_tBal : tokB 92 tBal = tBal := by decide +kernel

theorem latL_tFico :
    (Array.make 24#usize [
      60#u8, 112#u8, 62#u8, 70#u8, 73#u8, 67#u8, 79#u8, 32#u8, 83#u8, 99#u8,
      111#u8, 114#u8, 101#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8,
      32#u8, 32#u8, 32#u8, 58#u8, 32#u8 ]).val = latL tFico := by
  decide +kernel

theorem tokB_92_tFico : tokB 92 tFico = tFico := by decide +kernel

theorem step_nmadbs_l23 {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    {c : cbstm03a.Ctx} {ss hs : List (List UInt8)} {n : Nat}
    (hcap : c.html.val.length + (n + 1) ≤ Usize.max)
    (st : cbstm03a.St) (nm : List UInt8) (hnm : st.name.val = latL nm) (hnml : nm.length = 75)
    {k : cbstm03a.Ctx → Std.Result cbstm03a.Ctx}
    (hk : ∀ c1, c1.stmt.val.length = c.stmt.val.length →
      c1.html.val.length + n ≤ Usize.max →
      ∃ res, k c1 = .ok res ∧ CtxExt c1 res ss hs) :
    ∃ res, (do
      let l23 := Array.repeat 50#usize 32#u8
      let (s, to_slice_mut_back) ← lift (Array.to_slice_mut l23)
      let s1 ← lift (Array.to_slice st.name)
      let s2 ← cbstm03a.put s 0#usize 50#usize s1
      let s3 ←
        lift (Array.to_slice
          (Array.make 26#usize [
            60#u8, 112#u8, 32#u8, 115#u8, 116#u8, 121#u8, 108#u8, 101#u8, 61#u8,
            34#u8, 102#u8, 111#u8, 110#u8, 116#u8, 45#u8, 115#u8, 105#u8, 122#u8,
            101#u8, 58#u8, 49#u8, 54#u8, 112#u8, 120#u8, 34#u8, 62#u8
          ]))
      let l231 := to_slice_mut_back s2
      let s4 ← lift (Array.to_slice l231)
      let s5 ← lift (Array.to_slice (Array.make 2#usize [ 32#u8, 32#u8 ]))
      let c1 ← cbstm03a.html_p_line c s3 s4 s5 true
      k c1) = .ok res ∧
      CtxExt c res ss (hfield tPStyle (tok2 (nm.take 50) ++ [64, 64]) tEndP :: hs) := by
  simp only [lift_eq, bind_tc_ok, H.put_eq, Array.to_slice, Array.to_slice_mut,
    Array.repeat_val, Array.make_val, Array.from_val, array_from_slice_eq, Slice.from_val,
    length_putL, List.length_replicate, UScalar.ofNatCore_val_eq,
    Nat.reduceAdd, Nat.reduceLeDiff, ↓reduceDIte]
  refine step_p2 (f := id) H hcap _ _ _ tPStyle (nm.take 50) ?_ tokB_92_tPStyle (by decide) ?_
    (by have := List.length_take_le 50 nm; omega) rfl hk
  · exact latL_tPStyle
  · rw [Slice.from_val, hnm, putL_take_50 nm hnml]

theorem step_nmadbs_p2 {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    {c : cbstm03a.Ctx} {ss hs : List (List UInt8)} {m : Usize} {cap : Nat}
    (hcap : c.html.val.length + (cap + 1) ≤ Usize.max)
    (arr : Array U8 m) (bs : List UInt8) (hbs : arr.val = latL bs)
    {k : cbstm03a.Ctx → Std.Result cbstm03a.Ctx}
    (hk : ∀ c1, c1.stmt.val.length = c.stmt.val.length →
      c1.html.val.length + cap ≤ Usize.max →
      ∃ res, k c1 = .ok res ∧ CtxExt c1 res ss hs)
    (hm : m.val ≤ 500 := by decide) :
    ∃ res, (do
      let s6 ← lift (Array.to_slice (Array.make 3#usize [ 60#u8, 112#u8, 62#u8 ]))
      let s7 ← lift (Array.to_slice arr)
      let s8 ← lift (Array.to_slice (Array.make 2#usize [ 32#u8, 32#u8 ]))
      let c2 ← cbstm03a.html_p_line c s6 s7 s8 true
      k c2) = .ok res ∧
      CtxExt c res ss (hfield tP (tok2 bs ++ [64, 64]) tEndP :: hs) := by
  have hbslen : bs.length ≤ 500 := by
    have := arr.property; rw [hbs, length_latL] at this; omega
  simp only [lift_eq, bind_tc_ok, Array.to_slice, Array.make_val]
  refine step_p2 (f := id) H hcap _ _ _ tP bs ?_ tokB_92_tP (by decide) ?_ hbslen rfl hk
  · exact latL_tP
  · rw [Slice.from_val]; exact hbs

theorem step_nmadbs_pstar {α : Type _} {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    {c : cbstm03a.Ctx} {ss hs : List (List UInt8)} {n m : Usize} {cap : Nat}
    (hcap : c.html.val.length + (cap + 1) ≤ Usize.max)
    (preArr : Array U8 n) (arr : Array U8 m) (p bs : List UInt8)
    (hpre : preArr.val = latL p) (htokp : tokB 92 p = p) (hbs : arr.val = latL bs)
    {k : cbstm03a.Ctx → Std.Result α} {f : α → cbstm03a.Ctx}
    (hk : ∀ c1, c1.stmt.val.length = c.stmt.val.length →
      c1.html.val.length + cap ≤ Usize.max →
      ∃ res, k c1 = .ok res ∧ CtxExt c1 (f res) ss hs)
    (hn : n.val ≤ 500 := by decide) (hm : m.val ≤ 500 := by decide) :
    ∃ res, (do
      let s15 ← lift (Array.to_slice preArr)
      let s16 ← lift (Array.to_slice arr)
      let s17 ← lift (Array.to_slice (Array.make 1#usize [ 42#u8 ]))
      let c14 ← cbstm03a.html_p_line c s15 s16 s17 false
      k c14) = .ok res ∧
      CtxExt c (f res) ss (hfield p (tokB 92 bs) tEndP :: hs) := by
  have hplen : p.length ≤ 500 := by
    have := preArr.property; rw [hpre, length_latL] at this; omega
  have hbslen : bs.length ≤ 500 := by
    have := arr.property; rw [hbs, length_latL] at this; omega
  simp only [lift_eq, bind_tc_ok, Array.to_slice, Array.make_val]
  refine step_pstar H hcap _ _ _ p bs ?_ htokp hplen ?_ hbslen rfl hk
  · rw [Slice.from_val]; exact hpre
  · rw [Slice.from_val]; exact hbs

theorem html_nmadbs_ext {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    (c : cbstm03a.Ctx) (st : cbstm03a.St)
    (nm a1 a2 a3 aidT balT ficoT : List UInt8)
    (hnm : st.name.val = latL nm) (hnml : nm.length = 75)
    (ha1 : st.add1.val = latL a1)
    (ha2 : st.add2.val = latL a2)
    (ha3 : st.add3.val = latL a3)
    (haid : st.acct_id.val = latL aidT)
    (hbal : st.curr_bal.val = latL balT)
    (hfico : st.fico.val = latL ficoT)
    (hcap : c.html.val.length + 34 ≤ Usize.max) :
    ∃ c', cbstm03a.html_nmadbs c st = .ok c' ∧
      CtxExt c c' []
        [hfield tPStyle (tok2 (nm.take 50) ++ [64, 64]) tEndP,
         hfield tP (tok2 a1 ++ [64, 64]) tEndP,
         hfield tP (tok2 a2 ++ [64, 64]) tEndP,
         hfield tP (tok2 a3 ++ [64, 64]) tEndP,
         hLTDE, hLTRE, hLTRS, hL30_42, hL31, hLTDE, hLTRE, hLTRS, hL22_35,
         hfield tAcct (tokB 92 aidT) tEndP,
         hfield tBal (tokB 92 balT) tEndP,
         hfield tFico (tokB 92 ficoT) tEndP,
         hLTDE, hLTRE, hLTRS, hL30_42, hL43, hLTDE, hLTRE, hLTRS, hL47, hL48, hLTDE,
         hL50, hL51, hLTDE, hL53, hL54, hLTDE, hLTRE] := by
  unfold cbstm03a.html_nmadbs
  refine step_nmadbs_l23 H hcap st nm hnm hnml (fun c _ hcap => ?_)
  refine step_nmadbs_p2 H hcap st.add1 a1 ha1 (fun c _ hcap => ?_)
  refine step_nmadbs_p2 H hcap st.add2 a2 ha2 (fun c _ hcap => ?_)
  refine step_nmadbs_p2 H hcap st.add3 a3 ha3 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTDE (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTRE (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTRS (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L30_42 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L31 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTDE (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTRE (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTRS (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L22_35 (fun c _ hcap => ?_)
  refine step_nmadbs_pstar (f := id) H hcap _ st.acct_id tAcct aidT latL_tAcct tokB_92_tAcct haid (fun c _ hcap => ?_)
  refine step_nmadbs_pstar (f := id) H hcap _ st.curr_bal tBal balT latL_tBal tokB_92_tBal hbal (fun c _ hcap => ?_)
  refine step_nmadbs_pstar (f := id) H hcap _ st.fico tFico ficoT latL_tFico tokB_92_tFico hfico (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTDE (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTRE (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTRS (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L30_42 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L43 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTDE (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTRE (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTRS (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L47 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L48 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTDE (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L50 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L51 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTDE (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L53 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_L54 (fun c _ hcap => ?_)
  refine step_hw (f := id) H hcap _ _ hw_LTDE (fun c _ hcap => ?_)
  exact last_hw H hcap _ _ hw_LTRE

/-! ## 4. `create_statement_loop` and `write_trans` -/

def csOrder : Array U32 15#usize :=
  Array.make 15#usize [
    1#u32, 2#u32, 3#u32, 4#u32, 5#u32, 6#u32, 5#u32, 7#u32, 8#u32, 9#u32,
    10#u32, 11#u32, 12#u32, 13#u32, 12#u32 ]

theorem step_cs_loop {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    {c : cbstm03a.Ctx} {ss : List (List UInt8)} {n : Nat}
    (hcaps : c.stmt.val.length + (n + 1) ≤ Usize.max)
    (st : cbstm03a.St) (i i' : Usize) (idx : U32) (bs : List UInt8)
    {hbs : (latL bs).length = (80#usize).val}
    (hlt : i.val < 15) (hi' : i'.val = i.val + 1)
    (hidx : csOrder.val[i.val]'(by simp [csOrder]; omega) = idx)
    (hst : cbstm03a.st_line idx st = .ok (Array.from (latL bs) hbs))
    (hk : ∀ c1, c1.stmt.val.length + n ≤ Usize.max →
      ∃ res, cbstm03a.create_statement_loop c1 st.name st.add1 st.add2 st.add3
        st.acct_id st.curr_bal st.fico st.tranid st.trandt st.tranamt st.total_tramt csOrder i' = .ok res ∧
        CtxExt c1 res ss []) :
    ∃ res, cbstm03a.create_statement_loop c st.name st.add1 st.add2 st.add3
      st.acct_id st.curr_bal st.fico st.tranid st.trandt st.tranamt st.total_tramt csOrder i = .ok res ∧
      CtxExt c res (bs :: ss) [] := by
  obtain ⟨c1, hsw, he1⟩ := sw_ext H c (Array.from (latL bs) hbs) bs (Array.from_val _ _) (by omega)
  have hbody : cbstm03a.create_statement_loop.body st.name st.add1 st.add2 st.add3
      st.acct_id st.curr_bal st.fico st.tranid st.trandt st.tranamt st.total_tramt csOrder c i =
      .ok (.cont (c1, i')) := by
    refine eq_ok_of_wp ?_
    unfold cbstm03a.create_statement_loop.body
    have hlen : csOrder.val.length = 15 := by decide
    have hmax : i.val + 1 ≤ Usize.max := by have := usize_max_ge; omega
    aeneas_wp [array_index_usize_eq, hlen, hlt, hidx, hst, hsw, hmax]
    congr 3
    apply UScalar.eq_of_val_eq
    rw [UScalar.ofNatCore_val_eq, hi']
  rw [cbstm03a.create_statement_loop, loop_unfold]
  dsimp only
  rw [hbody, bind_ok]
  dsimp only
  rw [← cbstm03a.create_statement_loop]
  have hcaps1 : c1.stmt.val.length + n ≤ Usize.max := by
    have := he1.2.1; simp only [List.length_singleton] at this; omega
  obtain ⟨res, hres, he2⟩ := hk c1 hcaps1
  exact ⟨res, hres, CtxExt_cons_stmt he1 he2⟩

theorem done_cs_loop (c : cbstm03a.Ctx) (st : cbstm03a.St) (i : Usize) (hi : i.val = 15) :
    ∃ res, cbstm03a.create_statement_loop c st.name st.add1 st.add2 st.add3
      st.acct_id st.curr_bal st.fico st.tranid st.trandt st.tranamt st.total_tramt csOrder i = .ok res ∧
      CtxExt c res [] [] := by
  refine ⟨c, ?_, CtxExt_refl c⟩
  rw [cbstm03a.create_statement_loop, loop_unfold]
  dsimp only
  have hbody : cbstm03a.create_statement_loop.body st.name st.add1 st.add2 st.add3
      st.acct_id st.curr_bal st.fico st.tranid st.trandt st.tranamt st.total_tramt csOrder c i =
      .ok (.done c) := by
    refine eq_ok_of_wp ?_
    unfold cbstm03a.create_statement_loop.body
    aeneas_wp [hi]
  rw [hbody, bind_ok]

theorem create_statement_loop_ext {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    (c : cbstm03a.Ctx) (st : cbstm03a.St)
    (nm a1 a2 a3 aidT balT ficoT : List UInt8)
    (hnm : st.name.val = latL nm) (hnml : nm.length = 75)
    (ha1 : st.add1.val = latL a1) (ha1l : a1.length = 50)
    (ha2 : st.add2.val = latL a2) (ha2l : a2.length = 50)
    (ha3 : st.add3.val = latL a3) (ha3l : a3.length = 80)
    (haid : st.acct_id.val = latL aidT) (haidl : aidT.length = 20)
    (hbal : st.curr_bal.val = latL balT) (hball : balT.length = 13)
    (hfico : st.fico.val = latL ficoT) (hficol : ficoT.length = 20)
    (hcaps : c.stmt.val.length + 15 ≤ Usize.max) :
    ∃ c', cbstm03a.create_statement_loop c st.name st.add1 st.add2 st.add3
      st.acct_id st.curr_bal st.fico st.tranid st.trandt st.tranamt st.total_tramt csOrder 0#usize = .ok c' ∧
      CtxExt c c'
        [nm ++ c2625, a1 ++ c2680, a2 ++ c2760, a3, c2870, c2950, c2870,
         c3030 ++ aidT ++ c3070, c3110 ++ balT ++ c3143, c3190 ++ ficoT ++ c3230,
         c3270, c3350, c3430, c3510, c3430] [] := by
  refine step_cs_loop H hcaps st 0#usize 1#usize 1#u32 _ (by decide) rfl rfl (st_line_1 H st nm hnm hnml) (fun c hcaps => ?_)
  refine step_cs_loop H hcaps st 1#usize 2#usize 2#u32 _ (by decide) rfl rfl (st_line_2 H st a1 ha1 ha1l) (fun c hcaps => ?_)
  refine step_cs_loop H hcaps st 2#usize 3#usize 3#u32 _ (by decide) rfl rfl (st_line_3 H st a2 ha2 ha2l) (fun c hcaps => ?_)
  refine step_cs_loop H hcaps st 3#usize 4#usize 4#u32 _ (by decide) rfl rfl (st_line_4 H st a3 ha3 ha3l) (fun c hcaps => ?_)
  refine step_cs_loop H hcaps st 4#usize 5#usize 5#u32 _ (by decide) rfl rfl (st_line_5 H st) (fun c hcaps => ?_)
  refine step_cs_loop H hcaps st 5#usize 6#usize 6#u32 _ (by decide) rfl rfl (st_line_6 H st) (fun c hcaps => ?_)
  refine step_cs_loop H hcaps st 6#usize 7#usize 5#u32 _ (by decide) rfl rfl (st_line_5 H st) (fun c hcaps => ?_)
  refine step_cs_loop H hcaps st 7#usize 8#usize 7#u32 _ (by decide) rfl rfl (st_line_7 H st aidT haid haidl) (fun c hcaps => ?_)
  refine step_cs_loop H hcaps st 8#usize 9#usize 8#u32 _ (by decide) rfl rfl (st_line_8 H st balT hbal hball) (fun c hcaps => ?_)
  refine step_cs_loop H hcaps st 9#usize 10#usize 9#u32 _ (by decide) rfl rfl (st_line_9 H st ficoT hfico hficol) (fun c hcaps => ?_)
  refine step_cs_loop H hcaps st 10#usize 11#usize 10#u32 _ (by decide) rfl rfl (st_line_10 H st) (fun c hcaps => ?_)
  refine step_cs_loop H hcaps st 11#usize 12#usize 11#u32 _ (by decide) rfl rfl (st_line_11 H st) (fun c hcaps => ?_)
  refine step_cs_loop H hcaps st 12#usize 13#usize 12#u32 _ (by decide) rfl rfl (st_line_12 H st) (fun c hcaps => ?_)
  refine step_cs_loop H hcaps st 13#usize 14#usize 13#u32 _ (by decide) rfl rfl (st_line_13 H st) (fun c hcaps => ?_)
  refine step_cs_loop H hcaps st 14#usize 15#usize 12#u32 _ (by decide) rfl rfl (st_line_12 H st) (fun c _ => ?_)
  exact done_cs_loop c st 15#usize rfl

/-! ## 5. `create_statement` -/

theorem repeat_space_eq_ovw_nil (n : Usize) :
    (Array.repeat n 32#u8).val = latL (ovw [] (sp n.val)) := by
  simp [Array.repeat_val, ovw, sp, latL_replicate]

theorem from_slice_latL_ovw {n : Usize} (arr : Array U8 n) (J : List UInt8) (h) :
    (arr.from_slice (Slice.from (latL (ovw J (sp n.val))) h)).val =
      latL (ovw J (sp n.val)) := by
  simp [array_from_slice_eq, length_latL, length_ovw, length_sp]

theorem from_slice_putL_repeat {n : Usize} (src : List U8) (h) :
    ((Array.repeat n 32#u8).from_slice
      (Slice.from (putL (List.replicate n.val 32#u8) 0 n.val src) h)).val =
      putL (List.replicate n.val 32#u8) 0 n.val src := by
  simp [array_from_slice_eq, length_putL, List.length_replicate]

theorem step_str_space {α : Type} {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    {n : Usize} (arr : Array U8 n) (p : Usize)
    (cust : Array U8 500#usize) (j k : Usize) (jN lenN : Nat)
    (hj : j.val = jN) (hlen : k.val - j.val = lenN)
    (hjk : j.val ≤ k.val) (hk : k.val ≤ 500)
    (pre piece : List UInt8)
    (harr : arr.val = latL (ovw pre (sp n.val)))
    (hp : p.val = min pre.length n.val)
    (hslice : (cust.val.drop jN).take lenN = latL piece)
    {rest : (Slice U8 × (Slice U8 → Array U8 n)) → (Slice U8 × Usize) → Std.Result α} {P : α → Prop}
    (hrest : ∀ (s0 s3 : Slice U8) (p' : Usize),
      (arr.from_slice s3).val = latL (ovw (pre ++ tokB 64 piece) (sp n.val)) →
      p'.val = min (pre ++ tokB 64 piece).length n.val →
      ∃ res, rest (s0, arr.from_slice) (s3, p') = .ok res ∧ P res) :
    ∃ res, (do
      let x0 ← lift (Array.to_slice_mut arr)
      let s1 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) cust
          { start := j, «end» := k }
      let s2 ← lift (Array.to_slice (Array.make 1#usize [ 32#u8 ]))
      let x1 ← cbstm03a.str_part x0.1 p s1 s2
      rest x0 x1) = .ok res ∧ P res := by
  have hplen : piece.length ≤ 500 := by
    have h1 := congrArg List.length hslice
    have h2 := List.length_take_le lenN (cust.val.drop jN)
    rw [length_latL] at h1
    omega
  refine exists_ok_of_wp ?_
  aeneas_wp [array_index_range_nat cust j k jN lenN hj hlen hjk hk,
    H.str_part_space, Array.to_slice, Array.to_slice_mut, Array.make_val,
    Slice.from_val, UScalar.ofNatCore_val_eq,
    harr, hp, hslice, hplen, tokBL_space_latL, strPartL_chain_fst, strPartL_chain_snd,
    length_latL, length_ovw, length_sp, Nat.min_le_right, ↓reduceDIte]
  obtain ⟨res, hres, hp'⟩ := hrest _ _ _ (from_slice_latL_ovw arr _ _) (UScalar.ofNatCore_val_eq _)
  rw [hres, wp_ok]
  exact ⟨res, rfl, hp'⟩

theorem step_str_add_space {α : Type} {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    {n : Usize} (arr : Array U8 n) (p : Usize)
    (pre : List UInt8)
    (harr : arr.val = latL (ovw pre (sp n.val)))
    (hp : p.val = min pre.length n.val)
    {rest : (Slice U8 × (Slice U8 → Array U8 n)) → (Slice U8 × Usize) → Std.Result α} {P : α → Prop}
    (hrest : ∀ (s0 s7 : Slice U8) (p' : Usize),
      (arr.from_slice s7).val = latL (ovw (pre ++ [64]) (sp n.val)) →
      p'.val = min (pre ++ [64]).length n.val →
      ∃ res, rest (s0, arr.from_slice) (s7, p') = .ok res ∧ P res) :
    ∃ res, (do
      let x0 ← lift (Array.to_slice_mut arr)
      let s5 ← lift (Array.to_slice (Array.make 1#usize [ 32#u8 ]))
      let s6 ← lift (Array.to_slice (Std.Array.empty Std.U8))
      let x1 ← cbstm03a.str_part x0.1 p s5 s6
      rest x0 x1) = .ok res ∧ P res := by
  refine exists_ok_of_wp ?_
  aeneas_wp [H.str_part_empty, Array.to_slice, Array.to_slice_mut, Array.make_val,
    Std.Array.empty, Array.from_val, Slice.from_val, UScalar.ofNatCore_val_eq,
    harr, hp, latL_64, strPartL_chain_fst, strPartL_chain_snd,
    length_latL, length_ovw, length_sp, Nat.min_le_right, ↓reduceDIte]
  obtain ⟨res, hres, hp'⟩ := hrest _ _ _ (from_slice_latL_ovw arr _ _) (UScalar.ofNatCore_val_eq _)
  rw [hres, wp_ok]
  exact ⟨res, rfl, hp'⟩

theorem putL_zero_pad_latL (piece : List UInt8) (len : Nat) (h : piece.length ≤ len) :
    putL (List.replicate len 32#u8) 0 len (latL piece) =
      latL (piece ++ sp (len - piece.length)) := by
  rw [putL_zero_pad (latL piece) len (by simp [h]), length_latL, latL_append]
  simp [sp, latL_replicate]

theorem step_ok {α β : Type} {m : Std.Result α} {x : α} (hm : m = .ok x)
    {k : α → Std.Result β} {P : β → Prop}
    (hk : ∃ res, k x = .ok res ∧ P res) :
    ∃ res, (do let y ← m; k y) = .ok res ∧ P res := by
  rw [hm, bind_tc_ok]
  exact hk

theorem step_put_range {α : Type} {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    {n m : Usize} (recArr : Array U8 m) (j k : Usize) (jN lenN : Nat)
    (hj : j.val = jN) (hlen : k.val - j.val = lenN)
    (hjk : j.val ≤ k.val) (hk : k.val ≤ m.val)
    (piece out : List UInt8)
    (hslice : (recArr.val.drop jN).take lenN = latL piece)
    (hplen : piece.length ≤ n.val)
    (hout : piece ++ sp (n.val - piece.length) = out)
    {rest : (Slice U8 × (Slice U8 → Array U8 n)) → Slice U8 → Std.Result α} {P : α → Prop}
    (hrest : ∀ (s0 s2 : Slice U8),
      ((Array.repeat n 32#u8).from_slice s2).val = latL out →
      ∃ res, rest (s0, (Array.repeat n 32#u8).from_slice) s2 = .ok res ∧ P res) :
    ∃ res, (do
      let x0 ← lift (Array.to_slice_mut (Array.repeat n 32#u8))
      let s1 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) recArr
          { start := j, «end» := k }
      let s2 ← cbstm03a.put x0.1 0#usize n s1
      rest x0 s2) = .ok res ∧ P res := by
  refine exists_ok_of_wp ?_
  aeneas_wp [array_index_range_nat recArr j k jN lenN hj hlen hjk hk,
    H.put_eq, Array.to_slice, Array.to_slice_mut, Array.repeat_val,
    Slice.from_val, UScalar.ofNatCore_val_eq,
    length_putL, List.length_replicate, Nat.zero_add, Nat.le_refl, ↓reduceDIte]
  have h1 : ((Array.repeat n 32#u8).from_slice
      (Slice.from (putL (List.replicate n.val 32#u8) 0 n.val ((recArr.val.drop jN).take lenN))
        (by rw [length_putL _ _ _ _ (by simp [List.length_replicate]), List.length_replicate]; scalar_tac))).val =
      latL out := by
    rw [from_slice_putL_repeat, hslice, putL_zero_pad_latL piece n.val hplen, hout]
  obtain ⟨res, hres, hp'⟩ := hrest _ _ h1
  rw [hres, wp_ok]
  exact ⟨res, rfl, hp'⟩

theorem step_zoned_bal {α : Type} {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    (acct : Array U8 300#usize) (aval : List FVal) (ha : AccountRecord.Valid aval)
    (hacct : acct.val = latL (AccountRecord.encode aval))
    {rest : Array U8 13#usize → Std.Result α} {P : α → Prop}
    (hrest : ∀ a22 : Array U8 13#usize, a22.val = latL (edit9 (numOf (aval.getD 2 default))) →
      ∃ res, rest a22 = .ok res ∧ P res) :
    ∃ res, (do
      let s65 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) acct
          { start := 12#usize, «end» := 24#usize }
      let i ← cbstm03a.zoned s65
      let a22 ← cbstm03a.fmt_9_99 i
      rest a22) = .ok res ∧ P res := by
  obtain ⟨v, hz, hv_val, hv_lt⟩ := H.zoned_acct_bal
    (Slice.from ((acct.val.drop 12).take 12)
      (by have := List.length_take_le 12 (acct.val.drop 12); scalar_tac))
    aval ha (by rw [Slice.from_val, hacct, ← latL_drop, ← latL_take])
  have hfmt := H.fmt_9_99_eq v hv_lt
  have h1 : (Array.from (latL (edit9 v.val))
      (by rw [length_latL, length_edit9]; rfl) : Array U8 13#usize).val =
      latL (edit9 (numOf (aval.getD 2 default))) := by
    rw [Array.from_val, hv_val]
  obtain ⟨res, hres, hp'⟩ := hrest _ h1
  refine exists_ok_of_wp ?_
  aeneas_wp [array_index_range_nat acct 12#usize 24#usize 12 12 rfl rfl (by decide) (by decide),
    hz, hfmt]
  rw [hres, wp_ok]
  exact ⟨res, rfl, hp'⟩

theorem cust_slice_fields {cval : List FVal} (hc : CustomerRecord.Valid cval)
    {cust : Array U8 500#usize} (hcust : cust.val = latL (CustomerRecord.encode cval)) :
    (cust.val.drop 9).take 25 = latL (strOf (cval.getD 1 default)) ∧
    (cust.val.drop 34).take 25 = latL (strOf (cval.getD 2 default)) ∧
    (cust.val.drop 59).take 25 = latL (strOf (cval.getD 3 default)) ∧
    (cust.val.drop 84).take 50 = latL (strOf (cval.getD 4 default)) ∧
    (strOf (cval.getD 4 default)).length = 50 ∧
    (cust.val.drop 134).take 50 = latL (strOf (cval.getD 5 default)) ∧
    (strOf (cval.getD 5 default)).length = 50 ∧
    (cust.val.drop 184).take 50 = latL (strOf (cval.getD 6 default)) ∧
    (cust.val.drop 234).take 2 = latL (strOf (cval.getD 7 default)) ∧
    (cust.val.drop 236).take 3 = latL (strOf (cval.getD 8 default)) ∧
    (cust.val.drop 239).take 10 = latL (strOf (cval.getD 9 default)) ∧
    (cust.val.drop 329).take 3 = latL (Sem.digitChars {} 3 (numOf (cval.getD 17 default)).natAbs) := by
  have h1 := field_str_bytes customerRecord_contig hc 1 9 25 (by decide) ⟨false, rfl⟩ rfl rfl
  have h2 := field_str_bytes customerRecord_contig hc 2 34 25 (by decide) ⟨false, rfl⟩ rfl rfl
  have h3 := field_str_bytes customerRecord_contig hc 3 59 25 (by decide) ⟨false, rfl⟩ rfl rfl
  have h4 := field_str_bytes customerRecord_contig hc 4 84 50 (by decide) ⟨false, rfl⟩ rfl rfl
  have h5 := field_str_bytes customerRecord_contig hc 5 134 50 (by decide) ⟨false, rfl⟩ rfl rfl
  have h6 := field_str_bytes customerRecord_contig hc 6 184 50 (by decide) ⟨false, rfl⟩ rfl rfl
  have h7 := field_str_bytes customerRecord_contig hc 7 234 2 (by decide) ⟨false, rfl⟩ rfl rfl
  have h8 := field_str_bytes customerRecord_contig hc 8 236 3 (by decide) ⟨false, rfl⟩ rfl rfl
  have h9 := field_str_bytes customerRecord_contig hc 9 239 10 (by decide) ⟨false, rfl⟩ rfl rfl
  have h17 := (field_num_decode customerRecord_contig hc 17 329 3 { digits := 3 } (by decide) rfl rfl rfl).1
  rw [encodeNum_unsigned_display (by decide)] at h17
  simp only [hcust, ← latL_drop, ← latL_take]
  exact ⟨congrArg latL h1.1, congrArg latL h2.1, congrArg latL h3.1,
    congrArg latL h4.1, h4.2, congrArg latL h5.1, h5.2,
    congrArg latL h6.1, congrArg latL h7.1, congrArg latL h8.1, congrArg latL h9.1,
    congrArg latL h17⟩

theorem create_statement_ext {tbl : Array U8 256#usize} (H : Helpers1 tbl)
    (c : cbstm03a.Ctx) (st : cbstm03a.St)
    (cust : Array U8 500#usize) (acct : Array U8 300#usize)
    (cval aval : List FVal)
    (hc : CustomerRecord.Valid cval) (ha : AccountRecord.Valid aval)
    (hcust : cust.val = latL (CustomerRecord.encode cval))
    (hacct : acct.val = latL (AccountRecord.encode aval))
    (hcaps : c.stmt.val.length + 16 ≤ Usize.max)
    (hcaph : c.html.val.length + 56 ≤ Usize.max) :
    ∃ res : cbstm03a.Ctx × cbstm03a.St,
      cbstm03a.create_statement c st cust acct = .ok res ∧
      CtxExt c res.1
        (stmtHead
          (stName (strOf (cval.getD 1 default)) (strOf (cval.getD 2 default)) (strOf (cval.getD 3 default)))
          (strOf (cval.getD 4 default)) (strOf (cval.getD 5 default))
          (stAdd3 (strOf (cval.getD 6 default)) (strOf (cval.getD 7 default))
            (strOf (cval.getD 8 default)) (strOf (cval.getD 9 default)))
          (stAcctId (numOf (aval.getD 0 default)))
          (edit9 (numOf (aval.getD 2 default)))
          (stFico (numOf (cval.getD 17 default))))
        (htmlHead
          (stName (strOf (cval.getD 1 default)) (strOf (cval.getD 2 default)) (strOf (cval.getD 3 default)))
          (strOf (cval.getD 4 default)) (strOf (cval.getD 5 default))
          (stAdd3 (strOf (cval.getD 6 default)) (strOf (cval.getD 7 default))
            (strOf (cval.getD 8 default)) (strOf (cval.getD 9 default)))
          (stAcctId (numOf (aval.getD 0 default)))
          (edit9 (numOf (aval.getD 2 default)))
          (stFico (numOf (cval.getD 17 default)))) := by
  obtain ⟨h1, h2, h3, h4, h4l, h5, h5l, h6, h7, h8, h9, h17⟩ := cust_slice_fields hc hcust
  have haf := acct_fields ha
  have hd11 : (acct.val.drop 0).take 11 = latL (Sem.digitChars {} 11 (numOf (aval.getD 0 default)).natAbs) := by
    simp only [List.drop_zero, hacct, ← latL_take, haf.1]
  have hd11l : (Sem.digitChars {} 11 (numOf (aval.getD 0 default)).natAbs).length = 11 := by
    rw [← haf.1]; simp [acct_length ha]
  have hd3l : (Sem.digitChars {} 3 (numOf (cval.getD 17 default)).natAbs).length = 3 := by
    have h17' := (field_num_decode customerRecord_contig hc 17 329 3 { digits := 3 } (by decide) rfl rfl rfl).1
    rw [encodeNum_unsigned_display (by decide)] at h17'
    rw [← h17']; simp [cust_length hc]
  have hf90 := H.fmt_9_99_eq 0#i64 (by decide)
  have hfz0 := H.fmt_z_99_eq 0#i64 (by decide)
  unfold cbstm03a.create_statement
  dsimp only
  refine step_ok hf90 ?_
  refine step_ok hfz0 ?_
  refine step_st_sw (f := Prod.fst) H hcaps c2470 (st_line_0 H _) (fun c1 hcaps1 hh1 => ?_)
  obtain ⟨c2, hhdr, he_hdr⟩ := html_header_ext H c1 acct
    (Sem.digitChars {} 11 (numOf (aval.getD 0 default)).natAbs) hd11 hd11l (by omega)
  refine step_ok hhdr ?_
  refine step_str_space H (Array.repeat 75#usize 32#u8) 0#usize cust 9#usize 34#usize 9 25
    rfl rfl (by decide) (by decide) [] _ (repeat_space_eq_ovw_nil 75#usize) rfl h1 (fun _ s3 p h_a10 h_p => ?_)
  refine step_str_add_space H _ p _ h_a10 h_p (fun _ s7 p1 h_a11 h_p1 => ?_)
  refine step_str_space H _ p1 cust 34#usize 59#usize 34 25
    rfl rfl (by decide) (by decide) _ _ h_a11 h_p1 h2 (fun _ s11 p2 h_a12 h_p2 => ?_)
  refine step_str_add_space H _ p2 _ h_a12 h_p2 (fun _ s15 p3 h_a13 h_p3 => ?_)
  refine step_str_space H _ p3 cust 59#usize 84#usize 59 25
    rfl rfl (by decide) (by decide) _ _ h_a13 h_p3 h3 (fun _ s19 p4 h_a14 h_p4 => ?_)
  refine step_str_add_space H _ p4 _ h_a14 h_p4 (fun _ s23 _ h_a23 _ => ?_)
  refine step_put_range (n := 50#usize) H cust 84#usize 134#usize 84 50
    rfl rfl (by decide) (by decide) _ (strOf (cval.getD 4 default)) h4 (by rw [h4l]; decide)
    (by rw [h4l]; simp [sp]) (fun _ s26 h_a24 => ?_)
  refine step_put_range (n := 50#usize) H cust 134#usize 184#usize 134 50
    rfl rfl (by decide) (by decide) _ (strOf (cval.getD 5 default)) h5 (by rw [h5l]; decide)
    (by rw [h5l]; simp [sp]) (fun _ s29 h_a25 => ?_)
  refine step_str_space H (Array.repeat 80#usize 32#u8) 0#usize cust 184#usize 234#usize 184 50
    rfl rfl (by decide) (by decide) [] _ (repeat_space_eq_ovw_nil 80#usize) rfl h6 (fun _ s33 p5 h_a15 h_p5 => ?_)
  refine step_str_add_space H _ p5 _ h_a15 h_p5 (fun _ s37 p6 h_a16 h_p6 => ?_)
  refine step_str_space H _ p6 cust 234#usize 236#usize 234 2
    rfl rfl (by decide) (by decide) _ _ h_a16 h_p6 h7 (fun _ s41 p7 h_a17 h_p7 => ?_)
  refine step_str_add_space H _ p7 _ h_a17 h_p7 (fun _ s45 p8 h_a18 h_p8 => ?_)
  refine step_str_space H _ p8 cust 236#usize 239#usize 236 3
    rfl rfl (by decide) (by decide) _ _ h_a18 h_p8 h8 (fun _ s49 p9 h_a19 h_p9 => ?_)
  refine step_str_add_space H _ p9 _ h_a19 h_p9 (fun _ s53 p10 h_a20 h_p10 => ?_)
  refine step_str_space H _ p10 cust 239#usize 249#usize 239 10
    rfl rfl (by decide) (by decide) _ _ h_a20 h_p10 h9 (fun _ s57 p11 h_a21 h_p11 => ?_)
  refine step_str_add_space H _ p11 _ h_a21 h_p11 (fun _ s61 _ h_a26 _ => ?_)
  refine step_put_range (n := 20#usize) H acct 0#usize 11#usize 0 11
    rfl rfl (by decide) (by decide) _ (stAcctId (numOf (aval.getD 0 default))) hd11 (by rw [hd11l]; decide)
    (by rw [hd11l]; rfl) (fun _ s64 h_a27 => ?_)
  refine step_zoned_bal H acct aval ha hacct (fun a22 h_a22 => ?_)
  refine step_put_range (n := 20#usize) H cust 329#usize 332#usize 329 3
    rfl rfl (by decide) (by decide) _ (stFico (numOf (cval.getD 17 default))) h17 (by rw [hd3l]; decide)
    (by rw [hd3l]; rfl) (fun _ s68 h_a28 => ?_)
  have h_nm : (((((((Array.repeat 75#usize 32#u8).from_slice s3).from_slice s7).from_slice s11).from_slice s15).from_slice s19).from_slice s23).val =
      latL (stName (strOf (cval.getD 1 default)) (strOf (cval.getD 2 default)) (strOf (cval.getD 3 default))) := by
    simpa only [stName, List.nil_append, List.append_assoc, UScalar.ofNatCore_val_eq] using h_a23
  have h_a3 : (((((((((Array.repeat 80#usize 32#u8).from_slice s33).from_slice s37).from_slice s41).from_slice s45).from_slice s49).from_slice s53).from_slice s57).from_slice s61).val =
      latL (stAdd3 (strOf (cval.getD 6 default)) (strOf (cval.getD 7 default))
        (strOf (cval.getD 8 default)) (strOf (cval.getD 9 default))) := by
    simpa only [stAdd3, List.nil_append, List.append_assoc, UScalar.ofNatCore_val_eq] using h_a26
  have hnml : (stName (strOf (cval.getD 1 default)) (strOf (cval.getD 2 default)) (strOf (cval.getD 3 default))).length = 75 := by
    simp [stName, length_ovw]
  have ha3l : (stAdd3 (strOf (cval.getD 6 default)) (strOf (cval.getD 7 default))
      (strOf (cval.getD 8 default)) (strOf (cval.getD 9 default))).length = 80 := by
    simp [stAdd3, length_ovw]
  have haidl : (stAcctId (numOf (aval.getD 0 default))).length = 20 := by
    rw [stAcctId, List.length_append, hd11l, length_sp]
  have hball : (edit9 (numOf (aval.getD 2 default))).length = 13 := length_edit9 _
  have hficol : (stFico (numOf (cval.getD 17 default))).length = 20 := by
    rw [stFico, List.length_append, hd3l, length_sp]
  have hcaph2 : c2.html.val.length + 34 ≤ Usize.max := by
    have := he_hdr.2.2.2.1; simp only [List.length_cons, List.length_nil] at this; omega
  obtain ⟨c3, hnmadbs, he_nmadbs⟩ := html_nmadbs_ext H c2
    { «name» := _, add1 := _, add2 := _, add3 := _, acct_id := _,
      curr_bal := a22, fico := _, tranid := Array.repeat 16#usize 32#u8,
      trandt := Array.repeat 49#usize 32#u8,
      tranamt := Array.from (latL (editZ (0#i64).val)) (by rw [length_latL, length_editZ]; rfl),
      total_tramt := Array.from (latL (editZ (0#i64).val)) (by rw [length_latL, length_editZ]; rfl) }
    _ _ _ _ _ _ _ h_nm hnml h_a24 h_a25 h_a3 h_a27 h_a22 h_a28 hcaph2
  refine step_ok hnmadbs ?_
  have hcaps3 : c3.stmt.val.length + 15 ≤ Usize.max := by
    have h1s := he_hdr.2.1
    have h2s := he_nmadbs.2.1
    simp only [List.length_nil, Nat.add_zero] at h1s h2s
    omega
  obtain ⟨c4, hloop, he_loop⟩ := create_statement_loop_ext H c3
    { «name» := _, add1 := _, add2 := _, add3 := _, acct_id := _,
      curr_bal := a22, fico := _, tranid := Array.repeat 16#usize 32#u8,
      trandt := Array.repeat 49#usize 32#u8,
      tranamt := Array.from (latL (editZ (0#i64).val)) (by rw [length_latL, length_editZ]; rfl),
      total_tramt := Array.from (latL (editZ (0#i64).val)) (by rw [length_latL, length_editZ]; rfl) }
    _ _ _ _ _ _ _ h_nm hnml h_a24 h4l h_a25 h5l h_a3 ha3l h_a27 haidl h_a22 hball h_a28 hficol hcaps3
  refine step_ok hloop ?_
  refine ⟨(c4, _), rfl, ?_⟩
  have he12 := CtxExt_trans he_hdr he_nmadbs
  have he123 := CtxExt_trans he12 he_loop
  simpa only [stmtHead, htmlHead, stAcctId, List.nil_append, List.cons_append] using he123

/-! ## 6. Discharging `Helpers1` from `RustRun1` and `create_statement_spec` -/

theorem exists_lat_fin : ∀ n : Fin 256, ∃ b : Fin 256, cp037Code (UInt8.ofNat b.val) = n.val := by
  decide +kernel

theorem exists_lat (u : U8) : ∃ b : UInt8, u = lat b := by
  have hu : u.val < 256 := by scalar_tac
  obtain ⟨b, hb⟩ := exists_lat_fin ⟨u.val, hu⟩
  refine ⟨UInt8.ofNat b.val, ?_⟩
  apply UScalar.eq_of_val_eq
  rw [lat_val, hb]

theorem exists_latL : ∀ l : List U8, ∃ bs : List UInt8, l = latL bs
  | [] => ⟨[], rfl⟩
  | u :: us => by
    obtain ⟨b, rfl⟩ := exists_lat u
    obtain ⟨bs, rfl⟩ := exists_latL us
    exact ⟨b :: bs, rfl⟩

theorem take_min_length_left {α : Type} (l : List α) (k : Nat) :
    l.take (min l.length k) = l.take k := by
  by_cases h : l.length ≤ k
  · rw [Nat.min_eq_left h, List.take_of_length_le h, List.take_length]
  · rw [Nat.min_eq_right (by omega)]

theorem helpers1_inst (tbl : Array U8 256#usize) : Helpers1 tbl where
  vb_eq s := Rust.vb_eq s
  put_eq dst off len src h := Rust.put_val dst off len src h
  fill_eq dst off len ch h := Rust.fill_val dst off len ch h
  fmt_9_99_eq v hv := by
    obtain ⟨o, ho, hov⟩ := Rust.fmt_9_99_eq v (by omega)
    rw [ho]; congr 1; rw [Array.eq_iff, hov, Array.from_val]
  fmt_z_99_eq v hv := by
    obtain ⟨o, ho, hov⟩ := Rust.fmt_z_99_eq v (by omega)
    rw [ho]; congr 1; rw [Array.eq_iff, hov, Array.from_val]
  zoned_acct_bal s a ha hs := by
    have h2 := field_num_decode accountRecord_contig ha 2 12 12
      { digits := 12, scale := 2, signed := true } (by decide) rfl rfl rfl
    rw [h2.1] at hs
    obtain ⟨v, hv, hval⟩ := Rust.zoned_eq s 12 2 true (numOf (a.getD 2 default))
      (by decide) (by decide) h2.2.2 hs
    have hbd := ((holds_display rfl).mp h2.2.2).1
    exact ⟨v, hv, hval, by rw [hval]; exact hbd⟩
  str_part_space dst ptr src delim hdelim h hlen := by
    obtain ⟨bs, hsrc⟩ := exists_latL src.val
    have hbs_max : bs.length < Usize.max := by
      have := usize_max_ge
      have hbl : bs.length = src.val.length := by simp [hsrc]
      omega
    obtain ⟨s', ptr', hok, hs', hptr'⟩ :=
      Rust.str_part_single_eq dst ptr src delim 64 bs (by simpa using hdelim) hsrc h hbs_max
    rw [hok]; congr 1; apply Prod.ext
    · rw [Slice.eq_iff, hs', Slice.from_val, hsrc, tokBL_space_latL]
      dsimp only [strPartL]
      rw [take_min_length_left, length_latL]
    · apply UScalar.eq_of_val_eq
      rw [hptr', UScalar.ofNatCore_val_eq, hsrc, tokBL_space_latL]
      dsimp only [strPartL]
      rw [length_latL]
  str_part_star dst ptr src delim hdelim h hlen := by
    obtain ⟨bs, hsrc⟩ := exists_latL src.val
    have hbs_max : bs.length < Usize.max := by
      have := usize_max_ge
      have hbl : bs.length = src.val.length := by simp [hsrc]
      omega
    obtain ⟨s', ptr', hok, hs', hptr'⟩ :=
      Rust.str_part_single_eq dst ptr src delim 92 bs (by simpa using hdelim) hsrc h hbs_max
    rw [hok]; congr 1; apply Prod.ext
    · rw [Slice.eq_iff, hs', Slice.from_val, hsrc, tokBL_star_latL]
      dsimp only [strPartL]
      rw [take_min_length_left, length_latL]
    · apply UScalar.eq_of_val_eq
      rw [hptr', UScalar.ofNatCore_val_eq, hsrc, tokBL_star_latL]
      dsimp only [strPartL]
      rw [length_latL]
  str_part_two_space dst ptr src delim hdelim h hlen := by
    obtain ⟨bs, hsrc⟩ := exists_latL src.val
    have hbs_max : bs.length < Usize.max := by
      have := usize_max_ge
      have hbl : bs.length = src.val.length := by simp [hsrc]
      omega
    obtain ⟨s', ptr', hok, hs', hptr'⟩ :=
      Rust.str_part_double_eq dst ptr src delim bs hdelim hsrc h hbs_max
    rw [hok]; congr 1; apply Prod.ext
    · rw [Slice.eq_iff, hs', Slice.from_val, hsrc, tok2L_latL]
      dsimp only [strPartL]
      rw [take_min_length_left, length_latL]
    · apply UScalar.eq_of_val_eq
      rw [hptr', UScalar.ofNatCore_val_eq, hsrc, tok2L_latL]
      dsimp only [strPartL]
      rw [length_latL]
  str_part_empty dst ptr src delim hdelim h := by
    obtain ⟨s', ptr', hok, hs', hptr'⟩ := Rust.str_part_empty_eq dst ptr src delim hdelim h
    rw [hok]; congr 1; apply Prod.ext
    · rw [Slice.eq_iff, hs', Slice.from_val]
      dsimp only [strPartL]
      rw [take_min_length_left]
    · apply UScalar.eq_of_val_eq
      rw [hptr', UScalar.ofNatCore_val_eq]
      rfl

/-- **Specification of `cbstm03a.create_statement` (`5000-CREATE-STATEMENT`).** -/
theorem create_statement_spec
    (c : cbstm03a.Ctx) (st : cbstm03a.St)
    (cust_rec : Array U8 500#usize) (acct_rec : Array U8 300#usize)
    (cval aval : List FVal)
    (hc : CustomerRecord.Valid cval) (ha : AccountRecord.Valid aval)
    (hcust : cust_rec.val = latL (CustomerRecord.encode cval))
    (hacct : acct_rec.val = latL (AccountRecord.encode aval))
    (hcaps : c.stmt.val.length + 16 ≤ Usize.max)
    (hcaph : c.html.val.length + 56 ≤ Usize.max) :
    ∃ c' st',
      cbstm03a.create_statement c st cust_rec acct_rec = .ok (c', st') ∧
      c'.stmt.val.map (fun l => l.val.map (·.val)) =
        c.stmt.val.map (fun l => l.val.map (·.val)) ++ modelHeadStmt cval aval ∧
      c'.stmt.val.length = c.stmt.val.length + 16 ∧
      c'.html.val.map (fun l => l.val.map (·.val)) =
        c.html.val.map (fun l => l.val.map (·.val)) ++ modelHeadHtml cval aval ∧
      c'.html.val.length = c.html.val.length + 56 ∧
      c'.displays = c.displays ∧ c'.abended = c.abended ∧
      c'.xref_pos = c.xref_pos ∧ c'.xref_eof = c.xref_eof := by
  obtain ⟨⟨c', st'⟩, hok, hs, hsl, hh, hhl, hd, hab, hxp, hxe⟩ :=
    create_statement_ext (helpers1_inst (Array.repeat 256#usize 0#u8))
      c st cust_rec acct_rec cval aval hc ha hcust hacct hcaps hcaph
  exact ⟨c', st', hok, hs, hsl, hh, hhl, hd, hab, hxp, hxe⟩

#print axioms create_statement_spec

end EquivLean.Modernize.Cbstm03a.Rust.CS
