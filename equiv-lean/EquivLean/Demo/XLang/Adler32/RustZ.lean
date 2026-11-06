import EquivLean.Demo.XLang.Adler32.RustBase

/-!
# zlib adler32 → safe Rust: `adler32_z` and `adler32`

`blocks` is the C's loop over `NMAX`-byte blocks (each followed by `% BASE` of both sums);
`rustZ` is `adler32_z` on numbers, path by path as in the C (`len == 1`, `Z_NULL`, `len < 16`,
the blocks and the tail).  `adler32_z_eq`: the generated `adler32_z` returns `rustZ` whenever the
buffer has `len` bytes (or is `Z_NULL`), so it never panics; `adler32_eq` for the `uInt`
wrapper.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas adler32_rs

namespace EquivLean.Demo.XLang.Adler32.Rust

/-- The `NMAX` blocks of `bs` from the sums `a`, `s`: each block of 5552 bytes, then `% BASE` of
both sums; returns the sums and the bytes left (fewer than 5552). -/
def blocks (bs : List Nat) (a s : Nat) : Nat × Nat × List Nat :=
  if h : 5552 ≤ bs.length then
    blocks (bs.drop 5552) ((sums (bs.take 5552) a s).1 % 65521) ((sums (bs.take 5552) a s).2 % 65521)
  else (a, s, bs)
termination_by bs.length
decreasing_by simp only [List.length_drop]; omega

theorem blocks_rest_lt (bs : List Nat) (a s : Nat) : (blocks bs a s).2.2.length < 5552 := by
  induction h : bs.length using Nat.strong_induction_on generalizing bs a s with
  | _ m IH =>
    rw [blocks]
    split_ifs with hN
    · exact IH (bs.drop 5552).length (by simp only [List.length_drop]; omega) _ _ _ rfl
    · simp only
      omega

/-- `adler32_z(adler, buf, len)` on numbers, along the C's paths (the result's high half is
`sum2 * 65536`, the C's `sum2 << 16`). -/
def rustZ (adler : Nat) (buf : Option (List Nat)) (len : Nat) : Nat :=
  let s0 := adler / 65536 % 65536
  let a0 := adler % 65536
  if len = 1 then
    match buf with
    | none => 1
    | some bs =>
      let a1 := a0 + bs.getD 0 0
      let a2 := if 65521 ≤ a1 then a1 - 65521 else a1
      let s1 := s0 + a2
      let s2 := if 65521 ≤ s1 then s1 - 65521 else s1
      a2 ||| shl16N s2
  else
    match buf with
    | none => 1
    | some bs =>
      if len < 16 then
        let r := sums (bs.take len) a0 s0
        let a2 := if 65521 ≤ r.1 then r.1 - 65521 else r.1
        a2 ||| shl16N (r.2 % 65521)
      else
        let q := blocks (bs.take len) a0 s0
        if q.2.2.length ≠ 0 then
          let r := sums q.2.2 q.1 q.2.1
          r.1 % 65521 ||| shl16N (r.2 % 65521)
        else q.1 ||| shl16N q.2.1

/-- `do_bytes_eq` as a `wp` rule (its sums are computed terms). -/
theorem do_bytes_wp (buf : Slice U8) (i n : Usize) (a s : U64) (hin : i.val + n.val ≤ buf.val.length)
    (hn : n.val ≤ 5552) (ha : a.val < 131072) (hs : s.val < 131072)
    {Q : Except Error (U64 × U64) → Prop}
    (hq : ∀ r : U64 × U64,
      (r.1.val, r.2.val) = sums (((bytes buf).drop i.val).take n.val) a.val s.val → Q (.ok r)) :
    wp (do_bytes buf i n a s) Q := by
  obtain ⟨r, hr, hrv⟩ := do_bytes_eq buf i n a s hin hn ha hs
  rw [hr, wp_ok]
  exact hq r hrv

/-! ## The block loop -/

theorem blocks_body_done (b : Slice U8) (aa ss : U64) (i : Usize) {rest : Usize}
    (h : rest.val < 5552) :
    adler32_z_loop.body b aa ss i rest = .ok (.done (aa, ss, i, rest)) := by
  apply eq_ok_of_wp
  unfold adler32_z_loop.body
  aeneas_wp [nmax_val]
  a32_split
  all_goals try a32_contra
  all_goals try (exfalso; omega)
  all_goals simp

theorem blocks_body_step (b : Slice U8) {aa ss : U64} {i rest : Usize} (hN : 5552 ≤ rest.val)
    (hir : i.val + rest.val ≤ b.val.length) (ha : aa.val < 65536) (hs : ss.val < 65536) :
    ∃ c, adler32_z_loop.body b aa ss i rest = .ok c ∧
      ∃ (aa1 ss1 : U64) (i1 rest1 : Usize), c = .cont (aa1, ss1, i1, rest1) ∧
        aa1.val = (sums (((bytes b).drop i.val).take 5552) aa.val ss.val).1 % 65521 ∧
        ss1.val = (sums (((bytes b).drop i.val).take 5552) aa.val ss.val).2 % 65521 ∧
        i1.val = i.val + 5552 ∧ rest1.val = rest.val - 5552 := by
  have hmax := b.property
  apply exists_ok_of_wp
  unfold adler32_z_loop.body
  aeneas_wp [nmax_val]
  a32_split
  all_goals try a32_contra
  all_goals try (exfalso; omega)
  all_goals refine do_bytes_wp b i NMAX aa ss (by rw [nmax_val]; omega) (by rw [nmax_val])
              (by omega) (by omega) ?_
  all_goals rintro ⟨r1, r2⟩ hr
  all_goals aeneas_wp [nmax_val, base_val]
  all_goals a32_split
  all_goals try a32_contra
  all_goals try (exfalso; omega)
  all_goals simp only [nmax_val] at hr
  all_goals have hr1 := congrArg Prod.fst hr
  all_goals have hr2 := congrArg Prod.snd hr
  all_goals simp only at hr1 hr2
  all_goals refine ⟨_, rfl, _, _, _, _, rfl, ?_, ?_, ?_, ?_⟩
  all_goals simp only [UScalar.ofNatCore_val_eq, base_val, nmax_val, hr1, hr2]

theorem blocks_loop_eq (b : Slice U8) :
    ∀ (m : Nat) (aa ss : U64) (i rest : Usize), rest.val = m → i.val + rest.val ≤ b.val.length →
      aa.val < 65536 → ss.val < 65536 →
      ∃ r, adler32_z_loop b aa ss i rest = .ok r ∧
        (r.1.val, r.2.1.val, ((bytes b).drop r.2.2.1.val).take r.2.2.2.val) =
          blocks (((bytes b).drop i.val).take rest.val) aa.val ss.val ∧
        r.2.2.1.val + r.2.2.2.val = i.val + rest.val ∧ r.1.val < 65536 ∧ r.2.1.val < 65536 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro aa ss i rest hm hir ha hs
  have hlen : (((bytes b).drop i.val).take rest.val).length = rest.val := by
    simp [length_bytes]; omega
  by_cases hN : 5552 ≤ rest.val
  · obtain ⟨c, hc, aa1, ss1, i1, rest1, rfl, ha1, hs1, hi1, hr1⟩ :=
      blocks_body_step b hN hir ha hs
    obtain ⟨r, hr, hrv, hri, hra, hrs⟩ :=
      IH rest1.val (by omega) aa1 ss1 i1 rest1 rfl (by omega)
        (by rw [ha1]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
        (by rw [hs1]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
    refine ⟨r, ?_, ?_, by omega, hra, hrs⟩
    · unfold adler32_z_loop at hr ⊢
      rw [loop_cont hc]
      exact hr
    · rw [hrv]
      conv_rhs => rw [blocks]
      rw [dif_pos (by rw [hlen]; exact hN)]
      have e1 : (((bytes b).drop i.val).take rest.val).take 5552 = ((bytes b).drop i.val).take 5552 := by
        rw [List.take_take, Nat.min_eq_left hN]
      have e2 : (((bytes b).drop i.val).take rest.val).drop 5552 =
          ((bytes b).drop i1.val).take rest1.val := by
        rw [List.drop_take, List.drop_drop, hi1, hr1, Nat.add_comm]
      rw [e1, e2, ← ha1, ← hs1]
  · refine ⟨(aa, ss, i, rest), ?_, ?_, rfl, ha, hs⟩
    · unfold adler32_z_loop
      exact loop_done (blocks_body_done b aa ss i (by omega))
    · rw [blocks, dif_neg (by rw [hlen]; exact hN)]

/-- `blocks_loop_eq` as a `wp` rule. -/
theorem blocks_loop_wp (b : Slice U8) (aa ss : U64) (i rest : Usize)
    (hir : i.val + rest.val ≤ b.val.length) (ha : aa.val < 65536) (hs : ss.val < 65536)
    {Q : Except Error (U64 × U64 × Usize × Usize) → Prop}
    (hq : ∀ r : U64 × U64 × Usize × Usize,
      (r.1.val, r.2.1.val, ((bytes b).drop r.2.2.1.val).take r.2.2.2.val) =
          blocks (((bytes b).drop i.val).take rest.val) aa.val ss.val →
        r.2.2.1.val + r.2.2.2.val = i.val + rest.val → r.1.val < 65536 → r.2.1.val < 65536 →
        Q (.ok r)) :
    wp (adler32_z_loop b aa ss i rest) Q := by
  obtain ⟨r, hr, h1, h2, h3, h4⟩ := blocks_loop_eq b rest.val aa ss i rest rfl hir ha hs
  rw [hr, wp_ok]
  exact hq r h1 h2 h3 h4

/-! ## `adler32_z` -/

/-- Closes a leaf `x ||| y = x' ||| y'` after the model's `if`s are split. -/
macro "a32_or_leaf" : tactic => `(tactic| (
  split_ifs <;> first
    | (exfalso; omega)
    | (congr 1 <;> first | omega | (rw [Nat.mod_eq_of_lt (by omega)]; omega))))

/-- **`adler32_z`**: with `buf` holding `len` bytes (or `Z_NULL`), the generated `adler32_z`
returns `rustZ`; in particular it never panics. -/
theorem adler32_z_eq (adler : U64) (buf : Option (Slice U8)) (len : Usize)
    (hbuf : ∀ b, buf = some b → len.val = b.val.length) :
    ∃ r, adler32_z adler buf len = .ok r ∧ r.val = rustZ adler.val (buf.map bytes) len.val := by
  have hm1 := and_ffff (adler.val / 65536)
  have hm2 := and_ffff adler.val
  have hs0 : adler.val / 65536 % 65536 < 65536 := Nat.mod_lt _ (by decide)
  have ha0 : adler.val % 65536 < 65536 := Nat.mod_lt _ (by decide)
  cases buf with
  | none =>
    refine ⟨1#u64, ?_, ?_⟩
    · apply eq_ok_of_wp
      unfold adler32_z
      aeneas_wp [shr16_eq]
      a32_split
      all_goals simp
    · simp only [rustZ, Option.map_none]
      split_ifs <;> rfl
  | some b =>
    have hlb : b.val.length = len.val := (hbuf b rfl).symm
    clear hbuf
    have hmax : len.val ≤ Usize.max := by have := b.property; omega
    by_cases h1 : len.val = 1
    · -- one byte
      have hb0 : 0 < b.val.length := by omega
      have hbv : (b.val[0]'hb0).val < 256 := by
        have := (b.val[0]'hb0).hBounds
        simpa using this
      have hg : (bytes b).getD 0 0 = (b.val[0]'hb0).val := by
        simp [bytes, List.getD_eq_getElem?_getD, hb0]
      apply exists_ok_of_wp
      unfold adler32_z
      a32_wp [base_val, h1]
      a32_split'
      all_goals try a32_contra
      all_goals try (exfalso; omega)
      all_goals refine ⟨_, rfl, ?_⟩
      all_goals simp only [UScalar.val_or, rustZ, Option.map_some, hg, _root_.ite_true]
      all_goals split_ifs
      all_goals try (exfalso; omega)
      all_goals simp only [*]
      all_goals (refine congrArg₂ (· ||| ·) ?_ (congrArg shl16N ?_) <;> omega)
    by_cases h16 : len.val < 16
    · -- fewer than 16 bytes
      apply exists_ok_of_wp
      unfold adler32_z
      a32_wp [base_val]
      a32_split'
      all_goals try a32_contra
      all_goals try (exfalso; omega)
      all_goals refine do_bytes_wp b _ len _ _ (by simp only [usize_0_val]; omega) (by omega)
                  (by simp only [UScalar.val_and, u64_65535_val, and_ffff]; omega)
                  (by simp only [UScalar.val_and, u64_65535_val, and_ffff]; omega) ?_
      all_goals rintro ⟨r1, r2⟩ hr
      all_goals simp only [UScalar.val_and, u64_65535_val, and_ffff, usize_0_val, List.drop_zero] at hr
      all_goals simp only [*] at hr
      all_goals have hr1 := congrArg Prod.fst hr
      all_goals have hr2 := congrArg Prod.snd hr
      all_goals simp only at hr1 hr2
      all_goals a32_wp [base_val]
      all_goals a32_split'
      all_goals try a32_contra
      all_goals try (exfalso; omega)
      all_goals refine ⟨_, rfl, ?_⟩
      all_goals simp only [UScalar.val_or, rustZ, Option.map_some, h1, h16, _root_.ite_true,
        _root_.ite_false, ← hr1, ← hr2]
      all_goals split_ifs
      all_goals try (exfalso; omega)
      all_goals simp only [*]
      all_goals (refine congrArg₂ (· ||| ·) ?_ (congrArg shl16N ?_) <;> omega)
    · -- the blocks, then the tail
      apply exists_ok_of_wp
      unfold adler32_z
      a32_wp [base_val]
      a32_split'
      all_goals try a32_contra
      all_goals try (exfalso; omega)
      all_goals refine blocks_loop_wp b _ _ _ len (by simp only [usize_0_val]; omega)
                  (by simp only [UScalar.val_and, u64_65535_val, and_ffff]; omega)
                  (by simp only [UScalar.val_and, u64_65535_val, and_ffff]; omega) ?_
      all_goals rintro ⟨aa, ss, i1, rest⟩ hq hir hla hls
      all_goals simp only [UScalar.val_and, u64_65535_val, and_ffff, usize_0_val, List.drop_zero,
        Nat.zero_add] at hq hir hla hls
      all_goals simp only [*] at hq
      all_goals have hq3 := congrArg (fun t => t.2.2) hq
      all_goals simp only at hq3
      all_goals have hlen3 : (((bytes b).drop i1.val).take rest.val).length = rest.val := by
                  simp [length_bytes]; omega
      all_goals have hrl : rest.val < 5552 := by
                  have := blocks_rest_lt ((bytes b).take len.val) (adler.val % 65536)
                    (adler.val / 65536 % 65536)
                  rw [← hq3, hlen3] at this
                  exact this
      all_goals a32_wp [base_val]
      all_goals a32_split'
      all_goals try a32_contra
      all_goals try (exfalso; omega)
      · -- the tail
        refine do_bytes_wp b i1 rest aa ss (by omega) (by omega) (by omega) (by omega) ?_
        rintro ⟨r1, r2⟩ hr
        have hr1 := congrArg Prod.fst hr
        have hr2 := congrArg Prod.snd hr
        simp only at hr1 hr2
        a32_wp [base_val]
        a32_split'
        all_goals try a32_contra
        all_goals try (exfalso; omega)
        all_goals refine ⟨_, rfl, ?_⟩
        all_goals simp only [UScalar.val_or, rustZ, Option.map_some, h1, h16, _root_.ite_true,
          _root_.ite_false, ← hq, ← hr1, ← hr2]
        all_goals split_ifs
        all_goals try (exfalso; omega)
        all_goals simp only [*]
        all_goals (refine congrArg₂ (· ||| ·) ?_ (congrArg shl16N ?_) <;> omega)
      · -- no tail
        refine ⟨_, rfl, ?_⟩
        simp only [UScalar.val_or, rustZ, Option.map_some, h1, h16, _root_.ite_true,
          _root_.ite_false, ← hq]
        split_ifs
        all_goals try (exfalso; omega)
        all_goals simp only [*]

/-- **`adler32`** (the `uInt` wrapper): `rustZ` on the same arguments. -/
theorem adler32_eq (adler : U64) (buf : Option (Slice U8)) (len : U32)
    (hbuf : ∀ b, buf = some b → len.val = b.val.length) :
    ∃ r, adler32 adler buf len = .ok r ∧ r.val = rustZ adler.val (buf.map bytes) len.val := by
  have hc : (UScalar.cast .Usize len).val = len.val := by
    have h1 := len.hBounds
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    simp only [UScalarTy.U32_numBits_eq] at h1
    rcases System.Platform.numBits_eq with h | h <;>
      simp only [UScalarTy.Usize_numBits_eq, h] <;> omega
  obtain ⟨r, hr, hrv⟩ :=
    adler32_z_eq adler buf (UScalar.cast .Usize len) (fun b hb => by rw [hc]; exact hbuf b hb)
  refine ⟨r, ?_, by rw [hrv, hc]⟩
  apply eq_ok_of_wp
  unfold adler32
  aeneas_wp [hr]

end EquivLean.Demo.XLang.Adler32.Rust
