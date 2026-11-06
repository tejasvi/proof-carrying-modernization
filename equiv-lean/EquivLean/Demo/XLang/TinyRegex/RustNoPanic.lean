import EquivLean.Demo.XLang.TinyRegex.RustFinal

/-!
# tiny-regex-c, Rust side: no panic on any input

`re_match_total` and `re_matchp_total`: `re_match` and `re_matchp` return `ok` (no panic, no
divergence) on EVERY input: any pattern, any text of any length, and for `re_matchp` any `Regex`
value (the public API takes one; no `WF`).  This extends `RustFinal.re_match_no_panic` (texts
shorter than `2^28`, from the model equality) to all inputs.
No model is involved: above `Isize.max` the casts of `matchstar` wrap and the Rust code leaves the
model, but it still returns.  The proof follows the call structure: the class loop, `matchone`,
`scan_fwd`, the recursion group by strong induction on `30 - pi` (with the back scans by their
position), the search loop of `re_matchp`; `re_compile` is total by `re_compile_eq`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.XLang.TinyRegex.Rust

theorem exists_ok_of_wp_total {α : Type} {c : Result α} (h : wp c (fun o => ∃ b, o = .ok b)) :
    ∃ b, c = Result.ok b := by
  rcases (wp_iff _ _).1 h with ⟨a, rfl, _⟩ | ⟨e, rfl, ⟨b, hb⟩⟩
  · exact ⟨a, rfl⟩
  · cases hb

theorem wp_total_of_ex {α : Type} {c : Result α} (h : ∃ b, c = Result.ok b) :
    wp c (fun o => ∃ b, o = .ok b) := by
  obtain ⟨b, hb⟩ := h
  rw [hb]
  exact (wp_ok _ _).2 ⟨b, rfl⟩

theorem isize_val_le_max (t : Isize) : t.val ≤ Isize.max := by
  have h := t.hmax
  rw [← IScalar.max_ISize_eq, IScalar.max_def]
  omega

/-! ## Below the group -/

/-- The class loop returns for every byte (also `0`) and every start index. -/
theorem matchcharclass_total (re : tiny_regex.Regex) (c : U8) (k : Usize) :
    ∃ b, tiny_regex.matchcharclass re c k = Result.ok b := by
  apply exists_ok_of_wp_total
  have hmax := usize_max_ge
  have hlen := ccl_length re
  simp only [tiny_regex.matchcharclass, tiny_regex.matchcharclass_loop]
  refine wp_loop (loop_shape _) (fun _ => True) (fun k : Usize => 40 - k.val) ?_ _ trivial
  intro s _
  rw [tiny_regex.matchcharclass_loop.body]
  aeneas_wp [wp_Array_index_usize, tiny_regex.MAX_CHAR_CLASS_LEN, matchrange_eq, cb_eq,
    matchmetachar_eq, ismetachar_eq, index_ccl, loopCls_cont, loopCls_done]
  rust_split
  all_goals first | exact ⟨_, rfl⟩ | (exfalso; omega) | omega

theorem matchone_total (re : tiny_regex.Regex) (p : tiny_regex.RegexObj) (c : U8) :
    ∃ b, tiny_regex.matchone re p c = Result.ok b := by
  obtain ⟨b0, hb0⟩ := matchcharclass_total re c p.ccl
  apply exists_ok_of_wp_total
  unfold tiny_regex.matchone
  aeneas_wp [hb0, isdigit_eq, matchalphanum_eq, isspace_eq]
  rust_split
  all_goals exact ⟨_, rfl⟩

/-- The value of `matchone` on any byte. -/
noncomputable def moV (re : tiny_regex.Regex) (p : tiny_regex.RegexObj) (c : U8) : Bool :=
  Classical.choose (matchone_total re p c)

theorem matchone_moV (re : tiny_regex.Regex) (p : tiny_regex.RegexObj) (c : U8) :
    tiny_regex.matchone re p c = Result.ok (moV re p c) :=
  Classical.choose_spec (matchone_total re p c)

theorem scan_fwd_total (re : tiny_regex.Regex) (p : tiny_regex.RegexObj) (text : Slice U8) (ti : Usize)
    (ml : I32) : ∃ r, tiny_regex.scan_fwd re p text ti ml = Result.ok r := by
  apply exists_ok_of_wp_total
  have hlen := len_le_max text
  simp only [tiny_regex.scan_fwd, tiny_regex.scan_fwd_loop]
  refine wp_loop (loop_shape _) (fun _ => True)
    (fun s : Usize × I32 => text.val.length - s.1.val) ?_ _ trivial
  intro s _
  obtain ⟨t, m⟩ := s
  simp only []
  rw [tiny_regex.scan_fwd_loop.body]
  aeneas_wp [at_eq, matchone_moV, loopCls_cont, loopCls_done]
  rust_split
  all_goals first | exact ⟨_, rfl⟩ | (exfalso; omega) | omega

/-! ## The recursion group -/

def TotMP (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) : Prop :=
  ∀ ti ml pre, ∃ r, tiny_regex.matchpattern_loop re pi text ti ml pre = Result.ok r
def TotMQ (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) : Prop :=
  ∀ p ti ml, ∃ r, tiny_regex.matchquestion re p pi text ti ml = Result.ok r
def TotSB (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) : Prop :=
  ∀ t pre ml prelen, ∃ r, tiny_regex.star_back re pi text t pre ml prelen = Result.ok r
def TotMS (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) : Prop :=
  ∀ p ti ml, ∃ r, tiny_regex.matchstar re p pi text ti ml = Result.ok r
def TotPB (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) : Prop :=
  ∀ t pre ml, ∃ r, tiny_regex.plus_back re pi text t pre ml = Result.ok r
def TotMPl (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) : Prop :=
  ∀ p ti ml, ∃ r, tiny_regex.matchplus re p pi text ti ml = Result.ok r

set_option maxHeartbeats 1000000 in
theorem mp_total_step (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (hpi : pi.val ≤ 30)
    (IH : ∀ pi' : Usize, pi'.val ≤ 30 → 30 - pi'.val < 30 - pi.val →
      TotMP re text pi' ∧ TotMQ re text pi' ∧ TotMS re text pi' ∧ TotMPl re text pi') :
    TotMP re text pi := by
  intro ti ml pre
  apply exists_ok_of_wp_total
  have hmax := usize_max_ge
  have hlenm := len_le_max text
  have hp1 : pi.val + 1 ≤ Usize.max := by omega
  have hp2 : pi.val + 2 ≤ Usize.max := by omega
  rw [tiny_regex.matchpattern_loop.eq_1]
  by_cases hu : (objAt re pi.val).kind.val = 0
  · aeneas_wp [obj_eq, hp1, hp2, tiny_regex.UNUSED, hu,
      matchquestion_unused re (objAt re pi.val) _ text ti _ hu]
    exact ⟨_, rfl⟩
  have hpi29 : pi.val < 30 := by
    by_contra hc; exact hu (by rw [objAt_ge re (by omega)]; rfl)
  have hu1 : ∀ k, (objAt re (pi.val + 1)).kind.val = k → k ≠ 0 → pi.val + 2 ≤ 30 := by
    intro k hk hk0
    by_contra hc
    rw [objAt_ge re (by omega)] at hk
    exact hk0 (by rw [← hk]; rfl)
  have hlt2 : pi.val + 2 < 2 ^ UScalarTy.Usize.numBits :=
    (UScalar.lt_pow_iff_le_max _).2 (by rw [UScalar.max_USize_eq]; exact hp2)
  have hlt1 : pi.val + 1 < 2 ^ UScalarTy.Usize.numBits :=
    (UScalar.lt_pow_iff_le_max _).2 (by rw [UScalar.max_USize_eq]; exact hp1)
  by_cases hq : (objAt re (pi.val + 1)).kind.val = 4
  · obtain ⟨_, hMQ, _, _⟩ := IH (UScalar.ofNatCore (pi.val + 2) hlt2)
      (by simp; have := hu1 4 hq (by decide); omega) (by simp; omega)
    aeneas_wp [obj_eq, hp1, hp2, tiny_regex.UNUSED, tiny_regex.QUESTIONMARK, hu, hq]
    exact wp_total_of_ex (hMQ _ _ _)
  by_cases hs : (objAt re (pi.val + 1)).kind.val = 5
  · obtain ⟨_, _, hMS, _⟩ := IH (UScalar.ofNatCore (pi.val + 2) hlt2)
      (by simp; have := hu1 5 hs (by decide); omega) (by simp; omega)
    aeneas_wp [obj_eq, hp1, hp2, tiny_regex.UNUSED, tiny_regex.QUESTIONMARK, tiny_regex.STAR, hu,
      hq, hs]
    exact wp_total_of_ex (hMS _ _ _)
  by_cases hpl : (objAt re (pi.val + 1)).kind.val = 6
  · obtain ⟨_, _, _, hMPl⟩ := IH (UScalar.ofNatCore (pi.val + 2) hlt2)
      (by simp; have := hu1 6 hpl (by decide); omega) (by simp; omega)
    aeneas_wp [obj_eq, hp1, hp2, tiny_regex.UNUSED, tiny_regex.QUESTIONMARK, tiny_regex.STAR,
      tiny_regex.PLUS, hu, hq, hs, hpl]
    exact wp_total_of_ex (hMPl _ _ _)
  by_cases h0 : (tbyte text ti.val).val = 0
  · aeneas_wp [obj_eq, hp1, hp2, tiny_regex.UNUSED, tiny_regex.QUESTIONMARK, tiny_regex.STAR,
      tiny_regex.PLUS, tiny_regex.END, hu, hq, hs, hpl, at_eq, h0]
    rust_split
    all_goals first | exact ⟨_, rfl⟩ | (exfalso; simp_all)
  · have hti1 : ti.val + 1 ≤ Usize.max := by
      by_contra hc; exact h0 (by rw [tbyte_ge text (by omega)]; rfl)
    obtain ⟨hMP1, _, _, _⟩ := IH (UScalar.ofNatCore (pi.val + 1) hlt1) (by simp; omega)
      (by simp; omega)
    aeneas_wp [obj_eq, hp1, hp2, tiny_regex.UNUSED, tiny_regex.QUESTIONMARK, tiny_regex.STAR,
      tiny_regex.PLUS, tiny_regex.END, hu, hq, hs, hpl, at_eq, h0,
      matchone_moV re (objAt re pi.val) (tbyte text ti.val), hti1]
    rust_split
    all_goals first | exact ⟨_, rfl⟩ | exact wp_total_of_ex (hMP1 _ _ _)

set_option maxHeartbeats 1000000 in
theorem mq_total_step (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (hmp : TotMP re text pi) :
    TotMQ re text pi := by
  intro p ti ml
  apply exists_ok_of_wp_total
  have hlenm := len_le_max text
  rw [tiny_regex.matchquestion.eq_1]
  by_cases hu : p.kind.val = 0
  · aeneas_wp [tiny_regex.UNUSED, hu]
    exact ⟨_, rfl⟩
  obtain ⟨⟨r1, m1⟩, hR1⟩ := hmp ti ml ml
  have hR1' : tiny_regex.matchpattern re pi text ti ml = Result.ok (r1, m1) := by
    rw [tiny_regex.matchpattern.eq_1]; exact hR1
  by_cases h0 : (tbyte text ti.val).val = 0
  · aeneas_wp [tiny_regex.UNUSED, hu, hR1', at_eq, h0]
    rust_split
    all_goals first | exact ⟨_, rfl⟩ | (exfalso; simp_all)
  · have hti1' : ti.val + 1 ≤ Usize.max := by
      by_contra hc; exact h0 (by rw [tbyte_ge text (by omega)]; rfl)
    have hti1 : ti.val + 1 < 2 ^ UScalarTy.Usize.numBits :=
      (UScalar.lt_pow_iff_le_max _).2 (by rw [UScalar.max_USize_eq]; exact hti1')
    obtain ⟨⟨r2, m2⟩, hR2⟩ := hmp (UScalar.ofNatCore (ti.val + 1) hti1) m1 m1
    have hR2' : tiny_regex.matchpattern re pi text (UScalar.ofNatCore (ti.val + 1) hti1) m1 =
        Result.ok (r2, m2) := by
      rw [tiny_regex.matchpattern.eq_1]; exact hR2
    aeneas_wp [tiny_regex.UNUSED, hu, hR1', at_eq, h0, matchone_moV re p (tbyte text ti.val), hti1',
      hR2']
    rust_split
    all_goals exact ⟨_, rfl⟩

set_option maxHeartbeats 1000000 in
theorem sb_total_step (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (hmp : TotMP re text pi) :
    TotSB re text pi := by
  have hI := isize_bounds
  suffices H : ∀ (n : Nat) (t pre : Isize) (ml prelen : I32), (t.val + 1).toNat = n →
      ∃ r, tiny_regex.star_back re pi text t pre ml prelen = Result.ok r by
    intro t pre ml prelen; exact H _ t pre ml prelen rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHt =>
  intro t pre ml prelen hn
  apply exists_ok_of_wp_total
  rw [tiny_regex.star_back.eq_1]
  by_cases hlt : t.val < pre.val
  · aeneas_wp [hlt]
    exact ⟨_, rfl⟩
  by_cases h0 : t.val < 0
  · aeneas_wp [hlt, h0]
    exact ⟨_, rfl⟩
  have htmax := isize_val_le_max t
  obtain ⟨⟨r1, m1⟩, hR1⟩ := hmp (IScalar.hcast .Usize t) ml ml
  have hR1' : tiny_regex.matchpattern re pi text (IScalar.hcast .Usize t) ml =
      Result.ok (r1, m1) := by
    rw [tiny_regex.matchpattern.eq_1]; exact hR1
  aeneas_wp [hlt, h0, hR1']
  rust_split
  all_goals first
    | exact ⟨_, rfl⟩
    | (exfalso; simp only [IScalar.min_ISize_eq, IScalar.max_ISize_eq] at *; omega)
    | (refine wp_total_of_ex (IHt _ ?_ _ _ _ _ rfl); rw [IScalar.ofInt_val_eq]; omega)

set_option maxHeartbeats 1000000 in
theorem ms_total_step (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (hsb : TotSB re text pi) :
    TotMS re text pi := by
  intro p ti ml
  apply exists_ok_of_wp_total
  obtain ⟨⟨t, m⟩, hs⟩ := scan_fwd_total re p text ti ml
  rw [tiny_regex.matchstar.eq_1]
  aeneas_wp [hs]
  exact wp_total_of_ex (hsb _ _ _ _)

set_option maxHeartbeats 1000000 in
theorem pb_total_step (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (hmp : TotMP re text pi) :
    TotPB re text pi := by
  suffices H : ∀ (n : Nat) (t pre : Usize) (ml : I32), t.val = n →
      ∃ r, tiny_regex.plus_back re pi text t pre ml = Result.ok r by
    intro t pre ml; exact H _ t pre ml rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHt =>
  intro t pre ml hn
  apply exists_ok_of_wp_total
  rw [tiny_regex.plus_back.eq_1]
  by_cases hle : t.val ≤ pre.val
  · aeneas_wp [hle]
    exact ⟨_, rfl⟩
  obtain ⟨⟨r1, m1⟩, hR1⟩ := hmp t ml ml
  have hR1' : tiny_regex.matchpattern re pi text t ml = Result.ok (r1, m1) := by
    rw [tiny_regex.matchpattern.eq_1]; exact hR1
  aeneas_wp [hle, hR1']
  rust_split
  all_goals first
    | exact ⟨_, rfl⟩
    | (exfalso; omega)
    | (refine wp_total_of_ex (IHt _ ?_ _ _ _ rfl); simp; omega)

set_option maxHeartbeats 1000000 in
theorem mpl_total_step (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (hpb : TotPB re text pi) :
    TotMPl re text pi := by
  intro p ti ml
  apply exists_ok_of_wp_total
  obtain ⟨⟨t, m⟩, hs⟩ := scan_fwd_total re p text ti ml
  rw [tiny_regex.matchplus.eq_1]
  aeneas_wp [hs]
  exact wp_total_of_ex (hpb _ _ _)

/-- The whole recursion group returns `ok` for every regex, text and pattern index `pi ≤ 30`. -/
theorem group_total (re : tiny_regex.Regex) (text : Slice U8) :
    ∀ (N : Nat) (pi : Usize), 30 - pi.val = N → pi.val ≤ 30 →
      TotMP re text pi ∧ TotMQ re text pi ∧ TotSB re text pi ∧ TotMS re text pi ∧
        TotPB re text pi ∧ TotMPl re text pi := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro pi hN hpi
  have hmp := mp_total_step re text pi hpi (fun pi' h1 h2 =>
    let r := IH _ (by omega) pi' rfl h1
    ⟨r.1, r.2.1, r.2.2.2.1, r.2.2.2.2.2⟩)
  have hsb := sb_total_step re text pi hmp
  have hpb := pb_total_step re text pi hmp
  exact ⟨hmp, mq_total_step re text pi hmp, hsb, ms_total_step re text pi hsb, hpb,
    mpl_total_step re text pi hpb⟩

/-! ## `re_matchp`, `re_match` -/

theorem re_matchp_loop_total (re : tiny_regex.Regex) (text : Slice U8) (hmp0 : TotMP re text 0#usize)
    (idx : I32) (ti : Usize) (ml : I32) :
    ∃ r, tiny_regex.re_matchp_loop re text idx ti ml = Result.ok r := by
  apply exists_ok_of_wp_total
  have hlen := len_le_max text
  unfold tiny_regex.re_matchp_loop
  refine wp_loop (loop_shape _) (fun _ => True)
    (fun s : I32 × Usize × I32 => text.val.length - s.2.1.val) ?_ _ trivial
  intro s _
  obtain ⟨idx, ti, ml⟩ := s
  simp only []
  rw [tiny_regex.re_matchp_loop.body]
  obtain ⟨⟨r1, m1⟩, hR1⟩ := hmp0 ti ml ml
  have hR1' : tiny_regex.matchpattern re 0#usize text ti ml = Result.ok (r1, m1) := by
    rw [tiny_regex.matchpattern.eq_1]; exact hR1
  aeneas_wp [hR1', at_eq, loopCls_cont, loopCls_done]
  rust_split
  all_goals first | exact ⟨_, rfl⟩ | (exfalso; omega) | omega

/-- **No panic:** `re_matchp` returns `ok` for every regex value (compiled or not) and every
text. -/
theorem re_matchp_total (r : Option tiny_regex.Regex) (text : Slice U8) :
    ∃ v, tiny_regex.re_matchp r text = Result.ok v := by
  cases r with
  | none => exact ⟨_, rfl⟩
  | some re =>
    obtain ⟨hmp0, -⟩ := group_total re text _ 0#usize rfl (by simp)
    obtain ⟨hmp1, -⟩ := group_total re text _ 1#usize rfl (by simp)
    obtain ⟨⟨r1, m1⟩, hR1⟩ := hmp1 0#usize 0#i32 0#i32
    have hR1' : tiny_regex.matchpattern re 1#usize text 0#usize 0#i32 = Result.ok (r1, m1) := by
      rw [tiny_regex.matchpattern.eq_1]; exact hR1
    obtain ⟨v, hv⟩ := re_matchp_loop_total re text hmp0 (-1)#i32 0#usize 0#i32
    apply exists_ok_of_wp_total
    unfold tiny_regex.re_matchp
    simp only []
    aeneas_wp [obj_eq, hR1', hv]
    rust_split
    all_goals exact ⟨_, rfl⟩

/-- **No panic:** `re_match` returns `ok` for every pattern and every text, of any length. -/
theorem re_match_total (pattern text : Slice U8) :
    ∃ v, tiny_regex.re_match pattern text = Result.ok v := by
  obtain ⟨r, hr, -, -⟩ := re_compile_eq pattern
  unfold tiny_regex.re_match
  rw [hr]
  cases r with
  | none => simpa using re_matchp_total none text
  | some re => simpa using re_matchp_total (some re) text

end EquivLean.Demo.XLang.TinyRegex.Rust

#print axioms EquivLean.Demo.XLang.TinyRegex.Rust.re_match_total
#print axioms EquivLean.Demo.XLang.TinyRegex.Rust.re_matchp_total
