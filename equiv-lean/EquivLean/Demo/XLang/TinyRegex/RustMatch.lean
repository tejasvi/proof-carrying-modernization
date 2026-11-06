import EquivLean.Demo.XLang.TinyRegex.RustLeaves

/-!
# tiny-regex-c → model, Rust side: the matcher recursion group

The seven mutually recursive Rust functions (`matchpattern`, its loop `matchpattern_loop`,
`matchquestion`, `matchstar` + `star_back`, `matchplus` + `plus_back`) equal the model's
`mpLoop`, `matchquestion`, `matchstar` + `starBack`, `matchplus` + `plusBack` on the
representation `ctx re text`: each returns `ok` (no panic, no divergence) with the model's result
as a Rust tuple (`res`: the flag and `*matchlength` wrapped to `i32`), for every UB mask `ub` of the
model.  Hypotheses: the last object of `re` is `UNUSED` (`WF`, true after `re_compile`), the
pattern index is inside `objs`, the text index inside the text, the text shorter than `2^28`.

Strong induction on `30 - pi`; at each `pi`: `matchpattern_loop` (it calls the group at `pi + 1`
and `pi + 2`), then `matchquestion`, `star_back` (an inner induction on its position) and
`matchstar`, `plus_back` and `matchplus`, which call `matchpattern` at `pi`.  Every specification
takes the model's arguments separately from the Rust values, linked by hypotheses, so that a
recursive call is closed by unification against the model's call.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.XLang.TinyRegex.Rust

/-! ## The specifications at one pattern index -/

/-- `matchpattern_loop` at pattern index `pi` (model index `piN`). -/
def SpecMP (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (piN : Nat) : Prop :=
  ∀ (ti : Usize) (tiN : Nat) (ml pre : I32) (mlZ preZ : Int), ti.val = tiN →
    tiN ≤ text.val.length → ml = toI32 mlZ → pre = toI32 preZ → ∀ ub,
    tiny_regex.matchpattern_loop re pi text ti ml pre =
      Result.ok (res (mpLoop (ctx re text) preZ piN tiN mlZ ub))

/-- `matchquestion` with continuation index `pi`. -/
def SpecMQ (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (piN : Nat) : Prop :=
  ∀ (p : tiny_regex.RegexObj) (ti : Usize) (tiN : Nat) (ml : I32) (mlZ : Int), ti.val = tiN →
    tiN ≤ text.val.length → ml = toI32 mlZ → ∀ ub,
    tiny_regex.matchquestion re p pi text ti ml =
      Result.ok (res (matchquestion (ctx re text) (tok p) piN tiN mlZ ub))

/-- `star_back` (the second loop of `matchstar`) with continuation index `pi`. -/
def SpecSB (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (piN : Nat) : Prop :=
  ∀ (t pre : Isize) (tN preN : Nat) (ml prelen : I32) (mlZ prelenZ : Int), t.val = tN →
    pre.val = preN → tN ≤ text.val.length → ml = toI32 mlZ → prelen = toI32 prelenZ → ∀ ub,
    tiny_regex.star_back re pi text t pre ml prelen =
      Result.ok (res (starBack (ctx re text) piN prelenZ preN tN mlZ ub))

/-- `matchstar` with continuation index `pi`. -/
def SpecMS (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (piN : Nat) : Prop :=
  ∀ (p : tiny_regex.RegexObj) (ti : Usize) (tiN : Nat) (ml : I32) (mlZ : Int), ti.val = tiN →
    tiN ≤ text.val.length → ml = toI32 mlZ → ∀ ub,
    tiny_regex.matchstar re p pi text ti ml =
      Result.ok (res (matchstar (ctx re text) (tok p) piN tiN mlZ ub))

/-- `plus_back` (the second loop of `matchplus`) with continuation index `pi`. -/
def SpecPB (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (piN : Nat) : Prop :=
  ∀ (t pre : Usize) (tN preN : Nat) (ml : I32) (mlZ : Int), t.val = tN → pre.val = preN →
    tN ≤ text.val.length → ml = toI32 mlZ → ∀ ub,
    tiny_regex.plus_back re pi text t pre ml =
      Result.ok (res (plusBack (ctx re text) piN preN tN mlZ ub))

/-- `matchplus` with continuation index `pi`. -/
def SpecMPl (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (piN : Nat) : Prop :=
  ∀ (p : tiny_regex.RegexObj) (ti : Usize) (tiN : Nat) (ml : I32) (mlZ : Int), ti.val = tiN →
    tiN ≤ text.val.length → ml = toI32 mlZ → ∀ ub,
    tiny_regex.matchplus re p pi text ti ml =
      Result.ok (res (matchplus (ctx re text) (tok p) piN tiN mlZ ub))

/-! ## Helpers -/

theorem wp_of_eq {α : Type} {c : Result α} {v : α} (h : c = Result.ok v) : wp c (· = .ok v) := by
  rw [h]; exact (wp_ok _ _).2 rfl

theorem tok_type (o : tiny_regex.RegexObj) : (tok o).type = o.kind.val := rfl
theorem tok_ch (o : tiny_regex.RegexObj) : (tok o).ch = o.ch.val := rfl
theorem tok_ccl (o : tiny_regex.RegexObj) : (tok o).ccl = o.ccl.val := rfl

theorem res_ok (r : Res) : (res r).1 = r.ok := rfl
theorem res_ml (r : Res) : (res r).2 = toI32 r.ml := rfl

theorem toI32_add_one' (v : Int) : toI32 (v + 1) = core.num.I32.wrapping_add (toI32 v) 1#i32 :=
  (toI32_add_one v).symm

theorem toI32_sub_one' (v : Int) : toI32 (v - 1) = core.num.I32.wrapping_sub (toI32 v) 1#i32 :=
  (toI32_sub_one v).symm

/-- The model's `advance` stops inside the text. -/
theorem advance_le (C : Ctx) (p : Tok) :
    ∀ (n ti : Nat) (ml : Int) (ub : Nat), C.T.size - ti = n → ti ≤ C.T.size →
      (advance C p ti ml ub).1 ≤ C.T.size := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ti ml ub hn hti
  rw [advance.eq_1]
  by_cases h : ti < C.T.size
  · rw [dite_eq_left h]
    simp only []
    split_ifs
    · exact IH _ (by omega) _ _ _ rfl (by omega)
    · simp only []; omega
    · simp only []; omega
  · rw [dite_eq_right h]
    split_ifs <;> simp only [] <;> omega

theorem hcast_isize_val (t : Usize) (h : t.val < 2 ^ 28) :
    (UScalar.hcast .Isize t).val = t.val := by
  rw [UScalar.hcast_val_eq]
  have hn : IScalarTy.Isize.numBits = 32 ∨ IScalarTy.Isize.numBits = 64 := by
    rw [IScalarTy.Isize_numBits_eq]; exact System.Platform.numBits_eq
  rcases hn with hn | hn <;> rw [hn]
  · exact bmod_pow_numBits_eq_of_lt IScalarTy.I32 _ (by simp) (by simp; omega)
  · exact bmod_pow_numBits_eq_of_lt IScalarTy.I64 _ (by simp) (by simp; omega)

theorem hcast_usize_val (b : Isize) (h0 : 0 ≤ b.val) :
    (IScalar.hcast .Usize b).val = b.val.toNat := by
  rw [IScalar.hcast_val_eq]
  have hb := b.hBounds
  have hn : IScalarTy.Isize.numBits = UScalarTy.Usize.numBits := by
    rw [IScalarTy.Isize_numBits_eq, UScalarTy.Usize_numBits_eq]
  rw [Int.emod_eq_of_lt h0]
  rw [hn] at hb
  have : (2:Int) ^ (UScalarTy.Usize.numBits - 1) ≤ 2 ^ UScalarTy.Usize.numBits :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have h2 : ((2 ^ UScalarTy.Usize.numBits : Nat) : Int) = (2:Int) ^ UScalarTy.Usize.numBits := by
    push_cast; rfl
  omega

theorem matchquestion_unused (re : tiny_regex.Regex) (p : tiny_regex.RegexObj) (pi : Usize)
    (text : Slice U8) (ti : Usize) (ml : I32) (hu : p.kind.val = 0) :
    tiny_regex.matchquestion re p pi text ti ml = Result.ok (true, ml) := by
  rw [tiny_regex.matchquestion.eq_1]
  have : p.kind = tiny_regex.UNUSED := by
    simp only [tiny_regex.UNUSED]; exact UScalar.eq_of_val_eq (by rw [hu]; rfl)
  rw [ite_eq_left this]

theorem model_matchquestion_unused (C : Ctx) (p : Tok) (pi ti : Nat) (ml : Int) (ub : Nat)
    (hu : p.type = 0) : matchquestion C p pi ti ml ub = ⟨true, ml, ub⟩ := by
  rw [matchquestion.eq_1]
  simp [hu, UNUSED]

/-! ## `matchpattern_loop` -/

set_option maxHeartbeats 1000000 in
theorem mp_step (re : tiny_regex.Regex) (text : Slice U8) (hwf : WF re)
    (hlen : text.val.length < 2 ^ 28) (pi : Usize) (hpi : pi.val < 30)
    (IH : ∀ (pi' : Usize) (piN' : Nat), pi'.val = piN' → piN' < 30 → 30 - piN' < 30 - pi.val →
      SpecMP re text pi' piN' ∧ SpecMQ re text pi' piN' ∧ SpecMS re text pi' piN' ∧
        SpecMPl re text pi' piN') :
    SpecMP re text pi pi.val := by
  intro ti tiN ml pre mlZ preZ htiN hti hml hpre ub
  subst htiN hml hpre
  have hmax := usize_max_ge
  have hP := ctx_P_size re text
  have hp1 : pi.val + 1 ≤ Usize.max := by omega
  have hp2 : pi.val + 2 ≤ Usize.max := by omega
  rw [tiny_regex.matchpattern_loop.eq_1]
  apply eq_ok_of_wp
  generalize hV : res (mpLoop (ctx re text) preZ pi.val ti.val mlZ ub) = V
  by_cases hu : (objAt re pi.val).kind.val = 0
  · -- `UNUSED` (the end of the pattern): `matchquestion` returns at once
    aeneas_wp [obj_eq, hp1, hp2, tiny_regex.UNUSED, hu,
      matchquestion_unused re (objAt re pi.val) _ text ti _ hu]
    subst hV
    rw [mpLoop.eq_1]
    simp [hP, hpi, ctx_P_get, tok, hu, UNUSED, model_matchquestion_unused, res]
  have hpi28 : pi.val + 1 < 30 := by
    by_contra hc
    have h29 : pi.val = 29 := by omega
    exact hu (by rw [h29]; exact hwf)
  have hu1 : ∀ k, (objAt re (pi.val + 1)).kind.val = k → k ≠ 0 → pi.val + 2 < 30 := by
    intro k hk hk0
    by_contra hc
    have h28 : pi.val + 1 = 29 := by omega
    rw [h28] at hk
    exact hk0 (by rw [← hk]; exact hwf)
  have hlt2 : pi.val + 2 < 2 ^ UScalarTy.Usize.numBits :=
    (UScalar.lt_pow_iff_le_max _).2 (by rw [UScalar.max_USize_eq]; exact hp2)
  have hlt1 : pi.val + 1 < 2 ^ UScalarTy.Usize.numBits :=
    (UScalar.lt_pow_iff_le_max _).2 (by rw [UScalar.max_USize_eq]; exact hp1)
  by_cases hq : (objAt re (pi.val + 1)).kind.val = 4
  · -- `?` follows: `matchquestion` at `pi + 2`
    obtain ⟨_, hMQ, _, _⟩ := IH (UScalar.ofNatCore (pi.val + 2) hlt2) (pi.val + 2) (by simp)
      (hu1 4 hq (by decide)) (by omega)
    aeneas_wp [obj_eq, hp1, hp2, tiny_regex.UNUSED, tiny_regex.QUESTIONMARK, hu, hq]
    subst hV
    rw [mpLoop.eq_1]
    simp [hP, hpi, hpi28, ctx_P_get, tok_type, hu, hq, UNUSED, QUESTIONMARK]
    exact wp_of_eq (hMQ _ _ _ _ _ rfl hti rfl _)
  by_cases hs : (objAt re (pi.val + 1)).kind.val = 5
  · -- `*` follows: `matchstar` at `pi + 2`
    obtain ⟨_, _, hMS, _⟩ := IH (UScalar.ofNatCore (pi.val + 2) hlt2) (pi.val + 2) (by simp)
      (hu1 5 hs (by decide)) (by omega)
    aeneas_wp [obj_eq, hp1, hp2, tiny_regex.UNUSED, tiny_regex.QUESTIONMARK, tiny_regex.STAR, hu,
      hq, hs]
    subst hV
    rw [mpLoop.eq_1]
    simp [hP, hpi, hpi28, ctx_P_get, tok_type, hu, hs, UNUSED, QUESTIONMARK, STAR]
    exact wp_of_eq (hMS _ _ _ _ _ rfl hti rfl _)
  by_cases hpl : (objAt re (pi.val + 1)).kind.val = 6
  · -- `+` follows: `matchplus` at `pi + 2`
    obtain ⟨_, _, _, hMPl⟩ := IH (UScalar.ofNatCore (pi.val + 2) hlt2) (pi.val + 2) (by simp)
      (hu1 6 hpl (by decide)) (by omega)
    aeneas_wp [obj_eq, hp1, hp2, tiny_regex.UNUSED, tiny_regex.QUESTIONMARK, tiny_regex.STAR,
      tiny_regex.PLUS, hu, hq, hs, hpl]
    subst hV
    rw [mpLoop.eq_1]
    simp [hP, hpi, hpi28, ctx_P_get, tok_type, hu, hpl, UNUSED, QUESTIONMARK, STAR, PLUS]
    exact wp_of_eq (hMPl _ _ _ _ _ rfl hti rfl _)
  -- a plain object (or `$`): compare one byte, then the next object
  by_cases h0 : (tbyte text ti.val).val = 0
  · aeneas_wp [obj_eq, hp1, hp2, tiny_regex.UNUSED, tiny_regex.QUESTIONMARK, tiny_regex.STAR,
      tiny_regex.PLUS, tiny_regex.END, hu, hq, hs, hpl, at_eq, h0]
    rust_split
    all_goals (subst hV; rw [mpLoop.eq_1]
               simp_all [ctx_P_get, tok_type, UNUSED, QUESTIONMARK, STAR, PLUS, END, rd_eq, res,
                 Bool.beq_eq_decide_eq])
  · have hti' : ti.val < text.val.length := by
      by_contra hc; exact h0 (by rw [tbyte_ge text (by omega)]; rfl)
    obtain ⟨hMP1, _, _, _⟩ := IH (UScalar.ofNatCore (pi.val + 1) hlt1) (pi.val + 1) (by simp) hpi28
      (by omega)
    aeneas_wp [obj_eq, hp1, hp2, tiny_regex.UNUSED, tiny_regex.QUESTIONMARK, tiny_regex.STAR,
      tiny_regex.PLUS, tiny_regex.END, hu, hq, hs, hpl, at_eq, h0,
      matchone_eq re text (objAt re pi.val) (tbyte text ti.val) h0]
    rust_split
    all_goals try (exfalso; omega)
    all_goals first
      | (subst hV; rw [mpLoop.eq_1]
         simp_all [ctx_P_get, tok_type, UNUSED, QUESTIONMARK, STAR, PLUS, END, rd_eq, res,
           Bool.beq_eq_decide_eq]; done)
      | (subst hV; rw [mpLoop.eq_1]
         simp [ctx_P_get, tok_type, UNUSED, QUESTIONMARK, STAR, PLUS, END, rd_eq,
           Bool.beq_eq_decide_eq, *]
         exact wp_of_eq (hMP1 _ _ _ _ _ _ (by simp) (by omega) (toI32_add_one mlZ) rfl _))


/-! ## `matchquestion` -/

set_option maxHeartbeats 1000000 in
theorem mq_step (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (piN : Nat)
    (hmp : SpecMP re text pi piN) : SpecMQ re text pi piN := by
  intro p ti tiN ml mlZ htiN hti hml ub
  subst htiN hml
  have hmax := usize_max_ge
  have hlenm := len_le_max text
  rw [tiny_regex.matchquestion.eq_1]
  apply eq_ok_of_wp
  generalize hV : res (matchquestion (ctx re text) (tok p) piN ti.val mlZ ub) = V
  by_cases hu : p.kind.val = 0
  · aeneas_wp [tiny_regex.UNUSED, hu]
    subst hV
    rw [model_matchquestion_unused _ _ _ _ _ _ (by rw [tok_type]; exact hu)]
    rfl
  obtain ⟨⟨r1, m1⟩, hR1, hM1⟩ := ex_of_forall (hmp ti ti.val (toI32 mlZ) (toI32 mlZ) mlZ mlZ rfl hti
    rfl rfl)
  have hR1' : tiny_regex.matchpattern re pi text ti (toI32 mlZ) = Result.ok (r1, m1) := by
    rw [tiny_regex.matchpattern.eq_1]; exact hR1
  have hM1ok : ∀ u, (mpLoop (ctx re text) mlZ piN ti.val mlZ u).ok = r1 :=
    fun u => congrArg Prod.fst (hM1 u)
  have hM1ml : ∀ u, toI32 (mpLoop (ctx re text) mlZ piN ti.val mlZ u).ml = m1 :=
    fun u => congrArg Prod.snd (hM1 u)
  by_cases h0 : (tbyte text ti.val).val = 0
  · aeneas_wp [tiny_regex.UNUSED, hu, hR1', at_eq, h0]
    clear hR1 hR1' hM1
    rust_split
    all_goals (subst hV; rw [matchquestion.eq_1]
               simp_all [tok_type, UNUSED, rd_eq, res, Bool.beq_eq_decide_eq])
  · have hti' : ti.val < text.val.length := by
      by_contra hc; exact h0 (by rw [tbyte_ge text (by omega)]; rfl)
    have hti1 : ti.val + 1 < 2 ^ UScalarTy.Usize.numBits :=
      (UScalar.lt_pow_iff_le_max _).2 (by rw [UScalar.max_USize_eq]; omega)
    have hti1' : ti.val + 1 ≤ Usize.max := by omega
    have hm1 : m1 = toI32 (mpLoop (ctx re text) mlZ piN ti.val mlZ ub).ml := (hM1ml ub).symm
    obtain ⟨⟨r2, m2⟩, hR2, hM2⟩ := ex_of_forall (hmp (UScalar.ofNatCore (ti.val + 1) hti1)
      (ti.val + 1) m1 m1 _ _ (by simp) (by omega) hm1 hm1)
    have hR2' : tiny_regex.matchpattern re pi text (UScalar.ofNatCore (ti.val + 1) hti1) m1 =
        Result.ok (r2, m2) := by
      rw [tiny_regex.matchpattern.eq_1]; exact hR2
    have hM2ok : ∀ u, (mpLoop (ctx re text) (mpLoop (ctx re text) mlZ piN ti.val mlZ ub).ml piN
        (ti.val + 1) (mpLoop (ctx re text) mlZ piN ti.val mlZ ub).ml u).ok = r2 :=
      fun u => congrArg Prod.fst (hM2 u)
    have hM2ml : ∀ u, toI32 (mpLoop (ctx re text) (mpLoop (ctx re text) mlZ piN ti.val mlZ ub).ml piN
        (ti.val + 1) (mpLoop (ctx re text) mlZ piN ti.val mlZ ub).ml u).ml = m2 :=
      fun u => congrArg Prod.snd (hM2 u)
    aeneas_wp [tiny_regex.UNUSED, hu, hR1', at_eq, h0, matchone_eq re text p (tbyte text ti.val) h0,
      hti1', hR2']
    clear hR1 hR1' hM1 hR2 hR2' hM2 hm1
    rust_split
    all_goals (subst hV; rw [matchquestion.eq_1]
               simp_all [tok_type, UNUSED, rd_eq, res, Bool.beq_eq_decide_eq, toI32_add_one'])

/-! ## `matchstar` -/

theorem isize_bounds : Isize.min ≤ -2147483648 ∧ 2147483647 ≤ Isize.max := by
  rcases Isize.bounds_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
    simp only [I32.min_eq, I32.max_eq, I64.min_eq, I64.max_eq] <;> omega

theorem star_back_neg (re : tiny_regex.Regex) (pi : Usize) (text : Slice U8) (t pre : Isize)
    (ml prelen : I32) (h : t.val < pre.val) :
    tiny_regex.star_back re pi text t pre ml prelen = Result.ok (false, prelen) := by
  rw [tiny_regex.star_back.eq_1]
  have h' : t < pre := (IScalar.lt_equiv t pre).2 h
  rw [ite_eq_left h']

set_option maxHeartbeats 1000000 in
theorem sb_step (re : tiny_regex.Regex) (text : Slice U8) (hlen : text.val.length < 2 ^ 28)
    (pi : Usize) (piN : Nat) (hmp : SpecMP re text pi piN) : SpecSB re text pi piN := by
  have hI := isize_bounds
  suffices H : ∀ (n : Nat) (t pre : Isize) (tN preN : Nat) (ml prelen : I32) (mlZ prelenZ : Int),
      tN = n → t.val = tN → pre.val = preN → tN ≤ text.val.length → ml = toI32 mlZ →
      prelen = toI32 prelenZ → ∀ ub, tiny_regex.star_back re pi text t pre ml prelen =
        Result.ok (res (starBack (ctx re text) piN prelenZ preN tN mlZ ub)) by
    intro t pre tN preN ml prelen mlZ prelenZ h1 h2 h3 h4 h5
    exact H tN t pre tN preN ml prelen mlZ prelenZ rfl h1 h2 h3 h4 h5
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHt =>
  intro t pre tN preN ml prelen mlZ prelenZ hn htN hpreN htl hml hprelen ub
  subst hn hml hprelen
  rw [tiny_regex.star_back.eq_1]
  apply eq_ok_of_wp
  generalize hV : res (starBack (ctx re text) piN prelenZ preN tN mlZ ub) = V
  by_cases hlt : tN < preN
  · have hlt' : t.val < pre.val := by omega
    aeneas_wp [hlt']
    subst hV
    rw [starBack.eq_1]
    simp [show ¬ preN ≤ tN by omega, res]
  have hlt' : ¬ t.val < pre.val := by omega
  have h0 : ¬ t.val < 0 := by omega
  have hc : (IScalar.hcast .Usize t).val = tN := by rw [hcast_usize_val t (by omega)]; omega
  obtain ⟨⟨r1, m1⟩, hR1, hM1⟩ := ex_of_forall (hmp (IScalar.hcast .Usize t) tN (toI32 mlZ)
    (toI32 mlZ) mlZ mlZ hc htl rfl rfl)
  have hR1' : tiny_regex.matchpattern re pi text (IScalar.hcast .Usize t) (toI32 mlZ) =
      Result.ok (r1, m1) := by
    rw [tiny_regex.matchpattern.eq_1]; exact hR1
  have hM1ok : ∀ u, (mpLoop (ctx re text) mlZ piN tN mlZ u).ok = r1 :=
    fun u => congrArg Prod.fst (hM1 u)
  have hM1ml : ∀ u, toI32 (mpLoop (ctx re text) mlZ piN tN mlZ u).ml = m1 :=
    fun u => congrArg Prod.snd (hM1 u)
  clear hR1 hM1
  aeneas_wp [hlt', h0, hR1']
  rust_split
  · -- the attempt at `t` matches
    rename_i hr1
    subst hV
    rw [starBack.eq_1]
    simp [show preN ≤ tN by omega, hM1ok, hM1ml, hr1, res]
  · rename_i hr1 hb
    by_cases htz : tN = 0
    · -- `t = 0`: `text--` leaves the text, the next call returns at once
      subst htz
      have hneg := star_back_neg re pi text (IScalar.ofIntCore (t.val - 1)
        ((IScalar.inBounds_iff _).2 hb)) pre (core.num.I32.wrapping_sub m1 1#i32) (toI32 prelenZ)
        (by rw [IScalar.ofInt_val_eq]; omega)
      rw [hneg]
      subst hV
      rw [starBack.eq_1]
      simp [show preN ≤ 0 by omega, hM1ok, hr1, res]
    · subst hV
      rw [starBack.eq_1]
      simp only [show preN ≤ tN by omega, htz, hM1ok, hr1, _root_.ite_true, _root_.ite_false,
        _root_.dite_false, Bool.false_eq_true]
      refine wp_of_eq (IHt (tN - 1) (by omega) _ pre (tN - 1) preN _ (toI32 prelenZ) _ prelenZ rfl
        ?_ hpreN (by omega) ?_ rfl _)
      · rw [IScalar.ofInt_val_eq]; omega
      · simp only [toI32_sub_one', hM1ml]
  · exfalso; simp only [IScalar.min_ISize_eq, IScalar.max_ISize_eq] at *; omega

set_option maxHeartbeats 1000000 in
theorem ms_step (re : tiny_regex.Regex) (text : Slice U8) (hlen : text.val.length < 2 ^ 28)
    (pi : Usize) (piN : Nat) (hsb : SpecSB re text pi piN) : SpecMS re text pi piN := by
  intro p ti tiN ml mlZ htiN hti hml ub
  subst htiN hml
  have hmax := usize_max_ge
  rw [tiny_regex.matchstar.eq_1]
  apply eq_ok_of_wp
  have hadv := advance_le (ctx re text) (tok p) _ ti.val mlZ ub rfl (by rw [ctx_T_size]; exact hti)
  rw [ctx_T_size] at hadv
  have hlt : (advance (ctx re text) (tok p) ti.val mlZ ub).1 < 2 ^ UScalarTy.Usize.numBits :=
    (UScalar.lt_pow_iff_le_max _).2 (by rw [UScalar.max_USize_eq]; omega)
  have hu := usz_val hlt
  have ht : (UScalar.hcast .Isize (usz (advance (ctx re text) (tok p) ti.val mlZ ub).1)).val =
      (advance (ctx re text) (tok p) ti.val mlZ ub).1 := by
    rw [hcast_isize_val _ (by rw [hu]; omega), hu]
  have hpre : (UScalar.hcast .Isize ti).val = ti.val := hcast_isize_val ti (by omega)
  aeneas_wp [scan_fwd_eq re text p ti (toI32 mlZ) mlZ rfl ub, advRes]
  rw [matchstar.eq_1]
  simp only []
  exact wp_of_eq (hsb _ _ _ _ _ _ _ _ ht hpre (by omega) rfl rfl _)

/-! ## `matchplus` -/

set_option maxHeartbeats 1000000 in
theorem pb_step (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (piN : Nat)
    (hmp : SpecMP re text pi piN) : SpecPB re text pi piN := by
  suffices H : ∀ (n : Nat) (t pre : Usize) (tN preN : Nat) (ml : I32) (mlZ : Int), tN = n →
      t.val = tN → pre.val = preN → tN ≤ text.val.length → ml = toI32 mlZ → ∀ ub,
      tiny_regex.plus_back re pi text t pre ml =
        Result.ok (res (plusBack (ctx re text) piN preN tN mlZ ub)) by
    intro t pre tN preN ml mlZ h1 h2 h3 h4
    exact H tN t pre tN preN ml mlZ rfl h1 h2 h3 h4
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHt =>
  intro t pre tN preN ml mlZ hn htN hpreN htl hml ub
  subst hn htN hpreN hml
  rw [tiny_regex.plus_back.eq_1]
  apply eq_ok_of_wp
  generalize hV : res (plusBack (ctx re text) piN pre.val t.val mlZ ub) = V
  by_cases hle : t.val ≤ pre.val
  · aeneas_wp [hle]
    subst hV
    rw [plusBack.eq_1]
    simp [show ¬ pre.val < t.val by omega, res]
  obtain ⟨⟨r1, m1⟩, hR1, hM1⟩ := ex_of_forall (hmp t t.val (toI32 mlZ) (toI32 mlZ) mlZ mlZ rfl htl
    rfl rfl)
  have hR1' : tiny_regex.matchpattern re pi text t (toI32 mlZ) = Result.ok (r1, m1) := by
    rw [tiny_regex.matchpattern.eq_1]; exact hR1
  have hM1ok : ∀ u, (mpLoop (ctx re text) mlZ piN t.val mlZ u).ok = r1 :=
    fun u => congrArg Prod.fst (hM1 u)
  have hM1ml : ∀ u, toI32 (mpLoop (ctx re text) mlZ piN t.val mlZ u).ml = m1 :=
    fun u => congrArg Prod.snd (hM1 u)
  clear hR1 hM1
  aeneas_wp [hle, hR1']
  rust_split
  · rename_i hr1
    subst hV
    rw [plusBack.eq_1]
    simp [show pre.val < t.val by omega, hM1ok, hM1ml, hr1, res]
  · rename_i hr1 hb
    subst hV
    rw [plusBack.eq_1]
    simp only [show pre.val < t.val by omega, hM1ok, hr1, _root_.dite_true, _root_.ite_false,
      Bool.false_eq_true]
    refine wp_of_eq (IHt (t.val - 1) (by omega) _ pre (t.val - 1) pre.val _ _ rfl ?_ rfl
      (by omega) ?_ _)
    · simp
    · simp only [toI32_sub_one', hM1ml]
  · exfalso; omega

set_option maxHeartbeats 1000000 in
theorem mpl_step (re : tiny_regex.Regex) (text : Slice U8) (hlen : text.val.length < 2 ^ 28)
    (pi : Usize) (piN : Nat) (hpb : SpecPB re text pi piN) : SpecMPl re text pi piN := by
  intro p ti tiN ml mlZ htiN hti hml ub
  subst htiN hml
  have hmax := usize_max_ge
  rw [tiny_regex.matchplus.eq_1]
  apply eq_ok_of_wp
  have hadv := advance_le (ctx re text) (tok p) _ ti.val mlZ ub rfl (by rw [ctx_T_size]; exact hti)
  rw [ctx_T_size] at hadv
  have hlt : (advance (ctx re text) (tok p) ti.val mlZ ub).1 < 2 ^ UScalarTy.Usize.numBits :=
    (UScalar.lt_pow_iff_le_max _).2 (by rw [UScalar.max_USize_eq]; omega)
  have hu := usz_val hlt
  aeneas_wp [scan_fwd_eq re text p ti (toI32 mlZ) mlZ rfl ub, advRes]
  rw [matchplus.eq_1]
  simp only []
  exact wp_of_eq (hpb _ _ _ _ _ _ hu rfl hadv rfl _)

/-! ## The group -/

/-- **The matcher group equals the model** at every pattern index `pi < 30`. -/
theorem group_spec (re : tiny_regex.Regex) (text : Slice U8) (hwf : WF re)
    (hlen : text.val.length < 2 ^ 28) :
    ∀ (N : Nat) (pi : Usize) (piN : Nat), pi.val = piN → 30 - piN = N → piN < 30 →
      SpecMP re text pi piN ∧ SpecMQ re text pi piN ∧ SpecSB re text pi piN ∧
        SpecMS re text pi piN ∧ SpecPB re text pi piN ∧ SpecMPl re text pi piN := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro pi piN hpiN hN hpi
  subst hpiN
  have hmp := mp_step re text hwf hlen pi hpi (fun pi' piN' h1 h2 h3 =>
    let r := IH _ (by omega) pi' piN' h1 rfl h2
    ⟨r.1, r.2.1, r.2.2.2.1, r.2.2.2.2.2⟩)
  have hsb := sb_step re text hlen pi pi.val hmp
  have hpb := pb_step re text pi pi.val hmp
  exact ⟨hmp, mq_step re text pi pi.val hmp, hsb, ms_step re text hlen pi pi.val hsb, hpb,
    mpl_step re text hlen pi pi.val hpb⟩

/-! ## The functions of the group -/

theorem matchpattern_loop_eq (re : tiny_regex.Regex) (text : Slice U8) (pi ti : Usize)
    (ml pre : I32) (mlZ preZ : Int) (ub : Nat) (hwf : WF re) (hpi : pi.val < 30)
    (hti : ti.val ≤ text.length) (hlen : text.length < 2 ^ 28) (hml : ml = toI32 mlZ)
    (hpre : pre = toI32 preZ) :
    tiny_regex.matchpattern_loop re pi text ti ml pre =
      Result.ok (res (mpLoop (ctx re text) preZ pi.val ti.val mlZ ub)) :=
  (group_spec re text hwf hlen _ pi pi.val rfl rfl hpi).1 ti ti.val ml pre mlZ preZ rfl hti hml hpre ub

/-- The entry `re_matchp` uses: from object `pi` (0 or 1) at any text position, `*matchlength`
related mod `2^32`, for every UB mask. -/
theorem matchpattern_eq (re : tiny_regex.Regex) (text : Slice U8) (pi ti : Usize) (ml : I32)
    (mlZ : Int) (ub : Nat) (hwf : WF re) (hpi : pi.val < 30) (hti : ti.val ≤ text.length)
    (hlen : text.length < 2 ^ 28) (hml : ml = toI32 mlZ) :
    tiny_regex.matchpattern re pi text ti ml =
      Result.ok (res (mpLoop (ctx re text) mlZ pi.val ti.val mlZ ub)) := by
  rw [tiny_regex.matchpattern.eq_1]
  exact matchpattern_loop_eq re text pi ti ml ml mlZ mlZ ub hwf hpi hti hlen hml hml

/-- `matchquestion` with an `UNUSED` object returns at once (any continuation index). -/
theorem matchquestion_eq_unused (re : tiny_regex.Regex) (text : Slice U8) (p : tiny_regex.RegexObj)
    (pi ti : Usize) (ml : I32) (mlZ : Int) (ub : Nat) (hu : p.kind.val = 0) (hml : ml = toI32 mlZ) :
    tiny_regex.matchquestion re p pi text ti ml =
      Result.ok (res (matchquestion (ctx re text) (tok p) pi.val ti.val mlZ ub)) := by
  rw [matchquestion_unused re p pi text ti ml hu, model_matchquestion_unused _ _ _ _ _ _ hu, hml]
  rfl

theorem matchquestion_eq (re : tiny_regex.Regex) (text : Slice U8) (p : tiny_regex.RegexObj)
    (pi ti : Usize) (ml : I32) (mlZ : Int) (ub : Nat) (hwf : WF re) (hpi : pi.val < 30)
    (hti : ti.val ≤ text.length) (hlen : text.length < 2 ^ 28) (hml : ml = toI32 mlZ) :
    tiny_regex.matchquestion re p pi text ti ml =
      Result.ok (res (matchquestion (ctx re text) (tok p) pi.val ti.val mlZ ub)) :=
  (group_spec re text hwf hlen _ pi pi.val rfl rfl hpi).2.1 p ti ti.val ml mlZ rfl hti hml ub

theorem star_back_eq (re : tiny_regex.Regex) (text : Slice U8) (pi : Usize) (t pre : Isize)
    (ml prelen : I32) (tN preN : Nat) (mlZ prelenZ : Int) (ub : Nat) (hwf : WF re)
    (hpi : pi.val < 30) (ht : t.val = tN) (hpre : pre.val = preN) (htl : tN ≤ text.length)
    (hlen : text.length < 2 ^ 28) (hml : ml = toI32 mlZ) (hprelen : prelen = toI32 prelenZ) :
    tiny_regex.star_back re pi text t pre ml prelen =
      Result.ok (res (starBack (ctx re text) pi.val prelenZ preN tN mlZ ub)) :=
  (group_spec re text hwf hlen _ pi pi.val rfl rfl hpi).2.2.1 t pre tN preN ml prelen mlZ prelenZ ht
    hpre htl hml hprelen ub

theorem matchstar_eq (re : tiny_regex.Regex) (text : Slice U8) (p : tiny_regex.RegexObj)
    (pi ti : Usize) (ml : I32) (mlZ : Int) (ub : Nat) (hwf : WF re) (hpi : pi.val < 30)
    (hti : ti.val ≤ text.length) (hlen : text.length < 2 ^ 28) (hml : ml = toI32 mlZ) :
    tiny_regex.matchstar re p pi text ti ml =
      Result.ok (res (matchstar (ctx re text) (tok p) pi.val ti.val mlZ ub)) :=
  (group_spec re text hwf hlen _ pi pi.val rfl rfl hpi).2.2.2.1 p ti ti.val ml mlZ rfl hti hml ub

theorem plus_back_eq (re : tiny_regex.Regex) (text : Slice U8) (pi t pre : Usize) (ml : I32)
    (mlZ : Int) (ub : Nat) (hwf : WF re) (hpi : pi.val < 30) (htl : t.val ≤ text.length)
    (hlen : text.length < 2 ^ 28) (hml : ml = toI32 mlZ) :
    tiny_regex.plus_back re pi text t pre ml =
      Result.ok (res (plusBack (ctx re text) pi.val pre.val t.val mlZ ub)) :=
  (group_spec re text hwf hlen _ pi pi.val rfl rfl hpi).2.2.2.2.1 t pre t.val pre.val ml mlZ rfl rfl
    htl hml ub

theorem matchplus_eq (re : tiny_regex.Regex) (text : Slice U8) (p : tiny_regex.RegexObj)
    (pi ti : Usize) (ml : I32) (mlZ : Int) (ub : Nat) (hwf : WF re) (hpi : pi.val < 30)
    (hti : ti.val ≤ text.length) (hlen : text.length < 2 ^ 28) (hml : ml = toI32 mlZ) :
    tiny_regex.matchplus re p pi text ti ml =
      Result.ok (res (matchplus (ctx re text) (tok p) pi.val ti.val mlZ ub)) :=
  (group_spec re text hwf hlen _ pi pi.val rfl rfl hpi).2.2.2.2.2 p ti ti.val ml mlZ rfl hti hml ub

/-- No panic and termination of the whole group on its domain. -/
theorem group_no_panic (re : tiny_regex.Regex) (text : Slice U8) (pi ti : Usize) (ml : I32)
    (hwf : WF re) (hpi : pi.val < 30) (hti : ti.val ≤ text.length) (hlen : text.length < 2 ^ 28) :
    (∃ r, tiny_regex.matchpattern re pi text ti ml = Result.ok r) ∧
    (∀ p, ∃ r, tiny_regex.matchquestion re p pi text ti ml = Result.ok r) ∧
    (∀ p, ∃ r, tiny_regex.matchstar re p pi text ti ml = Result.ok r) ∧
    (∀ p, ∃ r, tiny_regex.matchplus re p pi text ti ml = Result.ok r) := by
  have h := toI32_val ml
  exact ⟨⟨_, matchpattern_eq re text pi ti ml ml.val 0 hwf hpi hti hlen h.symm⟩,
    fun p => ⟨_, matchquestion_eq re text p pi ti ml ml.val 0 hwf hpi hti hlen h.symm⟩,
    fun p => ⟨_, matchstar_eq re text p pi ti ml ml.val 0 hwf hpi hti hlen h.symm⟩,
    fun p => ⟨_, matchplus_eq re text p pi ti ml ml.val 0 hwf hpi hti hlen h.symm⟩⟩

end EquivLean.Demo.XLang.TinyRegex.Rust

#print axioms EquivLean.Demo.XLang.TinyRegex.Rust.group_spec
#print axioms EquivLean.Demo.XLang.TinyRegex.Rust.matchpattern_eq
#print axioms EquivLean.Demo.XLang.TinyRegex.Rust.group_no_panic
