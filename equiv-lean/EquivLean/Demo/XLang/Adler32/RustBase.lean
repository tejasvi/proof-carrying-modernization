import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Demo.Gen.Aeneas.Adler32Rs.Funs

/-!
# zlib adler32 → safe Rust: the generated code's primitive steps and the byte loop

The Rust translation (`examples/rust/adler32_rs`, extracted by Charon + Aeneas into
`Demo/Gen/Aeneas/Adler32Rs`) works on `u64` sums.  This file has the symbolic-execution helpers,
the scalar facts the code needs (`>>> 16`, `<<< 16`, the masks), the byte sums `sums` (the C's
`DO1` repeated), and `do_bytes` against `sums`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas adler32_rs

namespace EquivLean.Demo.XLang.Adler32.Rust

/-! ## Symbolic execution helpers -/

theorem ite_prop_intro {c : Prop} {inst : Decidable c} {P Q : Prop} (h1 : c → P) (h2 : ¬c → Q) :
    @ite Prop c inst P Q := by
  cases inst with
  | isTrue h => exact h1 h
  | isFalse h => exact h2 h

theorem dite_prop_intro {c : Prop} {inst : Decidable c} {P : c → Prop} {Q : ¬c → Prop}
    (h1 : ∀ h, P h) (h2 : ∀ h, Q h) : @dite Prop c inst P Q := by
  cases inst with
  | isTrue h => exact h1 h
  | isFalse h => exact h2 h

open Lean Meta Elab Tactic in
/-- Splits the goal when it is a `Prop`-valued `if`, building the proof term directly. -/
elab "a32_split1" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t := (← instantiateMVars (← g.getType)).consumeMData
    unless (t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5) && (t.getArg! 0).isProp do
      throwError "a32_split1: the goal is not an if"
    let c := t.getArg! 1
    let inst := t.getArg! 2
    let a := t.getArg! 3
    let b := t.getArg! 4
    let tag ← g.getTag
    let (ty1, ty2, thm) ←
      if t.isAppOfArity ``ite 5 then
        pure (← mkArrow c a, ← mkArrow (mkNot c) b, ``ite_prop_intro)
      else
        pure (Expr.forallE `h c (mkApp a (.bvar 0)).headBeta .default,
          Expr.forallE `h (mkNot c) (mkApp b (.bvar 0)).headBeta .default, ``dite_prop_intro)
    let g1 ← mkFreshExprSyntheticOpaqueMVar ty1 tag
    let g2 ← mkFreshExprSyntheticOpaqueMVar ty2 tag
    g.assign (mkAppN (mkConst thm) #[c, inst, a, b, g1, g2])
    let (_, g1') ← g1.mvarId!.intro1
    let (_, g2') ← g2.mvarId!.intro1
    replaceMainGoal [g1', g2']

/-- Splits the `if`s of a symbolically executed Rust function, branch by branch. -/
macro "a32_split" : tactic => `(tactic| repeat' a32_split1)

/-- Closes a branch with a hypothesis `false = true` or `¬True`. -/
macro "a32_contra" : tactic => `(tactic| first
  | exact absurd ‹false = true› Bool.false_ne_true
  | exact absurd trivial ‹¬True›)

theorem exists_ok_of_wp {α : Type} {c : Result α} {P : α → Prop}
    (h : wp c (fun r => ∃ v, r = .ok v ∧ P v)) : ∃ v, c = Result.ok v ∧ P v := by
  rcases (wp_iff _ _).1 h with ⟨a, rfl, ha⟩ | ⟨e, rfl, he⟩
  · obtain ⟨v, hv, hp⟩ := ha
    cases hv
    exact ⟨_, rfl, hp⟩
  · simp at he

theorem eq_ok_of_wp {α : Type} {c : Result α} {v : α} (h : wp c (· = .ok v)) : c = Result.ok v := by
  rcases (wp_iff _ _).1 h with ⟨a, rfl, ha⟩ | ⟨e, rfl, he⟩
  · cases ha; rfl
  · cases he

theorem loop_cont {α β : Type} {body : α → Result (ControlFlow α β)} {x y : α}
    (h : body x = .ok (.cont y)) : loop body x = loop body y := by
  rw [loop_unfold, h]
  simp

theorem loop_done {α β : Type} {body : α → Result (ControlFlow α β)} {x : α} {b : β}
    (h : body x = .ok (.done b)) : loop body x = .ok b := by
  rw [loop_unfold, h]
  simp

/-! ## Scalar facts -/

theorem shr16_eq (x : U64) :
    x >>> (16#i32) = .ok (UScalar.ofNatCore (x.val / 65536) (by
      have := x.hBounds
      simp only [UScalarTy.U64_numBits_eq] at this ⊢
      omega)) := by
  show UScalar.shiftRight_IScalar x 16#i32 = _
  simp only [UScalar.shiftRight_IScalar, UScalar.shiftRight]
  rw [if_pos (by decide), if_pos (by decide)]
  congr 1
  rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq]
  have h16 : (16#i32 : I32).toNat = 16 := by decide
  change (x.bv >>> (16#i32 : I32).toNat).toNat = x.val / 65536
  rw [h16, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rfl

theorem shl16_eq (x : U64) (h : x.val < 2 ^ 48) :
    x <<< (16#i32) = .ok (UScalar.ofNatCore (x.val * 65536) (by
      simp only [UScalarTy.U64_numBits_eq]
      omega)) := by
  show UScalar.shiftLeft_IScalar x 16#i32 = _
  simp only [UScalar.shiftLeft_IScalar, UScalar.shiftLeft]
  rw [if_pos (by decide), if_pos (by decide)]
  congr 1
  rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq]
  have h16 : (16#i32 : I32).toNat = 16 := by decide
  change (x.bv <<< (16#i32 : I32).toNat).toNat = x.val * 65536
  rw [h16, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  change x.val * 2 ^ 16 % 2 ^ 64 = x.val * 65536
  rw [Nat.mod_eq_of_lt (by omega)]

theorem shl16_eq' (x : U64) :
    x <<< (16#i32) = .ok (UScalar.ofNatCore (x.val * 65536 % 2 ^ 64) (by
      simp only [UScalarTy.U64_numBits_eq]
      exact Nat.mod_lt _ (by decide))) := by
  show UScalar.shiftLeft_IScalar x 16#i32 = _
  simp only [UScalar.shiftLeft_IScalar, UScalar.shiftLeft]
  rw [if_pos (by decide), if_pos (by decide)]
  congr 1
  rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq]
  have h16 : (16#i32 : I32).toNat = 16 := by decide
  change (x.bv <<< (16#i32 : I32).toNat).toNat = x.val * 65536 % 2 ^ 64
  rw [h16, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rfl

theorem shl1_eq (x : U64) (h : x.val < 2 ^ 63) :
    x <<< (1#i32) = .ok (UScalar.ofNatCore (x.val * 2) (by
      simp only [UScalarTy.U64_numBits_eq]
      omega)) := by
  show UScalar.shiftLeft_IScalar x 1#i32 = _
  simp only [UScalar.shiftLeft_IScalar, UScalar.shiftLeft]
  rw [if_pos (by decide), if_pos (by decide)]
  congr 1
  rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq]
  have h1 : (1#i32 : I32).toNat = 1 := by decide
  change (x.bv <<< (1#i32 : I32).toNat).toNat = x.val * 2
  rw [h1, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  change x.val * 2 ^ 1 % 2 ^ 64 = x.val * 2
  rw [Nat.mod_eq_of_lt (by omega)]

theorem and_ffff (n : Nat) : n &&& 65535 = n % 65536 :=
  Nat.and_two_pow_sub_one_eq_mod n 16

/-! ## Symbolic execution with named results

The `wp` rules below give the result of an arithmetic step as a new variable with an equation for
its value, instead of an `UScalar.ofNatCore` term: on `u64` code the leaves full of
`ofNatCore` terms make `simp` and `rw` loop.  `a32_wp` is `aeneas_wp` with these rules;
`a32_split` also introduces the new variables. -/

theorem fresh_of_eq {uty : UScalarTy} {Q : Except Error (UScalar uty) → Prop} (n : Nat)
    (h : n < 2 ^ uty.numBits) :
    Q (.ok (UScalar.ofNatCore n h)) ↔ ∀ z : UScalar uty, z.val = n → Q (.ok z) := by
  constructor
  · intro hq z hz
    have : z = UScalar.ofNatCore n h := by
      rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq]
      exact hz
    rw [this]
    exact hq
  · intro hq
    exact hq _ (UScalar.ofNatCore_val_eq h)

theorem wp_UScalar_add_fresh {uty : UScalarTy} (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x + y) Q ↔
      if x.val + y.val ≤ UScalar.max uty then ∀ z : UScalar uty, z.val = x.val + y.val → Q (.ok z)
      else Q (.error .integerOverflow) := by
  rw [wp_UScalar_add_val]
  by_cases h : x.val + y.val ≤ UScalar.max uty
  · rw [dif_pos h, if_pos h]
    exact fresh_of_eq _ _
  · rw [dif_neg h, if_neg h]

theorem wp_UScalar_sub_fresh {uty : UScalarTy} (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x - y) Q ↔
      if y.val ≤ x.val then ∀ z : UScalar uty, z.val = x.val - y.val → Q (.ok z)
      else Q (.error .integerOverflow) := by
  rw [wp_UScalar_sub_val]
  by_cases h : y.val ≤ x.val
  · rw [if_pos h, if_pos h]
    exact fresh_of_eq _ _
  · rw [if_neg h, if_neg h]

theorem wp_UScalar_mul_fresh {uty : UScalarTy} (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x * y) Q ↔
      if x.val * y.val ≤ UScalar.max uty then ∀ z : UScalar uty, z.val = x.val * y.val → Q (.ok z)
      else Q (.error .integerOverflow) := by
  rw [wp_UScalar_mul_val]
  by_cases h : x.val * y.val ≤ UScalar.max uty
  · rw [dif_pos h, if_pos h]
    exact fresh_of_eq _ _
  · rw [dif_neg h, if_neg h]

theorem wp_UScalar_rem_fresh {uty : UScalarTy} (x y : UScalar uty) (Q : Except Error (UScalar uty) → Prop) :
    wp (x % y) Q ↔
      if y.val ≠ 0 then ∀ z : UScalar uty, z.val = x.val % y.val → Q (.ok z)
      else Q (.error .divisionByZero) := by
  rw [wp_UScalar_rem_val]
  by_cases h : y.val ≠ 0
  · rw [if_pos h, if_pos h]
    exact fresh_of_eq _ _
  · rw [if_neg h, if_neg h]

theorem wp_shr16_fresh (x : U64) (Q : Except Error U64 → Prop) :
    wp (x >>> (16#i32)) Q ↔ ∀ z : U64, z.val = x.val / 65536 → Q (.ok z) := by
  rw [shr16_eq, wp_ok]
  exact fresh_of_eq _ _

/-- `x << 16` on `u64` values (kept opaque, so that `omega` sees an atom: this toolchain's `omega`
recurses without bound on some products of a sum with a constant). -/
@[irreducible] def shl16N (n : Nat) : Nat := n * 65536 % 2 ^ 64

theorem shl16N_eq (n : Nat) : shl16N n = n * 65536 % 2 ^ 64 := by
  unfold shl16N
  rfl

theorem wp_shl16_fresh (x : U64) (Q : Except Error U64 → Prop) :
    wp (x <<< (16#i32)) Q ↔ ∀ z : U64, z.val = shl16N x.val → Q (.ok z) := by
  rw [shl16_eq', wp_ok, shl16N_eq]
  exact fresh_of_eq _ _

theorem base_val : (BASE : U64).val = 65521 := by
  simp [BASE]

theorem nmax_val : (NMAX : Usize).val = 5552 := by
  simp [NMAX]

theorem u64_65535_val : (65535#u64 : U64).val = 65535 := rfl
theorem u64_1_val : (1#u64 : U64).val = 1 := rfl
theorem usize_0_val : (0#usize : Usize).val = 0 := rfl
theorem usize_1_val : (1#usize : Usize).val = 1 := rfl
theorem usize_16_val : (16#usize : Usize).val = 16 := rfl

open Lean Parser Tactic in
/-- `aeneas_wp` with the arithmetic results as new variables (see above). -/
syntax (name := a32Wp) "a32_wp" (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| a32_wp $[[$args,*]]?) => do
    let args : EquivLean.Aeneas.SimpArgs := (args.map (·.getElems)).getD #[]
    `(tactic| simp only [wp_bind, wp_bind_tc, wp_ok, wp_fail, wp_div, wp_pure, wp_lift, wp_ite,
        wp_dite, wp_massert, wp_ofOption, wp_Slice_index_usize, Slice.from_val,
        wp_UScalar_add_fresh, wp_UScalar_sub_fresh, wp_UScalar_mul_fresh, wp_UScalar_rem_fresh,
        wp_shr16_fresh, wp_shl16_fresh, wp_IScalar_rem, u64_65535_val, u64_1_val, usize_0_val,
        usize_1_val, usize_16_val, UScalar.val_and, and_ffff,
        UScalar.cast_val_mod_pow_greater_numBits_eq, IScalar.val_mod_pow_greater_numBits,
        UScalar.hcast_val_of_numBits_lt,
        UScalar.lt_equiv, UScalar.le_equiv, IScalar.lt_equiv, IScalar.le_equiv,
        UScalar.eq_equiv, IScalar.eq_equiv, bne_iff_ne, ne_eq, decide_eq_true_eq,
        Slice.len_val, Slice.length, IScalar.ofInt_val_eq,
        UScalarTy.U8_numBits_eq, UScalarTy.U32_numBits_eq, UScalarTy.U64_numBits_eq,
        IScalarTy.I32_numBits_eq, IScalarTy.I64_numBits_eq, Nat.reduceLeDiff, Nat.reduceLT,
        UScalar.max_USize_eq, UScalar.max_UScalarTy_U8_eq, UScalar.max_UScalarTy_U32_eq,
        UScalar.max_UScalarTy_U64_eq, U8.max_eq, U32.max_eq, U64.max_eq,
        IScalar.min_IScalarTy_I32_eq, IScalar.max_IScalarTy_I32_eq,
        IScalar.min_IScalarTy_I64_eq, IScalar.max_IScalarTy_I64_eq, I32.min_eq, I32.max_eq,
        I64.min_eq, I64.max_eq, Prod.mk.injEq, Aeneas.Std.uncurry_apply_pair, _root_.dite_true,
        _root_.dite_false, _root_.ite_true, _root_.ite_false, and_self, and_true, true_and,
        $args,*])

/-- Splits the `if`s and introduces the named results, branch by branch. -/
macro "a32_split'" : tactic => `(tactic| repeat' (first | a32_split1 | intro))

/-! ## The byte sums -/

/-- The bytes of a slice, as numbers. -/
def bytes (s : Slice U8) : List Nat := s.val.map (·.val)

theorem length_bytes (s : Slice U8) : (bytes s).length = s.val.length := by
  simp [bytes]

theorem bytes_lt (s : Slice U8) : ∀ b ∈ bytes s, b < 256 := by
  intro b hb
  simp only [bytes, List.mem_map] at hb
  obtain ⟨u, -, rfl⟩ := hb
  have := u.hBounds
  simpa using this

/-- `DO1` over the bytes `bs`, from the sums `a` and `s`. -/
def sums : List Nat → Nat → Nat → Nat × Nat
  | [], a, s => (a, s)
  | b :: bs, a, s => sums bs (a + b) (s + (a + b))

theorem sums_append (l1 l2 : List Nat) (a s : Nat) :
    sums (l1 ++ l2) a s = sums l2 (sums l1 a s).1 (sums l1 a s).2 := by
  induction l1 generalizing a s with
  | nil => rfl
  | cons b bs IH => exact IH _ _

theorem sums_bound (l : List Nat) (hl : ∀ b ∈ l, b < 256) (a s : Nat) :
    (sums l a s).1 ≤ a + 255 * l.length ∧ (sums l a s).2 ≤ s + l.length * (a + 255 * l.length) := by
  induction l generalizing a s with
  | nil => simp [sums]
  | cons b bs IH =>
    have hb := hl b (by simp)
    obtain ⟨h1, h2⟩ := IH (fun x hx => hl x (by simp [hx])) (a + b) (s + (a + b))
    simp only [sums, List.length_cons]
    constructor
    · omega
    · have : bs.length * (a + b + 255 * bs.length) ≤ bs.length * (a + 255 * (bs.length + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      have : (bs.length + 1) * (a + 255 * (bs.length + 1)) =
          bs.length * (a + 255 * (bs.length + 1)) + (a + 255 * (bs.length + 1)) := by ring
      omega

/-! ## `do_bytes` -/

theorem do_bytes_body_done (buf : Slice U8) (i n : Usize) (a s : U64) {k : Usize}
    (hk : n.val ≤ k.val) :
    do_bytes_loop.body buf i n a s k = .ok (.done (a, s)) := by
  apply eq_ok_of_wp
  unfold do_bytes_loop.body
  aeneas_wp
  a32_split
  all_goals try a32_contra
  all_goals try (exfalso; omega)
  all_goals simp

theorem do_bytes_body_step (buf : Slice U8) (i n : Usize) (a s : U64) {k : Usize}
    (hk : k.val < n.val) (hik : i.val + k.val < buf.val.length) (ha : a.val + 255 ≤ 2097152)
    (hs : s.val + 2097152 ≤ 17179869184) :
    ∃ c, do_bytes_loop.body buf i n a s k = .ok c ∧
      ∃ (a1 s1 : U64) (k1 : Usize), c = .cont (a1, s1, k1) ∧
        a1.val = a.val + (buf.val[i.val + k.val]'hik).val ∧ s1.val = s.val + a1.val ∧
        k1.val = k.val + 1 := by
  have hmax := buf.property
  have hb : (buf.val[i.val + k.val]'hik).val < 256 := by
    have := (buf.val[i.val + k.val]'hik).hBounds
    simpa using this
  apply exists_ok_of_wp
  unfold do_bytes_loop.body
  aeneas_wp
  a32_split
  all_goals try a32_contra
  all_goals try (exfalso; omega)
  all_goals simp

theorem do_bytes_loop_eq (buf : Slice U8) (i n : Usize) (hin : i.val + n.val ≤ buf.val.length) :
    ∀ (m : Nat) (k : Usize) (a s : U64), n.val - k.val = m → k.val ≤ n.val →
      a.val + 255 * m ≤ 2097152 → s.val + m * 2097152 ≤ 17179869184 →
      ∃ r, do_bytes_loop buf i n a s k = .ok r ∧
        (r.1.val, r.2.val) = sums (((bytes buf).drop (i.val + k.val)).take m) a.val s.val := by
  intro m
  induction m with
  | zero =>
    intro k a s hm hk _ _
    refine ⟨(a, s), ?_, by simp [sums]⟩
    unfold do_bytes_loop
    exact loop_done (do_bytes_body_done buf i n a s (by omega))
  | succ m IH =>
    intro k a s hm hk ha hs
    -- `c * (m + 1)` in a hypothesis sends this toolchain's `omega` into a deep recursion
    rw [Nat.mul_add_one, ← Nat.add_assoc] at ha
    rw [Nat.add_one_mul, ← Nat.add_assoc] at hs
    have hik : i.val + k.val < buf.val.length := by omega
    have h1 : k.val < n.val := by omega
    have h2 : a.val + 255 ≤ 2097152 := by omega
    have h3 : s.val + 2097152 ≤ 17179869184 := by omega
    obtain ⟨c, hc, a1, s1, k1, rfl, ha1, hs1, hk1⟩ := do_bytes_body_step buf i n a s h1 hik h2 h3
    have hb : (buf.val[i.val + k.val]'hik).val < 256 := by
      have := (buf.val[i.val + k.val]'hik).hBounds
      simpa using this
    obtain ⟨r, hr, hrv⟩ := IH k1 a1 s1 (by omega) (by omega) (by omega) (by
      have : a1.val ≤ 2097152 := by omega
      omega)
    refine ⟨r, ?_, ?_⟩
    · unfold do_bytes_loop at hr ⊢
      rw [loop_cont hc]
      exact hr
    · rw [hrv]
      have hl : i.val + k.val < (bytes buf).length := by rw [length_bytes]; exact hik
      rw [List.drop_eq_getElem_cons hl, List.take_succ_cons]
      simp only [sums, bytes, List.getElem_map, ha1, hs1, hk1, Nat.add_assoc]

/-- `do_bytes buf i n a s` with `i + n` within the slice, at most `NMAX` bytes and sums below
`2^17`: the byte sums of `buf[i .. i + n)`. -/
theorem do_bytes_eq (buf : Slice U8) (i n : Usize) (a s : U64) (hin : i.val + n.val ≤ buf.val.length)
    (hn : n.val ≤ 5552) (ha : a.val < 131072) (hs : s.val < 131072) :
    ∃ r, do_bytes buf i n a s = .ok r ∧
      (r.1.val, r.2.val) = sums (((bytes buf).drop i.val).take n.val) a.val s.val := by
  have h0 : (0#usize : Usize).val = 0 := rfl
  obtain ⟨r, hr, hrv⟩ :=
    do_bytes_loop_eq buf i n hin n.val 0#usize a s (by rw [h0, Nat.sub_zero]) (by rw [h0]; omega)
      (by omega) (by omega)
  refine ⟨r, hr, ?_⟩
  rw [h0, Nat.add_zero] at hrv
  exact hrv

end EquivLean.Demo.XLang.Adler32.Rust
