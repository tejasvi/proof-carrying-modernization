import EquivLean.Bridge.Aeneas.Loops
import EquivLean.Bridge.Aeneas.Corr

/-!
# Aeneas (Rust) bridge: tactics

* `aeneas_wp [extra] (at loc)?`: symbolic execution.  Turns `wp c Q` for a translated Rust
  computation into nested `if`s over the branch conditions of `c` (bind, `if`, `lift`,
  slice indexing, checked scalar arithmetic with both outcomes), and normalises the conditions
  to arithmetic on `.val` (comparisons, `!=`, `Slice.len`, the bounds `U32.max`, …).
* `aeneas_leaves [extra]`: closes the leaves: `split_ifs` over all conditions of both programs,
  `simp_all` (with `StepRel`, `loopCls`, scalar equality as value equality), then `scalar_tac`
  (Aeneas' linear arithmetic with scalar bounds).  Goals it cannot close are left to the user.
* `equiv_aeneas [defs] using I (with [extra])?`: the whole pipeline for `Equiv R t s` (or
  `Sim R t s`) between two Aeneas functions whose bodies are one loop each: unfold `defs`
  (the functions and their `_loop` definitions), pair the loops in lockstep with the coupling
  invariant `I` (`equiv_loop`/`sim_loop'`, no variant needed), run the source body and then
  the target body symbolically (`equiv_of_wp`), close the leaves.
* `equiv_aeneas_straight [defs] (with [extra])?`: the same for loop-free functions.
* `wp_aeneas_loop [defs] using Inv, V (with [extra])?`: one-sided loop proofs (`wp_loop`).
* `equiv_aeneas_pure [defs] (with [extra])?`: a Rust function against a pure Lean value.

`using I` takes the coupling invariant on the two loop states (tuples of the loop variables
in the order of the generated `loop` call).
-/

open Aeneas Aeneas.Std

namespace EquivLean.Aeneas

/-- `equiv_of_wp` with the target computation abstracted, so that the source can be executed
symbolically (and its branches split) before the target is unfolded. -/
theorem equiv_of_wp_staged {α β : Type _} {t : Result α} {s : Result β}
    {R : Except Error α → Except Error β → Prop}
    (h : ∀ T, T = t → wp s (fun os => wp T (fun ot => R ot os))) : Equiv R t s :=
  equiv_of_wp (h t rfl)

theorem sim_of_wp_staged {α β : Type _} {t : Result α} {s : Result β}
    {R : Except Error α → Except Error β → Prop}
    (h : ∀ T, T = t → wp s (fun os => wp T (fun ot => R ot os))) : Sim R t s :=
  sim_of_wp (h t rfl)

open Lean Parser Tactic

/-- Simp arguments of `simp`/`simp only`. -/
abbrev SimpArgs := TSyntaxArray [``simpStar, ``simpErase, ``simpLemma]

/-- An identifier as a `simp` argument. -/
def identSimpArg (d : Ident) : TSyntax [``simpStar, ``simpErase, ``simpLemma] :=
  ⟨Syntax.node .none ``simpLemma #[mkNullNode, mkNullNode, d.raw]⟩

/-- `simp_all` takes no `*` argument. -/
def toSimpAllArgs (xs : SimpArgs) : TSyntaxArray [``simpErase, ``simpLemma] :=
  xs.map (⟨·.raw⟩)

/-- Symbolic execution of Aeneas computations under `wp` (see the module doc). -/
syntax (name := aeneasWp) "aeneas_wp" (" [" simpArg,* "]")? (location)? : tactic

macro_rules
  | `(tactic| aeneas_wp $[[$args,*]]? $[$loc]?) => do
    let args : SimpArgs := (args.map (·.getElems)).getD #[]
    `(tactic| simp only [wp_bind, wp_bind_tc, wp_ok, wp_fail, wp_div, wp_pure, wp_lift, wp_ite,
        wp_dite, wp_massert, wp_ofOption, wp_Slice_index_usize, wp_Vec_index_usize, wp_Vec_push,
        alloc.vec.Vec.index_slice_index, alloc.vec.Vec.len_val, alloc.vec.Vec.length,
        alloc.vec.Vec.from_val, Slice.from_val,
        wp_UScalar_add_val, wp_UScalar_sub_val, wp_UScalar_mul_val, wp_UScalar_div_val,
        wp_UScalar_rem_val, wp_IScalar_add_val, wp_IScalar_sub_val, wp_IScalar_mul_val,
        wp_IScalar_neg_val, wp_IScalar_div_val, wp_IScalar_rem, wp_UScalar_shl, wp_UScalar_shr,
        UScalar.cast_val_mod_pow_greater_numBits_eq, IScalar.val_mod_pow_greater_numBits,
        UScalar.hcast_val_of_numBits_lt,
        UScalar.lt_equiv, UScalar.le_equiv, IScalar.lt_equiv, IScalar.le_equiv,
        UScalar.eq_equiv, IScalar.eq_equiv, bne_iff_ne, ne_eq, decide_eq_true_eq,
        Slice.len_val, Slice.length, UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq,
        UScalarTy.U8_numBits_eq, UScalarTy.U16_numBits_eq, UScalarTy.U32_numBits_eq,
        UScalarTy.U64_numBits_eq, UScalarTy.U128_numBits_eq, IScalarTy.I8_numBits_eq,
        IScalarTy.I16_numBits_eq, IScalarTy.I32_numBits_eq, IScalarTy.I64_numBits_eq,
        IScalarTy.I128_numBits_eq, Nat.reduceLeDiff, Nat.reduceLT,
        UScalar.max_USize_eq, UScalar.max_UScalarTy_U8_eq, UScalar.max_UScalarTy_U16_eq,
        UScalar.max_UScalarTy_U32_eq, UScalar.max_UScalarTy_U64_eq,
        UScalar.max_UScalarTy_U128_eq, U8.max_eq, U16.max_eq, U32.max_eq, U64.max_eq,
        U128.max_eq, IScalar.min_IScalarTy_I8_eq, IScalar.max_IScalarTy_I8_eq,
        IScalar.min_IScalarTy_I16_eq, IScalar.max_IScalarTy_I16_eq,
        IScalar.min_IScalarTy_I32_eq, IScalar.max_IScalarTy_I32_eq,
        IScalar.min_IScalarTy_I64_eq, IScalar.max_IScalarTy_I64_eq,
        IScalar.min_IScalarTy_I128_eq, IScalar.max_IScalarTy_I128_eq, I8.min_eq, I8.max_eq,
        I16.min_eq, I16.max_eq, I32.min_eq, I32.max_eq, I64.min_eq, I64.max_eq, I128.min_eq,
        I128.max_eq, Prod.mk.injEq, Aeneas.Std.uncurry_apply_pair, _root_.dite_true,
        _root_.dite_false, _root_.ite_true, _root_.ite_false, and_self, and_true, true_and,
        $args,*] $[$loc]?)

/-- Close the leaves of a symbolically executed goal (see the module doc). -/
syntax (name := aeneasLeaves) "aeneas_leaves" (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| aeneas_leaves $[[$args,*]]?) => do
    let args : SimpArgs := (args.map (·.getElems)).getD #[]
    let args' := toSimpAllArgs args
    `(tactic| ((try split_ifs) <;>
        (try simp_all [stepRel_def, loopCls, UScalar.eq_equiv, IScalar.eq_equiv, outcomeRel,
          alloc.vec.Vec.eq_iff, Slice.eq_iff, $args',*]) <;>
        (try scalar_tac) <;> (try scalar_tac +nonLin) <;> (try ring1)))

/-- Lockstep equivalence (or simulation) of two Aeneas functions with one loop each. -/
syntax (name := equivAeneas) "equiv_aeneas" (" [" ident,* "]")? " using " term
  (" with" " [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| equiv_aeneas $[[$defs,*]]? using $I $[with [$args,*]]?) => do
    let defs : Array Ident := (defs.map (·.getElems)).getD #[]
    let args : SimpArgs := (args.map (·.getElems)).getD #[]
    let defArgs : SimpArgs := defs.map identSimpArg
    `(tactic| (
      simp only [$defArgs,*]
      first
        | refine equiv_loop $I ?_ _ _ ?_
        | refine sim_loop' $I ?_ _ _ ?_
      · try simp only [Prod.forall]
        intros
        try simp only [Prod.mk.injEq] at *
        try casesm* _ ∧ _
        try subst_vars
        -- run the source body first (its branches become hypotheses), then the target body
        first | apply equiv_of_wp_staged | apply sim_of_wp_staged
        intro T hT
        try (aeneas_wp [$defArgs,*, $args,*] at ⊢)
        try split_ifs
        all_goals (subst hT)
        all_goals (try (aeneas_wp [$defArgs,*, $args,*] at *))
        all_goals (aeneas_leaves [$args,*])
      · aeneas_wp [$args,*]
        try simp_all
        try scalar_tac))

/-- Equivalence (or simulation) of two loop-free Aeneas functions. -/
syntax (name := equivAeneasStraight) "equiv_aeneas_straight" (" [" ident,* "]")?
  (" with" " [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| equiv_aeneas_straight $[[$defs,*]]? $[with [$args,*]]?) => do
    let defs : Array Ident := (defs.map (·.getElems)).getD #[]
    let args : SimpArgs := (args.map (·.getElems)).getD #[]
    let defArgs : SimpArgs := defs.map identSimpArg
    `(tactic| (
      first | apply equiv_of_wp | apply sim_of_wp
      aeneas_wp [$defArgs,*, $args,*] at *
      aeneas_leaves [$args,*]))

/-- One-sided loop proof: `wp` of an Aeneas function whose body is one loop, by the loop rule
`wp_loop` with invariant `Inv` and variant `V` on the loop state. -/
syntax (name := wpAeneasLoop) "wp_aeneas_loop" (" [" ident,* "]")? " using " term ", " term
  (" with" " [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| wp_aeneas_loop $[[$defs,*]]? using $inv, $var $[with [$args,*]]?) => do
    let defs : Array Ident := (defs.map (·.getElems)).getD #[]
    let args : SimpArgs := (args.map (·.getElems)).getD #[]
    let defArgs : SimpArgs := defs.map identSimpArg
    `(tactic| (
      simp only [$defArgs,*]
      refine wp_loop (loop_shape _) $inv $var ?_ _ ?_
      · try simp only [Prod.forall]
        intros
        aeneas_wp [$defArgs,*, $args,*] at *
        aeneas_leaves [$args,*]
      · aeneas_wp [$args,*]
        try simp_all
        try scalar_tac))

/-- A Rust function against a pure Lean value (`pureVal`): `Equiv`/`Sim` become a `wp`
(`equiv_pureVal_iff`, `sim_pureVal_iff`), which is executed symbolically. -/
syntax (name := equivAeneasPure) "equiv_aeneas_pure" (" [" ident,* "]")?
  (" with" " [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| equiv_aeneas_pure $[[$defs,*]]? $[with [$args,*]]?) => do
    let defs : Array Ident := (defs.map (·.getElems)).getD #[]
    let args : SimpArgs := (args.map (·.getElems)).getD #[]
    let defArgs : SimpArgs := defs.map identSimpArg
    `(tactic| (
      first | rw [equiv_pureVal_iff] | rw [sim_pureVal_iff]
      aeneas_wp [$defArgs,*, $args,*] at *
      aeneas_leaves [$args,*]))

end EquivLean.Aeneas
