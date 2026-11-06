import EquivLean.Bridge.Cir.Behaves
import EquivLean.Bridge.Cir.Loops
import EquivLean.Bridge.Cir.Corr
import EquivLean.Bridge.Aeneas.Behaves
import EquivLean.Bridge.Aeneas.Loops
import EquivLean.Demo.Gen.Cir.XBits
import EquivLean.Demo.Gen.Aeneas.Bits.Funs
import EquivLean.Tactic.Basic
import EquivLean.Tactic.LoopAuto
import EquivLean.Bridge.Registry

/-!
# C → Rust migration, loops in lockstep: `reverse_bits`

`examples/xlang/bits.c` (C, compiled by clang -fclangir and translated by cir2lean into
`EquivLean.Demo.Gen.Cir.XBits`) against `examples/rust/bits` (Rust, translated by Charon and
Aeneas into `EquivLean.Demo.Gen.Aeneas.Bits`):

```c
uint32_t reverse_bits(uint32_t x) {            pub fn reverse_bits(x: u32) -> u32 {
  uint32_t v = x;                                  let mut v = x;
  uint32_t r = 0;                                  let mut r: u32 = 0;
  for (uint32_t i = 0; i < 32; i++) {              let mut i: u32 = 0;
    r = (r << 1) | (v & 1u);                       while i < 32 {
    v >>= 1;                                           r = (r << 1u32) | (v & 1);
  }                                                    v >>= 1u32; i += 1;
  return r;                                        }
}                                                  r }
```

`reverse_bits_c_sim_rust`: for every input word and every initial C memory, the C function
simulates the Rust one: it has no undefined behaviour, returns, and returns the word Rust
returns (`RetU32`; Rust's checked operations cannot panic here, which the theorem shows too:
a Rust panic would be an outcome no C outcome matches).

The two loops are paired into one product loop by `equiv_loop_auto` (the lockstep rule
`EquivLean.wp_loop_rel`, with CIR's `cir.for` shape and Aeneas' `loop` shape and termination
found in the loop registry).  The coupling invariant `RevI` says only that the C
variables `v`, `r`, `i` hold the Rust variables' words (plus the C frame); nobody specifies
what bit reversal is.  No variant is needed: the Rust loop terminates whenever it is safe
(`EquivLean.Aeneas.loop_terminates`).  One iteration is executed by cirlean's `cir_vcg` on
the C side and by the Aeneas bridge's exact `wp` lemmas on the Rust side; the leaf that
relates the two new values of `r` is the bit-vector identity
`(r * 2) ||| (v &&& 1) = (r <<< 1) ||| (v &&& 1)` after `EquivLean.Cir.bitwise_false_eq`
and friends turned the C integers into bit vectors.  Standard axioms only.
-/

open EquivLean CIR Aeneas Aeneas.Std

namespace EquivLean.Demo.XLang.ReverseBits

def RetU32 : Exit × Mem → Except Error U32 → Prop
  | (.ret (some (.int r)), _), .ok v => r = v.val
  | _, _ => False

open Lean Elab Tactic Meta in
/-- Name the state at the head of the CIR loop in the goal: `cirH_s0 : σ₀ = <state>`. -/
elab "cir_gen_entry" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some x := t.find? (fun e => e.isAppOfArity ``CIR.evalFor 6 ||
      e.isAppOfArity ``CIR.evalWhile 5 || e.isAppOfArity ``CIR.evalDo 4)
      | throwError "cir_gen_entry: no CIR loop in the goal"
    let σS ← Term.exprToSyntax x.appArg!
    let σ₀ := mkIdent (Name.mkSimple "σ₀")
    let hgen := mkIdent (Name.mkSimple "cirH_gen")
    let hs0 := mkIdent (Name.mkSimple "cirH_s0")
    evalTactic (← `(tactic| generalize $hgen:ident : $σS = $σ₀:ident))
    evalTactic (← `(tactic| have $hs0:ident := ($hgen:ident).symm))
    evalTactic (← `(tactic| clear $hgen:ident))

@[simp] theorem ofInt_val_u32 (x : U32) : BitVec.ofInt 32 ((x.val : Nat) : Int) = x.bv :=
  Cir.ofInt_toNat x.bv

/-- Coupling at the loop head: the C frame is that of loop entry, the slots `v`, `r`, `i` hold
the Rust state's words. -/
def RevI (σ₀ : State) (n : Nat) (σ : State) (s : U32 × U32 × U32) : Prop :=
  LoopFrame σ₀ [n + 2, n + 3, n + 4] σ ∧
  IntSlot σ (n + 2) (.int false 32) ∧ IntSlot σ (n + 3) (.int false 32) ∧
  IntSlot σ (n + 4) (.int false 32) ∧
  σ.intAt (n + 2) = s.1.val ∧ σ.intAt (n + 3) = s.2.1.val ∧ σ.intAt (n + 4) = s.2.2.val

/-- When both loops leave: C completes normally, Rust returns the word in `r`. -/
def RevExit (σ₀ : State) (n : Nat) (o₁ : Step × State) (o₂ : Except Error U32) : Prop :=
  o₁.1 = .next ∧ ∃ v r i, o₂ = .ok r ∧ RevI σ₀ n o₁.2 (v, r, i)

set_option maxHeartbeats 40000000 in
theorem reverse_bits_c_sim_rust (x : U32) (m : Mem) :
    Sim RetU32 (evalCall Gen.XBits.ctx Gen.XBits.fn_reverse_bits.sym [.int x.val] m)
      (bits.reverse_bits x) := by
  equiv_intro P hs
  simp only [bits.reverse_bits, bits.reverse_bits_loop] at hs
  rw [Cir.wp_res]
  show Calls Gen.XBits.ctx Gen.XBits.fn_reverse_bits.sym [.int x.val] m
    (fun e m' => ∃ os, P os ∧ RetU32 (e, m') os)
  cir_start
  cir_vcg
  cir_gen_entry
  rw [← Cir.wp_res]
  -- pair the C `for` (goal) with the Rust `loop` (hypothesis `hs`): shapes and the Rust
  -- loop's termination come from the loop registry (`EquivLean.Bridge.Registry`)
  equiv_loop_auto (RevI σ₀ m.next) with (RevExit σ₀ m.next)
  case init =>
    subst cirH_s0
    refine ⟨⟨rfl, rfl, Nat.le_refl _, fun _ _ _ => rfl⟩, ?_⟩
    simp [IntSlot, State.intAt, upd, fitsTy]
    constructor
    · rw [Cir.inRange_false_iff]; unfold URange; omega
    · decide
  case step =>
    rintro σ ⟨v, r, i⟩ hI0
    have hI := hI0
    obtain ⟨⟨cirH_env, cirH_names, cirH_next, cirH_frame⟩, cirH_slot0, cirH_slot1,
      cirH_slot2, hv, hr, hi⟩ := hI
    equiv_intro Q hq
    simp only [bits.reverse_bits_loop.body] at hq
    obtain ⟨cirH_slot0, cirH_range0⟩ := cirH_slot0
    obtain ⟨cirH_slot1, cirH_range1⟩ := cirH_slot1
    obtain ⟨cirH_slot2, cirH_range2⟩ := cirH_slot2
    simp only at hv hr hi
    -- the slots' values stay integer variables in the symbolic state (no `Nat` casts there:
    -- the kernel would evaluate range checks on them); `hv`/`hr`/`hi` relate them to Rust
    generalize cirH_val0 : σ.intAt (m.next + 2) = cv at *
    generalize cirH_val1 : σ.intAt (m.next + 3) = cr at *
    generalize cirH_val2 : σ.intAt (m.next + 4) = ci at *
    by_cases hlt : i.val < 32
    · have hlt' : i < 32#u32 := by scalar_tac
      simp [hlt'] at hq
      rw [dif_pos (by scalar_tac)] at hq
      rw [Cir.wp_res]
      cir_vcg
      case h =>
        refine ⟨_, hq, ?_⟩
        simp only [StepRel, Cir.loopCls, EquivLean.Aeneas.loopCls_cont, id]
        rw [cirH_s0] at cirH_next cirH_frame
        unfold RevI LoopFrame IntSlot
        refine ⟨⟨?env, ?names, ?next, ?frame⟩, ⟨?s0, ?r0⟩, ⟨?s1, ?r1⟩, ⟨?s2, ?r2⟩, ?v, ?r, ?i⟩
        case r =>
          simp only [State.intAt, upd, Nat.add_left_cancel_iff, Nat.reduceEqDiff, ite_true, ite_false]
          subst hv hr
          rw [Cir.bitwise_false_eq, Cir.wrap_false_eq, Cir.bitwise_false_eq, Cir.ofInt_toNat,
            Cir.ofInt_toNat]
          show _ = (((_ : U32).bv.toNat : Nat) : Int)
          simp only [UScalar.bv_or, UScalar.bv_and, ofInt_val_u32, Int.toNat_one, pow_one,
            BitVec.ofInt_mul]
          have h1 : (1#u32).bv = 1#32 := rfl
          have h2 : BitVec.ofInt 32 2 = BitVec.twoPow 32 1 := by rfl
          have h3 : BitVec.ofInt 32 1 = 1#32 := by rfl
          rw [h1]
          congr 2
          rw [h2, h3, ← BitVec.shiftLeft_eq_mul_twoPow]
        case env => simpa using cirH_env
        case names => simpa using cirH_names
        case next => simpa using cirH_next
        case frame =>
          intro b hb hlt
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, not_or] at hb
          obtain ⟨h2, h3, h4, -⟩ := hb
          simpa [upd, h2, h3, h4] using cirH_frame b (by simp [h2, h3, h4]) (by simpa using hlt)
        case s0 => simp [State.intAt, upd]
        case s1 => simp [State.intAt, upd]
        case s2 => simp [State.intAt, upd]
        case r0 =>
          simp only [fitsTy, State.intAt, upd, Nat.add_left_cancel_iff, Nat.reduceEqDiff, ite_true,
            ite_false]
          simp only [fitsTy] at cirH_range0
          rw [Cir.inRange_false_iff] at cirH_range0 ⊢
          unfold URange at cirH_range0 ⊢
          omega
        case r1 =>
          simp only [fitsTy, State.intAt, upd, Nat.add_left_cancel_iff, Nat.reduceEqDiff, ite_true,
            ite_false]
          exact Cir.inRange_bitwise_false _ _ _ _
        case r2 =>
          simp only [fitsTy, State.intAt, upd, Nat.add_left_cancel_iff, Nat.reduceEqDiff, ite_true,
            ite_false]
          rw [Cir.inRange_false_iff]; unfold URange; omega
        case v =>
          simp only [State.intAt, upd, Nat.add_left_cancel_iff, Nat.reduceEqDiff, ite_true, ite_false]
          subst hv
          show _ = ((((v.bv >>> 1).toNat : Nat)) : Int)
          simp only [Int.toNat_one, pow_one, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
          have : (v.bv.toNat : Int) = ((v.val : Nat) : Int) := rfl
          omega
        case i =>
          simp only [State.intAt, upd, Nat.add_left_cancel_iff, Nat.reduceEqDiff, ite_true, ite_false]
          subst hi
          show _ = (((i.val + 1 : Nat)) : Int)
          push_cast; rfl
      -- a store's failed range check, if `cir_vcg` left it open (newer cirlean closes it itself)
      all_goals (rename_i hbad; exact Cir.bitwise_false_32_bad _ _ _ hbad)
    · have hlt' : ¬ (i < 32#u32) := by scalar_tac
      simp [hlt'] at hq
      rw [Cir.wp_res]
      cir_vcg
      all_goals first
        | (exfalso; simp only at hi; subst hi; omega)
        | (refine ⟨_, hq, ?_⟩
           simp only [StepRel, Cir.loopCls, EquivLean.Aeneas.loopCls_done, id]
           refine ⟨rfl, v, r, i, rfl, ?_⟩
           rw [cirH_s0] at cirH_next cirH_frame
           unfold RevI LoopFrame IntSlot
           have hint : ∀ m e n b, (State.mk (Mem.mk σ.mem.blocks m) e n).intAt b = σ.intAt b :=
             fun _ _ _ _ => rfl
           dsimp only
           simp only [hint, cirH_val0, cirH_val1, cirH_val2]
           refine ⟨⟨?env, ?names, ?next, ?frame⟩, ⟨?s0, ?r0⟩, ⟨?s1, ?r1⟩, ⟨?s2, ?r2⟩, ?v, ?r, ?i⟩
           case next => simpa using cirH_next
           case frame =>
             intro b hb hlt
             simpa using cirH_frame b hb (by simpa using hlt)
           all_goals first
             | rfl
             | trivial
             | rw [cirH_s0]
             | assumption)
  case post =>
    rintro ⟨st, σ⟩ o₂ ⟨hst, v, r, i, rfl, hI⟩ hP
    simp only at hst hI
    subst hst
    obtain ⟨⟨cirH_env, cirH_names, cirH_next, cirH_frame⟩, ⟨cirH_slot0, cirH_range0⟩,
      ⟨cirH_slot1, cirH_range1⟩, ⟨cirH_slot2, cirH_range2⟩, hv, hr, hi⟩ := hI
    simp only at hv hr hi
    generalize cirH_val0 : σ.intAt (m.next + 2) = cv at *
    generalize cirH_val1 : σ.intAt (m.next + 3) = cr at *
    generalize cirH_val2 : σ.intAt (m.next + 4) = ci at *
    have cirH_nx : m.next + 5 ≤ σ.mem.next := by rw [cirH_s0] at cirH_next; simpa using cirH_next
    have cirH_ret : σ.mem.blocks m.next =
        some ⟨.stack, true, .int false 32, .undef⟩ := by
      have := cirH_frame m.next (by simp) (by rw [cirH_s0]; simp)
      rw [this, cirH_s0]; simp [upd]
    simp only
    cir_vcg
    all_goals (try simp [cirH_slot1] at *)
    all_goals subst_vars
    all_goals first
      | (exact ⟨.ok r, hP, by simp only [RetU32]; omega⟩)
      | (simp_all [fitsTy]; done)
      | (simp only [fitsTy] at cirH_range1 ⊢; exact cirH_range1)
      | (exfalso; simp_all [fitsTy])

end EquivLean.Demo.XLang.ReverseBits
