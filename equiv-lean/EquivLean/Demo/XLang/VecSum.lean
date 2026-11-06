import EquivLean.Bridge.Cir.Tactic
import EquivLean.Bridge.Cir.Corr
import EquivLean.Bridge.Cir.Loops
import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Core.Facts
import EquivLean.Demo.Gen.Cir.XVec
import EquivLean.Demo.Gen.Aeneas.XVec.Funs

/-!
# C++ → Rust collections migration: a `std::vector` loop against a `Vec` loop, in lockstep

`examples/xlang/vec.cpp` (clang -fclangir with libc++ headers, translated by cir2lean into
`Gen.XVec`) against `examples/rust/xvec` (Charon + Aeneas → `EquivLean.Demo.Gen.Aeneas.XVec`):

```cpp
int vsum(const std::vector<int> &v) {            pub fn vsum(v: &Vec<i32>) -> i32 {
  int s = 0;                                         let mut s: i32 = 0;
  for (std::size_t i = 0; i < v.size(); ++i)         let mut i: usize = 0;
    s += v[i];                                       while i < v.len() { s += v[i]; i += 1; }
  return s;                                          s
}                                                }
```

Representation: the C++ vector is a block of the caller's memory holding `Val.vec g (xs.map .int)`
(cirlean's library model of `std::vector<int>`; `v.size()` and `v[i]` run against it), and
`xs = v.val.map (·.val)` couples it with the Rust `Vec<i32>`.

* `vsum_rust_sim_cpp`: the migration direction (C++ is the source).  The C++ function runs in a
  hypothesis (`cir_hrun`) up to its loop; the two loops are paired into one product loop by the
  core rule `wp_loop_rel` (target: Aeneas' `loop`, `EquivLean.Aeneas.loop_shape`; source:
  CIR's `cir.for`, `Cir.loopShape_for`; termination from the C++ loop, `Cir.terminates_for`:
  no variant).  The coupling invariant `VsI` says that the C++ slots `s` and `i` hold Rust's
  `s` and `i` (plus the C++ frame).  In one iteration, the C++ body runs in a hypothesis
  (`cir_hrun`: `v.size()`, `v[i]`, the signed `+=` whose overflow is undefined behaviour and
  closes its path, the `size_t` increment) and the Rust body in the goal (`aeneas_wp`: the
  checked `+=` panics exactly where C++ overflowed, which the C++ path facts refute).
* `vsum_cpp_safe`: off `Bad` (a prefix sum leaves `int`, or `2^63` elements or more) the C++
  function has no undefined behaviour (cirlean's `cir_loop`).
* `vsum_equiv`: hence equivalence off `Bad`, by `Equiv.of_sim_of_safe`.

Standard axioms only.
-/

open EquivLean CIR Aeneas Aeneas.Std

namespace EquivLean.Demo.XLang.VecSum

/-- Rust's outcome against C++'s: the same `int`; Rust does not panic. -/
def RetI32 : Except Error I32 → Exit × Mem → Prop
  | .ok r, (.ret (some (.int v)), _) => r.val = v
  | _, _ => False

open Lean Elab Tactic Meta in
/-- Name the state at the head of the CIR loop in the hypothesis `h` (the source):
`cirH_s0 : σ₀ = <state>`. -/
elab "cir_gen_entry_hyp " h:ident : tactic => do
  let g ← getMainGoal
  g.withContext do
    let d ← getLocalDeclFromUserName h.getId
    let t ← instantiateMVars d.type
    let some x := t.find? (fun e => e.isAppOfArity ``CIR.evalFor 6 ||
      e.isAppOfArity ``CIR.evalWhile 5 || e.isAppOfArity ``CIR.evalDo 4)
      | throwError "cir_gen_entry_hyp: no CIR loop in {h}"
    let σS ← Term.exprToSyntax x.appArg!
    let σ₀ := mkIdent (Name.mkSimple "σ₀")
    let hgen := mkIdent (Name.mkSimple "cirH_gen")
    let hs0 := mkIdent (Name.mkSimple "cirH_s0")
    evalTactic (← `(tactic| generalize $hgen:ident : $σS = $σ₀:ident at $h:ident))
    evalTactic (← `(tactic| have $hs0:ident := ($hgen:ident).symm))
    evalTactic (← `(tactic| clear $hgen:ident))

/-- Coupling at the loop heads: Rust state `(s, i)`, C++ state `σ`. -/
def VsI (σ₀ : State) (n : Nat) (xs : List Int) (p : I32 × Usize) (σ : State) : Prop :=
  LoopFrame σ₀ [n + 2, n + 3] σ ∧
  IntSlot σ (n + 2) (.int true 32) ∧ IntSlot σ (n + 3) (.int false 64) ∧
  σ.intAt (n + 2) = p.1.val ∧ σ.intAt (n + 3) = (p.2.val : Int) ∧ p.2.val ≤ xs.length

/-- Both loops leave: C++ completes normally, Rust returns the sum. -/
def VsExit (σ₀ : State) (n : Nat) (xs : List Int) (o₁ : Except Error I32) (o₂ : Step × State) : Prop :=
  o₂.1 = .next ∧ ∃ s i, o₁ = .ok s ∧ VsI σ₀ n xs (s, i) o₂.2

set_option maxHeartbeats 4000000 in
/-- **C++ → Rust, lockstep.**  The Rust rewrite simulates the C++ function: wherever C++ has no
undefined behaviour, Rust does not panic and returns the same `int`. -/
theorem vsum_rust_sim_cpp (v : alloc.vec.Vec I32) (xs : List Int) (hxs : xs = v.val.map (fun x => x.val))
    (m : Mem) (bv g : Nat) (k : BlockKind) (ty : Ty)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next) :
    Sim RetI32 (xvec.vsum v) (evalCall Gen.XVec.ctx Gen.XVec.fn_vsum.sym [.ptr (.loc bv [])] m) := by
  -- the elements' `int` range (they come from `i32`s): the C++ loads of `v[i]` pass their type
  -- check (otherwise cirlean reads them through the unsigned counterpart)
  have hxsb : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647 := by
    intro x hx
    rw [hxs, List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    have := y.hBounds
    simp only [IScalarTy.I32_numBits_eq] at this
    omega
  rw [Cir.sim_res_iff_holds]
  intro os hs
  cir_hrun hs
  cir_gen_entry_hyp hs
  simp only [xvec.vsum, xvec.vsum_loop]
  refine wp_loop_rel (EquivLean.Aeneas.loop_shape _) (Cir.loopShape_for _ _ _ _ _)
    (Cir.terminates_for _ _ _ _ _) (VsI σ₀ m.next xs) (R := VsExit σ₀ m.next xs)
    (Cir.wp_of_holds hs) ?init ?step ?post
  case init =>
    subst cirH_s0
    refine ⟨⟨rfl, rfl, Nat.le_refl _, fun _ _ _ => rfl⟩, ?_⟩
    simp [IntSlot, State.intAt, upd, fitsTy]
    constructor <;> decide
  case step =>
    rintro ⟨s, i⟩ σ ⟨⟨cirH_env, cirH_names, cirH_next, cirH_frame⟩, ⟨cirH_slot0, cirH_range0⟩,
      ⟨cirH_slot1, cirH_range1⟩, hsv, hiv, hle⟩
    simp only at hsv hiv hle
    rw [Cir.sim_res_iff_holds]
    intro os' hs'
    have cirH_nx : m.next + 4 ≤ σ.mem.next := by rw [cirH_s0] at cirH_next; simpa using cirH_next
    have cirH_vslot : σ.mem.blocks (m.next + 1) = some ⟨.stack, true,
        (Ty.record "std::__1::vector<int, std::__1::allocator<int>>").ptr, .ptr (.loc bv [])⟩ := by
      have := cirH_frame (m.next + 1) (by simp) (by rw [cirH_s0]; simp)
      rw [this, cirH_s0]; simp [upd]
    have cirH_vec : σ.mem.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩ := by
      have := cirH_frame bv (by simp; omega) (by rw [cirH_s0]; simp; omega)
      rw [this, cirH_s0]; simp only [upd]
      split_ifs <;> first | (exfalso; omega) | exact hv
    generalize cirH_val0 : σ.intAt (m.next + 2) = cs at *
    generalize cirH_val1 : σ.intAt (m.next + 3) = ci at *
    -- the slots' ranges as bounds: their loads pass the type check
    have hcs : -2147483648 ≤ cs ∧ cs ≤ 2147483647 := by
      simpa only [fitsTy, inRange_eq_true_iff, intMin_s32, intMax_s32] using cirH_range0
    have hci : 0 ≤ ci ∧ ci ≤ 18446744073709551615 := by
      simpa only [fitsTy, inRange_eq_true_iff, intMin_u, intMax_u64] using cirH_range1
    cir_hrun hs'
    all_goals (subst hs')
    all_goals
      subst hiv hsv
      subst hxs
      simp only [Int.toNat_natCast, List.getElem_map, List.length_map] at *
      have hlen := v.property
      have hmaplen : ((List.map (fun x : I32 => x.val) v.val).length : Int) = (v.val.length : Int) := by
        simp
      simp only [xvec.vsum_loop.body]
      aeneas_wp at ⊢
      split_ifs <;> (try (exfalso; omega))
    case' neg =>
      simp only [stepRel_def, EquivLean.Aeneas.loopCls_done, Cir.loopCls, id]
      refine ⟨rfl, s, i, rfl, ?_⟩
      unfold VsI LoopFrame IntSlot
      refine ⟨⟨?env, ?names, ?next, ?frame⟩, ⟨?s0, ?r0⟩, ⟨?s1, ?r1⟩, ?v0, ?v1, ?le⟩
      case env => rw [cirH_s0]
      case names => rw [cirH_s0]
      case next => exact cirH_next
      case frame => exact cirH_frame
      case s0 => exact cirH_slot0.trans (by rw [← cirH_val0]; rfl)
      case r0 =>
        change fitsTy (Ty.int true 32) (Val.int (σ.intAt (m.next + 2))) = true
        rw [cirH_val0]; exact cirH_range0
      case s1 => exact cirH_slot1.trans (by rw [← cirH_val1]; rfl)
      case r1 =>
        change fitsTy (Ty.int false 64) (Val.int (σ.intAt (m.next + 3))) = true
        rw [cirH_val1]; exact cirH_range1
      case v0 => exact cirH_val0
      case v1 => exact cirH_val1
      case le => simpa using hle
    case' pos =>
      simp only [stepRel_def, EquivLean.Aeneas.loopCls_cont, Cir.loopCls, id]
      have hirr : ∀ b, (σ.mem.next ≤ b ∧ b < σ.mem.next) = False := fun b => by
        apply propext; constructor
        · intro h; omega
        · intro h; exact h.elim
      unfold VsI LoopFrame IntSlot
      simp only [Mem.endScope_blocks, Mem.endScope_next, killRange, hirr, ite_false]
      refine ⟨⟨?env, ?names, ?next, ?frame⟩, ⟨?s0, ?r0⟩, ⟨?s1, ?r1⟩, ?v0, ?v1, ?le⟩
      case env => rw [cirH_s0]
      case names => rw [cirH_s0]
      case next => exact cirH_next
      case frame =>
        intro b hb hlt
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
        simp only [upd, ite_eq_right hb.1, ite_eq_right hb.2]
        exact cirH_frame b (by simp [hb.1, hb.2]) hlt
      all_goals simp only [State.intAt_mk, Mem.endScope_blocks, killRange, hirr, upd,
        Nat.add_left_cancel_iff, Nat.reduceEqDiff, ↓reduceIte,
        IScalar.ofInt_val_eq, UScalar.ofNatCore_val_eq, List.length_map, fitsTy, Nat.cast_add,
        Nat.cast_one]
      case r0 => assumption
      case r1 =>
        rw [Cir.inRange_false_iff]; unfold URange
        have h64 : (i.val : Int) + 1 ≤ 18446744073709551615 := by omega
        constructor
        · show (0 : Int) ≤ (i.val : Int) + 1
          omega
        · show (i.val : Int) + 1 < 2 ^ 64
          omega
      case le => omega
  case post =>
    rintro o₁ ⟨st, σ⟩ ⟨hst, s, i, rfl, hI⟩ hK
    simp only at hst hI
    subst hst
    obtain ⟨⟨cirH_env, cirH_names, cirH_next, cirH_frame⟩, ⟨cirH_slot0, cirH_range0⟩,
      ⟨cirH_slot1, cirH_range1⟩, hsv, hiv, hle⟩ := hI
    simp only at hsv hiv
    have cirH_nx : m.next + 4 ≤ σ.mem.next := by rw [cirH_s0] at cirH_next; simpa using cirH_next
    have cirH_ret : σ.mem.blocks m.next = some ⟨.stack, true, .int true 32, .undef⟩ := by
      have := cirH_frame m.next (by simp) (by rw [cirH_s0]; simp)
      rw [this, cirH_s0]; simp [upd]
    generalize cirH_val0 : σ.intAt (m.next + 2) = cs at *
    generalize cirH_val1 : σ.intAt (m.next + 3) = ci at *
    have hcs : -2147483648 ≤ cs ∧ cs ≤ 2147483647 := by
      simpa only [fitsTy, inRange_eq_true_iff, intMin_s32, intMax_s32] using cirH_range0
    simp only at hK
    cir_hrun hK
    subst hK
    simp [RetI32, hsv]

set_option maxHeartbeats 4000000 in
/-- Off its undefined-behaviour inputs, the C++ function is safe (no overflow, terminates). -/
theorem vsum_cpp_safe (xs : List Int) (m : Mem) (bv g : Nat) (k : BlockKind) (ty : Ty)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g (xs.map .int)⟩) (hbv : bv < m.next)
    (hlen : xs.length < 2 ^ 63) (hxs : ∀ x ∈ xs, -2147483648 ≤ x ∧ x ≤ 2147483647)
    (hsum : Lib.PrefixSumsIn (-2147483648) 2147483647 xs) :
    Safe (evalCall Gen.XVec.ctx Gen.XVec.fn_vsum.sym [.ptr (.loc bv [])] m) := by
  rw [Cir.safe_res_iff_holds]
  have := hsum.succNat
  show Calls Gen.XVec.ctx Gen.XVec.fn_vsum.sym [.ptr (.loc bv [])] m (fun _ _ => True)
  cir_start
  cir_vcg
  cir_loop (fun s i => i ≤ xs.length ∧ s = (xs.take i).sum) (fun s i => xs.length - i)
  all_goals cir_vcg

/-- The inputs on which the C++ function has undefined behaviour or is out of the modelled
range: a prefix sum overflows `int`, or the vector has `2^63` elements or more. -/
def Bad (v : alloc.vec.Vec I32) : Prop :=
  ¬ Lib.PrefixSumsIn (-2147483648) 2147483647 (v.val.map (fun x => x.val)) ∨
    2 ^ 63 ≤ v.val.length

/-- **C++ → Rust, equivalence off `Bad`.**  Both are safe and return the same `int`. -/
theorem vsum_equiv (v : alloc.vec.Vec I32) (m : Mem) (bv g : Nat) (k : BlockKind) (ty : Ty)
    (hv : m.blocks bv = some ⟨k, true, ty, .vec g ((v.val.map (fun x => x.val)).map .int)⟩)
    (hbv : bv < m.next) (hgood : ¬ Bad v) :
    Equiv RetI32 (xvec.vsum v)
      (evalCall Gen.XVec.ctx Gen.XVec.fn_vsum.sym [.ptr (.loc bv [])] m) := by
  simp only [Bad, not_or, not_not, not_le] at hgood
  have hxs : ∀ x ∈ v.val.map (fun y : I32 => y.val), -2147483648 ≤ x ∧ x ≤ 2147483647 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    have := y.hBounds
    simp only [IScalarTy.I32_numBits_eq] at this
    omega
  exact Equiv.of_sim_of_safe (vsum_rust_sim_cpp v _ rfl m bv g k ty hv hbv)
    (fun _ => vsum_cpp_safe _ m bv g k ty hv hbv (by simpa using hgood.2) hxs hgood.1)

end EquivLean.Demo.XLang.VecSum

#print axioms EquivLean.Demo.XLang.VecSum.vsum_equiv
