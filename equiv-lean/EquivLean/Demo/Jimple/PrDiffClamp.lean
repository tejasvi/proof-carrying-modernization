import EquivLean.Demo.Gen.Jimple.PrClamp
import EquivLean.Bridge.Jimple.Rel

/-!
# Java PR diff (loop-free): `Clamp.clamp` before and after, through the relational product

Old (`examples/java/prclamp_old/Clamp.java`): explicit comparisons; new
(`examples/java/prclamp_new/Clamp.java`): `Math.max(lo, Math.min(x, hi))`.  Both compiled by
`javac --release 17` and Soot 4.7.1 (`EquivLean/Demo/Gen/Jimple/PrClamp.lean`).  They agree when
`lo ≤ hi` (for `lo > hi ≤ x` the old code returns `hi`, the new one `lo`): the coupling `J0`
carries `lo ≤ hi`.  `clamp_equiv`: the two versions are equivalent (`Equiv (· = ·)`) on every
input with `lo ≤ hi`; `clamp_sim` (new ⊑ old) and `clamp_sim_rev` (old ⊑ new) are its two
directions, each `sim_of_prodVC` of a product verification condition `ProdVC`
(`Bridge/Jimple/Rel.lean`) for the single lockstep pair `(0, 0, J0)`.

* new ⊑ old (`clamp_vc`): the source's half (`old_phase`: existential execution of the old code
  with `jbodyEWP`, ending with the value `newVal` related by `RelO (· = ·)`) is proved first; then
  the target's terms that mention the source program (`tgtPost …`, `tgtAssert …`) are
  generalized away and `jvc` executes the new code (Math.min / Math.max library models).
* old ⊑ new (`clamp_vc_rev`): the same layout with the new code as the existentially executed
  source.  Its source half (`new_phase`) is proved statement by statement (`newStep0` …
  `newStep5`: one step of `bodyEWP` at a symbolic fuel, `jvc` on that statement only) and the
  steps are composed with `bodyEWP` locally irreducible (`new_run`).  Running `jvc` over the
  whole source body instead leaves the kernel a definitional step between
  `ewpR P (.ret …) K` and `ewpR P (step P b 4 …) K'` (the `Math.max` statement), which it tries
  by evaluating `step` first and then fails with deep recursion; at a symbolic fuel no such step
  between two statements arises.  Elaborating the composition with `bodyEWP` reducible makes
  the elaborator evaluate the program (`whnf` of the expected type).
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Gen

namespace EquivLean.Demo.PrDiffClamp
abbrev bOld := ClampOld.Clamp.«clamp(int,int,int)»
abbrev bNew := ClampNew.Clamp.«clamp(int,int,int)»

def J0 (fr₁ : Frame) (σ₁ : State) (fr₂ : Frame) (σ₂ : State) : Prop :=
  ∃ x lo hi : I32, σ₁ = σ₂ ∧ lo.toInt ≤ hi.toInt ∧
    fr₁ = Frame.init true [.int x, .int lo, .int hi] ∧ fr₂ = Frame.init true [.int x, .int lo, .int hi]

def pairs : List (Nat × Nat × Coupling) := [(0, 0, J0)]

/-- What the new code returns (the paths of `Math.max(lo, Math.min(x, hi))`). -/
def newVal (x lo hi : I32) : I32 :=
  if x.toInt ≤ hi.toInt then (if x.toInt ≤ lo.toInt then lo else x)
  else (if hi.toInt ≤ lo.toInt then lo else hi)

set_option maxHeartbeats 0 in
/-- The source half: the old code ends with the value `newVal`, when `lo ≤ hi`. -/
theorem old_phase (x lo hi : I32) (σ : State) (hle : lo.toInt ≤ hi.toInt) :
    tgtPost ClampOld.prog bOld (· = ·) 6 0 (Frame.init true [.int x, .int lo, .int hi]) σ
      (.normal (some (.int (newVal x lo hi))) σ) := by
  simp only [newVal]
  jvc [tgtPost, RelO, jbodyEWP, bodyEWPStep, ewpR_ret]

set_option maxHeartbeats 0 in
/-- The product verification condition: new code (target) against old code (source). -/
theorem clamp_vc : ProdVC ClampNew.prog bNew ClampOld.prog bOld pairs (· = ·) 0 20 6 := by
  intro p hp
  have hp' : p = (0, 0, J0) := by simpa [pairs] using hp
  subst hp'
  intro fr₁ σ₁ fr₂ σ₂ hJ
  obtain ⟨x, lo, hi, h1, hle, h3, h4⟩ := hJ
  subst h1 h3 h4
  have h2 := old_phase x lo hi σ₁ hle
  simp only [tgtCuts, pairs, List.map_cons, List.map_nil]
  generalize tgtPost ClampOld.prog bOld (· = ·) 6 0 (Frame.init true [.int x, .int lo, .int hi]) σ₁ = Q at h2 ⊢
  generalize tgtAssert ClampOld.prog bOld [(0, 0, J0)] 6 0 (Frame.init true [.int x, .int lo, .int hi]) σ₁ = A
  simp only [newVal] at h2
  jvc

/-- **Java PR diff, new ⊑ old**: on every input with `lo ≤ hi`, every terminating run of the new
`clamp` is matched by a run of the old one with the same outcome (value and final state), and the
new code cannot go wrong where the old one cannot. -/
theorem clamp_sim (x lo hi : I32) (σ : State) (hle : lo.toInt ≤ hi.toInt) :
    Sim (· = ·)
      (Call.mk ClampNew.prog (mref ClampNew.prog "Clamp" "clamp") [.int x, .int lo, .int hi] σ)
      (Call.mk ClampOld.prog (mref ClampOld.prog "Clamp" "clamp") [.int x, .int lo, .int hi] σ) :=
  sim_of_prodVC (b₁ := bNew) (b₂ := bOld) rfl rfl clamp_vc (J₀ := J0) (by simp [pairs])
    ⟨x, lo, hi, rfl, hle, rfl, rfl⟩

/-! ## The other direction: old ⊑ new (the new code is the existentially executed source) -/

/-- What the old code returns. -/
def oldVal (x lo hi : I32) : I32 :=
  if x.toInt < lo.toInt then lo else if hi.toInt < x.toInt then hi else x

/-- The values of the library models `Math.min(x, hi)` and `Math.max(lo, m)` on `int`. -/
abbrev minVal (x hi : I32) : I32 := if x.toInt ≤ hi.toInt then x else hi
abbrev maxVal (lo m : I32) : I32 := if lo.toInt ≥ m.toInt then lo else m

/-- The new code's frame before each of its statements 0 … 5 (statements 0-2 copy the
parameters, 3 calls `Math.min`, 4 calls `Math.max`, 5 returns). -/
abbrev nfr0 (x lo hi : I32) : Frame := Frame.init true [.int x, .int lo, .int hi]
abbrev nfr1 (x lo hi : I32) : Frame := (nfr0 x lo hi).setLocal 0 (.int x)
abbrev nfr2 (x lo hi : I32) : Frame := (nfr1 x lo hi).setLocal 1 (.int lo)
abbrev nfr3 (x lo hi : I32) : Frame := (nfr2 x lo hi).setLocal 2 (.int hi)
abbrev nfr4 (x lo hi : I32) : Frame := (nfr3 x lo hi).setLocal 0 (.int (minVal x hi))
abbrev nfr5 (x lo hi : I32) : Frame := (nfr4 x lo hi).setLocal 0 (.int (maxVal lo (minVal x hi)))

section
variable (x lo hi : I32) (σ : State) (Post : Outcome → Prop) (n : Nat)

/-! One existential step of the new code per lemma, at a symbolic fuel `n`. -/

set_option maxHeartbeats 0 in
theorem newStep0 (h : bodyEWP ClampNew.prog bNew [] Post n 1 (nfr1 x lo hi) σ) :
    bodyEWP ClampNew.prog bNew [] Post (n + 1) 0 (nfr0 x lo hi) σ := by
  rw [bodyEWP_succ]; simp only [bodyEWPStep]
  jvc [ewpR_ret]
  exact h

set_option maxHeartbeats 0 in
theorem newStep1 (h : bodyEWP ClampNew.prog bNew [] Post n 2 (nfr2 x lo hi) σ) :
    bodyEWP ClampNew.prog bNew [] Post (n + 1) 1 (nfr1 x lo hi) σ := by
  rw [bodyEWP_succ]; simp only [bodyEWPStep]
  jvc [ewpR_ret]

set_option maxHeartbeats 0 in
theorem newStep2 (h : bodyEWP ClampNew.prog bNew [] Post n 3 (nfr3 x lo hi) σ) :
    bodyEWP ClampNew.prog bNew [] Post (n + 1) 2 (nfr2 x lo hi) σ := by
  rw [bodyEWP_succ]; simp only [bodyEWPStep]
  jvc [ewpR_ret]

set_option maxHeartbeats 0 in
/-- `Math.min`. -/
theorem newStep3 (h : bodyEWP ClampNew.prog bNew [] Post n 4 (nfr4 x lo hi) σ) :
    bodyEWP ClampNew.prog bNew [] Post (n + 1) 3 (nfr3 x lo hi) σ := by
  rw [bodyEWP_succ]; simp only [bodyEWPStep]
  jvc [ewpR_ret]

set_option maxHeartbeats 0 in
/-- `Math.max`. -/
theorem newStep4 (h : bodyEWP ClampNew.prog bNew [] Post n 5 (nfr5 x lo hi) σ) :
    bodyEWP ClampNew.prog bNew [] Post (n + 1) 4 (nfr4 x lo hi) σ := by
  rw [bodyEWP_succ]; simp only [bodyEWPStep]
  jvc [ewpR_ret]

set_option maxHeartbeats 0 in
/-- `return`. -/
theorem newStep5 (h : Post (.normal (some (.int (maxVal lo (minVal x hi)))) σ)) :
    bodyEWP ClampNew.prog bNew [] Post (n + 1) 5 (nfr5 x lo hi) σ := by
  rw [bodyEWP_succ]; simp only [bodyEWPStep]
  jvc [ewpR_ret]
end

/-- For `lo ≤ hi` the old code's value is `Math.max(lo, Math.min(x, hi))`. -/
theorem oldVal_eq (x lo hi : I32) (hle : lo.toInt ≤ hi.toInt) :
    oldVal x lo hi = maxVal lo (minVal x hi) := by
  unfold oldVal maxVal minVal
  by_cases h1 : x.toInt < lo.toInt
  · simp only [h1, (show x.toInt ≤ hi.toInt by omega), (show lo.toInt ≥ x.toInt by omega),
      ↓reduceIte]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : hi.toInt < x.toInt
    · simp only [h2, (show ¬ x.toInt ≤ hi.toInt by omega), ↓reduceIte]
      by_cases h3 : lo.toInt ≥ hi.toInt
      · simp only [h3, ↓reduceIte]; exact BitVec.eq_of_toInt_eq (by omega)
      · simp only [h3, ↓reduceIte]
    · simp only [h2, (show x.toInt ≤ hi.toInt by omega), ↓reduceIte]
      by_cases h3 : lo.toInt ≥ x.toInt
      · simp only [h3, ↓reduceIte]; exact BitVec.eq_of_toInt_eq (by omega)
      · simp only [h3, ↓reduceIte]

section
-- the elaborator would otherwise evaluate the program while checking the composition
attribute [local irreducible] bodyEWP

/-- A run of the new code: the six steps composed (the fuel written as the successors the
step lemmas produce). -/
theorem new_run (x lo hi : I32) (σ : State) (Post : Outcome → Prop)
    (h : Post (.normal (some (.int (maxVal lo (minVal x hi)))) σ)) :
    bodyEWP ClampNew.prog bNew [] Post (0 + 1 + 1 + 1 + 1 + 1 + 1) 0 (nfr0 x lo hi) σ :=
  newStep0 x lo hi σ Post (0 + 1 + 1 + 1 + 1 + 1) (newStep1 x lo hi σ Post (0 + 1 + 1 + 1 + 1)
    (newStep2 x lo hi σ Post (0 + 1 + 1 + 1) (newStep3 x lo hi σ Post (0 + 1 + 1)
    (newStep4 x lo hi σ Post (0 + 1) (newStep5 x lo hi σ Post 0 h)))))

/-- The source half of old ⊑ new: the new code ends with the old code's value, when `lo ≤ hi`. -/
theorem new_phase (x lo hi : I32) (σ : State) (hle : lo.toInt ≤ hi.toInt) :
    tgtPost ClampNew.prog bNew (· = ·) 6 0 (Frame.init true [.int x, .int lo, .int hi]) σ
      (.normal (some (.int (oldVal x lo hi))) σ) := by
  simp only [tgtPost]
  rw [show (6 : Nat) = 0 + 1 + 1 + 1 + 1 + 1 + 1 from rfl]
  exact new_run x lo hi σ _ (by simp only [RelO, oldVal_eq x lo hi hle])
end

set_option maxHeartbeats 0 in
/-- The product verification condition: old code (target) against new code (source). -/
theorem clamp_vc_rev : ProdVC ClampOld.prog bOld ClampNew.prog bNew pairs (· = ·) 0 20 6 := by
  intro p hp
  have hp' : p = (0, 0, J0) := by simpa [pairs] using hp
  subst hp'
  intro fr₁ σ₁ fr₂ σ₂ hJ
  obtain ⟨x, lo, hi, h1, hle, h3, h4⟩ := hJ
  subst h1 h3 h4
  have h2 := new_phase x lo hi σ₁ hle
  simp only [tgtCuts, pairs, List.map_cons, List.map_nil]
  generalize tgtPost ClampNew.prog bNew (· = ·) 6 0 (Frame.init true [.int x, .int lo, .int hi]) σ₁ = Q at h2 ⊢
  generalize tgtAssert ClampNew.prog bNew [(0, 0, J0)] 6 0 (Frame.init true [.int x, .int lo, .int hi]) σ₁ = A
  simp only [oldVal] at h2
  jvc

/-- **Java PR diff, old ⊑ new**: on every input with `lo ≤ hi`, every terminating run of the old
`clamp` is matched by a run of the new one with the same outcome. -/
theorem clamp_sim_rev (x lo hi : I32) (σ : State) (hle : lo.toInt ≤ hi.toInt) :
    Sim (· = ·)
      (Call.mk ClampOld.prog (mref ClampOld.prog "Clamp" "clamp") [.int x, .int lo, .int hi] σ)
      (Call.mk ClampNew.prog (mref ClampNew.prog "Clamp" "clamp") [.int x, .int lo, .int hi] σ) :=
  sim_of_prodVC (b₁ := bOld) (b₂ := bNew) rfl rfl clamp_vc_rev (J₀ := J0) (by simp [pairs])
    ⟨x, lo, hi, rfl, hle, rfl, rfl⟩

/-- **The pull request preserves behaviour** on every input with `lo ≤ hi`: the two versions are
equivalent (simulation both ways, equal outcomes: value and final state). -/
theorem clamp_equiv (x lo hi : I32) (σ : State) (hle : lo.toInt ≤ hi.toInt) :
    Equiv (· = ·)
      (Call.mk ClampNew.prog (mref ClampNew.prog "Clamp" "clamp") [.int x, .int lo, .int hi] σ)
      (Call.mk ClampOld.prog (mref ClampOld.prog "Clamp" "clamp") [.int x, .int lo, .int hi] σ) :=
  ⟨clamp_sim x lo hi σ hle, (clamp_sim_rev x lo hi σ hle).mono fun _ _ e => e.symm⟩

end EquivLean.Demo.PrDiffClamp

#print axioms EquivLean.Demo.PrDiffClamp.clamp_vc
#print axioms EquivLean.Demo.PrDiffClamp.clamp_sim
#print axioms EquivLean.Demo.PrDiffClamp.old_phase
#print axioms EquivLean.Demo.PrDiffClamp.new_phase
#print axioms EquivLean.Demo.PrDiffClamp.clamp_vc_rev
#print axioms EquivLean.Demo.PrDiffClamp.clamp_sim_rev
#print axioms EquivLean.Demo.PrDiffClamp.clamp_equiv
