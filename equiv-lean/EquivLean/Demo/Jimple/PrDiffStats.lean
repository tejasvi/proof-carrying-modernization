import EquivLean.Demo.Gen.Jimple.PrDiff
import EquivLean.Bridge.Jimple.Rel

/-!
# Java PR diff with a loop: `Stats.total`, index loop → enhanced `for`

Old (`examples/java/prdiff_old/Stats.java`): `for (int i = 0; i < a.length; i++) s += a[i];`
New (`examples/java/prdiff_new/Stats.java`): `for (int x : a) s += x;`
Both compiled by `javac --release 17` and converted by Soot 4.7.1
(`EquivLean/Demo/Gen/Jimple/PrDiff.lean`).  In the Jimple, the new loop keeps `a.length` in a
local (statement 2) and tests it at its head (statement 4); the old loop re-reads `lengthof` at
its head (statement 3).

`stats_equiv`: the two methods are equivalent (`Equiv (· = ·)`: simulation both ways, same
return value and final state, `int` overflow included) on every non-null `int[]` argument;
`stats_sim` (new ⊑ old) and `stats_sim_rev` (old ⊑ new) are its two directions.  It is proved with the
relational product of `Bridge/Jimple/Rel.lean` (`sim_of_prodVC`), lockstep pairs
`(0, 0, J0)` (entry) and `(4, 3, JL)` (loop heads; coupling: same array, same sum, same index,
the new code's length local = the array's length); the reverse direction uses the mirrored pairs
`(0, 0)`, `(3, 4)` (`pairsR`, `JLr`).  The source is executed existentially and its run is built
in lockstep with the target's run, so neither direction assumes that the source loop terminates.

Proof layout (each direction): the source's three segments are proved first (`src_entry`,
`src_iter`, `src_exit`, resp. `srcR_*`: `jvc` with `jbodyEWP`); `stats_vc` (`stats_vc_rev`) then
generalizes the target's references to the source (`tgtAssert …`, `tgtPost …`), runs `jvc` on
the target, and closes the cut-point leaves with the source lemmas.
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Gen

namespace EquivLean.Demo.PrDiffStats
abbrev bOld := StatsOld.Stats.«total(int[])»
abbrev bNew := StatsNew.Stats.«total(int[])»

def IntArr (σ : State) (a : Addr) (xs : List Value) : Prop :=
  σ.heap a = some (.array (.prim .int) xs) ∧ xs.length < 2147483647 ∧ ∀ v ∈ xs, ∃ x : I32, v = .int x

def J0 (fr₁ : Frame) (σ₁ : State) (fr₂ : Frame) (σ₂ : State) : Prop :=
  ∃ a xs, σ₁ = σ₂ ∧ IntArr σ₁ a xs ∧ fr₁ = Frame.init true [.ref a] ∧ fr₂ = Frame.init true [.ref a]

def JL (fr₁ : Frame) (σ₁ : State) (fr₂ : Frame) (σ₂ : State) : Prop :=
  ∃ a xs s i, σ₁ = σ₂ ∧ IntArr σ₁ a xs ∧
    fr₁.get 0 = some (.ref a) ∧ fr₁.get 1 = some (.int (BitVec.ofNat 32 xs.length)) ∧
    fr₁.get 3 = some (.int s) ∧ fr₁.get 4 = some (.int i) ∧
    fr₂.get 0 = some (.ref a) ∧ fr₂.get 2 = some (.int s) ∧ fr₂.get 3 = some (.int i) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ xs.length

def pairs : List (Nat × Nat × Coupling) := [(0, 0, J0), (4, 3, JL)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
/-- Source, loop exit: from the loop head with `i ≥ length`, the old code returns `s`. -/
theorem src_exit (fr : Frame) (σ : State) (a : Addr) (xs : List Value) (s i : I32)
    (h0 : fr.get 0 = some (.ref a)) (h2 : fr.get 2 = some (.int s)) (h3 : fr.get 3 = some (.int i))
    (ha : σ.heap a = some (.array (.prim .int) xs)) (hl : xs.length < 2147483647)
    (hge : xs.length ≤ i.toInt) :
    tgtPost StatsOld.prog bOld (· = ·) 8 3 fr σ (.normal (some (.int s)) σ) := by
  simp only [tgtPost]
  jvc [RelO, jbodyEWP, bodyEWPStep, ewpR_ret]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
/-- Source, one iteration: from the loop head with `i < length`, the old code reaches its loop
head again, coupled with the target's next loop head (sum `s + x`, index `i + 1`). -/
theorem src_iter (fr : Frame) (σ : State) (a : Addr) (xs : List Value) (s i x : I32)
    (h0 : fr.get 0 = some (.ref a)) (h2 : fr.get 2 = some (.int s)) (h3 : fr.get 3 = some (.int i))
    (ha : σ.heap a = some (.array (.prim .int) xs)) (hl : xs.length < 2147483647)
    (hxs : ∀ v ∈ xs, ∃ x : I32, v = .int x)
    (hi0 : 0 ≤ i.toInt) (hlt : i.toInt < xs.length)
    (hx : ∀ h : (i.toInt).toNat < xs.length, xs[(i.toInt).toNat] = .int x)
    (fr₁ : Frame) (g0 : fr₁.get 0 = some (.ref a))
    (g1 : fr₁.get 1 = some (.int (BitVec.ofNat 32 xs.length)))
    (g3 : fr₁.get 3 = some (.int (s + x))) (g4 : fr₁.get 4 = some (.int (i + 1))) :
    tgtAssert StatsOld.prog bOld pairs 8 3 fr σ 4 fr₁ σ := by
  simp only [tgtAssert]
  jvc [jbodyEWP, bodyEWPStep, ewpR_ret, srcCuts, pairs, PairRel, JL, IntArr, List.map_cons,
    List.map_nil, List.lookup, List.mem_cons, List.mem_nil_iff]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
/-- Source, entry: the old code reaches its loop head coupled with the target's (sum 0, index 0). -/
theorem src_entry (σ : State) (a : Addr) (xs : List Value)
    (ha : σ.heap a = some (.array (.prim .int) xs)) (hl : xs.length < 2147483647)
    (hxs : ∀ v ∈ xs, ∃ x : I32, v = .int x)
    (fr₁ : Frame) (g0 : fr₁.get 0 = some (.ref a))
    (g1 : fr₁.get 1 = some (.int (BitVec.ofNat 32 xs.length)))
    (g3 : fr₁.get 3 = some (.int 0)) (g4 : fr₁.get 4 = some (.int 0)) :
    tgtAssert StatsOld.prog bOld pairs 8 0 (Frame.init true [.ref a]) σ 4 fr₁ σ := by
  simp only [tgtAssert]
  jvc [jbodyEWP, bodyEWPStep, ewpR_ret, srcCuts, pairs, PairRel, JL, IntArr, List.map_cons,
    List.map_nil, List.lookup, List.mem_cons, List.mem_nil_iff]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem stats_vc : ProdVC StatsNew.prog bNew StatsOld.prog bOld pairs (· = ·) 0 20 8 := by
  intro p hp
  simp only [pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · intro fr₁ σ₁ fr₂ σ₂ hJ
    obtain ⟨a, xs, h1, ⟨ha, hl, hxs⟩, h3, h4⟩ := hJ
    subst h1 h3 h4
    have hS := src_entry σ₁ a xs ha hl hxs
    simp only [pairs] at hS
    simp only [tgtCuts, pairs, List.map_cons, List.map_nil]
    generalize tgtAssert StatsOld.prog bOld [(0, 0, J0), (4, 3, JL)] 8 0 (Frame.init true [.ref a]) σ₁ = A at hS ⊢
    generalize tgtPost StatsOld.prog bOld (· = ·) 8 0 (Frame.init true [.ref a]) σ₁ = Q
    jvc
    all_goals (refine hS _ ?_ ?_ ?_ ?_ <;> simp [jsimp])
  · intro fr₁ σ₁ fr₂ σ₂ hJ
    obtain ⟨a, xs, s, i, h1, ⟨ha, hl, hxs⟩, f0, f1, f3, f4, e0, e2, e3, hi0, hile⟩ := hJ
    subst h1
    have hX := src_exit fr₂ σ₁ a xs s i e0 e2 e3 ha hl
    have hI := fun x hlt hx => src_iter fr₂ σ₁ a xs s i x e0 e2 e3 ha hl hxs hi0 hlt hx
    simp only [pairs] at hI
    simp only [tgtCuts, pairs, List.map_cons, List.map_nil]
    generalize tgtAssert StatsOld.prog bOld [(0, 0, J0), (4, 3, JL)] 8 3 fr₂ σ₁ = A at hI ⊢
    generalize tgtPost StatsOld.prog bOld (· = ·) 8 3 fr₂ σ₁ = Q at hX ⊢
    jvc
    all_goals (refine hI _ ‹_› (fun _ => by assumption) _ ?_ ?_ ?_ ?_ <;> simp [jsimp, f0, f1])
/-- **Java PR diff with a loop, new ⊑ old**: for every non-null `int[]` argument, every
terminating run of the enhanced-for version is matched by a run of the index-loop version with
the same outcome (value and final state, overflow included); the new code cannot go wrong where
the old one cannot. -/
theorem stats_sim (a : Addr) (xs : List Value) (σ : State) (h : IntArr σ a xs) :
    Sim (· = ·)
      (Call.mk StatsNew.prog (mref StatsNew.prog "Stats" "total") [.ref a] σ)
      (Call.mk StatsOld.prog (mref StatsOld.prog "Stats" "total") [.ref a] σ) :=
  sim_of_prodVC (b₁ := bNew) (b₂ := bOld) rfl rfl stats_vc (J₀ := J0) (by simp [pairs])
    ⟨a, xs, rfl, h, rfl, rfl⟩


/-! ## The other direction: old ⊑ new (the new code is the existentially executed source) -/

/-- Loop coupling for the reverse product (old at 3, new at 4). -/
def JLr (fr₁ : Frame) (σ₁ : State) (fr₂ : Frame) (σ₂ : State) : Prop :=
  ∃ a xs s i, σ₁ = σ₂ ∧ IntArr σ₁ a xs ∧
    fr₁.get 0 = some (.ref a) ∧ fr₁.get 2 = some (.int s) ∧ fr₁.get 3 = some (.int i) ∧
    fr₂.get 0 = some (.ref a) ∧ fr₂.get 1 = some (.int (BitVec.ofNat 32 xs.length)) ∧
    fr₂.get 3 = some (.int s) ∧ fr₂.get 4 = some (.int i) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ xs.length

def pairsR : List (Nat × Nat × Coupling) := [(0, 0, J0), (3, 4, JLr)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem srcR_exit (fr : Frame) (σ : State) (a : Addr) (xs : List Value) (s i : I32)
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.int (BitVec.ofNat 32 xs.length)))
    (h3 : fr.get 3 = some (.int s)) (h4 : fr.get 4 = some (.int i))
    (ha : σ.heap a = some (.array (.prim .int) xs)) (hl : xs.length < 2147483647)
    (hge : xs.length ≤ i.toInt) :
    tgtPost StatsNew.prog bNew (· = ·) 8 4 fr σ (.normal (some (.int s)) σ) := by
  simp only [tgtPost]
  jvc [RelO, jbodyEWP, bodyEWPStep, ewpR_ret]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem srcR_iter (fr : Frame) (σ : State) (a : Addr) (xs : List Value) (s i x : I32)
    (h0 : fr.get 0 = some (.ref a)) (h1 : fr.get 1 = some (.int (BitVec.ofNat 32 xs.length)))
    (h3 : fr.get 3 = some (.int s)) (h4 : fr.get 4 = some (.int i))
    (ha : σ.heap a = some (.array (.prim .int) xs)) (hl : xs.length < 2147483647)
    (hxs : ∀ v ∈ xs, ∃ x : I32, v = .int x)
    (hi0 : 0 ≤ i.toInt) (hlt : i.toInt < xs.length)
    (hx : ∀ h : (i.toInt).toNat < xs.length, xs[(i.toInt).toNat] = .int x)
    (fr₁ : Frame) (g0 : fr₁.get 0 = some (.ref a))
    (g2 : fr₁.get 2 = some (.int (s + x))) (g3 : fr₁.get 3 = some (.int (i + 1))) :
    tgtAssert StatsNew.prog bNew pairsR 8 4 fr σ 3 fr₁ σ := by
  simp only [tgtAssert]
  jvc [jbodyEWP, bodyEWPStep, ewpR_ret, srcCuts, pairsR, PairRel, JLr, IntArr, List.map_cons,
    List.map_nil, List.lookup, List.mem_cons, List.mem_nil_iff]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem srcR_entry (σ : State) (a : Addr) (xs : List Value)
    (ha : σ.heap a = some (.array (.prim .int) xs)) (hl : xs.length < 2147483647)
    (hxs : ∀ v ∈ xs, ∃ x : I32, v = .int x)
    (fr₁ : Frame) (g0 : fr₁.get 0 = some (.ref a))
    (g2 : fr₁.get 2 = some (.int 0)) (g3 : fr₁.get 3 = some (.int 0)) :
    tgtAssert StatsNew.prog bNew pairsR 8 0 (Frame.init true [.ref a]) σ 3 fr₁ σ := by
  simp only [tgtAssert]
  jvc [jbodyEWP, bodyEWPStep, ewpR_ret, srcCuts, pairsR, PairRel, JLr, IntArr, List.map_cons,
    List.map_nil, List.lookup, List.mem_cons, List.mem_nil_iff]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem stats_vc_rev : ProdVC StatsOld.prog bOld StatsNew.prog bNew pairsR (· = ·) 0 20 8 := by
  intro p hp
  simp only [pairsR, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · intro fr₁ σ₁ fr₂ σ₂ hJ
    obtain ⟨a, xs, h1, ⟨ha, hl, hxs⟩, h3, h4⟩ := hJ
    subst h1 h3 h4
    have hS := srcR_entry σ₁ a xs ha hl hxs
    simp only [pairsR] at hS
    simp only [tgtCuts, pairsR, List.map_cons, List.map_nil]
    generalize tgtAssert StatsNew.prog bNew [(0, 0, J0), (3, 4, JLr)] 8 0 (Frame.init true [.ref a]) σ₁ = A at hS ⊢
    generalize tgtPost StatsNew.prog bNew (· = ·) 8 0 (Frame.init true [.ref a]) σ₁ = Q
    jvc
    all_goals (refine hS _ ?_ ?_ ?_ <;> simp [jsimp])
  · intro fr₁ σ₁ fr₂ σ₂ hJ
    obtain ⟨a, xs, s, i, h1, ⟨ha, hl, hxs⟩, f0, f2, f3, e0, e1, e3, e4, hi0, hile⟩ := hJ
    subst h1
    have hX := srcR_exit fr₂ σ₁ a xs s i e0 e1 e3 e4 ha hl
    have hI := fun x hlt hx => srcR_iter fr₂ σ₁ a xs s i x e0 e1 e3 e4 ha hl hxs hi0 hlt hx
    simp only [pairsR] at hI
    simp only [tgtCuts, pairsR, List.map_cons, List.map_nil]
    generalize tgtAssert StatsNew.prog bNew [(0, 0, J0), (3, 4, JLr)] 8 4 fr₂ σ₁ = A at hI ⊢
    generalize tgtPost StatsNew.prog bNew (· = ·) 8 4 fr₂ σ₁ = Q at hX ⊢
    jvc
    all_goals (refine hI _ ‹_› (fun _ => by assumption) _ ?_ ?_ ?_ <;> simp [jsimp, f0])

/-- **Java PR diff with a loop, old ⊑ new.** -/
theorem stats_sim_rev (a : Addr) (xs : List Value) (σ : State) (h : IntArr σ a xs) :
    Sim (· = ·)
      (Call.mk StatsOld.prog (mref StatsOld.prog "Stats" "total") [.ref a] σ)
      (Call.mk StatsNew.prog (mref StatsNew.prog "Stats" "total") [.ref a] σ) :=
  sim_of_prodVC (b₁ := bOld) (b₂ := bNew) rfl rfl stats_vc_rev (J₀ := J0) (by simp [pairsR])
    ⟨a, xs, rfl, h, rfl, rfl⟩

/-- **The pull request preserves behaviour**: on every non-null `int[]`, the two versions are
equivalent (simulation both ways, equal outcomes). -/
theorem stats_equiv (a : Addr) (xs : List Value) (σ : State) (h : IntArr σ a xs) :
    Equiv (· = ·)
      (Call.mk StatsNew.prog (mref StatsNew.prog "Stats" "total") [.ref a] σ)
      (Call.mk StatsOld.prog (mref StatsOld.prog "Stats" "total") [.ref a] σ) :=
  ⟨stats_sim a xs σ h, (stats_sim_rev a xs σ h).mono fun _ _ e => e.symm⟩

end EquivLean.Demo.PrDiffStats

#print axioms EquivLean.Demo.PrDiffStats.src_entry
#print axioms EquivLean.Demo.PrDiffStats.src_iter
#print axioms EquivLean.Demo.PrDiffStats.src_exit
#print axioms EquivLean.Demo.PrDiffStats.stats_vc
#print axioms EquivLean.Demo.PrDiffStats.stats_sim
#print axioms EquivLean.Demo.PrDiffStats.stats_sim_rev
#print axioms EquivLean.Demo.PrDiffStats.stats_equiv
