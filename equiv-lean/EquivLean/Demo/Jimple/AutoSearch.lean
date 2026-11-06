import EquivLean.Demo.Gen.Jimple.Search
import EquivLean.Demo.Jimple.PrDiffStats
import EquivLean.Bridge.Jimple.Auto

/-!
# Java search loop: early `return` → flag and `break`, with nothing written

Old (`examples/java/search_old/Search.java`):
`for (int i = 0; i < a.length; i++) if (a[i] == k) return true; return false;`
New (`examples/java/search_new/Search.java`):
`boolean found = false; for (int x : a) if (x == k) { found = true; break; } return found;`
Both compiled by `javac --release 17` and converted by Soot 4.7.1
(`EquivLean/Demo/Gen/Jimple/Search.lean`).

The two loops leave differently (the old one returns from inside the loop, the new one breaks
out and returns its flag after the loop) but run in lockstep.  Each theorem is one call
`equiv_jimple`, with the hypotheses of `PrDiffStats` on the array argument (`IntArr`) and any key
`k`; the generated loop coupling (heads: statement 5 of the new body, 3 of the old one) relates
the two index counters, keeps the array, its length and the key at their entry values, and keeps
the new code's flag at `0`: the flag is assigned inside the loop, but only on the iteration that
leaves it, so it is `0` at every visit of the head.  `search_equiv`: the two versions are
equivalent (simulation both ways, same result and final state).
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Gen

namespace EquivLean.Demo.AutoSearch
open EquivLean.Demo.PrDiffStats (IntArr)

set_option maxRecDepth 30000 in
/-- **new ⊑ old**, nothing written. -/
theorem search_sim (a : Addr) (xs : List Value) (k : I32) (σ : State) (h : IntArr σ a xs) :
    Sim (· = ·)
      (Call.mk SearchNew.prog (mref SearchNew.prog "Search" "contains") [.ref a, .int k] σ)
      (Call.mk SearchOld.prog (mref SearchOld.prog "Search" "contains") [.ref a, .int k] σ) := by
  equiv_jimple

set_option maxRecDepth 30000 in
/-- **old ⊑ new**, nothing written. -/
theorem search_sim_rev (a : Addr) (xs : List Value) (k : I32) (σ : State) (h : IntArr σ a xs) :
    Sim (· = ·)
      (Call.mk SearchOld.prog (mref SearchOld.prog "Search" "contains") [.ref a, .int k] σ)
      (Call.mk SearchNew.prog (mref SearchNew.prog "Search" "contains") [.ref a, .int k] σ) := by
  equiv_jimple

set_option maxRecDepth 30000 in
/-- **The change preserves behaviour**, one tactic call for both directions. -/
theorem search_equiv (a : Addr) (xs : List Value) (k : I32) (σ : State) (h : IntArr σ a xs) :
    Equiv (· = ·)
      (Call.mk SearchNew.prog (mref SearchNew.prog "Search" "contains") [.ref a, .int k] σ)
      (Call.mk SearchOld.prog (mref SearchOld.prog "Search" "contains") [.ref a, .int k] σ) := by
  equiv_jimple

end EquivLean.Demo.AutoSearch

#print axioms EquivLean.Demo.AutoSearch.search_sim
#print axioms EquivLean.Demo.AutoSearch.search_sim_rev
#print axioms EquivLean.Demo.AutoSearch.search_equiv
