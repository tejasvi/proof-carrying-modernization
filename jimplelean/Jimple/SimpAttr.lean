/-
  Jimple/SimpAttr.lean — the `jsimp` simp set used by the verification tactics.
-/
import Lean

register_simp_attr jsimp

/-- Rewrites `jsym` uses only under `jimple.modelContracts` (string concatenation's recipes). -/
register_simp_attr jsimpc

/-- Frame lemmas: `P σ … → Agree σ σ' → P σ' …`, or `… → Agree σ σ' → f σ' … = f σ …`. The jvc
    loop proves a leaf goal about a later state from a hypothesis about an earlier one with them,
    leaving the heap agreement (`jFrameStep`). -/
register_label_attr jframe
