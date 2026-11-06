import Lean

/-!
# The loop-shape database

Bridges register, for every loop construct of their encoding,

* `@[equiv_loop_shape]` a theorem whose conclusion is `LoopShape (L …) (iter …) cls`;
* `@[equiv_loop_term]` a theorem whose conclusion is `LoopShape.Terminates (L …) (iter …) cls`.

`equiv_loop_auto` (`EquivLean.Tactic.LoopAuto`) then pairs the loop at the head of the goal
with the loop at the head of a hypothesis for any two registered encodings, with no lemma
names in the proof.
-/

register_label_attr equiv_loop_shape
register_label_attr equiv_loop_term
