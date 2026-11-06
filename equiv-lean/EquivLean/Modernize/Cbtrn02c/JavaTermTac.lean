-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermTac.lean (sha256 a6f1b9536682d20c...); only the module root renamed.
import Jimple.TermSplit

/-!
# Termination packages: `jcontract_term_v`

`jcontract_term_v [h]` proves `ContractTerm P sig S` as `jcontract_term [h]` does, and also when
`sig` is an instance method (a constructor): the virtual implementations are enumerated over the
program's classes, as `jcontract_ok` does (`forall_progClass_of_mem`); each class implementing
`sig` must select the method of `h : ∀ args σ, S.pre args σ → MTerm P m args σ`
(`vterm_of_jimple`).
-/

namespace Jimple

macro "jcontract_term_v" " [" f:term "]" : tactic => `(tactic| (
  refine ⟨?_, ?_⟩
  · intro m ht
    obtain ⟨hsel, hb⟩ := ht
    rcases hsel with h | h | ⟨hs, _⟩
    all_goals first
      | (have hn := congrArg MethodSig.name hs
         simp (config := { decide := true }) only [jground, clinitSig] at hn)
      | (simp (config := { decide := true }) only [jground, reduceCtorEq,
           Program.Target.jimple.injEq] at h
         try subst h
         try simp (config := { decide := true }) only [jground] at hb)
    all_goals exact $f
  · apply forall_progClass_of_mem
    simp (config := { decide := true }) only [jground, List.forall_mem_cons,
      List.forall_mem_nil, List.not_mem_nil, false_implies, implies_true, and_true, true_implies]
    repeat' constructor
    all_goals first
      | (intro hf; exact False.elim hf)
      | exact vterm_of_jimple (by exact rfl) $f))

end Jimple
