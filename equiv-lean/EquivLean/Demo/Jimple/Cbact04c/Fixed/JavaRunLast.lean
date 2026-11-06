import EquivLean.Demo.Jimple.Cbact04c.Fixed.JavaRunDefs

/-!
# CBACT04C in Java, the fixed port: after the last account is posted

The verification condition of `run` from cut 48 (statement 48, after the `post` of the last
account behind the loop): the posted account is added to the `ArrayList` and the `Result` is
returned, with the rewrites `jRunFix`.
-/

open Jimple EquivLean.Demo.Cbact04c.Java

namespace EquivLean.Demo.Cbact04c.JavaF

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg48 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (σ0 : State) (fr : Frame) (σ : State)
    (hpre : runPreG ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0)
    (h : J48 ca aa da acctOf rateOf cs [.ref ca, .ref aa, .ref da] σ0 fr σ) :
    RunWP ca aa da acctOf rateOf cs σ0 48 fr σ := by
  obtain ⟨-, hrun⟩ := hpre
  have hrun' := Hide.intro hrun
  clear hrun
  obtain ⟨l, ys, mods, w, hf, f9, f13, hw, f5, hl, hlf, hpairs, hg, hin3⟩ := h
  have hg' := Hide.intro hg
  clear hg
  unfold RunWP
  jvc [runInv, runSpecG, callees, inlineFuel, fields_get_cons, fields_get_nil]
  have hl1 : l < σ.next := State.lt_next_of_heap hl
  have hl' : l ≠ σ.next := Nat.ne_of_lt hl1
  simp only [runPostG]
  refine ⟨σ.next, ?_⟩
  simp [State.heap_setObj, State.heap_alloc, State.next_alloc, State.next_setObj,
    Fields.get_set, hl', hl1]
  refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
  rw [jRunFix_last hf]
  have hpairs1 : Pairs (AcctAtC "Cbact04cFixed$Account"
      (σ.setObj l (.list .arrayList (ys ++ [w]) (mods + 1)))) (ys ++ [w])
      ((jRun acctOf rateOf cs).rewrites ++
        [jPost (jRun acctOf rateOf cs).acct (jRun acctOf rateOf cs).total]) :=
    pairs_append (acctAtC_setObj_list hl (Hide.elim hw))
      (pairs_mono (fun _ _ h => acctAtC_setObj_list hl h) (Hide.elim hpairs))
  have hn := Nat.le_of_eq (State.next_setObj σ l (.list .arrayList (ys ++ [w]) (mods + 1)))
  exact pairs_mono (fun _ _ h => acctAtC_of_grows
    (grows_setObj (grows_setObj (grows_alloc _ _) hn) hn) h) hpairs1

end EquivLean.Demo.Cbact04c.JavaF
