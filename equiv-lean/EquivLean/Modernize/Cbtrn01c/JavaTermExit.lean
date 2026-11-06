-- Termination package by JimpleLean's session: TermPk/Cbtrn01c/JavaTermExit.lean (sha256 c82a0c429fde5aed...); only the module root renamed.
import EquivLean.Modernize.Cbtrn01c.JavaRunExit
import EquivLean.Modernize.Cbtrn01c.JavaTermDefs

/-!
# CBTRN01C → Java, termination: thin twin of `run_seg29_exit` (`JavaRunExit`)

The statement and the preamble of the original, the cut assertions the variants (`runVs`),
calls by `callWPT` without preconditions (`callWPThin`); variant goals by the program variant closer.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple EquivLean.Modernize.TermCommon

namespace EquivLean.Modernize.Cbtrn01c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_tseg29_exit (a1 a2 a3 a4 a5 a6 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State) (d : Value) (res l : Addr) (fs : List (FieldKey × Value))
    (ys : List Value) (m : Nat)
    (f5 : fr.get 5 = some (.int 1#32)) (f9 : fr.get 9 = some (.ref res))
    (f11 : fr.get 11 = some (.ref l))
    (hres : σ.heap res = some (.plain "Cbtrn01c$Result" fs))
    (hfd : Fields.get fs ("Cbtrn01c$Result", "displays") = some (.ref l))
    (hfa : Fields.get fs ("Cbtrn01c$Result", "abended") = some (.int 0))
    (hrl : res ≠ l) (hl : σ.heap l = some (.list .arrayList ys m))
    (hD : Hide (Forall2 (JStrAt σ) ys ((headL vals1 vals3 vals5 vals1.length true).map jline))) :
    RunThinWP a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 29 fr σ := by

  unfold RunThinWP
  jvc [runInv, runSpecG, runPostG, callees, runArgs, inlineFuel, fields_get_cons, fields_get_nil,
    jstrLitT]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip
  all_goals cbtrn01c_variant

end EquivLean.Modernize.Cbtrn01c.Java
