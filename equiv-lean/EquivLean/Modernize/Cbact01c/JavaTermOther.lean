-- Termination package by JimpleLean's session: TermPk/Cbact01c/JavaTermOther.lean (sha256 5897ba78f6169186...); only the module root renamed.
import EquivLean.Modernize.Cbact01c.JavaRunOther
import EquivLean.Modernize.Cbact01c.JavaTermDefs

/-!
# CBACT01C → Java, termination: thin twins of `JavaRunOther`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

attribute [local jsimp high] Jimple.ite_nat_ne
open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_tentry (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal))
    (et : JType) (xs : List Value) (ha : σ0.heap a = some (.array et xs))
    (hlen : xs.length < 2147483648)
    (i1 : σ0.initOf "Cbact01c" = .done) (i2 : σ0.initOf "Cbact01c$Result" = .done)
    (i3 : σ0.initOf "Cbact01c$AccountRecord" = .done) (i4 : σ0.initOf "Cbact01c$ArrArrayRec" = .done)
    (i5 : σ0.initOf "Cbact01c$OutAcctRec" = .done) :
    RunThinWP0 σ0 a vals := by

  unfold RunThinWP0
  jvc [runEnv, runCallees, spacesSig, padSig, cobdatftSig, displayAcctRecordSig, writeOutRecordSig,
    writeArrayRecordSig, writeVbrcRecordsSig, accountRecordTextSig, spacesSpecF, runSpecG, runInv,
    runInv10, Grows, resCls, inlineFuel, jstrLit, exists_and_left, exists_and_right, and_assoc,
    exists_eq_left, exists_eq_left', exists_eq_right, exists_eq_right', runVs, runVar]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_tseg10_eof (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal))
    (fr : Frame) (σ : Jimple.State) (et : JType) (xs : List Value) (i : I32) (cd : I64) (d : Addr)
    (s : JStr) (fs : List (FieldKey × Value)) (ys1 ys2 ys3 ys4 : List Value) (m1 m2 m3 m4 : Nat)
    (ha : σ0.heap a = some (.array et xs)) (ha0 : a < σ0.next) (hlen : xs.length < 2147483648)
    (f0 : fr.get 0 = some (.ref σ0.next)) (f1 : fr.get 1 = some (.ref a))
    (f7 : fr.get 7 = some (.int i)) (f12 : fr.get 12 = some (.int 0#32))
    (f11 : fr.get 11 = some (.int 0#32)) (f3 : fr.get 3 = some (.long cd))
    (f9 : fr.get 9 = some (.ref d)) (hd : σ.heap d = some (.str s))
    (hR : σ.heap σ0.next = some (.plain resCls fs))
    (hl1 : σ.heap (σ0.next + 1) = some (.list .arrayList ys1 m1))
    (hl2 : σ.heap (σ0.next + 2) = some (.list .arrayList ys2 m2))
    (hl3 : σ.heap (σ0.next + 3) = some (.list .arrayList ys3 m3))
    (hl4 : σ.heap (σ0.next + 4) = some (.list .arrayList ys4 m4))
    (hin : i.toInt = xs.length)
    (hdB1 : d ≠ σ0.next + 1) (hdB2 : d ≠ σ0.next + 2) (hdB3 : d ≠ σ0.next + 3)
    (hdB4 : d ≠ σ0.next + 4)
    (hR1 : Fields.get fs (resCls, "displays") = some (.ref (σ0.next + 1)))
    (hR2 : Fields.get fs (resCls, "outFileWrites") = some (.ref (σ0.next + 2)))
    (hR3 : Fields.get fs (resCls, "arryFileWrites") = some (.ref (σ0.next + 3)))
    (hR4 : Fields.get fs (resCls, "vbrcFileWrites") = some (.ref (σ0.next + 4)))
    (hR5 : Fields.get fs (resCls, "abended") = some (.int 0))
    (hD : Hide (RunData σ0 vals σ i.toNat cd s ys1 ys2 ys3 ys4))
    (hg1 : σ0.next ≤ σ.next) (hg2 : ∀ x, x < σ0.next → σ.heap x = σ0.heap x)
    (hinits : σ.inits = σ0.inits) (hstatics : σ.statics = σ0.statics)
    (i1 : σ0.initOf "Cbact01c" = .done) :
    RunThinWP σ0 a vals 10 fr σ := by

  unfold RunThinWP
  jvc [runEnv, runCallees, runSpecG, runInv, runInv10, Grows, resCls, inlineFuel, jstrLit,
    exists_and_left, exists_and_right, and_assoc, exists_eq_left, exists_eq_left', exists_eq_right,
    exists_eq_right', runVs, runVar]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_tseg10_exit (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal))
    (fr : Frame) (σ : Jimple.State) (et : JType) (xs : List Value) (i : I32) (cd : I64) (d : Addr)
    (s : JStr) (fs : List (FieldKey × Value)) (ys1 ys2 ys3 ys4 : List Value) (m1 m2 m3 m4 : Nat)
    (ha : σ0.heap a = some (.array et xs))
    (f0 : fr.get 0 = some (.ref σ0.next)) (f11 : fr.get 11 = some (.int 1#32))
    (hR : σ.heap σ0.next = some (.plain resCls fs))
    (hl1 : σ.heap (σ0.next + 1) = some (.list .arrayList ys1 m1))
    (hl2 : σ.heap (σ0.next + 2) = some (.list .arrayList ys2 m2))
    (hl3 : σ.heap (σ0.next + 3) = some (.list .arrayList ys3 m3))
    (hl4 : σ.heap (σ0.next + 4) = some (.list .arrayList ys4 m4))
    (hin : i.toInt = xs.length) (hlenv : xs.length = vals.length)
    (hR1 : Fields.get fs (resCls, "displays") = some (.ref (σ0.next + 1)))
    (hR2 : Fields.get fs (resCls, "outFileWrites") = some (.ref (σ0.next + 2)))
    (hR3 : Fields.get fs (resCls, "arryFileWrites") = some (.ref (σ0.next + 3)))
    (hR4 : Fields.get fs (resCls, "vbrcFileWrites") = some (.ref (σ0.next + 4)))
    (hR5 : Fields.get fs (resCls, "abended") = some (.int 0))
    (hD : Hide (RunData σ0 vals σ i.toNat cd s ys1 ys2 ys3 ys4))
    (hg1 : σ0.next ≤ σ.next) (hl40 : σ0.next + 4 < σ.next) :
    RunThinWP σ0 a vals 10 fr σ := by

  unfold RunThinWP
  jvc [runEnv, runCallees, runSpecG, runInv, Grows, resCls, inlineFuel, jstrLit, runVs, runVar]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact01c.Java
