-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermWt.lean (sha256 19285fd44b77b813...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM2xb2
import EquivLean.Modernize.Cbtrn02c.JavaTermDefsH

/-!
# CBTRN02C → Java, termination: thin twins of `JavaRunM2xb2`

The statements and preambles of the originals over the thin cut list (each cut assertion
a variant comparison, the entry's `True`), calls by `callWPThin` (`callWPT` without the
callee preconditions, which `MethodVC` checks).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem wt_tentry (r wT lK : Addr) (σ0 : State)
    (hpre : writeTransactionSpecX.pre [.ref r, .ref wT, .ref lK] σ0) :
    WtThinWP [.ref r, .ref wT, .ref lK] σ0 0 (Frame.init true [.ref r, .ref wT, .ref lK]) σ0 := by
  obtain ⟨r', wT', lK', fsR, lT, lD, fsT, sId, idcs, ks, mK, ts, mT, ds, mD, hargs, hR, hRT, hRD,
    ⟨ab, hab⟩, hT, hallT, hid, hsId, hlK, hlen, hsh, hlT, hlD, hnd, i1, i2, i3⟩ := hpre
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl⟩ := hargs
  have e1 : fld σ0 wT trIdKey = .ref sId := fld_of hT hid
  have e2 : listOf σ0 lK = ks := listOf_of hlK
  have e3 : refField σ0 r ltKey = lT := refField_of hR hRT
  have e4 : refField σ0 r dispKey = lD := refField_of hR hRD
  have e5 : listOf σ0 lT = ts := listOf_of hlT
  have e6 : listOf σ0 lD = ds := listOf_of hlD
  have e7 : fieldsOf σ0 wT = fsT := fieldsOf_of hT
  have e8 : fieldsOf σ0 r = fsR := fieldsOf_of hR
  have hkeep := Hide.intro (And.intro e1 (And.intro e2 (And.intro e3 (And.intro e4 (And.intro e5
    (And.intro e6 (And.intro e7 e8)))))))
  clear e1 e2 e3 e4 e5 e6 e7 e8
  unfold WtThinWP
  jvc [wtCalleesX, findKeySig, findKeySpecF, findKeySpec, copyTranSig, copyTranSpecF, abendSig,
    abendSpec22, Grows, narrow_long, narrow_cls]

end EquivLean.Modernize.Cbtrn02c.Java
