-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermUa.lean (sha256 76ca030c9e25f4d4...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM3
import EquivLean.Modernize.Cbtrn02c.JavaTermDefsH

/-!
# CBTRN02C → Java, termination: thin twins of `JavaRunM3`

The statements and preambles of the originals over the thin cut list (each cut assertion
a variant comparison, the entry's `True`), calls by `callWPThin` (`callWPT` without the
callee preconditions, which `MethodVC` checks).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ua_tentry (r d wA aD : Addr) (σ0 : State)
    (hpre : updateAccountSpec.pre [.ref r, .ref d, .ref wA, .ref aD] σ0) :
    UaThinWP [.ref r, .ref d, .ref wA, .ref aD] σ0 0 (Frame.init true [.ref r, .ref d, .ref wA, .ref aD]) σ0 := by
  obtain ⟨r', d', wA', aD', fsR, fsd, fsA, lAR, amt, bal, cc, cdb, id, xsA, ys, m, hargs, hR, hRk, hd,
    hamt, hA, hall, hbal, hcc, hcd, hid, haD, hlen, hsh, hne, hidx, hlAR, n1, n2, n3, n4, n5, i1,
    i2⟩ := hpre
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
  have hlAR' : refField σ0 r arKey = lAR := refField_of hR hRk
  have hfA : fieldsOf σ0 wA = fsA := fieldsOf_of hA
  have eb : lng' σ0 wA acBalKey = bal := by simp [lng', fld', fieldsOf, hA, hbal]
  have ec : lng' σ0 wA acCcKey = cc := by simp [lng', fld', fieldsOf, hA, hcc]
  have ed : lng' σ0 wA acCdKey = cdb := by simp [lng', fld', fieldsOf, hA, hcd]
  have ei : lng' σ0 wA acctIdKey = id := by simp [lng', fld', fieldsOf, hA, hid]
  have ea : lng' σ0 d dAmtKey' = amt := by simp [lng', fld', fieldsOf, hd, hamt]
  have earr : arrOf σ0 aD = xsA := by simp [arrOf, haD]
  have hkeep := Hide.intro (And.intro hlAR' (And.intro hfA (And.intro eb (And.intro ec
    (And.intro ed (And.intro ei ea))))))
  clear hlAR' hfA eb ec ed ei ea
  unfold UaThinWP
  jvc [uaCallees, findAccountSig', findAccountSpecF, findAccountSpec, copyAccountSig,
    copyAccountSpecF, Grows, narrow_long, narrow_cls]

end EquivLean.Modernize.Cbtrn02c.Java
