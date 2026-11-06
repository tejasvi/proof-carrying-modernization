-- Termination package by JimpleLean's session: TermT4/Callee.lean (sha256 5d9bcfa695a315b8...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.Link
import EquivLean.Demo.Thrift.Java.Term.RbTotal
import EquivLean.Demo.Thrift.Java.Term.WbdTotal
import EquivLean.Demo.Thrift.Java.Term.GttTotal
import EquivLean.Demo.Thrift.Java.Term.CcrlTotal
import EquivLean.Demo.Thrift.Java.Term.CrbaTotal

/-!
# Thrift → Java (T4), termination: the small protocol methods as callees under `TRepConc`

`readByte()`, `writeByteDirect(byte)` and `checkReadBytesAvailable(TList)` terminate given `TConc`;
on their callers' contracts `CPAt` and `TRepConc` give it.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem rbA_termR (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rbSpecA P R).pre args σ → MTerm P rbRef args σ := by
  intro args σ hpre
  obtain ⟨p, t, tmp, hargs, hCP⟩ := hpre
  exact rb_termI R hF hV hT args σ
    ⟨⟨p, t, tmp, hargs, hCP, CPAtH.intro hCP, classOK_of_cpAt hCP⟩, tconc_of_args hR hargs hCP⟩

theorem wbdA_termR (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (wbdSpecA P R).pre args σ → MTerm P wbdRef args σ := by
  intro args σ hpre
  obtain ⟨p, t, tmp, b, hargs, hCP⟩ := hpre
  exact wbd_termI R hF hV hT args σ
    ⟨⟨p, t, tmp, b, hargs, hCP, CPAtH.intro hCP, classOK_of_cpAt hCP⟩, tconc_of_args hR hargs hCP⟩

theorem crbaA_termR (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (crbaSpec P R).pre args σ → MTerm P crbaRef args σ := by
  intro args σ hpre
  obtain ⟨p, l, t, tmp, lfs, b, s, hargs, hH, hl, he, hs, hi⟩ := hpre
  have hC := CPAtH.elim hH
  exact crba_termI R hF hV hT args σ
    ⟨⟨p, l, t, tmp, lfs, b, s, hargs, hC, hH, classOK_of_cpAt hC, hl, he, hs, hi⟩, tconc_of_args hR hargs hC⟩

end EquivLean.Demo.Thrift.Java
