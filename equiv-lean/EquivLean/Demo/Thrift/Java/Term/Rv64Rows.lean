-- Termination package by JimpleLean's session: TermT4/Rv64Rows.lean (sha256 0ea936a161581e27...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Rv64P
import EquivLean.Demo.Thrift.Java.Term.Rv64Total

/-!
# Thrift → Java (T4): the varint64 read theorems (D, M), total

Each D/M theorem of `Rv64P.lean` with termination: `readVarint64()` terminates on the theorem's
premises, and every run ends as the theorem states. Premise: the transport's class is concrete
(`TConc`), as for `rv64_total`. `Rv64P` is in the `t4-java` build only (`lt4.sh`), so this module and
the ones it imports are built there.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem rv64_term_at {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hCP : CPAt P R σ p t tmp) (hin : σ.initOf tpeCls = .done) (hc : TConc P [.ref p] σ) :
    MTerm P rv64Ref [.ref p] σ :=
  rv64_term R hF hV hT [.ref p] σ ⟨p, t, tmp, rfl, hCP, CPAtH.intro hCP, classOK_of_cpAt hCP, hin⟩ hc

/-- **D for varint64, total.** -/
theorem rv64_D_total {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hCP : CPAt P R σ p t tmp) (hin : σ.initOf tpeCls = .done) (x : I64) (rest : Spec.Bytes)
    (hsrc : R.src σ t = Spec.varint (Spec.toU 64 x.toInt) ++ rest) (hc : TConc P [.ref p] σ) :
    (∃ o, MExec P rv64Ref [.ref p] σ o) ∧ ∀ o, MExec P rv64Ref [.ref p] σ o →
    ∃ σ', o = .normal (some (.long x)) σ' ∧ R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧
      CPAt P R σ' p t tmp :=
  ⟨(rv64_term_at hF hV hT hCP hin hc).run, fun _ hm => rv64_D hF hV hCP hin x rest hsrc hm⟩

/-- **M for varint64 (more than 10 continuation bytes), total.** -/
theorem rv64_M_overlong_total {P : Program} {R : TRep}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC]) (hV : Valid P (tContracts R).env)
    (hT : TransportTerm P R) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (hov : Spec.VarintOverlong 10 (R.src σ t)) (hc : TConc P [.ref p] σ) :
    (∃ o, MExec P rv64Ref [.ref p] σ o) ∧ ∀ o, MExec P rv64Ref [.ref p] σ o →
    ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs) :=
  ⟨(rv64_term_at hF hV hT hCP hin hc).run, fun _ hm => rv64_M_overlong hF hV hCP hin hov hm⟩

/-- **M for varint64 (the input ends inside the varint), total.** -/
theorem rv64_M_truncated_total {P : Program} {R : TRep}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC]) (hV : Valid P (tContracts R).env)
    (hT : TransportTerm P R) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (htr : Spec.VarintTruncated 10 (R.src σ t)) (hc : TConc P [.ref p] σ) :
    (∃ o, MExec P rv64Ref [.ref p] σ o) ∧ ∀ o, MExec P rv64Ref [.ref p] σ o →
    ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain ttExcCls fs) :=
  ⟨(rv64_term_at hF hV hT hCP hin hc).run, fun _ hm => rv64_M_truncated hF hV hCP hin htr hm⟩

/-- **M for varint64 (a varint of at most 10 bytes with value `≥ 2^64`), total.** -/
theorem rv64_M_exceeds_total {P : Program} {R : TRep}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC]) (hV : Valid P (tContracts R).env)
    (hT : TransportTerm P R) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) {v : Nat} {rest : Spec.Bytes}
    (hrd : Spec.readVarint 10 (R.src σ t) = some (v, rest)) (hc : TConc P [.ref p] σ) :
    (∃ o, MExec P rv64Ref [.ref p] σ o) ∧ ∀ o, MExec P rv64Ref [.ref p] σ o →
    ∃ σ', o = .normal (some (.long (BitVec.ofNat 64 v))) σ' ∧ R.src σ' t = rest :=
  ⟨(rv64_term_at hF hV hT hCP hin hc).run, fun _ hm => rv64_M_exceeds hF hV hCP hin hrd hm⟩

/-- **M on `exVarint64Exceeds`, total.** -/
theorem rv64_exVarint64Exceeds_total {P : Program} {R : TRep}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC]) (hV : Valid P (tContracts R).env)
    (hT : TransportTerm P R) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (rest : Spec.Bytes)
    (hsrc : R.src σ t = Spec.exVarint64Exceeds ++ rest) (hc : TConc P [.ref p] σ) :
    (∃ o, MExec P rv64Ref [.ref p] σ o) ∧ ∀ o, MExec P rv64Ref [.ref p] σ o →
    ∃ σ', o = .normal (some (.long 0#64)) σ' ∧ R.src σ' t = rest :=
  ⟨(rv64_term_at hF hV hT hCP hin hc).run,
    fun _ hm => rv64_exVarint64Exceeds hF hV hCP hin rest hsrc hm⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.rv64_D_total
#print axioms EquivLean.Demo.Thrift.Java.rv64_M_overlong_total
#print axioms EquivLean.Demo.Thrift.Java.rv64_M_truncated_total
#print axioms EquivLean.Demo.Thrift.Java.rv64_M_exceeds_total
#print axioms EquivLean.Demo.Thrift.Java.rv64_exVarint64Exceeds_total
