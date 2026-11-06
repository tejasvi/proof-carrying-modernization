-- Termination package by JimpleLean's session: TermT4/Rv32Rows.lean (sha256 6d2aea65de946fcf...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.Rv32Total

/-!
# Thrift → Java (T4): the varint32 theorems (E, D, M; rows V1, V2), total

Each E/D/M theorem of `Rv32P.lean` with termination: `readVarint32()` / `writeVarint32(x)` terminates on
the theorem's premises, and every run ends as the theorem states. Premise: the transport's class is
concrete (`TConc`), as for `rv32_total` / `wv32_total`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem rv32_term_at {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hCP : CPAt P R σ p t tmp) (hin : σ.initOf tpeCls = .done) (hc : TConc P [.ref p] σ) :
    MTerm P rv32Ref [.ref p] σ :=
  rv32_term R hF hV hT [.ref p] σ ⟨p, t, tmp, rfl, hCP, hin⟩ hc

/-- **D for varint32, total.** -/
theorem rv32_D_total {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hCP : CPAt P R σ p t tmp) (hin : σ.initOf tpeCls = .done) (x : I32) (rest : Spec.Bytes)
    (hsrc : R.src σ t = Spec.varint (Spec.toU 32 x.toInt) ++ rest) (hc : TConc P [.ref p] σ) :
    (∃ o, MExec P rv32Ref [.ref p] σ o) ∧ ∀ o, MExec P rv32Ref [.ref p] σ o →
    ∃ σ', o = .normal (some (.int x)) σ' ∧ R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧
      CPAt P R σ' p t tmp :=
  ⟨(rv32_term_at hF hV hT hCP hin hc).run, fun _ hm => rv32_D hF hV hCP hin x rest hsrc hm⟩

/-- **M for varint32 (more than 5 continuation bytes), total.** -/
theorem rv32_M_overlong_total {P : Program} {R : TRep}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC]) (hV : Valid P (tContracts R).env)
    (hT : TransportTerm P R) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (hov : Spec.VarintOverlong 5 (R.src σ t)) (hc : TConc P [.ref p] σ) :
    (∃ o, MExec P rv32Ref [.ref p] σ o) ∧ ∀ o, MExec P rv32Ref [.ref p] σ o →
    ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs) :=
  ⟨(rv32_term_at hF hV hT hCP hin hc).run, fun _ hm => rv32_M_overlong hF hV hCP hin hov hm⟩

/-- **M for varint32 (the input ends inside the varint), total.** -/
theorem rv32_M_truncated_total {P : Program} {R : TRep}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC]) (hV : Valid P (tContracts R).env)
    (hT : TransportTerm P R) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (htr : Spec.VarintTruncated 5 (R.src σ t)) (hc : TConc P [.ref p] σ) :
    (∃ o, MExec P rv32Ref [.ref p] σ o) ∧ ∀ o, MExec P rv32Ref [.ref p] σ o →
    ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain ttExcCls fs) :=
  ⟨(rv32_term_at hF hV hT hCP hin hc).run, fun _ hm => rv32_M_truncated hF hV hCP hin htr hm⟩

/-- **M for varint32 (a varint of at most 5 bytes with value `≥ 2^32`), total.** -/
theorem rv32_M_exceeds_total {P : Program} {R : TRep}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC]) (hV : Valid P (tContracts R).env)
    (hT : TransportTerm P R) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) {v : Nat} {rest : Spec.Bytes}
    (hrd : Spec.readVarint 5 (R.src σ t) = some (v, rest)) (hc : TConc P [.ref p] σ) :
    (∃ o, MExec P rv32Ref [.ref p] σ o) ∧ ∀ o, MExec P rv32Ref [.ref p] σ o →
    ∃ σ', o = .normal (some (.int (BitVec.ofNat 32 v))) σ' ∧ R.src σ' t = rest :=
  ⟨(rv32_term_at hF hV hT hCP hin hc).run, fun _ hm => rv32_M_exceeds hF hV hCP hin hrd hm⟩

/-- **M on `exVarint32Exceeds`, total.** -/
theorem rv32_exVarint32Exceeds_total {P : Program} {R : TRep}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC]) (hV : Valid P (tContracts R).env)
    (hT : TransportTerm P R) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (rest : Spec.Bytes)
    (hsrc : R.src σ t = Spec.exVarint32Exceeds ++ rest) (hc : TConc P [.ref p] σ) :
    (∃ o, MExec P rv32Ref [.ref p] σ o) ∧ ∀ o, MExec P rv32Ref [.ref p] σ o →
    ∃ σ', o = .normal (some (.int 5#32)) σ' ∧ R.src σ' t = rest :=
  ⟨(rv32_term_at hF hV hT hCP hin hc).run, fun _ hm => rv32_exVarint32Exceeds hF hV hCP hin rest hsrc hm⟩

/-- **V1/V2, M on `exVarint32Overlong`, total.** -/
theorem rv32_exVarint32Overlong_total {P : Program} {R : TRep}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC]) (hV : Valid P (tContracts R).env)
    (hT : TransportTerm P R) {σ : State} {p t tmp : Addr} (hCP : CPAt P R σ p t tmp)
    (hin : σ.initOf tpeCls = .done) (rest : Spec.Bytes)
    (hsrc : R.src σ t = Spec.exVarint32Overlong ++ rest) (hc : TConc P [.ref p] σ) :
    (∃ o, MExec P rv32Ref [.ref p] σ o) ∧ ∀ o, MExec P rv32Ref [.ref p] σ o →
    ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs) :=
  ⟨(rv32_term_at hF hV hT hCP hin hc).run, fun _ hm => rv32_exVarint32Overlong hF hV hCP hin rest hsrc hm⟩

/-- **E for varint32, total.** -/
theorem wv32_E_total {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hCP : CPAt P R σ p t tmp) (x : I32) (hc : TConc P [.ref p, .int x] σ) :
    (∃ o, MExec P wv32Ref [.ref p, .int x] σ o) ∧ ∀ o, MExec P wv32Ref [.ref p, .int x] σ o →
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ Spec.varint (Spec.toU 32 x.toInt) ∧
      R.src σ' t = R.src σ t ∧ CPAt P R σ' p t tmp :=
  ⟨(wv32_term R hF hV hT [.ref p, .int x] σ ⟨p, t, tmp, x, rfl, hCP⟩ hc).run,
    fun _ hm => wv32_E hF hV hCP x hm⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.rv32_D_total
#print axioms EquivLean.Demo.Thrift.Java.rv32_M_overlong_total
#print axioms EquivLean.Demo.Thrift.Java.rv32_M_truncated_total
#print axioms EquivLean.Demo.Thrift.Java.rv32_M_exceeds_total
#print axioms EquivLean.Demo.Thrift.Java.rv32_exVarint32Exceeds_total
#print axioms EquivLean.Demo.Thrift.Java.rv32_exVarint32Overlong_total
#print axioms EquivLean.Demo.Thrift.Java.wv32_E_total
