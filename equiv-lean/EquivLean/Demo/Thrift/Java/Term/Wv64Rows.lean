-- Termination package by JimpleLean's session: TermT4/Wv64Rows.lean (sha256 3dae7782f6a25df6...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.Wv64Total

/-!
# Thrift → Java (T4): the varint64 write theorem (E), total

`wv64_E` of `Wv64.lean` with termination: `writeVarint64(x)` terminates on the theorem's premises, and
every run ends as the theorem states. Premise: the transport's class is concrete (`TConc`), as for
`wv64_total`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- **E for varint64, total.** -/
theorem wv64_E_total {P : Program} {R : TRep} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hCP : CPAt P R σ p t tmp) (x : I64) (hc : TConc P [.ref p, .long x] σ) :
    (∃ o, MExec P wv64Ref [.ref p, .long x] σ o) ∧ ∀ o, MExec P wv64Ref [.ref p, .long x] σ o →
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ Spec.varint (Spec.toU 64 x.toInt) ∧
      R.src σ' t = R.src σ t ∧ CPAt P R σ' p t tmp :=
  ⟨(wv64_term R hF hV hT [.ref p, .long x] σ ⟨p, t, tmp, x, rfl, hCP⟩ hc).run,
    fun _ hm => wv64_E hF hV hCP x hm⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.wv64_E_total
