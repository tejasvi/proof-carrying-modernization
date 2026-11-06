-- Termination package by JimpleLean's session: TermT4/BinWRows.lean (sha256 b4d48858fdb6bec6...); the module root and ac65118's bwi16 names renamed.
import EquivLean.Demo.Thrift.Java.Term.BinWTotal

/-!
# Thrift → Java (T4): the binary writers' E theorems, total

Each E theorem of `BinW.lean` with termination: `writeI16(x)` / `writeI32(x)` / `writeI64(x)`
terminates on the theorem's premises, and every run ends as the theorem states. Premise: the
transport's class is concrete (`BConc`), as for `bwi16_total` / `wi32_total` / `wi64_total`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- **E for binary i16, total.** -/
theorem wi16_E_total {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hBP : BPAt P R σ p t tmp) (x : I32) (hc : BConc P [.ref p, .int x] σ) :
    (∃ o, MExec P bwi16Ref [.ref p, .int x] σ o) ∧ ∀ o, MExec P bwi16Ref [.ref p, .int x] σ o →
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ Spec.beI16 x.toInt ∧
      R.src σ' t = R.src σ t ∧ BPAt P R σ' p t tmp :=
  ⟨(bwi16_term R hF hV hT [.ref p, .int x] σ ⟨p, t, tmp, x, rfl, hBP⟩ hc).run,
    fun _ hm => wi16_E hF hV hBP x hm⟩

/-- **E for binary i32, total.** -/
theorem wi32_E_total {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hBP : BPAt P R σ p t tmp) (x : I32) (hc : BConc P [.ref p, .int x] σ) :
    (∃ o, MExec P wi32Ref [.ref p, .int x] σ o) ∧ ∀ o, MExec P wi32Ref [.ref p, .int x] σ o →
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ Spec.beI32 x.toInt ∧
      R.src σ' t = R.src σ t ∧ BPAt P R σ' p t tmp :=
  ⟨(wi32_term R hF hV hT [.ref p, .int x] σ ⟨p, t, tmp, x, rfl, hBP⟩ hc).run,
    fun _ hm => wi32_E hF hV hBP x hm⟩

/-- **E for binary i64, total.** -/
theorem wi64_E_total {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hBP : BPAt P R σ p t tmp) (x : I64) (hc : BConc P [.ref p, .long x] σ) :
    (∃ o, MExec P wi64Ref [.ref p, .long x] σ o) ∧ ∀ o, MExec P wi64Ref [.ref p, .long x] σ o →
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ Spec.beI64 x.toInt ∧
      R.src σ' t = R.src σ t ∧ BPAt P R σ' p t tmp :=
  ⟨(wi64_term R hF hV hT [.ref p, .long x] σ ⟨p, t, tmp, x, rfl, hBP⟩ hc).run,
    fun _ hm => wi64_E hF hV hBP x hm⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.wi16_E_total
#print axioms EquivLean.Demo.Thrift.Java.wi32_E_total
#print axioms EquivLean.Demo.Thrift.Java.wi64_E_total
