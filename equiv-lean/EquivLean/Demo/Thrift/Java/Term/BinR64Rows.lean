-- Termination package by JimpleLean's session: TermT4/BinR64Rows.lean (sha256 4dff958e11b2388b...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.BinR64Total

/-!
# Thrift → Java (T4): the binary reader's D and M theorems (i64), total

Each D/M theorem of `BinR64.lean` with termination: `readI64()` terminates on the theorem's premises,
and every run ends as the theorem states. Premise: the transport's class is concrete (`BConc`), as for
`ri64_total`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem ri64_term_at {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hBP : BPAt P R σ p t tmp) (hc : BConc P [.ref p] σ) : MTerm P ri64Ref [.ref p] σ :=
  ri64_term R hF hV hT [.ref p] σ ⟨p, t, tmp, rfl, hBP⟩ hc

/-- **D for binary i64, total.** -/
theorem ri64_D_total {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hBP : BPAt P R σ p t tmp) (v : Int) (hv : Spec.InI64 v) (rest : Spec.Bytes)
    (hsrc : R.src σ t = Spec.beI64 v ++ rest) (hc : BConc P [.ref p] σ) :
    (∃ o, MExec P ri64Ref [.ref p] σ o) ∧ ∀ o, MExec P ri64Ref [.ref p] σ o →
    ∃ σ', o = .normal (some (.long (BitVec.ofInt 64 v))) σ' ∧ R.src σ' t = rest ∧
      R.sink σ' t = R.sink σ t ∧ BPAt P R σ' p t tmp :=
  ⟨(ri64_term_at hF hV hT hBP hc).run, fun _ hm => ri64_D hF hV hBP v hv rest hsrc hm⟩

/-- **M for binary i64 (fewer than eight bytes), total.** -/
theorem ri64_M_total {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hBP : BPAt P R σ p t tmp) (hshort : (R.src σ t).length < 8) (hc : BConc P [.ref p] σ) :
    (∃ o, MExec P ri64Ref [.ref p] σ o) ∧ ∀ o, MExec P ri64Ref [.ref p] σ o →
    ∃ e σ', o = .exc e σ' ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs) :=
  ⟨(ri64_term_at hF hV hT hBP hc).run, fun _ hm => ri64_M hF hV hBP hshort hm⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.ri64_D_total
#print axioms EquivLean.Demo.Thrift.Java.ri64_M_total
