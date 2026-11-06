-- Termination package by JimpleLean's session: TermT4/BinRRows.lean (sha256 3e03182d9c380818...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.BinRTotal

/-!
# Thrift → Java (T4): the binary readers' D and M theorems (i16, i32), total

Each D/M theorem of `BinR.lean` with termination: `readI16()` / `readI32()` terminates on the
theorem's premises, and every run ends as the theorem states. Premise: the transport's class is
concrete (`BConc`), as for `ri16_total` / `ri32_total`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem ri16_term_at {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hBP : BPAt P R σ p t tmp) (hc : BConc P [.ref p] σ) : MTerm P ri16Ref [.ref p] σ :=
  ri16_term R hF hV hT [.ref p] σ ⟨p, t, tmp, rfl, hBP⟩ hc

/-- **D for binary i16, total.** -/
theorem ri16_D_total {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hBP : BPAt P R σ p t tmp) (v : Int) (hv : Spec.InI16 v) (rest : Spec.Bytes)
    (hsrc : R.src σ t = Spec.beI16 v ++ rest) (hc : BConc P [.ref p] σ) :
    (∃ o, MExec P ri16Ref [.ref p] σ o) ∧ ∀ o, MExec P ri16Ref [.ref p] σ o →
    ∃ σ', o = .normal (some (.int (BitVec.ofInt 32 v))) σ' ∧ R.src σ' t = rest ∧
      R.sink σ' t = R.sink σ t ∧ BPAt P R σ' p t tmp :=
  ⟨(ri16_term_at hF hV hT hBP hc).run, fun _ hm => ri16_D hF hV hBP v hv rest hsrc hm⟩

/-- **M for binary i16 (fewer than two bytes), total.** -/
theorem ri16_M_total {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hBP : BPAt P R σ p t tmp) (hshort : (R.src σ t).length < 2) (hc : BConc P [.ref p] σ) :
    (∃ o, MExec P ri16Ref [.ref p] σ o) ∧ ∀ o, MExec P ri16Ref [.ref p] σ o →
    ∃ e σ', o = .exc e σ' ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs) :=
  ⟨(ri16_term_at hF hV hT hBP hc).run, fun _ hm => ri16_M hF hV hBP hshort hm⟩

theorem ri32_term_at {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hBP : BPAt P R σ p t tmp) (hc : BConc P [.ref p] σ) : MTerm P ri32Ref [.ref p] σ :=
  ri32_term R hF hV hT [.ref p] σ ⟨p, t, tmp, rfl, hBP⟩ hc

/-- **D for binary i32, total.** -/
theorem ri32_D_total {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hBP : BPAt P R σ p t tmp) (v : Int) (hv : Spec.InI32 v) (rest : Spec.Bytes)
    (hsrc : R.src σ t = Spec.beI32 v ++ rest) (hc : BConc P [.ref p] σ) :
    (∃ o, MExec P ri32Ref [.ref p] σ o) ∧ ∀ o, MExec P ri32Ref [.ref p] σ o →
    ∃ σ', o = .normal (some (.int (BitVec.ofInt 32 v))) σ' ∧ R.src σ' t = rest ∧
      R.sink σ' t = R.sink σ t ∧ BPAt P R σ' p t tmp :=
  ⟨(ri32_term_at hF hV hT hBP hc).run, fun _ hm => ri32_D hF hV hBP v hv rest hsrc hm⟩

/-- **M for binary i32 (fewer than four bytes), total.** -/
theorem ri32_M_total {P : Program} {R : TRep} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) {σ : State} {p t tmp : Addr}
    (hBP : BPAt P R σ p t tmp) (hshort : (R.src σ t).length < 4) (hc : BConc P [.ref p] σ) :
    (∃ o, MExec P ri32Ref [.ref p] σ o) ∧ ∀ o, MExec P ri32Ref [.ref p] σ o →
    ∃ e σ', o = .exc e σ' ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs) :=
  ⟨(ri32_term_at hF hV hT hBP hc).run, fun _ hm => ri32_M hF hV hBP hshort hm⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.ri16_D_total
#print axioms EquivLean.Demo.Thrift.Java.ri16_M_total
#print axioms EquivLean.Demo.Thrift.Java.ri32_D_total
#print axioms EquivLean.Demo.Thrift.Java.ri32_M_total
