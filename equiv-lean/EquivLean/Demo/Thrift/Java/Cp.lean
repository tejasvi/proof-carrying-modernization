import EquivLean.Demo.Thrift.Java.Tr
import EquivLean.Demo.Thrift.Spec

/-!
# Thrift → Java (T4): the compact protocol object

`CPAt P R σ p t tmp`: `p` is a `TCompactProtocol` over the transport object `t` (of a program class
below `TTransport`, a working transport for `R`), with its scratch array `temp = tmp`; `p` and
`tmp` are not objects of the transport.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev cpC := EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol»
abbrev tpC := EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TProtocol»
abbrev ttC := EquivLean.Gen.ThriftJ.«org.apache.thrift.transport.TTransport»

def cpCls : ClassName := "org.apache.thrift.protocol.TCompactProtocol"
def tpCls : ClassName := "org.apache.thrift.protocol.TProtocol"

/-- A compact protocol object `p` over the transport object `t`, with its scratch array `tmp`. -/
def CPAt (P : Program) (R : TRep) (σ : State) (p t tmp : Addr) : Prop :=
  ∃ fs xs c fst, σ.heap p = some (.plain cpCls fs) ∧
    Fields.get fs (tpCls, "trans_") = some (.ref t) ∧
    Fields.get fs (cpCls, "temp") = some (.ref tmp) ∧
    σ.heap tmp = some (.array (.prim .byte) xs) ∧ xs.length = 16 ∧
    σ.heap t = some (.plain c fst) ∧ P.isProgClass c = true ∧ P.isSubclass c ttCls = some true ∧
    R.inv σ t ∧ p ≠ t ∧ tmp ≠ t ∧ p ≠ tmp ∧ ¬ R.owns σ t p ∧ ¬ R.owns σ t tmp

/-- A folded copy of `CPAt` (kept as a hypothesis through the symbolic execution). -/
def CPAtH (P : Program) (R : TRep) (σ : State) (p t tmp : Addr) : Prop := CPAt P R σ p t tmp

attribute [irreducible] CPAtH

theorem CPAtH.intro {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} (h : CPAt P R σ p t tmp) :
    CPAtH P R σ p t tmp := by unfold CPAtH; exact h

theorem CPAtH.elim {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} (h : CPAtH P R σ p t tmp) :
    CPAt P R σ p t tmp := by unfold CPAtH at h; exact h

/-- A protocol call changed only the scratch array, the transport object and its objects. -/
def PFrame (R : TRep) (σ σ' : State) (t tmp : Addr) : Prop :=
  σ.next ≤ σ'.next ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
  (∀ a, a < σ.next → a ≠ t → a ≠ tmp → ¬ R.owns σ t a → σ'.heap a = σ.heap a)

/-- The representation of `t` in a state that differs from `σ0` only at the scratch array. -/
theorem rep_scratch (R : TRep) {σ0 σ : State} {t tmp : Addr} (hinv : R.inv σ0 t)
    (heq : ∀ a, a ≠ tmp → σ.heap a = σ0.heap a) (hnext : σ0.next ≤ σ.next) (ht : tmp ≠ t)
    (ho : ¬ R.owns σ0 t tmp) :
    R.inv σ t ∧ R.sink σ t = R.sink σ0 t ∧ R.src σ t = R.src σ0 t ∧ R.bufArr σ t = R.bufArr σ0 t ∧
      R.bufPos σ t = R.bufPos σ0 t ∧ R.bufLen σ t = R.bufLen σ0 t ∧
      (∀ b, R.owns σ t b ↔ R.owns σ0 t b) := by
  apply R.local_ σ0 σ t hinv (heq t (Ne.symm ht)) _ hnext
  intro b hb
  exact heq b (fun e => ho (e ▸ hb))

/-- `CPAt` after a change of the scratch array only. -/
theorem cpAt_scratch {P : Program} {R : TRep} {σ0 σ : State} {p t tmp : Addr} {xs : List Value}
    (h : CPAt P R σ0 p t tmp) (heq : ∀ a, a ≠ tmp → σ.heap a = σ0.heap a)
    (hnext : σ0.next ≤ σ.next) (htmp : σ.heap tmp = some (.array (.prim .byte) xs))
    (hlen : xs.length = 16) : CPAt P R σ p t tmp := by
  obtain ⟨fs, xs0, c, fst, hp, htr, hte, htm, hl, ht, hc1, hc2, hinv, hpt, htt, hptm, hop, hot⟩ := h
  obtain ⟨hinv', -, -, -, -, -, how⟩ := rep_scratch R hinv heq hnext htt hot
  refine ⟨fs, xs, c, fst, by rw [heq p hptm]; exact hp, htr, hte, htmp, hlen,
    by rw [heq t (Ne.symm htt)]; exact ht, hc1, hc2, hinv', hpt, htt, hptm, ?_, ?_⟩
  · rw [how]; exact hop
  · rw [how]; exact hot

/-- `CPAt` after a transport call (`t`'s objects and `t` changed, `t` kept its class). -/
theorem cpAt_call {P : Program} {R : TRep} {σ σ' : State} {p t tmp x : Addr}
    (h : CPAt P R σ p t tmp) (hf : TFrame R σ σ' t x) (hinv : R.inv σ' t)
    (hp : p ≠ x) (htm : tmp ≠ x) : CPAt P R σ' p t tmp ∧
      (∀ a, a < σ.next → a ≠ t → ¬ R.owns σ t a → a ≠ x → σ'.heap a = σ.heap a) := by
  obtain ⟨fs, xs, c, fst, hph, htr, hte, htmh, hl, hth, hc1, hc2, hinv0, hpt, htt, hptm, hop, hot⟩ := h
  obtain ⟨hn, -, -, hheap, how, hcls⟩ := hf
  have hplt : p < σ.next := State.lt_next_of_heap hph
  have htlt : tmp < σ.next := State.lt_next_of_heap htmh
  obtain ⟨fst', hth'⟩ := hcls c fst hth
  refine ⟨⟨fs, xs, c, fst', by rw [hheap p hplt hpt hop hp]; exact hph, htr, hte,
    by rw [hheap tmp htlt htt hot htm]; exact htmh, hl, hth', hc1, hc2, hinv, hpt, htt, hptm,
    how p hplt hop, how tmp htlt hot⟩, hheap⟩

/-- The protocol object determines its transport and scratch array. -/
theorem cpAt_uniq {P : Program} {R : TRep} {σ : State} {p t tmp t' tmp' : Addr}
    (h : CPAt P R σ p t tmp) (h' : CPAt P R σ p t' tmp') : t' = t ∧ tmp' = tmp := by
  obtain ⟨fs, -, -, -, hp, htr, hte, -⟩ := h
  obtain ⟨fs', -, -, -, hp', htr', hte', -⟩ := h'
  rw [hp] at hp'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp'
  subst hp'
  rw [htr] at htr'
  rw [hte] at hte'
  simp only [Option.some.injEq, Value.ref.injEq] at htr' hte'
  exact ⟨htr'.symm, hte'.symm⟩

theorem setObj_heap_ne {σ : State} {a b : Addr} {o : Obj} (h : b ≠ a) :
    (σ.setObj a o).heap b = σ.heap b := by
  rw [State.heap_setObj, if_neg h]

theorem setObj_heap_self {σ : State} {a : Addr} {o : Obj} (h : a < σ.next) :
    (σ.setObj a o).heap a = some o := by
  rw [State.heap_setObj_of_lt h, if_pos rfl]

end EquivLean.Demo.Thrift.Java
