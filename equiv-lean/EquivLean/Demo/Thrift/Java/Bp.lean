import EquivLean.Demo.Thrift.Java.Lem
import EquivLean.Demo.Thrift.Java.TrL

/-!
# Thrift → Java (T4): the binary protocol object

`BPAt P R σ p t tmp`: `p` is a `TBinaryProtocol` over the transport object `t` (of a program class
below `TTransport`, a working transport for `R`), with its scratch array `inoutTemp = tmp` (16
bytes); `p` and `tmp` are not objects of the transport. As `CPAt` for the compact protocol.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev bpC := EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TBinaryProtocol»

def bpCls : ClassName := "org.apache.thrift.protocol.TBinaryProtocol"

/-- A binary protocol object `p` over the transport object `t`, with its scratch array `tmp`. -/
def BPAt (P : Program) (R : TRep) (σ : State) (p t tmp : Addr) : Prop :=
  ∃ fs xs c fst, σ.heap p = some (.plain bpCls fs) ∧
    Fields.get fs (tpCls, "trans_") = some (.ref t) ∧
    Fields.get fs (bpCls, "inoutTemp") = some (.ref tmp) ∧
    σ.heap tmp = some (.array (.prim .byte) xs) ∧ xs.length = 16 ∧
    σ.heap t = some (.plain c fst) ∧ P.isProgClass c = true ∧ P.isSubclass c ttCls = some true ∧
    R.inv σ t ∧ p ≠ t ∧ tmp ≠ t ∧ p ≠ tmp ∧ ¬ R.owns σ t p ∧ ¬ R.owns σ t tmp

/-- A folded copy of `BPAt` (kept as a hypothesis through the symbolic execution). -/
def BPAtH (P : Program) (R : TRep) (σ : State) (p t tmp : Addr) : Prop := BPAt P R σ p t tmp

attribute [irreducible] BPAtH

theorem BPAtH.intro {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} (h : BPAt P R σ p t tmp) :
    BPAtH P R σ p t tmp := by unfold BPAtH; exact h

theorem BPAtH.elim {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} (h : BPAtH P R σ p t tmp) :
    BPAt P R σ p t tmp := by unfold BPAtH at h; exact h

/-- `BPAt` after a change of the scratch array only. -/
theorem bpAt_scratch {P : Program} {R : TRep} {σ0 σ : State} {p t tmp : Addr} {xs : List Value}
    (h : BPAt P R σ0 p t tmp) (heq : ∀ a, a ≠ tmp → σ.heap a = σ0.heap a)
    (hnext : σ0.next ≤ σ.next) (htmp : σ.heap tmp = some (.array (.prim .byte) xs))
    (hlen : xs.length = 16) : BPAt P R σ p t tmp := by
  obtain ⟨fs, xs0, c, fst, hp, htr, hte, htm, hl, ht, hc1, hc2, hinv, hpt, htt, hptm, hop, hot⟩ := h
  obtain ⟨hinv', -, -, -, -, -, how⟩ := rep_scratch R hinv heq hnext htt hot
  refine ⟨fs, xs, c, fst, by rw [heq p hptm]; exact hp, htr, hte, htmp, hlen,
    by rw [heq t (Ne.symm htt)]; exact ht, hc1, hc2, hinv', hpt, htt, hptm, ?_, ?_⟩
  · rw [how]; exact hop
  · rw [how]; exact hot

/-- `BPAt` after a transport call (`t`'s objects and `t` changed, `t` kept its class). -/
theorem bpAt_call {P : Program} {R : TRep} {σ σ' : State} {p t tmp x : Addr}
    (h : BPAt P R σ p t tmp) (hf : TFrame R σ σ' t x) (hinv : R.inv σ' t)
    (hp : p ≠ x) (htm : tmp ≠ x) : BPAt P R σ' p t tmp ∧
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
theorem bpAt_uniq {P : Program} {R : TRep} {σ : State} {p t tmp t' tmp' : Addr}
    (h : BPAt P R σ p t tmp) (h' : BPAt P R σ p t' tmp') : t' = t ∧ tmp' = tmp := by
  obtain ⟨fs, -, -, -, hp, htr, hte, -⟩ := h
  obtain ⟨fs', -, -, -, hp', htr', hte', -⟩ := h'
  rw [hp] at hp'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp'
  subst hp'
  rw [htr] at htr'
  rw [hte] at hte'
  simp only [Option.some.injEq, Value.ref.injEq] at htr' hte'
  exact ⟨htr'.symm, hte'.symm⟩

theorem classOK_of_bpAt {P : Program} {R : TRep} {σ : State} {p t tmp : Addr}
    (h : BPAt P R σ p t tmp) : ClassOK P σ t := by
  obtain ⟨-, -, c, fst, -, -, -, -, -, ht, hc, -⟩ := h
  unfold Program.isProgClass at hc
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hc
  exact ⟨c, fst, d, ht, hd⟩

end EquivLean.Demo.Thrift.Java
