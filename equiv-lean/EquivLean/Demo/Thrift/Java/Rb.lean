import EquivLean.Demo.Thrift.Java.Lem
import EquivLean.Demo.Thrift.Java.TrL

/-!
# Thrift → Java (T4): `TCompactProtocol.readByte()` reads the next byte

The buffer fast path (`getBytesRemainingInBuffer() > 0`: the byte at `getBufferPosition()` in
`getBuffer()`, then `consumeBuffer(1)`) or `readAll(temp, 0, 1)`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev rbRef : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«readByte()».ref

/-- `t` takes over no object that existed and that it did not use. -/
def OwnsMono (R : TRep) (σ σ' : State) (t : Addr) : Prop :=
  ∀ a, a < σ.next → ¬ R.owns σ t a → ¬ R.owns σ' t a

/-- What `readByte()` guarantees: the next byte, consumed. -/
def rbN (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr), args = [.ref p] → CPAt P R σ p t tmp →
    ∃ u rest, R.src σ t = u :: rest ∧ r = some (jbyte u) ∧ R.src σ' t = rest ∧
      R.sink σ' t = R.sink σ t ∧ CPAt P R σ' p t tmp ∧ PFrame R σ σ' t tmp ∧ OwnsMono R σ σ' t

/-- `readByte()` on an empty source: a `TTransportException`. -/
def rbE (P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p t tmp : Addr), args = [.ref p] → CPAt P R σ p t tmp →
    R.src σ t = [] ∧ (∃ fs, σ'.heap e = some (.plain ttExcCls fs))

attribute [irreducible] rbN rbE

def rbSpec (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr), args = [.ref p] ∧ CPAt P R σ p t tmp)
  (rbN P R) (rbE P R)

def rbSpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr), args = [.ref p] ∧ CPAt P R σ p t tmp ∧ CPAtH P R σ p t tmp ∧
     ClassOK P σ t)
  (rbN P R) (rbE P R)

/-! ## The closers of `rb_body` -/

/-- The call `readAll(temp, 0, 1)`: its precondition. -/
theorem rb_readAll_pre (R : TRep) {σ : State} {t tmp : Addr} {xs : List Value}
    (hinv : R.inv σ t) (htmp : σ.heap tmp = some (.array (.prim .byte) xs)) (hlen : xs.length = 16)
    (ht : tmp ≠ t) (ho : ¬ R.owns σ t tmp) :
    ∃ t' buf off len, (t = t' ∧ tmp = buf ∧ (0#32 : I32) = off ∧ (1#32 : I32) = len) ∧ R.inv σ t' ∧
      ∃ x, σ.heap buf = some (.array (.prim .byte) x) ∧ 0 ≤ BitVec.toInt off ∧ 0 ≤ BitVec.toInt len ∧
        BitVec.toInt off + BitVec.toInt len ≤ (x.length : Int) ∧ ¬buf = t' ∧ ¬R.owns σ t' buf :=
  ⟨t, tmp, 0#32, 1#32, ⟨rfl, rfl, rfl, rfl⟩, hinv, xs, htmp, by decide, by decide,
    by rw [hlen]; decide, ht, ho⟩

/-- A non-empty source. -/
theorem src_cons_of_len {bs : Bytes} {n : Nat} (h : 1 ≤ n) (hn : n ≤ bs.length) :
    ∃ u rest, bs = u :: rest := by
  cases bs with
  | nil => simp only [List.length_nil] at hn; omega
  | cons u rest => exact ⟨u, rest, rfl⟩

/-- The buffer's first byte is the source's first byte. -/
theorem buf_head {arr : List Value} {pos n : Nat} {u : UInt8} {rest : Bytes}
    (h : (arr.drop pos).take n = ((u :: rest).map jbyte).take n) (hn : 0 < n) (hp : pos < arr.length) :
    arr[pos] = jbyte u := by
  have h1 := congrArg List.head? h
  rw [List.head?_take, List.head?_take, if_neg (by omega), if_neg (by omega), List.head?_drop,
    List.getElem?_eq_getElem hp] at h1
  simpa using h1

/-- `readAll` threw: the source was empty. -/
theorem rb_exc_post {P : Program} {R : TRep} {σ σ' : State} {p t tmp e : Addr}
    {w : List (FieldKey × Value)} (hCP : CPAtH P R σ p t tmp)
    (hlen : (R.src σ t).length < (1#32 : I32).toNat) (he : σ'.heap e = some (.plain ttExcCls w)) :
    rbE P R [.ref p] σ e σ' := by
  have hC := CPAtH.elim hCP
  unfold rbE
  intro p' t' tmp' hargs hCP'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := cpAt_uniq hCP' hC
  have h1 : (1#32 : I32).toNat = 1 := rfl
  rw [h1] at hlen
  exact ⟨List.eq_nil_of_length_eq_zero (by omega), w, he⟩

/-- `readAll` filled `temp[0]`: the byte read is the source's first byte. -/
theorem rb_slow_post {P : Program} {R : TRep} {σ σ' : State} {p t tmp : Addr}
    {xs : List Value} {c : ClassName} {fst w : List (FieldKey × Value)}
    (hCP : CPAtH P R σ p t tmp)
    (hlen1 : (1#32 : I32).toNat ≤ (R.src σ t).length)
    (hinv' : R.inv σ' t)
    (htmp' : σ'.heap tmp = some (.array (.prim .byte)
        (List.take (0#32 : I32).toNat xs ++
          (List.take (1#32 : I32).toNat (List.map jbyte (R.src σ t)) ++ List.drop 1 xs))))
    (htmp : σ.heap tmp = some (.array (.prim .byte) xs))
    (hsrc : R.src σ' t = List.drop (1#32 : I32).toNat (R.src σ t))
    (hsink : R.sink σ' t = R.sink σ t)
    (hnext : σ.next ≤ σ'.next) (hin : σ'.inits = σ.inits) (hst : σ'.statics = σ.statics)
    (hfr : ∀ a, a < σ.next → ¬a = t → ¬R.owns σ t a → ¬a = tmp → σ'.heap a = σ.heap a)
    (hown : ∀ a, a < σ.next → ¬R.owns σ t a → ¬R.owns σ' t a)
    (ht : σ.heap t = some (.plain c fst))
    (ht' : σ'.heap t = some (.plain c w)) :
    rbN P R [.ref p] σ (some (jbyte ((R.src σ t)[0]'(by
      have : (1#32 : I32).toNat = 1 := rfl; omega)))) σ' := by
  have hC := CPAtH.elim hCP
  obtain ⟨fs, xs0, c0, fst0, hph, htr, hte, htmh, hl, hth, hc1, hc2, hinv0, hpt, htt, hptm, hop, hot⟩ :=
    CPAtH.elim hCP
  have hplt : p < σ.next := State.lt_next_of_heap hph
  have htlt : tmp < σ.next := State.lt_next_of_heap htmh
  have hpe : σ'.heap p = σ.heap p := hfr p hplt hpt hop hptm
  rw [htmh] at htmp
  simp only [Option.some.injEq, Obj.array.injEq, true_and] at htmp
  subst htmp
  obtain ⟨u, rest, hsrc0⟩ := src_cons_of_len (by decide) hlen1
  have hget : ∀ (l : Bytes) (h : 0 < l.length), l = u :: rest → l[0]'h = u := by
    intro l h e; subst e; rfl
  unfold rbN
  intro p' t' tmp' hargs hCP'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := cpAt_uniq hCP' hC
  rw [hth] at ht
  simp only [Option.some.injEq, Obj.plain.injEq] at ht
  obtain ⟨rfl, -⟩ := ht
  refine ⟨u, rest, hsrc0, by rw [hget _ _ hsrc0], by rw [hsrc, hsrc0]; rfl, hsink, ?_, ?_, hown⟩
  · -- the scratch array `temp` after `readAll`
    have hx : ∀ (ys : List Value), ys.length = 16 →
        (List.take (0#32 : I32).toNat ys ++
          (List.take (1#32 : I32).toNat (List.map jbyte (u :: rest)) ++ List.drop 1 ys)).length = 16 := by
      intro ys hys
      simp only [show (0#32 : I32).toNat = 0 from rfl, show (1#32 : I32).toNat = 1 from rfl,
        List.take_zero, List.nil_append, List.map_cons, List.take_succ_cons, List.take_zero,
        List.singleton_append, List.length_cons, List.length_drop, hys]
    rw [hsrc0] at htmp'
    exact ⟨fs, _, c0, w, by rw [hpe]; exact hph, htr, hte, htmp', hx xs0 hl, ht', hc1, hc2, hinv',
      hpt, htt, hptm, hown p hplt hop, hown tmp htlt hot⟩
  · exact ⟨hnext, hin, hst, fun a ha hat hatm hao => hfr a ha hat hao hatm⟩

/-- The buffer fast path: the byte at the buffer position is the source's first byte. -/
theorem rb_fast_post {P : Program} {R : TRep} {σ σ' : State} {p t tmp : Addr}
    {u : UInt8} {c : ClassName} {fst w : List (FieldKey × Value)}
    (hCP : CPAtH P R σ p t tmp)
    (hinv' : R.inv σ' t)
    (hsink : R.sink σ' t = R.sink σ t)
    (hnext : σ'.next = σ.next) (hin : σ'.inits = σ.inits) (hst : σ'.statics = σ.statics)
    (hfr : ∀ a, ¬a = t → σ'.heap a = σ.heap a)
    (hown : ∀ a, R.owns σ' t a ↔ R.owns σ t a)
    (ht : σ.heap t = some (.plain c fst))
    (ht' : σ'.heap t = some (.plain c w))
    (hsrc : R.src σ t = u :: R.src σ' t) :
    rbN P R [.ref p] σ (some (jbyte u)) σ' := by
  have hC := CPAtH.elim hCP
  obtain ⟨fs, xs0, c0, fst0, hph, htr, hte, htmh, hl, hth, hc1, hc2, hinv0, hpt, htt, hptm, hop, hot⟩ :=
    CPAtH.elim hCP
  rw [hth] at ht
  simp only [Option.some.injEq, Obj.plain.injEq] at ht
  obtain ⟨rfl, -⟩ := ht
  unfold rbN
  intro p' t' tmp' hargs hCP'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨rfl, rfl⟩ := cpAt_uniq hCP' hC
  refine ⟨u, R.src σ' t, hsrc, rfl, rfl, hsink, ?_, ?_, fun a _ h => by rw [hown]; exact h⟩
  · exact ⟨fs, xs0, c0, w, by rw [hfr p hpt]; exact hph, htr, hte, by rw [hfr tmp htt]; exact htmh,
      hl, ht', hc1, hc2, hinv', hpt, htt, hptm, by rw [hown]; exact hop, by rw [hown]; exact hot⟩
  · exact ⟨Nat.le_of_eq hnext.symm, hin, hst, fun a _ hat _ _ => hfr a hat⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rb_body (R : TRep) : BodyVCP (Contains · [cpC, tpC, ttC]) (fun _ => (tContracts R).env) 0
    rbRef (fun P => rbSpecI P R) [] 60 := by
  jverify_body [Contains, CPAt, ClassOK, rbSpecI, tc_write, tc_readAll, tc_getBytesRemainingInBuffer,
    tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer, tc_checkReadBytesAvailable, BufView, TFrame,
    List.getElem?_eq_getElem, List.cons_append, List.nil_append, List.getElem?_cons_zero,
    List.getElem_cons_zero, getElem?_zero_of_one32, ttCls, cpCls, tpCls]
  case some.true.normal.isTrue.left => exact rb_readAll_pre R ‹_› ‹_› ‹_› ‹_› ‹_›
  case some.true.normal.isTrue.right.normal =>
    exact rb_slow_post ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case some.true.normal.isTrue.right.exc => exact rb_exc_post ‹_› ‹_› ‹_›
  case some.true.normal.isFalse.right.normal.right.normal.right.normal =>
    exact rb_fast_post ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

end EquivLean.Demo.Thrift.Java
