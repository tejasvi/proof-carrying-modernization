-- Termination package by JimpleLean's session: TermT4/RlbAll.lean (sha256 ac9a485ed52115d8...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.RlbP
import EquivLean.Demo.Thrift.Java.Term.GttAll

/-!
# Thrift → Java (T4): `readListBegin()` on every header byte

`rlb_body`'s contract (`rlbSpecI`) asks for a known element-type nibble (`NibbleOKL`), because
`getTType`'s contract does. Against `getTType`'s contract on every nibble (`gttSpecAll`, `Γ6All`),
`readListBegin()` is verified without it (`rlbSpecAll`): with a valid size, an element nibble 14 or 15 makes it
throw the `TProtocolException` of `getTType` (`rlbBadCase`); otherwise it behaves as `rlb_body` states. The
invariant is `rlb_body`'s without the nibble fact (`rlbInvAll`); the closers are `rlb_body`'s, two of them
restated without that fact. New names only.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The contracts `readListBegin()` uses, with `getTType`'s on every nibble. -/
def Γ6All (P : Program) (R : TRep) : SpecEnv := fun sig =>
  if sig = rbSig then some (rbSpecA P R)
  else if sig = gttSig then some gttSpecAll
  else if sig = ccrlSig then some ccrlSpec
  else if sig = crbaSig then some (crbaSpec P R)
  else Γ2 P R sig

/-- A valid size and an element nibble without TType: `getTType`'s `TProtocolException`. -/
def rlbBadCase (R : TRep) (σ : State) (t : Addr) (lim : I64) (e : Addr) (σ' : State) : Prop :=
  ∃ u rest size rest', R.src σ t = u :: rest ∧ listSizeJ u rest = some (size, rest') ∧ 0 ≤ size.toInt ∧
    InLimit lim size ∧ Spec.ttypeOfCompact (u.toNat % 16) = none ∧
    ∃ fs, σ'.heap e = some (.plain tpeCls fs)

/-- When `readListBegin()` throws, on every header byte: `rlbE`'s cases, or `rlbBadCase`. -/
def rlbEAll (P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (lim : I64), args = [.ref p] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim) →
    rlbE P R args σ e σ' ∨ rlbBadCase R σ t lim e σ'

attribute [irreducible] rlbBadCase rlbEAll

/-- `rlbSpecI` without `NibbleOKL`: the exceptions are `rlbEAll`. -/
def rlbSpecAll (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (lim : I64), args = [.ref p] ∧ CPAt P R σ p t tmp ∧
     CPAtH P R σ p t tmp ∧ LimitAt σ p lim ∧ σ.initOf tpeCls = .done ∧ σ.initOf tlCls = .done ∧
     σ.initOf ttExcCls = .done)
  (rlbN P R) (rlbEAll P R)

/-- `rlbInv` without the nibble fact. -/
def rlbInvAll (P : Program) (R : TRep) : Invariants :=
  [(2, fun args σ0 fr σ =>
    ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (lim : I64), args = [.ref p] →
    σ0.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim) →
    ∃ u : UInt8, R.src σ0 t = u :: R.src σ t ∧
      fr.get 3 = some (.ref p) ∧ fr.get 1 = some (jbyte u) ∧
      σ.heap p = some (.plain cpCls fs) ∧ CPAtH P R σ p t tmp ∧
      R.sink σ t = R.sink σ0 t ∧ σ0.next ≤ σ.next ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
      (∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬ R.owns σ0 t a → σ.heap a = σ0.heap a) ∧
      OwnsMono R σ0 σ t),
   (7, fun args σ0 fr σ =>
    ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (lim : I64), args = [.ref p] →
    σ0.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim) →
    ∃ (u : UInt8) (rest : Bytes) (size : I32), R.src σ0 t = u :: rest ∧
      listSizeJ u rest = some (size, R.src σ t) ∧
      fr.get 3 = some (.ref p) ∧ fr.get 1 = some (jbyte u) ∧ fr.get 2 = some (.int size) ∧
      σ.heap p = some (.plain cpCls fs) ∧ CPAtH P R σ p t tmp ∧
      R.sink σ t = R.sink σ0 t ∧ σ0.next ≤ σ.next ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
      (∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬ R.owns σ0 t a → σ.heap a = σ0.heap a) ∧
      OwnsMono R σ0 σ t)]

theorem rlbEAll_of_rlbE {P : Program} {R : TRep} {args : List Value} {σ σ' : State} {e : Addr}
    (h : rlbE P R args σ e σ') : rlbEAll P R args σ e σ' := by
  unfold rlbEAll
  intro _ _ _ _ _ _ _ _ _ _
  exact Or.inl h

/-- The cut at statement 7 from the short form (`rlb_cut7_short` without the nibble fact). -/
theorem rlb_cut7_shortAll {R : TRep} {σ0 σ : State} {t tmp : Addr} {u : UInt8}
    (hcond : ¬ JInt.shr (BitVec.signExtend 32 u.toBitVec) 4#32 &&& 15#32 = 15#32)
    (hh : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬R.owns σ0 t a → σ.heap a = σ0.heap a) :
    ∃ u' rest, (u = u' ∧ R.src σ t = rest) ∧ ∃ x, listSizeJ u' rest = some (x, R.src σ t) ∧
      BitVec.signExtend 32 u.toBitVec = BitVec.signExtend 32 u'.toBitVec ∧
      JInt.shr (BitVec.signExtend 32 u.toBitVec) 4#32 &&& 15#32 = x ∧
      ∀ a, a < σ0.next → ¬a = t → ¬a = tmp → ¬R.owns σ0 t a → σ.heap a = σ0.heap a := by
  refine ⟨u, R.src σ t, ⟨rfl, rfl⟩, JInt.shr (BitVec.signExtend 32 u.toBitVec) 4#32 &&& 15#32, ?_,
    rfl, rfl, hh⟩
  rw [listSizeJ_short (hi15_not hcond), shr4_sx]

/-- The cut at statement 7 from the long form (`rlb_cut7_long` without the nibble fact). -/
theorem rlb_cut7_longAll {P : Program} {R : TRep} {σ0 σ1 σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {u : UInt8} {v : Nat}
    (hcond : JInt.shr (BitVec.signExtend 32 u.toBitVec) 4#32 &&& 15#32 = 15#32)
    (hp1 : σ1.heap p = some (.plain cpCls fs)) (hH1 : CPAtH P R σ1 p t tmp)
    (hn1 : σ0.next ≤ σ1.next)
    (hh1 : ∀ a, a < σ0.next → a ≠ t → a ≠ tmp → ¬R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hom1 : OwnsMono R σ0 σ1 t)
    (hrv : Spec.readVarint 5 (R.src σ1 t) = some (v, R.src σ t))
    (hn2 : σ1.next ≤ σ.next)
    (hh2 : ∀ a, a < σ1.next → a ≠ t → a ≠ tmp → ¬R.owns σ1 t a → σ.heap a = σ1.heap a)
    (hom2 : OwnsMono R σ1 σ t) :
    ∃ u' rest, (u = u' ∧ R.src σ1 t = rest) ∧ ∃ x, listSizeJ u' rest = some (x, R.src σ t) ∧
      BitVec.signExtend 32 u.toBitVec = BitVec.signExtend 32 u'.toBitVec ∧ BitVec.ofNat 32 v = x ∧
      σ.heap p = some (.plain cpCls fs) ∧ σ0.next ≤ σ.next ∧
      (∀ a, a < σ0.next → ¬a = t → ¬a = tmp → ¬R.owns σ0 t a → σ.heap a = σ0.heap a) ∧
      OwnsMono R σ0 σ t := by
  refine ⟨u, R.src σ1 t, ⟨rfl, rfl⟩, BitVec.ofNat 32 v, listSizeJ_long (hi15_of hcond) hrv, rfl,
    rfl, heap_p_of_call (CPAtH.elim hH1) hp1 hh2, Nat.le_trans hn1 hn2, ?_, ?_⟩
  · intro a ha hat hatm hao
    rw [hh2 a (Nat.lt_of_lt_of_le ha hn1) hat hatm (hom1 a ha hao), hh1 a ha hat hatm hao]
  · intro a ha hao
    exact hom2 a (Nat.lt_of_lt_of_le ha hn1) (hom1 a ha hao)

/-- `getTType` threw, after a valid size: the element nibble is 14 or 15 (`rlbBadCase`). -/
theorem rlb_gtt_excAll {P : Program} {R : TRep} {σ0 σ σ' : State} {p t tmp e : Addr}
    {fs w : List (FieldKey × Value)} {lim : I64} {u : UInt8} {rest : Bytes} {size : I32}
    (hH0 : CPAtH P R σ0 p t tmp) (hp0 : σ0.heap p = some (.plain cpCls fs))
    (hlim0 : Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim))
    (hsrc0 : R.src σ0 t = u :: rest) (hsz : listSizeJ u rest = some (size, R.src σ t))
    (h0 : 0 ≤ size.toInt) (hin : InLimit lim size)
    (hn : Spec.ttypeOfCompact ((BitVec.signExtend 32 u.toBitVec).toNat % 16) = none)
    (hexc : σ'.heap e = some (.plain tpeCls w)) :
    rlbEAll P R [.ref p] σ0 e σ' := by
  unfold rlbEAll
  intro p' t' tmp' fs' lim' hargs hp htr hte hlim
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  rw [hp0] at hp
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp
  subst hp
  obtain ⟨h1, h2⟩ := cpAt_fields (CPAtH.elim hH0) hp0 htr hte
  subst t' tmp'
  rw [hlim0] at hlim
  simp only [Option.some.injEq, Value.long.injEq] at hlim
  subst hlim
  rw [sx_toNat_mod16] at hn
  refine Or.inr ?_
  unfold rlbBadCase
  exact ⟨u, rest, size, R.src σ t, hsrc0, hsz, h0, hin, hn, w, hexc⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rlbAll_body (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC] →
    MethodVC P (Γ6All P R) 2 rlbRef (rlbSpecAll P R) (rlbInvAll P R) 300 := by
  intro P hF
  jverify [findHandler, Program.subtype, Program.isSubclass, Program.supers, supersN_succ_eq,
    supersFold, Program.fuel, Program.lookup, fieldKey, Program.resolveField, resolveFieldN_succ_eq,
    resolveIfaces, Program.isProgClass, Program.selectStatic, Program.chainN, Program.selectSpecial,
    Program.staticDecl, Targets, Shapes, ShapeIs,
    Contains, CPAt, ClassOK, rlbSpecAll, rlbInvAll, LimitAt, Γ6All, Γ2, rbSig, gttSig, ccrlSig, crbaSig,
    rv32Sig, wv32Sig, Program.selectVirtual, tc_write, tc_readAll, tc_getBytesRemainingInBuffer,
    tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, TFrame,
    PFrame, gttN, gttE, gttSpecAll, ccrlN, ccrlE, crbaN, crbaE, instanceFields_tl, jbyte,
    tlNew, ttCls, cpCls, tpCls, tpeCls, tlCls]
  case left.right.exc => exact rlbEAll_of_rlbE (rlb_rb_exc ‹_› ‹_› ‹_›)
  case right.left.isTrue.left =>
    refine rfb_g6 ‹_› (fun c hc2 => ?_)
    have h := isSub_fold hc2
    rw [supersN_succ_eq] at h
    exact h
  case right.left.isTrue.right.normal =>
    exact rlb_cut7_longAll ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.left.isTrue.right.exc.some => exact rlbEAll_of_rlbE (rlb_rv32_exc ‹_› ‹_› ‹_› ‹_›)
  case right.left.isFalse => exact rlb_cut7_shortAll ‹_› ‹_›
  case right.right.normal.normal.left =>
    exact rlb_crba_pre ‹_› (tl_get_elemType _ _ _) (tl_get_size _ _ _)
  case right.right.normal.normal.right.normal =>
    exact rlb_post ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
      (tl_get_elemType _ _ _) (tl_get_size _ _ _) ‹_›
  case right.right.normal.normal.right.exc =>
    exact rlbEAll_of_rlbE (rlb_crba_exc ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
  case right.right.normal.exc => exact rlb_gtt_excAll ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case right.right.exc => exact rlbEAll_of_rlbE (rlb_ccrl_exc ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)

end EquivLean.Demo.Thrift.Java
