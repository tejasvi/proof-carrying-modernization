-- Termination package by JimpleLean's session: TermT4/RfbAll.lean (sha256 d41a77744486b8e1...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.FhR
import EquivLean.Demo.Thrift.Java.Term.GttAll

/-!
# Thrift → Java (T4): `readFieldBegin()` on every header byte

`rfb_body`'s contract (`rfbSpecI`) asks for a known type nibble (`NibbleOK`), because `getTType`'s contract
does. Against `getTType`'s contract on every nibble (`gttSpecAll`, `Γ3All`), `readFieldBegin()` is verified
without that precondition (`rfbSpecAll`): a header byte `u ≠ 0` with nibble 14 or 15 makes it throw the
`TProtocolException` of `getTType` (`rfbBad`); otherwise it behaves as `rfb_body` states. The invariant
and every closer of `rfb_body` are reused; new names only.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The contracts `readFieldBegin()` uses, with `getTType`'s on every nibble. -/
def Γ3All (P : Program) (R : TRep) : SpecEnv := fun sig =>
  if sig = rbSig then some (rbSpecA P R)
  else if sig = gttSig then some gttSpecAll
  else if sig = rfiSig then some (rfiSpecA P R)
  else Γ2 P R sig

/-- The first byte is a header byte (`≠ 0`) whose type nibble has no TType (14 or 15). -/
def BadNibble (src : Bytes) : Prop :=
  ∃ u rest, src = u :: rest ∧ u.toNat ≠ 0 ∧ Spec.ttypeOfCompact (u.toNat % 16) = none

/-- On a bad nibble, the exception is `getTType`'s `TProtocolException`. -/
def rfbBad (P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)), args = [.ref p] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) → BadNibble (R.src σ t) →
    ∃ fs', σ'.heap e = some (.plain tpeCls fs')

/-- The first byte is not a bad nibble. -/
def NotBadAt (R : TRep) (args : List Value) (σ : State) : Prop :=
  ∀ (p t : Addr) (fs : List (FieldKey × Value)), args = [.ref p] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    ¬ BadNibble (R.src σ t)

/-- When `readFieldBegin()` throws, on every header byte: `rfbBad` for a bad nibble, `rfbE` otherwise. -/
def rfbEAll (P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  rfbBad P R args σ e σ' ∧ (NotBadAt R args σ → rfbE P R args σ e σ')

attribute [irreducible] rfbBad rfbEAll

/-- `rfbSpecI` without `NibbleOK`: the exceptions are `rfbEAll`. -/
def rfbSpecAll (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (last : I32), args = [.ref p] ∧ CPAt P R σ p t tmp ∧
     CPAtH P R σ p t tmp ∧ LastAt σ p last ∧ BoolAt σ p ∧ σ.initOf tpeCls = .done ∧
     σ.initOf cpCls = .done ∧ σ.initOf tfCls = .done)
  (rfbN P R) (rfbEAll P R)

/-- `getTType` threw: the nibble is 14 or 15. -/
theorem rfb_g4all {P : Program} {R : TRep} {σ0 σ1 σ' : State} {p t tmp e : Addr} {u : UInt8}
    {w : List (FieldKey × Value)} (hH0 : CPAtH P R σ0 p t tmp) (hsrc : R.src σ0 t = u :: R.src σ1 t)
    (hu : ¬ BitVec.signExtend 32 u.toBitVec = 0#32)
    (hn : Spec.ttypeOfCompact (((BitVec.signExtend 32 u.toBitVec).toNat &&& 15) % 16) = none)
    (hexc : σ'.heap e = some (.plain tpeCls w)) :
    rfbEAll P R [.ref p] σ0 e σ' := by
  unfold rfbEAll
  refine ⟨?_, fun hnb => ?_⟩
  · unfold rfbBad
    intro _ _ _ _ _ _ _ _ _
    exact ⟨w, hexc⟩
  · exfalso
    obtain ⟨fs, xs, c, fst, hp, htr, -⟩ := CPAtH.elim hH0
    rw [sx_toNat_and15, Nat.mod_mod] at hn
    exact hnb p t fs rfl hp htr ⟨u, _, hsrc, sx_ne_zero hu, hn⟩

/-- `readByte()` threw (no byte): as `rfb_g5`; no bad nibble. -/
theorem rfb_g5all {P : Program} {R : TRep} {σ0 σ' : State} {p t tmp e : Addr}
    {w : List (FieldKey × Value)} (hH0 : CPAtH P R σ0 p t tmp) (hsrc : R.src σ0 t = [])
    (hexc : σ'.heap e = some (.plain ttExcCls w)) : rfbEAll P R [.ref p] σ0 e σ' := by
  unfold rfbEAll
  refine ⟨?_, fun _ => rfb_g5 hH0 hsrc hexc⟩
  unfold rfbBad
  intro p' t' tmp' fs hargs hp htr hte hbad
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨h1, h2⟩ := cpAt_fields (CPAtH.elim hH0) hp htr hte
  subst t' tmp'
  obtain ⟨u, rest, hs, -⟩ := hbad
  rw [hsrc] at hs
  cases hs

/-- `readFieldId` threw (after `getTType` returned): as `rfb_g8`; the nibble had a TType. -/
theorem rfb_g8all {P : Program} {R : TRep} {σ0 σ1 σ' : State} {p t tmp e : Addr}
    {fs : List (FieldKey × Value)} {last : I32} {u : UInt8} {tt : Nat}
    (hH0 : CPAtH P R σ0 p t tmp) (hp0 : σ0.heap p = some (.plain cpCls fs))
    (hlast0 : Fields.get fs (cpCls, "lastFieldId_") = some (.int last))
    (hf : fieldIdJ last (BitVec.signExtend 32 u.toBitVec) (R.src σ1 t) = none)
    (hsrc : R.src σ0 t = u :: R.src σ1 t) (hu : u.toNat ≠ 0)
    (hexc : (Spec.VarintOverlong 5 (R.src σ1 t) ∧ ∃ fs, σ'.heap e = some (.plain tpeCls fs)) ∨
      (Spec.VarintTruncated 5 (R.src σ1 t) ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs)))
    (htt : Spec.ttypeOfCompact (u.toNat % 16) = some tt) :
    rfbEAll P R [.ref p] σ0 e σ' := by
  unfold rfbEAll
  refine ⟨?_, fun _ => rfb_g8 hH0 hp0 hlast0 hf hsrc hu hexc⟩
  unfold rfbBad
  intro p' t' tmp' fs' hargs hp htr hte hbad
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  obtain ⟨h1, h2⟩ := cpAt_fields (CPAtH.elim hH0) hp htr hte
  subst t' tmp'
  obtain ⟨u', rest, hs, -, hnone⟩ := hbad
  rw [hsrc] at hs
  simp only [List.cons.injEq] at hs
  obtain ⟨rfl, -⟩ := hs
  rw [htt] at hnone
  cases hnone

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rfbAll_body (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC] →
    MethodVC P (Γ3All P R) 3 rfbRef (rfbSpecAll P R) (rfbInv P R) 200 := by
  intro P hF
  jverify [findHandler, Program.subtype, Program.isSubclass, Program.supers, supersN_succ_eq,
    supersFold, Program.fuel, Program.lookup, fieldKey, Program.resolveField, resolveFieldN_succ_eq,
    resolveIfaces, Program.isProgClass, Program.selectStatic, Program.chainN, Program.selectSpecial,
    Program.staticDecl, Targets, Shapes, ShapeIs,
    Contains, CPAt, ClassOK, rfbSpecAll, rfbInv, LastAt, BoolAt, Γ3All, Γ2, rbSig, gttSig, rfiSig,
    rv32Sig, wv32Sig, Program.selectVirtual, tc_write, tc_readAll, tc_getBytesRemainingInBuffer,
    tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer, tc_checkReadBytesAvailable, tc_none, TFrame,
    PFrame, RFrame, gttN, gttE, gttSpecAll, instanceFields_tf, jbyte, tfNew, ttCls, cpCls, tpCls, tpeCls,
    tfCls]
  case left.right.normal.isTrue => exact rfb_g1 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case left.right.normal.isFalse.normal => exact rfb_g3 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  case left.right.normal.isFalse.exc => exact rfb_g4all ‹_› ‹_› ‹_› ‹_› ‹_›
  case left.right.exc => exact rfb_g5all ‹_› ‹_› ‹_›
  case right.left =>
    refine rfb_g6 ‹_› (fun c hc2 => ?_)
    have h := isSub_fold hc2
    rw [supersN_succ_eq] at h
    exact h
  case right.right.normal =>
    exact rfb_g7 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
      ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› (by exact tf_get_type _ _ _ _) (by exact tf_get_id _ _ _ _)
  case right.right.exc.some => exact rfb_g8all ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

end EquivLean.Demo.Thrift.Java
