-- Termination package by JimpleLean's session: TermT4/RsbAll.lean (sha256 78c32f2ae04122cb...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.RsbP
import EquivLean.Demo.Thrift.Java.Term.RlbAll

/-!
# Thrift → Java (T4): `readSetBegin()` on every header byte

`readSetBegin()` is `new TSet(readListBegin())`. Against `readListBegin()`'s contract on every header byte
(`rlbSpecAAll`, `Γ7All`), it is verified without `NibbleOKL` (`rsbSpecAll`): it throws what
`readListBegin()` throws on every header byte (`rlbEAll`, so a valid size and an element nibble 14 or 15
give `getTType`'s `TProtocolException`). The invariant and the closers are `rsb_body`'s, three of them
restated for `rlbEAll`. New names only.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- `readListBegin()` on every header byte, for the callers (`rlbSpecA` without `NibbleOKL`). -/
def rlbSpecAAll (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (lim : I64), args = [.ref p] ∧ CPAt P R σ p t tmp ∧
     LimitAt σ p lim ∧ σ.initOf tpeCls = .done ∧ σ.initOf tlCls = .done ∧ σ.initOf ttExcCls = .done)
  (rlbN P R) (rlbEAll P R)

/-- The contracts `readSetBegin()` uses, with `readListBegin()`'s on every header byte. -/
def Γ7All (P : Program) (R : TRep) : SpecEnv := fun sig =>
  if sig = rlbSig then some (rlbSpecAAll P R) else (tContracts R).env sig

/-- `rsbSpecI` without `NibbleOKL`: the exceptions are `rlbEAll`. -/
def rsbSpecAll (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (lim : I64), args = [.ref p] ∧ CPAt P R σ p t tmp ∧
     CPAtH P R σ p t tmp ∧ LimitAt σ p lim ∧ σ.initOf tpeCls = .done ∧ σ.initOf tlCls = .done ∧
     σ.initOf ttExcCls = .done ∧ σ.initOf tsCls = .done)
  (rsbN P R) (rlbEAll P R)

/-- `readListBegin()` threw with no object (impossible), for `rlbEAll`. -/
theorem rsb_exc_noneAll {P : Program} {R : TRep} {σc σ' : State} {p t tmp e : Addr}
    {fs : List (FieldKey × Value)} {lim : I64}
    (hE : rlbEAll P R [.ref p] σc e σ') (hpc : σc.heap p = some (.plain cpCls fs))
    (htr : Fields.get fs (tpCls, "trans_") = some (.ref t))
    (hte : Fields.get fs (cpCls, "temp") = some (.ref tmp))
    (hlim : Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim))
    (hd : σ'.heap e = none) : False := by
  unfold rlbEAll at hE
  rcases hE p t tmp fs lim rfl hpc htr hte hlim with hE' | hB
  · exact rsb_exc_none hE' hpc htr hte hlim hd
  · unfold rlbBadCase at hB
    obtain ⟨-, -, -, -, -, -, -, -, -, w, hw⟩ := hB
    rw [hd] at hw
    cases hw

/-- `readListBegin()` threw: so does `readSetBegin()` (as `rlbE_shift`, for `rlbEAll`). -/
theorem rlbEAll_shift {P : Program} {R : TRep} {σ0 σc σ' : State} {p t tmp e : Addr}
    {fs : List (FieldKey × Value)}
    (hE : rlbEAll P R [.ref p] σc e σ') (hH0 : CPAtH P R σ0 p t tmp)
    (hp0 : σ0.heap p = some (.plain cpCls fs)) (hpc : σc.heap p = some (.plain cpCls fs))
    (hsrc : R.src σc t = R.src σ0 t) : rlbEAll P R [.ref p] σ0 e σ' := by
  unfold rlbEAll at hE ⊢
  intro p' t' tmp' fs' lim hargs hp htr hte hlim
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  rw [hp0] at hp
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp
  subst hp
  obtain ⟨h1, h2⟩ := cpAt_fields (CPAtH.elim hH0) hp0 htr hte
  subst t' tmp'
  rcases hE p t tmp fs lim rfl hpc htr hte hlim with hE' | hB
  · exact Or.inl (rlbE_shift hE' hH0 hp0 hpc hsrc)
  · refine Or.inr ?_
    unfold rlbBadCase at hB ⊢
    rw [hsrc] at hB
    exact hB

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem rsbAll_body (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC] →
    MethodVC P (Γ7All P R) 3 rsbRef (rsbSpecAll P R) (rsbInv P R) 100 := by
  intro P hF
  jverify [findHandler, Program.subtype, Program.isSubclass, Program.supers, supersN_succ_eq,
    supersFold, Program.fuel, Program.lookup, fieldKey, Program.resolveField, resolveFieldN_succ_eq,
    resolveIfaces, Program.isProgClass, Program.selectStatic, Program.chainN, Program.selectSpecial,
    Program.staticDecl, Targets, Shapes, ShapeIs,
    Contains, rsbSpecAll, rlbSpecAAll, rsbInv, LimitAt, Γ7All, rlbSig, Program.selectVirtual, tc_write,
    tc_readAll, tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer,
    tc_checkReadBytesAvailable, tc_none, instanceFields_ts, tsNew, cpCls, tpCls, tlCls, tsCls]
  all_goals first
    | exact alloc_cpAtH _ ‹_›
    | exact alloc_src _ ‹_›
    | exact alloc_sink _ ‹_›
    | exact alloc_notown _ ‹_›
    | exact rsb_cut3 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact (rsb_exc_noneAll ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).elim
    | exact rlbEAll_shift ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact rsb_post ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
        (ts_get_elemType _ _ _) (ts_get_size _ _ _)
    -- `readListBegin()`'s precondition at the call (after `new TSet`): the protocol object
    | exact ⟨_, _, CPAtH.elim ‹_›⟩

end EquivLean.Demo.Thrift.Java
