import EquivLean.Modernize.Cbstm03b.Java.Term.Xref
import EquivLean.Modernize.Cbstm03b.Java.Term.Cust
import EquivLean.Modernize.Cbstm03b.Java.Term.Acct

/-!
# CBSTM03B → Java: `call` terminates, and is totally correct given its contract

`call` has no loop: it reads the area's DD name and operation and calls the file procedure of the DD name. Its
termination VC answers these calls by `procSpecT dd`: `procSpec dd`'s precondition (`ProcPre`, folded for the
symbolic executor) and no postcondition (after the call `call` returns). These contracts hold trivially and
terminate (`trnx_cterm`, `xref_cterm`, `cust_cterm`, `acct_cterm`). At each call the precondition is `runSpec`'s,
the heap grown by the string constants `call` allocates, with the DD name of the branch taken.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

/-- `procSpec dd`'s precondition, folded for the symbolic executor. -/
@[irreducible] def ProcPre (dd : List UInt8) (args : List Value) (σ : State) : Prop := (procSpec dd).pre args σ

/-- A file procedure, for `call`'s termination: `procSpec dd`'s precondition, no postcondition. -/
def procSpecT (dd : List UInt8) : Spec := ⟨ProcPre dd, fun _ _ _ => True⟩

/-- The callee contracts of `call`'s termination VC. -/
def callCalleesT : Contracts :=
  [(trnxProcSig, procSpecT ddTrnx), (xrefProcSig, procSpecT ddXref), (custProcSig, procSpecT ddCust),
    (acctProcSig, procSpecT ddAcct)]

theorem procT_sat (dd : List UInt8) (m : MethodRef) : Sat Gen.prog m (procSpecT dd) := fun _ _ _ _ _ => trivial

set_option maxHeartbeats 4000000 in
theorem trnxT_ok : ContractOK Gen.prog trnxProcSig (procSpecT ddTrnx) := by jcontract_ok [procT_sat ddTrnx trnxProcRef]
set_option maxHeartbeats 4000000 in
theorem xrefT_ok : ContractOK Gen.prog xrefProcSig (procSpecT ddXref) := by jcontract_ok [procT_sat ddXref xrefProcRef]
set_option maxHeartbeats 4000000 in
theorem custT_ok : ContractOK Gen.prog custProcSig (procSpecT ddCust) := by jcontract_ok [procT_sat ddCust custProcRef]
set_option maxHeartbeats 4000000 in
theorem acctT_ok : ContractOK Gen.prog acctProcSig (procSpecT ddAcct) := by jcontract_ok [procT_sat ddAcct acctProcRef]

theorem callCalleesT_valid : Valid Gen.prog callCalleesT.env := by
  apply Contracts.valid_of_ok
  simp only [callCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨trnxT_ok, xrefT_ok, custT_ok, acctT_ok⟩

theorem procT_cterm {sig : MethodSig} {dd : List UInt8} (h : ContractTerm Gen.prog sig (procSpec dd)) :
    ContractTerm Gen.prog sig (procSpecT dd) :=
  ContractTerm.mono h fun _ _ hp => by
    simp only [procSpecT] at hp
    unfold ProcPre at hp
    exact hp

theorem callCalleesT_term :
    ∀ sig S, (callCalleesT.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [callCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨procT_cterm trnx_cterm, procT_cterm xref_cterm, procT_cterm cust_cterm, procT_cterm acct_cterm⟩) _ _

/-! ## The paths -/

theorem grows_allocT (σ : State) (o : Obj) : Grows σ (σ.alloc o).2 :=
  ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun _ hx => State.heap_alloc_of_lt hx o⟩

/-- `Grows σ0 σ` for `σ` built from `σ0` by allocations. -/
macro "growsT_tac" : tactic => `(tactic| repeat (first | exact grows_refl _ | refine grows_trans ?_ (grows_allocT _ _)))

/-- `InitsDone` of a state with the same class initialization states. -/
theorem initsDone_of_inits {σ0 σ : State} (hi : σ.inits = σ0.inits) (h : InitsDone σ0) : InitsDone σ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := h
  have e := State.initOf_eq_of_inits hi
  exact ⟨(e _).trans i1, (e _).trans i2, (e _).trans i3, (e _).trans i4, (e _).trans i5, (e _).trans i6,
    (e _).trans i7, (e _).trans i8, (e _).trans i9, (e _).trans i10, (e _).trans i11⟩

/-- `procSpec dd`'s precondition at a call of `call`: `runSpec`'s, in a heap grown from the entry heap, for the DD
    name `dd`. -/
theorem procPre_of (dd : List UInt8) (oe st q xop : Addr) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (σ0 σ : State) (fsq : List (FieldKey × Value))
    (hkept : Kept (EnvAtM σ0 oe oeM ∧ StateAtM σ0 st s ∧ SepM σ0 st ∧
      JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ0 (.ref q) a ∧ Glue.ValidSt s ∧ Model.LkM03bArea.Valid a ∧
      Glue.KeyOk a ∧ InitsDone σ0))
    (hq : σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq))
    (gop : Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bOper") = some (.ref xop))
    (hg : Grows σ0 σ) (hi : σ.inits = σ0.inits) (hdd : Model.aDd a = dd) :
    ProcPre dd [.ref oe, .ref st, .ref q, .ref xop] σ := by
  obtain ⟨hE, hS, hsep, hA, hV, hVa, hK, hI⟩ := Kept.elim hkept
  unfold ProcPre
  exact ⟨oe, st, q, .ref xop, oeM, s, a, rfl, envAtM_grows hE hg, stateAtM_grows hS hg, sepM_grows hS hsep hg,
    jRecAt_grows hA hg, hV, hVa, hK, hdd, ⟨fsq, heap_grows hg hq, gop⟩, initsDone_of_inits hi hI⟩

/-- The termination paths of `call` from statement `pc`. -/
@[irreducible] def callTWP (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPT Gen.prog callCalleesT.env 1)
    Gen.Cbstm03b.«call(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea)» [] (fun _ => True) 200 pc fr σ

set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000000 in
theorem call_tentry (oe st q : Addr) (oeM : Model.OpenErrs) (s : Model.StM) (a : List EquivLean.Cobol.Rec.FVal)
    (args : List Value) (σ0 : State) (hpre : (runSpecG oe st q oeM s a).pre args σ0) :
    callTWP 0 (Frame.init true args) σ0 := by
  obtain ⟨rfl, hE, hS, hsep, hA, hV, hVa, hK, hI⟩ := hpre
  have hkept := Kept.intro (And.intro hE (And.intro hS (And.intro hsep (And.intro hA (And.intro hV
    (And.intro hVa (And.intro hK hI)))))))
  obtain ⟨q', fsq, dd, op, rc, key, kl, fldt, sdd, sop, src, skey, sfl, hqq, hq, ha, -, -, -, -, -, -, -,
    gdd, jdd, gop, jop, -, -, -, -, -, -, -⟩ := areaAt_of hA hVa
  cases hqq
  obtain ⟨xdd, rfl, hxdd⟩ := jdd
  obtain ⟨xop, rfl, hxop⟩ := jop
  have had : Model.aDd a = dd := by rw [ha]; rfl
  have hlt_q := State.lt_next_of_heap hq
  have hlt_dd := State.lt_next_of_heap hxdd
  have hlt_op := State.lt_next_of_heap hxop
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := hI
  clear hE hS hsep hA hV hVa hK ha
  simp only [callTWP]
  jvc [ite_nat_ne, callCalleesT, trnxProcSig, xrefProcSig, custProcSig, acctProcSig, procParams, procSpecT,
    findHandler]
  all_goals first
    | exact procPre_of ddTrnx oe st q xop oeM s a σ0 _ fsq hkept hq gop (by growsT_tac) rfl
        (cp037Str_inj (‹cp037Str (Model.aDd a) = JStr.ofString "TRNXFILE"›.trans dd_texts.1.symm))
    | exact procPre_of ddXref oe st q xop oeM s a σ0 _ fsq hkept hq gop (by growsT_tac) rfl
        (cp037Str_inj (‹cp037Str (Model.aDd a) = JStr.ofString "XREFFILE"›.trans dd_texts.2.1.symm))
    | exact procPre_of ddCust oe st q xop oeM s a σ0 _ fsq hkept hq gop (by growsT_tac) rfl
        (cp037Str_inj (‹cp037Str (Model.aDd a) = JStr.ofString "CUSTFILE"›.trans dd_texts.2.2.1.symm))
    | exact procPre_of ddAcct oe st q xop oeM s a σ0 _ fsq hkept hq gop (by growsT_tac) rfl
        (cp037Str_inj (‹cp037Str (Model.aDd a) = JStr.ofString "ACCTFILE"›.trans dd_texts.2.2.2.symm))

/-! ## Termination and total correctness -/

theorem call_tvc (oe st q : Addr) (oeM : Model.OpenErrs) (s : Model.StM) (a : List EquivLean.Cobol.Rec.FVal) :
    TermVC Gen.prog callCalleesT.env (fun _ => 0) 1 1 callRef (runSpecG oe st q oeM s a) [] 200 := by
  refine ⟨Gen.Cbstm03b.«call(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea)», rfl,
    fun args σ0 hpre => ⟨?_, fun p hp => nomatch hp⟩⟩
  rw [SpecEnv.below_const _ _ (by decide)]
  have h := call_tentry oe st q oeM s a args σ0 hpre
  unfold callTWP at h
  exact h

/-- `call` terminates, for the contract with fixed ghost values. -/
theorem runG_term (oe st q : Addr) (oeM : Model.OpenErrs) (s : Model.StM) (a : List EquivLean.Cobol.Rec.FVal) :
    ∀ args σ, (runSpecG oe st q oeM s a).pre args σ → MTerm Gen.prog callRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) callCalleesT_valid callCalleesT_term (call_tvc oe st q oeM s a)

/-- **`call` terminates** on every input of `runSpec`. -/
theorem run_term : ∀ args σ, runSpec.pre args σ → MTerm Gen.prog callRef args σ := by
  intro args σ hpre
  obtain ⟨oe, st, q, oeM, s, a, h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpre
  exact runG_term oe st q oeM s a args σ ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **CBSTM03B → Java, total correctness**, given `call`'s contract (`Sat`, partial correctness): on every input of
    `runSpec`, `call` has an outcome, and every outcome satisfies `runSpec`. -/
theorem run_total (hrun : Sat Gen.prog callRef runSpec) : ∀ args σ, runSpec.pre args σ →
    (∃ o, MExec Gen.prog callRef args σ o) ∧ ∀ o, MExec Gen.prog callRef args σ o → runSpec.post args σ o :=
  total_of_sat_mterm hrun run_term

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.run_term
#print axioms EquivLean.Modernize.Cbstm03b.Java.run_total
