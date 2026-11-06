import EquivLean.Modernize.Cbstm03a.Java.RunLink

/-!
# CBSTM03A → Java: `run` terminates, and total correctness

`RunCalleeTerms`: one `ContractTerm` per contract of `runCallees` (the helpers terminate on their preconditions);
with the callee contracts, the partial-correctness segments and the thin segments, `run` terminates on every input
of `runSpecJ` (`run_term_of`), and `run_total_of` is total correctness.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

/-- The callees of `run` terminate on their contracts' preconditions. -/
structure RunCalleeTerms : Prop where
  trnxText : ContractTerm Gen.prog trnxTextSig trnxTextSpec
  xrefText : ContractTerm Gen.prog xrefTextSig xrefTextSpec
  custText : ContractTerm Gen.prog custTextSig custTextSpec
  acctText : ContractTerm Gen.prog acctTextSig acctTextSpec
  spaces : ContractTerm Gen.prog spacesSig spacesSpecI
  fix : ContractTerm Gen.prog fixSig fixSpecI
  «repeat» : ContractTerm Gen.prog repeatSig repeatSpec
  seqRead : ContractTerm Gen.prog seqReadSig seqReadSpec
  setTrct : ContractTerm Gen.prog setTrctSig setTrctSpec
  getTrct : ContractTerm Gen.prog getTrctSig getTrctSpec
  cardOff : ContractTerm Gen.prog cardOffSig cardOffSpec
  tranOff : ContractTerm Gen.prog tranOffSig tranOffSpec
  memWrite : ContractTerm Gen.prog memWriteSig memWriteSpec
  memRead : ContractTerm Gen.prog memReadSig memReadSpec
  abend : ContractTerm Gen.prog abendSig abendSpec
  createStatement : ContractTerm Gen.prog createStatementSig createStatementSpec
  writeTrans : ContractTerm Gen.prog writeTransSig writeTransSpec
  stmt : ContractTerm Gen.prog stmtSig stmtSpec
  html : ContractTerm Gen.prog htmlSig htmlSpec
  ebcCompare : ContractTerm Gen.prog ebcCompareSig ebcCompareSpec
  decodeZoned : ContractTerm Gen.prog decodeZonedSig decodeZonedSpec
  trunc11 : ContractTerm Gen.prog trunc11Sig trunc11Spec
  fmtZ : ContractTerm Gen.prog fmtZSig fmtZSpec

theorem runCallees_below : runCallees.env.below (fun _ => 0) 1 = runCallees.env :=
  SpecEnv.below_const _ _ (by decide)

theorem runCallees_term (ht : RunCalleeTerms) :
    ∀ sig S, (runCallees.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [runCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨ht.trnxText, ht.xrefText, ht.custText, ht.acctText, ht.spaces, ht.fix, ht.repeat, ht.seqRead,
      ht.setTrct, ht.getTrct, ht.cardOff, ht.tranOff, ht.memWrite, ht.memRead, ht.abend, ht.createStatement,
      ht.writeTrans, ht.stmt, ht.html, ht.ebcCompare, ht.decodeZoned, ht.trunc11, ht.fmtZ⟩) _ _

/-- **`run` terminates** on every input of `runSpecJ`. -/
theorem run_term_of (hc : RunCalleeSats) (ht : RunCalleeTerms) (h : ∀ g, RunSegs g) (hn : ∀ g, RunThinSegs g) :
    ∀ args σ, runSpecJ.pre args σ → MTerm Gen.prog runRefA args σ := by
  intro args σ hpre
  obtain ⟨g, hg⟩ := hpre
  exact TermVC.mterm (rank := fun _ => 0) (r := 1) (runCallees_valid hc) (runCallees_term ht)
    (run_termvc_of g runCallees_below (h g) (hn g)) args σ hg

/-- **`run`, total correctness**: on every input of `runSpecJ`, `run` has an outcome, and every outcome satisfies
`runSpecJ`. -/
theorem run_total_of (hc : RunCalleeSats) (ht : RunCalleeTerms) (h : ∀ g, RunSegs g) (hn : ∀ g, RunThinSegs g) :
    ∀ args σ, runSpecJ.pre args σ →
      (∃ o, MExec Gen.prog runRefA args σ o) ∧ ∀ o, MExec Gen.prog runRefA args σ o → runSpecJ.post args σ o :=
  total_of_sat_mterm (run_satJ_of hc h) (run_term_of hc ht h hn)

end EquivLean.Modernize.Cbstm03a.Java
