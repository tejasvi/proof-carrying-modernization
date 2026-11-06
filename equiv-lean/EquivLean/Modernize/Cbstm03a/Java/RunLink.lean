import EquivLean.Modernize.Cbstm03a.Java.RunTerm

/-!
# CBSTM03A → Java: the callee contracts of `run` hold when each callee satisfies its contract

`RunCalleeSats`: one `Sat` per contract of `runCallees` (proved by the helper packages); `runCallees_valid`: the
table's validity (`jcontract_ok` per contract, `Contracts.valid_of_ok`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

/-- The contracts of `run`'s callees, each satisfied by its method. -/
structure RunCalleeSats : Prop where
  trnxText : Sat Gen.prog trnxTextRef trnxTextSpec
  xrefText : Sat Gen.prog xrefTextRef xrefTextSpec
  custText : Sat Gen.prog custTextRef custTextSpec
  acctText : Sat Gen.prog acctTextRef acctTextSpec
  spaces : Sat Gen.prog spacesRef spacesSpecI
  fix : Sat Gen.prog fixRef fixSpecI
  «repeat» : Sat Gen.prog repeatRef repeatSpec
  seqRead : Sat Gen.prog seqReadRef seqReadSpec
  setTrct : Sat Gen.prog setTrctRef setTrctSpec
  getTrct : Sat Gen.prog getTrctRef getTrctSpec
  cardOff : Sat Gen.prog cardOffRef cardOffSpec
  tranOff : Sat Gen.prog tranOffRef tranOffSpec
  memWrite : Sat Gen.prog memWriteRef memWriteSpec
  memRead : Sat Gen.prog memReadRef memReadSpec
  abend : Sat Gen.prog abendRef abendSpec
  createStatement : Sat Gen.prog createStatementRef createStatementSpec
  writeTrans : Sat Gen.prog writeTransRef writeTransSpec
  stmt : Sat Gen.prog stmtRef stmtSpec
  html : Sat Gen.prog htmlRef htmlSpec
  ebcCompare : Sat Gen.prog ebcCompareRef ebcCompareSpec
  decodeZoned : Sat Gen.prog decodeZonedRef decodeZonedSpec
  trunc11 : Sat Gen.prog trunc11Ref trunc11Spec
  fmtZ : Sat Gen.prog fmtZRef fmtZSpec

theorem runCallees_valid (h : RunCalleeSats) : Valid Gen.prog runCallees.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [runCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (by jcontract_ok [h.trnxText])
  · exact (by jcontract_ok [h.xrefText])
  · exact (by jcontract_ok [h.custText])
  · exact (by jcontract_ok [h.acctText])
  · exact (by jcontract_ok [h.spaces])
  · exact (by jcontract_ok [h.fix])
  · exact (by jcontract_ok [h.repeat])
  · exact (by jcontract_ok [h.seqRead])
  · exact (by jcontract_ok [h.setTrct])
  · exact (by jcontract_ok [h.getTrct])
  · exact (by jcontract_ok [h.cardOff])
  · exact (by jcontract_ok [h.tranOff])
  · exact (by jcontract_ok [h.memWrite])
  · exact (by jcontract_ok [h.memRead])
  · exact (by jcontract_ok [h.abend])
  · exact (by jcontract_ok [h.createStatement])
  · exact (by jcontract_ok [h.writeTrans])
  · exact (by jcontract_ok [h.stmt])
  · exact (by jcontract_ok [h.html])
  · exact (by jcontract_ok [h.ebcCompare])
  · exact (by jcontract_ok [h.decodeZoned])
  · exact (by jcontract_ok [h.trunc11])
  · exact (by jcontract_ok [h.fmtZ]))

/-- **`run` satisfies its contract** given the callee contracts and the segments of its verification
conditions. -/
theorem run_satJ_of (hc : RunCalleeSats) (h : ∀ g, RunSegs g) : Sat Gen.prog runRefA runSpecJ :=
  runSpecJ_of_ghost fun g => run_sat_of g (runCallees_valid hc) (h g)

end EquivLean.Modernize.Cbstm03a.Java
