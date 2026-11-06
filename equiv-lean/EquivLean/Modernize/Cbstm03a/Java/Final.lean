import EquivLean.Modernize.Cbstm03a.Java.Top
import EquivLean.Modernize.Cbstm03a.Java.Segs
import EquivLean.Modernize.Cbstm03a.Java.Run5.ThC168
import EquivLean.Modernize.Cbstm03a.Java.Num.Sats
import EquivLean.Modernize.Cbstm03a.Java.Mem.Sats
import EquivLean.Modernize.Cbstm03a.Java.Mw.VC
import EquivLean.Modernize.Cbstm03a.Java.Cs.Sat
import EquivLean.Modernize.Cbstm03a.Java.Text.Out
import EquivLean.Modernize.Cbstm03a.Java.Text.Abend
import EquivLean.Modernize.Cbstm03a.Java.Text.TextXT
import EquivLean.Modernize.Cbstm03a.Java.Text.TextA
import EquivLean.Modernize.Cbstm03a.Java.Text.TextC5
import EquivLean.Modernize.Cbstm03a.Java.Text.WriteTrans
import EquivLean.Modernize.Cbstm03a.Java.Dz.Sat
import EquivLean.Modernize.Cbstm03a.Java.Terms

/-!
# CBSTM03A → Java: the final link

`run`'s callee contracts from the helper packages (their own callee tables linked here with `jcontract_ok`), its
verification conditions from the segment packages (`Segs.lean`, `run_thin168`), and the generated statement from
`run`'s contract (`Top.lean`): `java_statement : Statement`. Total correctness: `JavaRun.lean` (`java_total`), from
the callees' termination contracts (`Terms.lean`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

/-- The helper table of `stmt`/`html`. -/
theorem outCallees_valid : Valid Gen.prog Txt.outCallees.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [Txt.outCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  exact (by jcontract_ok [fix_sat]))

theorem stmt_satF : Sat Gen.prog stmtRef stmtSpec := Txt.stmt_sat outCallees_valid
theorem html_satF : Sat Gen.prog htmlRef htmlSpec := Txt.html_sat outCallees_valid

/-- The helper table of the record texts. -/
theorem txtCallees_valid : Valid Gen.prog Txt.txtCallees.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [Txt.txtCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact (by jcontract_ok [fix_sat])
  · exact (by jcontract_ok [spaces_sat])
  · exact (by jcontract_ok [zu_sat])
  · exact (by jcontract_ok [zs_sat]))

/-- The helper table of `writeTrans`. -/
theorem wtCallees_valid : Valid Gen.prog Txt.wtCallees.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [Txt.wtCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact (by jcontract_ok [fix_sat])
  · exact (by jcontract_ok [fmtZ_sat])
  · exact (by jcontract_ok [star_sat]))

/-- The helper table of `memWrite`. -/
theorem mwCallees_valid : Valid Gen.prog mwCallees.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [mwCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact (by jcontract_ok [spaces_sat])
  · exact (by jcontract_ok [slotIndex_sat])
  · exact (by jcontract_ok [slotLen_sat])
  · exact (by jcontract_ok [slotStart_sat]))

/-- The helper table of `createStatement`. -/
theorem csCallees_valid : Valid Gen.prog csCallees.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [csCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (by jcontract_ok [stmt_satF])
  · exact (by jcontract_ok [html_satF])
  · exact (by jcontract_ok [fix_sat])
  · exact (by jcontract_ok [spaces_sat])
  · exact (by jcontract_ok [repeat_sat])
  · exact (by jcontract_ok [app_sat])
  · exact (by jcontract_ok [para_sat])
  · exact (by jcontract_ok [star_sat])
  · exact (by jcontract_ok [fmtCurrBal_sat])
  · exact (by jcontract_ok [decodeZoned_sat]))

/-- `run`'s callee contracts. -/
theorem runCalleeSats : RunCalleeSats where
  trnxText := Txt.trnxText_sat txtCallees_valid
  xrefText := Txt.xrefText_sat txtCallees_valid
  custText := Txt.custText_sat txtCallees_valid
  acctText := Txt.acctText_sat txtCallees_valid
  spaces := spaces_sat
  fix := fix_sat
  «repeat» := repeat_sat
  seqRead := seqRead_sat
  setTrct := setTrct_sat
  getTrct := getTrct_sat
  cardOff := cardOff_sat
  tranOff := tranOff_sat
  memWrite := memWrite_sat mwCallees_valid
  memRead := memRead_sat spaces_sat
  abend := Txt.abend_sat
  createStatement := createStatement_sat csCallees_valid
  writeTrans := Txt.writeTrans_sat wtCallees_valid
  stmt := stmt_satF
  html := html_satF
  ebcCompare := ebcCompare_sat
  decodeZoned := decodeZoned_sat
  trunc11 := trunc11_sat
  fmtZ := fmtZ_sat

/-- `run`'s thin segments, all eleven. -/
theorem run_thin_segs (g : RunG) : RunThinSegs g := run_thin_segs_of (fun g => run_thin168 g) g

/-- `run` satisfies `runSpec` (partial correctness). -/
theorem run_sat : Sat Gen.prog runRef runSpec := runSpec_sat_of (run_satJ_of runCalleeSats run_segs)

/-- **CBSTM03A → Java, the generated statement.** -/
theorem java_statement : Statement :=
  statement_of_runSpecJ (run_satJ_of runCalleeSats run_segs)

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.java_statement
