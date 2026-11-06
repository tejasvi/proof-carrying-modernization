import EquivLean.Modernize.Cbstm03a.Java.RunTotal
import EquivLean.Modernize.Cbstm03a.Java.Term.Iface
import EquivLean.Modernize.Cbstm03a.Java.Term2.Leaves
import EquivLean.Modernize.Cbstm03a.Java.Term2.MemReadTerm
import EquivLean.Modernize.Cbstm03a.Java.Term2.MemWriteTerm
import EquivLean.Modernize.Cbstm03a.Java.Term2.Out
import EquivLean.Modernize.Cbstm03a.Java.Term2.WriteTransTerm
import EquivLean.Modernize.Cbstm03a.Java.Thin3.CS.Main
import EquivLean.Modernize.Cbstm03a.Java.Num.Sats
import EquivLean.Modernize.Cbstm03a.Java.Mem.Sats
import EquivLean.Modernize.Cbstm03a.Java.Dz.Sat

/-!
# CBSTM03A → Java: `run`'s callees terminate

`runCalleeTerms : RunCalleeTerms` from the helpers' termination contracts (`Term.Iface`, `Term2`); `memRead`,
`memWrite`, `stmt`, `html`, `writeTrans` and `createStatement` take their own callees' contracts, linked here from
the helper sats with `jcontract_ok`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

/-- `writeTrans` terminates on `writeTransSpec`'s inputs: `writeTransSpecB` allows transaction ids of up to `2^30`
characters, `writeTransSpec` fewer than `10^6`. -/
theorem writeTrans_cterm : ContractTerm Gen.prog writeTransSig writeTransSpec :=
  ContractTerm.mono
    (writeTrans_ctermB (by jcontract_ok [fix_sat]) fixI_cterm (by jcontract_ok [fmtZ_sat]) fmtZ_cterm
      (by jcontract_ok [star_sat]) star_cterm)
    fun _ _ ⟨res, ld, ls, lh, disp, st, ht, ab, tv, rv, amt, t, tr, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ =>
      ⟨res, ld, ls, lh, disp, st, ht, ab, tv, rv, amt, t, tr, h1, h2, h3, h4, h5, h6, by omega, h8, h9⟩

theorem decodeZoned_ok : ContractOK Gen.prog decodeZonedSig decodeZonedSpec := by jcontract_ok [decodeZoned_sat]
theorem repeat_ok : ContractOK Gen.prog repeatSig repeatSpec := by jcontract_ok [repeat_sat]
theorem fixI_ok : ContractOK Gen.prog fixSig fixSpecI := by jcontract_ok [fix_sat]
theorem app_ok : ContractOK Gen.prog appSig appSpec := by jcontract_ok [app_sat]
theorem fmtCurrBal_ok : ContractOK Gen.prog fmtCurrBalSig fmtCurrBalSpec := by jcontract_ok [fmtCurrBal_sat]
theorem para_ok : ContractOK Gen.prog paraSig paraSpec := by jcontract_ok [para_sat]
theorem star_ok : ContractOK Gen.prog starSig starSpec := by jcontract_ok [star_sat]
theorem spacesI_ok : ContractOK Gen.prog spacesSig spacesSpecI := by jcontract_ok [spaces_sat]

/-- `run`'s callees terminate. -/
theorem runCalleeTerms : RunCalleeTerms where
  trnxText := trnxText_cterm
  xrefText := xrefText_cterm
  custText := custText_cterm
  acctText := acctText_cterm
  spaces := spacesI_cterm
  fix := fixI_cterm
  «repeat» := repeat_cterm
  seqRead := seqRead_cterm
  setTrct := setTrct_cterm
  getTrct := getTrct_cterm
  cardOff := cardOff_cterm
  tranOff := tranOff_cterm
  memWrite := memWrite_cterm (by jcontract_ok [slotIndex_sat]) (by jcontract_ok [slotLen_sat])
    (by jcontract_ok [slotStart_sat]) spacesI_ok spacesI_cterm
  memRead := memRead_cterm (by jcontract_ok [slotIndex_sat]) (by jcontract_ok [slotLen_sat])
    (by jcontract_ok [slotStart_sat]) spacesI_ok spacesI_cterm
  abend := abend_cterm
  createStatement := createStatement_cterm fixI_ok fixI_cterm spacesI_ok spacesI_cterm repeat_ok repeat_cterm app_ok
    app_cterm para_ok para_cterm star_ok star_cterm fmtCurrBal_ok fmtCurrBal_cterm decodeZoned_ok decodeZoned_cterm
  writeTrans := writeTrans_cterm
  stmt := stmt_cterm fixI_ok fixI_cterm
  html := html_cterm fixI_ok fixI_cterm
  ebcCompare := ebcCompare_cterm
  decodeZoned := decodeZoned_cterm
  trunc11 := trunc11_cterm
  fmtZ := fmtZ_cterm

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.writeTrans_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.runCalleeTerms
