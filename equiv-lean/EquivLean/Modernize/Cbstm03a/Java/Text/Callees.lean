import EquivLean.Modernize.Cbstm03a.Java.Text.Lib2
import EquivLean.Modernize.Cbstm03a.Java.Iface1

/-!
# CBSTM03A → Java: the callee tables of the output and record-text methods

Built from the interface contracts only (`CbA.Iface0` v2, `CbANum.Iface1`): `stmt` and `html` call `fix`;
the record texts call `fix`, `spaces`, `zu`, `zs`; `writeTrans` (with `stmt` and `html` inlined) calls `fix`,
`fmtZ`, `star`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Txt

/-- The callees of `stmt` and `html`. -/
def outCallees : Contracts := [(fixSig, fixSpec)]

/-- The callees of `trnxText`, `xrefText`, `custText`, `acctText`. -/
def txtCallees : Contracts := [(fixSig, fixSpec), (spacesSig, spacesSpec), (zuSig, zuSpec), (zsSig, zsSpec)]

/-- The callees of `writeTrans`, `stmt` and `html` inlined. -/
def wtCallees : Contracts := [(fixSig, fixSpec), (fmtZSig, fmtZSpec), (starSig, starSpec)]

end EquivLean.Modernize.Cbstm03a.Java.Txt
