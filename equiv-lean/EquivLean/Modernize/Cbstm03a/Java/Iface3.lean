import EquivLean.Modernize.Cbstm03a.Java.Iface0

/-!
# CBSTM03A → Java: the contracts of the output methods and the record texts

* `stmt(res, s)`, `html(res, s)`: `fix(s, 80)` / `fix(s, 100)` appended to the statement / HTML list of the
  `Result` object;
* `abend(res, msg, rc)`: the three display lines appended, `abended` set, `res` returned;
* `writeTrans(res, tid, trest, amt)`, `createStatement(res, custRec, acctRec)`: the lines of `jWriteTrans` /
  `jCreateStatement` appended (the Java's `stmt` and `html` calls, one by one);
* `trnxText(r)`, `xrefText(r)`, `custText(r)`, `acctText(r)`: the record's fixed-width text, spaces for `null`.

The `Result` object (`ResAtL σ res ld ls lh disp st ht ab`): its lists `displays`, `stmtFileWrites`,
`htmlFileWrites` are three distinct `ArrayList`s at `ld`, `ls`, `lh` holding exactly the strings `disp`, `st`,
`ht`; `abended` is `ab`. The output methods change no object of the entry heap but the `Result` object and its
lists (`KeepsRes`); the text methods only allocate (`Grows`). Every method keeps `inits` and `statics`.

The texts of the callees `zu`, `zs`, `fmtZ`, `fmtCurrBal`, `decodeZoned`, `app`, `para`, `star` are written here
as Lean functions following the Java (`zuI`, `zsI`, `fmtZI`, `fmtCurrBalI`, `decodeZonedI`, `appT`, `paraT`,
`starT`). A record object's string fields are strings (not `null`), its `long` fields not `Long.MIN_VALUE`
(`zu`/`zs` negate them).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

/-! ## Characters, literals, substrings -/

/-- A Java string literal. -/
abbrev jl (s : String) : JStr := JStr.ofString s

def chStar : JChar := BitVec.ofNat 16 42
def chDash : JChar := BitVec.ofNat 16 45
def chDot : JChar := BitVec.ofNat 16 46
def chDollar : JChar := BitVec.ofNat 16 36
def chZero : JChar := BitVec.ofNat 16 48

/-- `s.substring(b, e)` (JimpleLean's model of it, for `b ≤ e ≤ s.length`). -/
def sub (s : JStr) (b e : Nat) : JStr := (s.take e).drop b

/-- A line of the statement file: `fix(s, 80)`. -/
def sl (s : JStr) : JStr := fixStr s 80
/-- A line of the HTML file: `fix(s, 100)`. -/
def hl (s : JStr) : JStr := fixStr s 100

/-! ## The texts of the callees -/

/-- `zu(v, n)` (`v ≠ Long.MIN_VALUE`, `n ≥ 0`): the last `n` decimal digits of `|v|`. -/
def zuI (v : Int) (n : Nat) : JStr := zpadStr v.natAbs n

/-- The last character of `zs`: the last digit `d`, the sign overpunched (`{`, `A`–`I`; `}`, `J`–`R`). -/
def zsLast (neg : Bool) (d : Nat) : JChar :=
  if neg then (if d = 0 then BitVec.ofNat 16 125 else BitVec.ofNat 16 (73 + d))
  else (if d = 0 then BitVec.ofNat 16 123 else BitVec.ofNat 16 (64 + d))

/-- `zs(v, n)` (`v ≠ Long.MIN_VALUE`, `n ≥ 1`): the last `n` digits of `|v|`, the last one with the sign. -/
def zsI (v : Int) (n : Nat) : JStr :=
  zpadStr (v.natAbs / 10) (n - 1) ++ [zsLast (decide (v < 0)) (v.natAbs % 10)]

/-- `fmtCurrBal(v)` (`v ≠ Long.MIN_VALUE`): `|v| mod 10¹¹` as 9 digits, `.`, 2 digits, then `-` or a space. -/
def fmtCurrBalI (v : Int) : JStr :=
  zpadStr (v.natAbs % 100000000000 / 100) 9 ++ [chDot] ++ zpadStr (v.natAbs % 100000000000 % 100) 2 ++
    [if v < 0 then chDash else space]

/-- The number of leading `0` characters. -/
def lead0T (s : JStr) : Nat := (s.takeWhile (· == chZero)).length

/-- `fmtZ(v)` (`v ≠ Long.MIN_VALUE`): `fmtCurrBal(v)` with the leading zeros of the integer part as spaces. -/
def fmtZI (v : Int) : JStr :=
  List.replicate (lead0T (zpadStr (v.natAbs % 100000000000 / 100) 9)) space ++
    (zpadStr (v.natAbs % 100000000000 / 100) 9).drop (lead0T (zpadStr (v.natAbs % 100000000000 / 100) 9)) ++
    [chDot] ++ zpadStr (v.natAbs % 100000000000 % 100) 2 ++ [if v < 0 then chDash else space]

/-- `decodeZoned`: the digit of a character before the last one (its low four bits, mod 10). -/
def zdig (c : JChar) : Nat := c.toNat % 16 % 10

/-- `decodeZoned`: the digit and the sign of the last character. -/
def zlast (c : JChar) : Nat × Bool :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then (c.toNat - 48, false)
  else if c.toNat = 123 then (0, false)
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 73 then (c.toNat - 64, false)
  else if c.toNat = 125 then (0, true)
  else if 74 ≤ c.toNat ∧ c.toNat ≤ 82 then (c.toNat - 73, true)
  else if 112 ≤ c.toNat ∧ c.toNat ≤ 121 then (c.toNat - 112, true)
  else (zdig c, false)

/-- `decodeZoned(s)` (at most 18 characters, no overflow): the value of the zoned decimal `s`. -/
def decodeZonedI (s : JStr) : Int :=
  match s.getLast? with
  | none => 0
  | some c =>
    if (zlast c).2 then -(((s.dropLast.foldl (fun v d => v * 10 + zdig d) 0) * 10 + (zlast c).1 : Nat) : Int)
    else (((s.dropLast.foldl (fun v d => v * 10 + zdig d) 0) * 10 + (zlast c).1 : Nat) : Int)

/-- `s` cut before the first occurrence of `d` (`s.indexOf(d)`). -/
def cutAtT (s d : JStr) : JStr :=
  if 0 ≤ JStr.indexOf s d then s.take (JStr.indexOf s d).toNat else s

/-- `app(dst, cap, src, delim)` on the builder's text `dst`: `src` cut before `delim` (none for `null`),
as much of it as fits in `cap` characters. -/
def appT (dst : JStr) (cap : Nat) (src : JStr) (delim : Option JStr) : JStr :=
  dst ++ (match delim with
    | none => src
    | some d => cutAtT src d).take (cap - dst.length)

/-- `star(prefix, field)`. -/
def starT (pre field : JStr) : JStr :=
  fixStr (appT (appT (appT [] 100 pre (some [chStar])) 100 field (some [chStar])) 100 (jl "</p>")
    (some [chStar])) 100

/-- `para(prefix, field)`. -/
def paraT (pre field : JStr) : JStr :=
  fixStr (appT (appT (appT (appT [] 100 pre (some [chStar])) 100 field (some [space, space])) 100
    [space, space] none) 100 (jl "</p>") (some [chStar])) 100

/-! ## The HTML constants -/

abbrev L01 : JStr := jl "<!DOCTYPE html>"
abbrev L02 : JStr := jl "<html lang=\"en\">"
abbrev L03 : JStr := jl "<head>"
abbrev L04 : JStr := jl "<meta charset=\"utf-8\">"
abbrev L05 : JStr := jl "<title>HTML Table Layout</title>"
abbrev L06 : JStr := jl "</head>"
abbrev L07 : JStr := jl "<body style=\"margin:0px;\">"
abbrev L08 : JStr :=
  jl "<table  align=\"center\" frame=\"box\" style=\"width:70%; font:12px Segoe UI,sans-serif;\">"
abbrev LTRS : JStr := jl "<tr>"
abbrev LTRE : JStr := jl "</tr>"
abbrev LTDE : JStr := jl "</td>"
abbrev L10 : JStr := jl "<td colspan=\"3\" style=\"padding:0px 5px;background-color:#1d1d96b3;\">"
abbrev L15 : JStr := jl "<td colspan=\"3\" style=\"padding:0px 5px;background-color:#FFAF33;\">"
abbrev L16 : JStr := jl "<p style=\"font-size:16px\">Bank of XYZ</p>"
abbrev L17 : JStr := jl "<p>410 Terry Ave N</p>"
abbrev L18 : JStr := jl "<p>Seattle WA 99999</p>"
abbrev L22_35 : JStr := jl "<td colspan=\"3\" style=\"padding:0px 5px;background-color:#f2f2f2;\">"
abbrev L30_42 : JStr :=
  jl "<td colspan=\"3\" style=\"padding:0px 5px;background-color:#33FFD1; text-align:center;\">"
abbrev L31 : JStr := jl "<p style=\"font-size:16px\">Basic Details</p>"
abbrev L43 : JStr := jl "<p style=\"font-size:16px\">Transaction Summary</p>"
abbrev L47 : JStr := jl "<td style=\"width:25%; padding:0px 5px; background-color:#33FF5E; text-align:left;\">"
abbrev L48 : JStr := jl "<p style=\"font-size:16px\">Tran ID</p>"
abbrev L50 : JStr := jl "<td style=\"width:55%; padding:0px 5px; background-color:#33FF5E; text-align:left;\">"
abbrev L51 : JStr := jl "<p style=\"font-size:16px\">Tran Details</p>"
abbrev L53 : JStr := jl "<td style=\"width:20%; padding:0px 5px; background-color:#33FF5E; text-align:right;\">"
abbrev L54 : JStr := jl "<p style=\"font-size:16px\">Amount</p>"
abbrev L58 : JStr := jl "<td style=\"width:25%; padding:0px 5px; background-color:#f2f2f2; text-align:left;\">"
abbrev L61 : JStr := jl "<td style=\"width:55%; padding:0px 5px; background-color:#f2f2f2; text-align:left;\">"
abbrev L64 : JStr := jl "<td style=\"width:20%; padding:0px 5px; background-color:#f2f2f2; text-align:right;\">"
abbrev L75 : JStr := jl "<h3>End of Statement</h3>"
abbrev L78 : JStr := jl "</table>"
abbrev L79 : JStr := jl "</body>"
abbrev L80 : JStr := jl "</html>"

/-! ## The lines `writeTrans` and `createStatement` write -/

/-- `writeTrans(res, tid, trest, amt)`: the statement line and the HTML lines (each `fix`ed by `stmt`/`html`). -/
def jWriteTrans (tid trest : JStr) (amt : Int) : List JStr × List JStr :=
  ([sl (tid ++ [space] ++ sub trest 16 65 ++ [chDollar] ++ fmtZI amt)],
   [hl LTRS, hl L58, hl (starT (jl "<p>") tid), hl LTDE, hl L61, hl (starT (jl "<p>") (sub trest 16 65)),
    hl LTDE, hl L64, hl (starT (jl "<p>") (fmtZI amt)), hl LTDE, hl LTRE])

/-- `createStatement`'s name line (`st-name`): first, middle and last name, each cut at its first space. -/
def stNameT (cr : JStr) : JStr :=
  fixStr (appT (appT (appT (appT (appT (appT [] 75 (sub cr 9 34) (some [space])) 75 [space] none) 75
    (sub cr 34 59) (some [space])) 75 [space] none) 75 (sub cr 59 84) (some [space])) 75 [space] none) 75

/-- `createStatement`'s third address line (`st-add3`): line 3, state, country, zip, each cut at its first
space. -/
def stAdd3T (cr : JStr) : JStr :=
  fixStr (appT (appT (appT (appT (appT (appT (appT (appT [] 80 (sub cr 184 234) (some [space])) 80 [space] none)
    80 (sub cr 234 236) (some [space])) 80 [space] none) 80 (sub cr 236 239) (some [space])) 80 [space] none) 80
    (sub cr 239 249) (some [space])) 80 [space] none) 80

/-- `createStatement(res, custRec, acctRec)`: the statement lines and the HTML lines (each `fix`ed by
`stmt`/`html`), from the customer record's text `cr` and the account record's text `ar`. -/
def jCreateStatement (cr ar : JStr) : List JStr × List JStr :=
  ([sl (List.replicate 31 chStar ++ jl "START OF STATEMENT" ++ List.replicate 31 chStar),
    sl (stNameT cr ++ List.replicate 5 space),
    sl (sub cr 84 134 ++ List.replicate 30 space),
    sl (sub cr 134 184 ++ List.replicate 30 space),
    sl (stAdd3T cr),
    sl (List.replicate 80 chDash),
    sl (List.replicate 33 space ++ jl "Basic Details " ++ List.replicate 33 space),
    sl (List.replicate 80 chDash),
    sl (jl "Account ID         :" ++ fixStr (sub ar 0 11) 20 ++ List.replicate 40 space),
    sl (jl "Current Balance    :" ++ fmtCurrBalI (decodeZonedI (sub ar 12 24)) ++ List.replicate 47 space),
    sl (jl "FICO Score         :" ++ fixStr (sub cr 329 332) 20 ++ List.replicate 40 space),
    sl (List.replicate 80 chDash),
    sl (List.replicate 30 space ++ jl "TRANSACTION SUMMARY " ++ List.replicate 30 space),
    sl (List.replicate 80 chDash),
    sl (jl "Tran ID         " ++ fixStr (jl "Tran Details    ") 51 ++ jl "  Tran Amount"),
    sl (List.replicate 80 chDash)],
   [hl L01, hl L02, hl L03, hl L04, hl L05, hl L06, hl L07, hl L08, hl LTRS, hl L10,
    hl (jl "<h3>Statement for Account Number: " ++ fixStr (sub ar 0 11) 20 ++ jl "</h3>"),
    hl LTDE, hl LTRE, hl LTRS, hl L15, hl L16, hl L17, hl L18, hl LTDE, hl LTRE, hl LTRS, hl L22_35,
    hl (paraT (jl "<p style=\"font-size:16px\">") (sub (stNameT cr) 0 50)),
    hl (paraT (jl "<p>") (sub cr 84 134)),
    hl (paraT (jl "<p>") (sub cr 134 184)),
    hl (paraT (jl "<p>") (stAdd3T cr)),
    hl LTDE, hl LTRE, hl LTRS, hl L30_42, hl L31, hl LTDE, hl LTRE, hl LTRS, hl L22_35,
    hl (starT (jl "<p>Account ID         : ") (fixStr (sub ar 0 11) 20)),
    hl (starT (jl "<p>Current Balance    : ") (fmtCurrBalI (decodeZonedI (sub ar 12 24)))),
    hl (starT (jl "<p>FICO Score         : ") (fixStr (sub cr 329 332) 20)),
    hl LTDE, hl LTRE, hl LTRS, hl L30_42, hl L43, hl LTDE, hl LTRE, hl LTRS, hl L47, hl L48, hl LTDE,
    hl L50, hl L51, hl LTDE, hl L53, hl L54, hl LTDE, hl LTRE])

/-! ## The `Result` object -/

abbrev resC : ClassName := "Cbstm03a$Result"

/-- The object at `l` is an `ArrayList` holding exactly the strings `ss`. -/
def ListAt (σ : State) (l : Addr) (ss : List JStr) : Prop :=
  ∃ xs m, σ.heap l = some (.list .arrayList xs m) ∧ Forall2 (JStrAt σ) xs ss

/-- The `Result` object at `res`: its lists `displays`, `stmtFileWrites`, `htmlFileWrites` at `ld`, `ls`, `lh`
(three distinct lists) hold `disp`, `st`, `ht`; `abended` is `ab`. -/
def ResAtL (σ : State) (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) : Prop :=
  ∃ fs, σ.heap res = some (.plain resC fs) ∧
    Fields.get fs (resC, "displays") = some (.ref ld) ∧
    Fields.get fs (resC, "stmtFileWrites") = some (.ref ls) ∧
    Fields.get fs (resC, "htmlFileWrites") = some (.ref lh) ∧
    Fields.get fs (resC, "abended") = some (.int (if ab then 1 else 0)) ∧
    ld ≠ ls ∧ ld ≠ lh ∧ ls ≠ lh ∧ ListAt σ ld disp ∧ ListAt σ ls st ∧ ListAt σ lh ht

/-- The `Result` object at `res` (its lists somewhere) holds `disp`, `st`, `ht`, `ab`. -/
def ResAt (σ : State) (res : Addr) (disp st ht : List JStr) (ab : Bool) : Prop :=
  ∃ ld ls lh, ResAtL σ res ld ls lh disp st ht ab

/-- Every object of `σ` but the `Result` object and its three lists is unchanged in `σ'`. -/
def KeepsRes (res ld ls lh : Addr) (σ σ' : State) : Prop :=
  σ.next ≤ σ'.next ∧ ∀ y, y < σ.next → y ≠ res → y ≠ ld → y ≠ ls → y ≠ lh → σ'.heap y = σ.heap y

/-! ## The records -/

abbrev trnxC : ClassName := "Cbstm03a$TrnxRecord"
abbrev xrefC : ClassName := "Cbstm03a$CardXrefRecord"
abbrev custC : ClassName := "Cbstm03a$CustomerRecord"
abbrev acctC : ClassName := "Cbstm03a$AccountRecord"

/-- String field `f` holds a string (not `null`) with the text `s`. -/
def SFld (σ : State) (c : ClassName) (fs : List (FieldKey × Value)) (f : String) (s : JStr) : Prop :=
  ∃ x, Fields.get fs (c, f) = some (.ref x) ∧ σ.heap x = some (.str s) ∧ s.length < 2147483648

/-- `long` field `f` holds `l`, not `Long.MIN_VALUE`. -/
def LFld (c : ClassName) (fs : List (FieldKey × Value)) (f : String) (l : I64) : Prop :=
  Fields.get fs (c, f) = some (.long l) ∧ -9223372036854775808 < l.toInt

/-- A `TrnxRecord`'s field values (the string fields by their texts). -/
structure TrnxR where
  cardNum : JStr
  id : JStr
  typeCd : JStr
  catCd : I64
  source : JStr
  desc : JStr
  amt : I64
  merchantId : I64
  merchantName : JStr
  merchantCity : JStr
  merchantZip : JStr
  origTs : JStr
  procTs : JStr
  filler1 : JStr

def TrnxAt (σ : State) (x : Addr) (t : TrnxR) : Prop :=
  ∃ fs, σ.heap x = some (.plain trnxC fs) ∧
    SFld σ trnxC fs "trnxCardNum" t.cardNum ∧ SFld σ trnxC fs "trnxId" t.id ∧
    SFld σ trnxC fs "trnxTypeCd" t.typeCd ∧ LFld trnxC fs "trnxCatCd" t.catCd ∧
    SFld σ trnxC fs "trnxSource" t.source ∧ SFld σ trnxC fs "trnxDesc" t.desc ∧
    LFld trnxC fs "trnxAmt" t.amt ∧ LFld trnxC fs "trnxMerchantId" t.merchantId ∧
    SFld σ trnxC fs "trnxMerchantName" t.merchantName ∧ SFld σ trnxC fs "trnxMerchantCity" t.merchantCity ∧
    SFld σ trnxC fs "trnxMerchantZip" t.merchantZip ∧ SFld σ trnxC fs "trnxOrigTs" t.origTs ∧
    SFld σ trnxC fs "trnxProcTs" t.procTs ∧ SFld σ trnxC fs "filler1" t.filler1

/-- `v` is `null` (`none`) or a `TrnxRecord` holding `t`. -/
def TrnxAtN (σ : State) (v : Value) : Option TrnxR → Prop
  | none => v = .null
  | some t => ∃ x, v = .ref x ∧ TrnxAt σ x t

def trnxTextR (t : TrnxR) : JStr :=
  fixStr t.cardNum 16 ++ fixStr t.id 16 ++ fixStr t.typeCd 2 ++ zuI t.catCd.toInt 4 ++ fixStr t.source 10 ++
    fixStr t.desc 100 ++ zsI t.amt.toInt 11 ++ zuI t.merchantId.toInt 9 ++ fixStr t.merchantName 50 ++
    fixStr t.merchantCity 50 ++ fixStr t.merchantZip 10 ++ fixStr t.origTs 26 ++ fixStr t.procTs 26 ++
    fixStr t.filler1 20

def trnxTextO : Option TrnxR → JStr
  | none => List.replicate 350 space
  | some t => trnxTextR t

/-- A `CardXrefRecord`'s field values. -/
structure XrefR where
  cardNum : JStr
  custId : I64
  acctId : I64
  filler1 : JStr

def XrefAt (σ : State) (x : Addr) (t : XrefR) : Prop :=
  ∃ fs, σ.heap x = some (.plain xrefC fs) ∧
    SFld σ xrefC fs "xrefCardNum" t.cardNum ∧ LFld xrefC fs "xrefCustId" t.custId ∧
    LFld xrefC fs "xrefAcctId" t.acctId ∧ SFld σ xrefC fs "filler1" t.filler1

def XrefAtN (σ : State) (v : Value) : Option XrefR → Prop
  | none => v = .null
  | some t => ∃ x, v = .ref x ∧ XrefAt σ x t

def xrefTextR (t : XrefR) : JStr :=
  fixStr t.cardNum 16 ++ zuI t.custId.toInt 9 ++ zuI t.acctId.toInt 11 ++ fixStr t.filler1 14

def xrefTextO : Option XrefR → JStr
  | none => List.replicate 50 space
  | some t => xrefTextR t

/-- A `CustomerRecord`'s field values. -/
structure CustR where
  custId : I64
  firstName : JStr
  middleName : JStr
  lastName : JStr
  addrLine1 : JStr
  addrLine2 : JStr
  addrLine3 : JStr
  addrStateCd : JStr
  addrCountryCd : JStr
  addrZip : JStr
  phoneNum1 : JStr
  phoneNum2 : JStr
  ssn : I64
  govtIssuedId : JStr
  dobYyyymmdd : JStr
  eftAccountId : JStr
  priCardHolderInd : JStr
  ficoCreditScore : I64
  filler1 : JStr

def CustAt (σ : State) (x : Addr) (t : CustR) : Prop :=
  ∃ fs, σ.heap x = some (.plain custC fs) ∧
    LFld custC fs "custId" t.custId ∧ SFld σ custC fs "custFirstName" t.firstName ∧
    SFld σ custC fs "custMiddleName" t.middleName ∧ SFld σ custC fs "custLastName" t.lastName ∧
    SFld σ custC fs "custAddrLine1" t.addrLine1 ∧ SFld σ custC fs "custAddrLine2" t.addrLine2 ∧
    SFld σ custC fs "custAddrLine3" t.addrLine3 ∧ SFld σ custC fs "custAddrStateCd" t.addrStateCd ∧
    SFld σ custC fs "custAddrCountryCd" t.addrCountryCd ∧ SFld σ custC fs "custAddrZip" t.addrZip ∧
    SFld σ custC fs "custPhoneNum1" t.phoneNum1 ∧ SFld σ custC fs "custPhoneNum2" t.phoneNum2 ∧
    LFld custC fs "custSsn" t.ssn ∧ SFld σ custC fs "custGovtIssuedId" t.govtIssuedId ∧
    SFld σ custC fs "custDobYyyymmdd" t.dobYyyymmdd ∧ SFld σ custC fs "custEftAccountId" t.eftAccountId ∧
    SFld σ custC fs "custPriCardHolderInd" t.priCardHolderInd ∧
    LFld custC fs "custFicoCreditScore" t.ficoCreditScore ∧ SFld σ custC fs "filler1" t.filler1

def CustAtN (σ : State) (v : Value) : Option CustR → Prop
  | none => v = .null
  | some t => ∃ x, v = .ref x ∧ CustAt σ x t

def custTextR (t : CustR) : JStr :=
  zuI t.custId.toInt 9 ++ fixStr t.firstName 25 ++ fixStr t.middleName 25 ++ fixStr t.lastName 25 ++
    fixStr t.addrLine1 50 ++ fixStr t.addrLine2 50 ++ fixStr t.addrLine3 50 ++ fixStr t.addrStateCd 2 ++
    fixStr t.addrCountryCd 3 ++ fixStr t.addrZip 10 ++ fixStr t.phoneNum1 15 ++ fixStr t.phoneNum2 15 ++
    zuI t.ssn.toInt 9 ++ fixStr t.govtIssuedId 20 ++ fixStr t.dobYyyymmdd 10 ++ fixStr t.eftAccountId 10 ++
    fixStr t.priCardHolderInd 1 ++ zuI t.ficoCreditScore.toInt 3 ++ fixStr t.filler1 168

def custTextO : Option CustR → JStr
  | none => List.replicate 500 space
  | some t => custTextR t

/-- An `AccountRecord`'s field values. -/
structure AcctR where
  acctId : I64
  activeStatus : JStr
  currBal : I64
  creditLimit : I64
  cashCreditLimit : I64
  openDate : JStr
  expiraionDate : JStr
  reissueDate : JStr
  currCycCredit : I64
  currCycDebit : I64
  addrZip : JStr
  groupId : JStr
  filler1 : JStr

def AcctAt (σ : State) (x : Addr) (t : AcctR) : Prop :=
  ∃ fs, σ.heap x = some (.plain acctC fs) ∧
    LFld acctC fs "acctId" t.acctId ∧ SFld σ acctC fs "acctActiveStatus" t.activeStatus ∧
    LFld acctC fs "acctCurrBal" t.currBal ∧ LFld acctC fs "acctCreditLimit" t.creditLimit ∧
    LFld acctC fs "acctCashCreditLimit" t.cashCreditLimit ∧ SFld σ acctC fs "acctOpenDate" t.openDate ∧
    SFld σ acctC fs "acctExpiraionDate" t.expiraionDate ∧ SFld σ acctC fs "acctReissueDate" t.reissueDate ∧
    LFld acctC fs "acctCurrCycCredit" t.currCycCredit ∧ LFld acctC fs "acctCurrCycDebit" t.currCycDebit ∧
    SFld σ acctC fs "acctAddrZip" t.addrZip ∧ SFld σ acctC fs "acctGroupId" t.groupId ∧
    SFld σ acctC fs "filler1" t.filler1

def AcctAtN (σ : State) (v : Value) : Option AcctR → Prop
  | none => v = .null
  | some t => ∃ x, v = .ref x ∧ AcctAt σ x t

def acctTextR (t : AcctR) : JStr :=
  zuI t.acctId.toInt 11 ++ fixStr t.activeStatus 1 ++ zsI t.currBal.toInt 12 ++ zsI t.creditLimit.toInt 12 ++
    zsI t.cashCreditLimit.toInt 12 ++ fixStr t.openDate 10 ++ fixStr t.expiraionDate 10 ++
    fixStr t.reissueDate 10 ++ zsI t.currCycCredit.toInt 12 ++ zsI t.currCycDebit.toInt 12 ++
    fixStr t.addrZip 10 ++ fixStr t.groupId 10 ++ fixStr t.filler1 178

def acctTextO : Option AcctR → JStr
  | none => List.replicate 300 space
  | some t => acctTextR t

/-! ## Methods -/

abbrev stmtRef : MethodRef := Gen.Cbstm03a.«stmt(Cbstm03a$Result,java.lang.String)».ref
abbrev htmlRef : MethodRef := Gen.Cbstm03a.«html(Cbstm03a$Result,java.lang.String)».ref
abbrev abendRef : MethodRef := Gen.Cbstm03a.«abend(Cbstm03a$Result,java.lang.String,java.lang.String)».ref
abbrev writeTransRef : MethodRef :=
  Gen.Cbstm03a.«writeTrans(Cbstm03a$Result,java.lang.String,java.lang.String,long)».ref
abbrev createStatementRef : MethodRef :=
  Gen.Cbstm03a.«createStatement(Cbstm03a$Result,java.lang.String,java.lang.String)».ref
abbrev trnxTextRef : MethodRef := Gen.Cbstm03a.«trnxText(Cbstm03a$TrnxRecord)».ref
abbrev xrefTextRef : MethodRef := Gen.Cbstm03a.«xrefText(Cbstm03a$CardXrefRecord)».ref
abbrev custTextRef : MethodRef := Gen.Cbstm03a.«custText(Cbstm03a$CustomerRecord)».ref
abbrev acctTextRef : MethodRef := Gen.Cbstm03a.«acctText(Cbstm03a$AccountRecord)».ref

def stmtSig : MethodSig := ⟨"Cbstm03a", .void, "stmt", [.cls resC, .cls "java.lang.String"]⟩
def htmlSig : MethodSig := ⟨"Cbstm03a", .void, "html", [.cls resC, .cls "java.lang.String"]⟩
def abendSig : MethodSig :=
  ⟨"Cbstm03a", .cls resC, "abend", [.cls resC, .cls "java.lang.String", .cls "java.lang.String"]⟩
def writeTransSig : MethodSig :=
  ⟨"Cbstm03a", .void, "writeTrans", [.cls resC, .cls "java.lang.String", .cls "java.lang.String", .prim .long]⟩
def createStatementSig : MethodSig :=
  ⟨"Cbstm03a", .void, "createStatement", [.cls resC, .cls "java.lang.String", .cls "java.lang.String"]⟩
def trnxTextSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "trnxText", [.cls trnxC]⟩
def xrefTextSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "xrefText", [.cls xrefC]⟩
def custTextSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "custText", [.cls custC]⟩
def acctTextSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "acctText", [.cls acctC]⟩

/-! ## The contracts -/

/-- `stmt(res, s)`: `fix(s, 80)` appended to the statement list. -/
def stmtSpec : Spec := Spec.of
  (fun args σ => ∃ (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (s : Value),
     args = [.ref res, s] ∧ ResAtL σ res ld ls lh disp st ht ab ∧ StrOk σ s ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (s : Value),
     args = [.ref res, s] → ResAtL σ res ld ls lh disp st ht ab →
     r = none ∧ ResAtL σ' res ld ls lh disp (st ++ [sl (argText σ s)]) ht ab ∧ KeepsRes res ld ls lh σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `html(res, s)`: `fix(s, 100)` appended to the HTML list. -/
def htmlSpec : Spec := Spec.of
  (fun args σ => ∃ (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (s : Value),
     args = [.ref res, s] ∧ ResAtL σ res ld ls lh disp st ht ab ∧ StrOk σ s ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (s : Value),
     args = [.ref res, s] → ResAtL σ res ld ls lh disp st ht ab →
     r = none ∧ ResAtL σ' res ld ls lh disp st (ht ++ [hl (argText σ s)]) ab ∧ KeepsRes res ld ls lh σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `abend(res, msg, rc)` (both strings): `msg`, `RETURN CODE: rc`, `ABENDING PROGRAM` displayed, `abended`
set, `res` returned. -/
def abendSpec : Spec := Spec.of
  (fun args σ => ∃ (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (mv rv : Value) (m c : JStr),
     args = [.ref res, mv, rv] ∧ ResAtL σ res ld ls lh disp st ht ab ∧ JStrAt σ mv m ∧ JStrAt σ rv c ∧
     σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (mv rv : Value),
     args = [.ref res, mv, rv] → ResAtL σ res ld ls lh disp st ht ab →
     r = some (.ref res) ∧
       ResAtL σ' res ld ls lh (disp ++ [argText σ mv, jl "RETURN CODE: " ++ argText σ rv, jl "ABENDING PROGRAM"])
         st ht true ∧
       KeepsRes res ld ls lh σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `writeTrans(res, tid, trest, amt)` (`trest` of at least 65 characters, the id shorter than 10^6 so that the
concatenated line stays a Java string, `amt ≠ Long.MIN_VALUE`): the lines of `jWriteTrans` appended. -/
def writeTransSpec : Spec := Spec.of
  (fun args σ => ∃ (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (tv rv : Value) (amt : I64)
       (t tr : JStr),
     args = [.ref res, tv, rv, .long amt] ∧ ResAtL σ res ld ls lh disp st ht ab ∧ JStrAt σ tv t ∧
     JStrAt σ rv tr ∧ 65 ≤ tr.length ∧ tr.length < 2147483648 ∧ t.length < 1000000 ∧
     -9223372036854775808 < amt.toInt ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (tv rv : Value) (amt : I64),
     args = [.ref res, tv, rv, .long amt] → ResAtL σ res ld ls lh disp st ht ab →
     r = none ∧
       ResAtL σ' res ld ls lh disp (st ++ (jWriteTrans (argText σ tv) (argText σ rv) amt.toInt).1)
         (ht ++ (jWriteTrans (argText σ tv) (argText σ rv) amt.toInt).2) ab ∧
       KeepsRes res ld ls lh σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `createStatement(res, custRec, acctRec)` (texts of at least 332 and 24 characters): the lines of
`jCreateStatement` appended. -/
def createStatementSpec : Spec := Spec.of
  (fun args σ => ∃ (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (cv av : Value) (c a : JStr),
     args = [.ref res, cv, av] ∧ ResAtL σ res ld ls lh disp st ht ab ∧ JStrAt σ cv c ∧ JStrAt σ av a ∧
     332 ≤ c.length ∧ c.length < 2147483648 ∧ 24 ≤ a.length ∧ a.length < 2147483648 ∧
     σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (cv av : Value),
     args = [.ref res, cv, av] → ResAtL σ res ld ls lh disp st ht ab →
     r = none ∧
       ResAtL σ' res ld ls lh disp (st ++ (jCreateStatement (argText σ cv) (argText σ av)).1)
         (ht ++ (jCreateStatement (argText σ cv) (argText σ av)).2) ab ∧
       KeepsRes res ld ls lh σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `trnxText(r)`: the record's text (350 spaces for `null`), a new string. -/
def trnxTextSpec : Spec := Spec.of
  (fun args σ => ∃ (v : Value) (t : Option TrnxR), args = [v] ∧ TrnxAtN σ v t ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (v : Value) (t : Option TrnxR), args = [v] → TrnxAtN σ v t →
     ∃ y, r = some (.ref y) ∧ σ.next ≤ y ∧ σ'.heap y = some (.str (trnxTextO t)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `xrefText(r)`: the record's text (50 spaces for `null`), a new string. -/
def xrefTextSpec : Spec := Spec.of
  (fun args σ => ∃ (v : Value) (t : Option XrefR), args = [v] ∧ XrefAtN σ v t ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (v : Value) (t : Option XrefR), args = [v] → XrefAtN σ v t →
     ∃ y, r = some (.ref y) ∧ σ.next ≤ y ∧ σ'.heap y = some (.str (xrefTextO t)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `custText(r)`: the record's text (500 spaces for `null`), a new string. -/
def custTextSpec : Spec := Spec.of
  (fun args σ => ∃ (v : Value) (t : Option CustR), args = [v] ∧ CustAtN σ v t ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (v : Value) (t : Option CustR), args = [v] → CustAtN σ v t →
     ∃ y, r = some (.ref y) ∧ σ.next ≤ y ∧ σ'.heap y = some (.str (custTextO t)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `acctText(r)`: the record's text (300 spaces for `null`), a new string. -/
def acctTextSpec : Spec := Spec.of
  (fun args σ => ∃ (v : Value) (t : Option AcctR), args = [v] ∧ AcctAtN σ v t ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (v : Value) (t : Option AcctR), args = [v] → AcctAtN σ v t →
     ∃ y, r = some (.ref y) ∧ σ.next ≤ y ∧ σ'.heap y = some (.str (acctTextO t)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

end EquivLean.Modernize.Cbstm03a.Java
