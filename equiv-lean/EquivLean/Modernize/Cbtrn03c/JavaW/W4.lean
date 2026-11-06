import EquivLean.Modernize.Cbtrn03c.JavaW.W2
import EquivLean.Modernize.Cbtrn03c.JavaW.Bridge

/-!
# CBTRN03C → Java: `writeHeaders`, `writeDetail`, the contracts and their cuts

As `writePageTotals` (`W2.lean`): the ghost values are parameters, one cut at each `writeLine`
call (`writeHeaders`: statements 14, 17, 35, 38; `writeDetail`: statement 37).  Segments in
`W4a`, `W4b`, `W4c`; `W4v` puts them together.

Locals of `writeHeaders`: `$r1` (the builder) 0, `r0` (the `Ws` object) 1, `$r2` (the line) 2.
Locals of `writeDetail`: `r0` 0, `r2` (the line) 3.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

def linesCallees : Contracts :=
  [(padSig, padSpecF), (spacesSig, spacesSpec), (repeatSig, repeatSpec), (digitsSig, digitsSpec),
   (editSig, editSpec), (writeLineSig, writeLineSpec), (incLineSig, incLineSpec)]

theorem linesCallees_valid : Valid Gen.prog linesCallees.env := by
  apply Contracts.valid_of_ok
  simp only [linesCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨padF_ok, spaces_ok, repeat_ok, digits_ok, edit_ok, writeLine_ok, incLine_ok⟩

theorem cp037Str_length (bs : List UInt8) : (cp037Str bs).length = bs.length := by
  simp [cp037Str]

theorem zpadJ_length' (c m : Nat) : (zpadJ c m).length = m := zpadJ_length c m

/-! ## `writeHeaders` -/

/-- `REPORT-NAME-HEADER` with the date strings `rs`, `re`. -/
def nameHeaderJ (rs re : JStr) : JStr :=
  fixJ (JStr.ofString "DALYREPT") 38 ++ (fixJ (JStr.ofString "Daily Transaction Report") 41 ++
    (JStr.ofString "Date Range: " ++ (rs ++ (JStr.ofString " to " ++ re))))

/-- `TRANSACTION-HEADER-1`. -/
def header1J : JStr :=
  fixJ (JStr.ofString "Transaction ID") 17 ++ (fixJ (JStr.ofString "Account ID") 12 ++
    (fixJ (JStr.ofString "Transaction Type") 19 ++ (fixJ (JStr.ofString "Tran Category") 35 ++
      (fixJ (JStr.ofString "Tran Source") 14 ++ (space :: fixJ (JStr.ofString "        Amount") 16)))))

/-- The builder of `TRANSACTION-HEADER-1` after two and after four fields. -/
def hdrP1 : JStr := fixJ (JStr.ofString "Transaction ID") 17 ++ fixJ (JStr.ofString "Account ID") 12
def hdrP2 : JStr :=
  hdrP1 ++ (fixJ (JStr.ofString "Transaction Type") 19 ++ fixJ (JStr.ofString "Tran Category") 35)

theorem nameHeaderJ_length (rs re : JStr) :
    (nameHeaderJ rs re).length = rs.length + re.length + 95 := by
  have h1 : (JStr.ofString "Date Range: ").length = 12 := by decide
  have h2 : (JStr.ofString " to ").length = 4 := by decide
  simp only [nameHeaderJ, List.length_append, fixJ_length, h1, h2]
  omega

theorem header1J_length : header1J.length = 114 := by
  simp [header1J, fixJ_length]

theorem dashJ_length : dashJ.length = 133 := by
  simp [dashJ, repJ_length]

abbrev writeHeadersRef : MethodRef := Gen.Cbtrn03c.«writeHeaders(Cbtrn03c$Ws)».ref

def hdr1V (v : WsV) (r1 : Value) : WsV :=
  { v with
    wrs := v.wrs ++ [r1]
    lc := incL v.lc }

def hdr2V (v : WsV) (r1 r2 : Value) : WsV :=
  { v with
    wrs := v.wrs ++ [r1] ++ [r2]
    lc := incL (incL v.lc) }

def hdr3V (v : WsV) (r1 r2 r3 : Value) : WsV :=
  { v with
    wrs := v.wrs ++ [r1] ++ [r2] ++ [r3]
    lc := incL (incL (incL v.lc)) }

def hdr4V (v : WsV) (r1 r2 r3 r4 : Value) : WsV :=
  { v with
    wrs := v.wrs ++ [r1] ++ [r2] ++ [r3] ++ [r4]
    lc := incL (incL (incL (incL v.lc))) }

/-- The report record at `r` holds the text `t`. -/
def RecT (σ : State) (r : Addr) (t : JStr) : Prop :=
  ∃ f z, σ.heap r = some (.plain fdC f) ∧ Fields.get f (fdC, "fdReptfileRec") = some (.ref z) ∧
    σ.heap z = some (.str t)

/-- A new report record (allocated since `σ0`) holding `t`. -/
def NewRecT (σ0 σ : State) (r : Addr) (t : JStr) : Prop :=
  ∃ f z, σ.heap r = some (.plain fdC f) ∧ Fields.get f (fdC, "fdReptfileRec") = some (.ref z) ∧
    σ.heap z = some (.str t) ∧ σ0.next ≤ r ∧ σ0.next ≤ z

/-- `writeHeaders` for given ghost values (the date strings at `xs`, `xe` hold `rs`, `re`). -/
def writeHeadersSpecG (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) : Spec := Spec.of
  (fun args σ => args = [.ref w] ∧ WsAt σ w ld lr v ∧ v.rsRef = .ref xs ∧
     σ.heap xs = some (.str rs) ∧ v.reRef = .ref xe ∧ σ.heap xe = some (.str re) ∧
     rs.length < 1000 ∧ re.length < 1000 ∧ σ.initOf "Cbtrn03c" = .done ∧ σ.initOf fdC = .done)
  (fun args σ r σ' => ∃ r1 r2 r3 r4, r = none ∧
     WsAt σ' w ld lr (hdr4V v (.ref r1) (.ref r2) (.ref r3) (.ref r4)) ∧
     RecT σ' r1 (fixJ (nameHeaderJ rs re) 133) ∧ RecT σ' r2 (fixJ (spJ 133) 133) ∧
     RecT σ' r3 (fixJ header1J 133) ∧ RecT σ' r4 (fixJ dashJ 133) ∧
     Frame3 σ σ' w ld lr ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- At the first `writeLine` (statement 14). -/
def whI1 (w ld lr : Addr) (v : WsV) (rs re : JStr) (σ0 : State) (fr : Frame) (σ : State) :
    Prop :=
  ∃ y, fr.get 1 = some (.ref w) ∧ fr.get 2 = some (.ref y) ∧
    σ.heap y = some (.str (nameHeaderJ rs re)) ∧ rs.length < 1000 ∧ re.length < 1000 ∧
    WsAt σ w ld lr v ∧ Frame3 σ0 σ w ld lr ∧ w < σ0.next ∧ ld < σ0.next ∧ lr < σ0.next ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

/-- At the second `writeLine` (statement 17). -/
def whI2 (w ld lr : Addr) (v : WsV) (rs re : JStr) (σ0 : State) (fr : Frame) (σ : State) :
    Prop :=
  ∃ y r1, fr.get 1 = some (.ref w) ∧ fr.get 2 = some (.ref y) ∧
    σ.heap y = some (.str (spJ 133)) ∧ WsAt σ w ld lr (hdr1V v (.ref r1)) ∧
    NewRecT σ0 σ r1 (fixJ (nameHeaderJ rs re) 133) ∧
    Frame3 σ0 σ w ld lr ∧ w < σ0.next ∧ ld < σ0.next ∧ lr < σ0.next ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

/-- Building `TRANSACTION-HEADER-1` (statement 25: two fields appended). -/
def whI2a (w ld lr : Addr) (v : WsV) (rs re : JStr) (σ0 : State) (fr : Frame) (σ : State) :
    Prop :=
  ∃ sb r1 r2, fr.get 1 = some (.ref w) ∧ fr.get 0 = some (.ref sb) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" hdrP1) ∧ σ0.next ≤ sb ∧
    WsAt σ w ld lr (hdr2V v (.ref r1) (.ref r2)) ∧
    NewRecT σ0 σ r1 (fixJ (nameHeaderJ rs re) 133) ∧ NewRecT σ0 σ r2 (fixJ (spJ 133) 133) ∧
    Frame3 σ0 σ w ld lr ∧ w < σ0.next ∧ ld < σ0.next ∧ lr < σ0.next ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

/-- Building `TRANSACTION-HEADER-1` (statement 29: four fields appended). -/
def whI2b (w ld lr : Addr) (v : WsV) (rs re : JStr) (σ0 : State) (fr : Frame) (σ : State) :
    Prop :=
  ∃ sb r1 r2, fr.get 1 = some (.ref w) ∧ fr.get 0 = some (.ref sb) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" hdrP2) ∧ σ0.next ≤ sb ∧
    WsAt σ w ld lr (hdr2V v (.ref r1) (.ref r2)) ∧
    NewRecT σ0 σ r1 (fixJ (nameHeaderJ rs re) 133) ∧ NewRecT σ0 σ r2 (fixJ (spJ 133) 133) ∧
    Frame3 σ0 σ w ld lr ∧ w < σ0.next ∧ ld < σ0.next ∧ lr < σ0.next ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

/-- At the third `writeLine` (statement 35). -/
def whI3 (w ld lr : Addr) (v : WsV) (rs re : JStr) (σ0 : State) (fr : Frame) (σ : State) :
    Prop :=
  ∃ y r1 r2, fr.get 1 = some (.ref w) ∧ fr.get 2 = some (.ref y) ∧
    σ.heap y = some (.str header1J) ∧ WsAt σ w ld lr (hdr2V v (.ref r1) (.ref r2)) ∧
    NewRecT σ0 σ r1 (fixJ (nameHeaderJ rs re) 133) ∧ NewRecT σ0 σ r2 (fixJ (spJ 133) 133) ∧
    Frame3 σ0 σ w ld lr ∧ w < σ0.next ∧ ld < σ0.next ∧ lr < σ0.next ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

/-- At the fourth `writeLine` (statement 38). -/
def whI4 (w ld lr : Addr) (v : WsV) (rs re : JStr) (σ0 : State) (fr : Frame) (σ : State) :
    Prop :=
  ∃ y r1 r2 r3, fr.get 1 = some (.ref w) ∧ fr.get 2 = some (.ref y) ∧
    σ.heap y = some (.str dashJ) ∧ WsAt σ w ld lr (hdr3V v (.ref r1) (.ref r2) (.ref r3)) ∧
    NewRecT σ0 σ r1 (fixJ (nameHeaderJ rs re) 133) ∧ NewRecT σ0 σ r2 (fixJ (spJ 133) 133) ∧
    NewRecT σ0 σ r3 (fixJ header1J 133) ∧
    Frame3 σ0 σ w ld lr ∧ w < σ0.next ∧ ld < σ0.next ∧ lr < σ0.next ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

def writeHeadersInv (w ld lr : Addr) (v : WsV) (rs re : JStr) : Invariants :=
  [(14, fun _ σ0 fr σ => whI1 w ld lr v rs re σ0 fr σ),
   (17, fun _ σ0 fr σ => whI2 w ld lr v rs re σ0 fr σ),
   (25, fun _ σ0 fr σ => whI2a w ld lr v rs re σ0 fr σ),
   (29, fun _ σ0 fr σ => whI2b w ld lr v rs re σ0 fr σ),
   (35, fun _ σ0 fr σ => whI3 w ld lr v rs re σ0 fr σ),
   (38, fun _ σ0 fr σ => whI4 w ld lr v rs re σ0 fr σ)]

/-- The paths of `writeHeaders` from statement `pc`. -/
def whWP (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) (args : List Value)
    (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog linesCallees.env 0) Gen.Cbtrn03c.«writeHeaders(Cbtrn03c$Ws)»
    ((writeHeadersInv w ld lr v rs re).inst args σ0)
    ((writeHeadersSpecG w ld lr v xs xe rs re).post args σ0) 120 pc fr σ

/-! ## `writeDetail` -/

/-- The builder of `TRANSACTION-DETAIL-REPORT`: up to the type code (statement 18). -/
def detP1 (t : List EquivLean.Cobol.Rec.FVal) (acct : I64) : JStr :=
  fixJ (cp037Str (Model.tId t)) 16 ++ (space ::
    (zpadJ acct.toInt.natAbs 11 ++ (space ::
      (fixJ (cp037Str (Model.tType t)) 2 ++ [BitVec.ofNat 16 45]))))

/-- … up to the category description (statement 28). -/
def detP2 (t : List EquivLean.Cobol.Rec.FVal) (acct : I64) (ys cs : JStr) : JStr :=
  detP1 t acct ++ (fixJ ys 15 ++ (space ::
    (zpadJ (BitVec.ofInt 64 (Model.tCat t)).toInt.natAbs 4 ++ (BitVec.ofNat 16 45 ::
      (fixJ cs 29 ++ [space])))))

/-- `TRANSACTION-DETAIL-REPORT` for the transaction `t`, the account id `acct`, the type and
category descriptions `ys`, `cs`. -/
def detailJ (t : List EquivLean.Cobol.Rec.FVal) (acct : I64) (ys cs : JStr) : JStr :=
  detP2 t acct ys cs ++ (fixJ (cp037Str (Model.tSource t)) 10 ++ (JStr.ofString "    " ++
    (editJ (decide ((BitVec.ofInt 64 (Model.tAmt t)).toInt < 0)) false
      ((BitVec.ofInt 64 (Model.tAmt t)).toInt.natAbs % 100000000000) ++ JStr.ofString "  ")))

theorem detailJ_length (t : List EquivLean.Cobol.Rec.FVal) (acct : I64) (ys cs : JStr) :
    (detailJ t acct ys cs).length = 114 := by
  have h1 : (JStr.ofString "    ").length = 4 := by decide
  have h2 : (JStr.ofString "  ").length = 2 := by decide
  simp only [detailJ, detP2, detP1, List.length_append, List.length_cons, List.length_nil,
    fixJ_length, zpadJ_length, editJ_length, h1, h2]

abbrev writeDetailRef : MethodRef :=
  Gen.Cbtrn03c.«writeDetail(Cbtrn03c$Ws,Cbtrn03c$TranRecord,java.lang.String,java.lang.String)».ref

def det1V (v : WsV) (r1 : Value) : WsV :=
  { v with
    wrs := v.wrs ++ [r1]
    lc := incL v.lc }

/-- The fields of the transaction record at `c` that the detail line shows. -/
def DetailFields (σ : State) (c : Addr) (t : List EquivLean.Cobol.Rec.FVal) : Prop :=
  ∃ fs, σ.heap c = some (.plain Top.tranC fs) ∧
    Top.SFld σ Top.tranC fs "tranId" (Model.tId t) ∧
    Top.SFld σ Top.tranC fs "tranTypeCd" (Model.tType t) ∧
    Top.LFld Top.tranC fs "tranCatCd" (Model.tCat t) ∧
    Top.SFld σ Top.tranC fs "tranSource" (Model.tSource t) ∧
    Top.LFld Top.tranC fs "tranAmt" (Model.tAmt t)

theorem detailFields_of {σ : State} {c : Addr} {t : List EquivLean.Cobol.Rec.FVal}
    (h : Top.TranFields σ c t) : DetailFields σ c t := by
  obtain ⟨fs, hc, h0, h1, h2, h3, -, h5, -⟩ := h
  exact ⟨fs, hc, h0, h1, h2, h3, h5⟩

/-- `writeDetail` for given ghost values (the transaction record at `c` holds `t`, the
descriptions at `yx`, `cx` hold `ys`, `cs`). -/
def writeDetailSpecG (w ld lr : Addr) (v : WsV) (c yx cx : Addr)
    (t : List EquivLean.Cobol.Rec.FVal) (ys cs : JStr) : Spec := Spec.of
  (fun args σ => args = [.ref w, .ref c, .ref yx, .ref cx] ∧ WsAt σ w ld lr v ∧
     -9223372036854775808 < v.acctId.toInt ∧ DetailFields σ c t ∧
     (Model.tId t).length < 1000 ∧ (Model.tType t).length < 1000 ∧
     (Model.tSource t).length < 1000 ∧
     -9223372036854775808 < (BitVec.ofInt 64 (Model.tCat t)).toInt ∧
     -9223372036854775808 < (BitVec.ofInt 64 (Model.tAmt t)).toInt ∧
     σ.heap yx = some (.str ys) ∧ ys.length < 1000 ∧ σ.heap cx = some (.str cs) ∧
     cs.length < 1000 ∧ σ.initOf "Cbtrn03c" = .done ∧ σ.initOf fdC = .done)
  (fun args σ r σ' => ∃ r1, r = none ∧ WsAt σ' w ld lr (det1V v (.ref r1)) ∧
     RecT σ' r1 (fixJ (detailJ t v.acctId ys cs) 133) ∧
     Frame3 σ σ' w ld lr ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- Building the detail line (statement 18: up to the type code). -/
def wdA (w ld lr : Addr) (v : WsV) (c yx cx : Addr) (t : List EquivLean.Cobol.Rec.FVal)
    (ys cs : JStr) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ sb, fr.get 0 = some (.ref w) ∧ fr.get 1 = some (.ref sb) ∧ fr.get 3 = some (.ref yx) ∧
    fr.get 4 = some (.ref cx) ∧ fr.get 6 = some (.ref c) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (detP1 t v.acctId)) ∧ σ0.next ≤ sb ∧
    WsAt σ w ld lr v ∧ DetailFields σ c t ∧ (Model.tSource t).length < 1000 ∧
    -9223372036854775808 < (BitVec.ofInt 64 (Model.tCat t)).toInt ∧
    -9223372036854775808 < (BitVec.ofInt 64 (Model.tAmt t)).toInt ∧
    σ.heap yx = some (.str ys) ∧ ys.length < 1000 ∧ σ.heap cx = some (.str cs) ∧
    cs.length < 1000 ∧ Frame3 σ0 σ w ld lr ∧ w < σ0.next ∧ ld < σ0.next ∧ lr < σ0.next ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

/-- Building the detail line (statement 28: up to the category description). -/
def wdB (w ld lr : Addr) (v : WsV) (c : Addr) (t : List EquivLean.Cobol.Rec.FVal)
    (ys cs : JStr) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ sb, fr.get 0 = some (.ref w) ∧ fr.get 1 = some (.ref sb) ∧ fr.get 6 = some (.ref c) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (detP2 t v.acctId ys cs)) ∧
    σ0.next ≤ sb ∧ WsAt σ w ld lr v ∧ DetailFields σ c t ∧ (Model.tSource t).length < 1000 ∧
    -9223372036854775808 < (BitVec.ofInt 64 (Model.tAmt t)).toInt ∧
    Frame3 σ0 σ w ld lr ∧ w < σ0.next ∧ ld < σ0.next ∧ lr < σ0.next ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

/-- At the `writeLine` (statement 37). -/
def wdI1 (w ld lr : Addr) (v : WsV) (t : List EquivLean.Cobol.Rec.FVal) (ys cs : JStr)
    (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ y, fr.get 0 = some (.ref w) ∧ fr.get 3 = some (.ref y) ∧
    σ.heap y = some (.str (detailJ t v.acctId ys cs)) ∧ WsAt σ w ld lr v ∧
    Frame3 σ0 σ w ld lr ∧ w < σ0.next ∧ ld < σ0.next ∧ lr < σ0.next ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

def writeDetailInv (w ld lr : Addr) (v : WsV) (c yx cx : Addr) (t : List EquivLean.Cobol.Rec.FVal)
    (ys cs : JStr) : Invariants :=
  [(18, fun _ σ0 fr σ => wdA w ld lr v c yx cx t ys cs σ0 fr σ),
   (28, fun _ σ0 fr σ => wdB w ld lr v c t ys cs σ0 fr σ),
   (37, fun _ σ0 fr σ => wdI1 w ld lr v t ys cs σ0 fr σ)]

/-- The paths of `writeDetail` from statement `pc`. -/
def wdWP (w ld lr : Addr) (v : WsV) (c yx cx : Addr) (t : List EquivLean.Cobol.Rec.FVal)
    (ys cs : JStr) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) :
    Prop :=
  bodyWP Gen.prog (callWP Gen.prog linesCallees.env 0)
    Gen.Cbtrn03c.«writeDetail(Cbtrn03c$Ws,Cbtrn03c$TranRecord,java.lang.String,java.lang.String)»
    ((writeDetailInv w ld lr v c yx cx t ys cs).inst args σ0)
    ((writeDetailSpecG w ld lr v c yx cx t ys cs).post args σ0) 120 pc fr σ

end EquivLean.Modernize.Cbtrn03c.Java
