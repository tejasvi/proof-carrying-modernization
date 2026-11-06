import EquivLean.Modernize.Cbact04c.JavaRunFrame
import EquivLean.Modernize.Cbact04c.JavaRunRec
import EquivLean.Modernize.Cbact04c.JavaRunModelFacts
import EquivLean.Modernize.Cbact04c.JavaRunHelpers3
import EquivLean.Modernize.Cbact04c.JavaRunHelpers4
import EquivLean.Modernize.Cbact04c.JavaRunCopySpecs
import EquivLean.Modernize.Cbact04c.JavaRunCallSpecs
import EquivLean.Modernize.Cbact04c.JavaRunCtorF

/-!
# CBACT04C → Java: the invariants of `run`

The ghost inputs `G` (the argument objects and the field values they hold), the contract
`runSpecG g` with fixed ghosts, and the assertions at the cut points of `run`'s body:
* 28 — the account-table copy loop (`J28`);
* 85 — the read loop (`J85`): the locals and the heap hold the model state after `i` records.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

abbrev FV := EquivLean.Cobol.Rec.FVal

/-- The inputs of `run`: the argument objects and the field values they hold. -/
structure G where
  a1 : Addr
  a2 : Addr
  a3 : Addr
  a4 : Addr
  p1 : Addr
  cs : Addr
  tcat : List (List FV)
  xrefs : List (List FV)
  accts : List (List FV)
  discs : List (List FV)
  link : List FV
  clk : List UInt8

namespace G

def args (g : G) : List Value := [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4, .ref g.p1, .ref g.cs]
def parm (g : G) : List UInt8 := Model.parmOf g.link
def step (g : G) : Model.St → List FV → Model.St := Model.step g.xrefs g.discs g.parm g.clk
/-- The model state after the first `n` category records. -/
def st (g : G) (n : Nat) : Model.St := (g.tcat.take n).foldl g.step (Model.init g.accts)
/-- What the model outputs. -/
def out (g : G) : Model.Out := Model.run g.tcat g.xrefs g.accts g.discs g.parm g.clk
/-- The `n`-th category record. -/
def trec (g : G) (n : Nat) : List FV := g.tcat.getD n []

end G

/-- The classes `run` uses are initialized. -/
def Inits (σ : State) : Prop :=
  σ.initOf "Cbact04c" = .done ∧ σ.initOf "Cbact04c$Result" = .done ∧
  σ.initOf "Cbact04c$AccountRecord" = .done ∧ σ.initOf "Cbact04c$CardXrefRecord" = .done ∧
  σ.initOf "Cbact04c$DisGroupRecord" = .done ∧ σ.initOf "Cbact04c$TranCatBalRecord" = .done ∧
  σ.initOf "Cbact04c$ExternalParms" = .done ∧ σ.initOf "Cbact04c$TranRecord" = .done

/-- The precondition of `run` with fixed ghosts. -/
def RunPreG (g : G) (args : List Value) (σ : State) : Prop :=
  args = g.args ∧ RunIn g.args σ g.tcat g.xrefs g.accts g.discs g.link g.clk ∧ Inits σ

/-- The postcondition of `run` (the body of `runSpec`'s) with fixed ghosts. -/
def RunPostG (g : G) (r : Option Value) (σ' : State) : Prop :=
  ∃ res fs l k xs mods lw kw ws mw lr kr rs mr, r = some (.ref res) ∧
    σ'.heap res = some (.plain "Cbact04c$Result" fs) ∧
    Fields.get fs ("Cbact04c$Result", "displays") = some (.ref l) ∧
    σ'.heap l = some (.list k xs mods) ∧ Forall2 (JStrAt σ') xs (g.out.disp.map jline) ∧
    Fields.get fs ("Cbact04c$Result", "transactFileWrites") = some (.ref lw) ∧
    σ'.heap lw = some (.list kw ws mw) ∧
    Forall2 (JRecAt TranRecord "Cbact04c$TranRecord" σ') ws g.out.writes ∧
    Fields.get fs ("Cbact04c$Result", "accountFileRewrites") = some (.ref lr) ∧
    σ'.heap lr = some (.list kr rs mr) ∧
    Forall2 (JRecAt AccountRecord "Cbact04c$AccountRecord" σ') rs g.out.rewrites ∧
    Fields.get fs ("Cbact04c$Result", "abended") = some (.int 0)

def runSpecG (g : G) : Spec := Spec.of (RunPreG g) (fun _ _ r σ' => RunPostG g r σ')

/-! ## The heap between two statements of `run` -/

/-- The addresses `run` allocates and keeps: the `Result` and its three lists, the copy of the
account table, the transaction object; the strings of `PARM-DATE` and the clock. -/
structure Hp where
  res : Addr
  ld : Addr
  lw : Addr
  lr : Addr
  A : Addr
  T : Addr
  parmV : Value
  clkV : Value

/-- The `Result` object and its lists (unchanged by the loop). -/
def ResAt (σ : State) (h : Hp) : Prop :=
  ∃ fs, σ.heap h.res = some (.plain "Cbact04c$Result" fs) ∧
    Fields.get fs ("Cbact04c$Result", "displays") = some (.ref h.ld) ∧
    Fields.get fs ("Cbact04c$Result", "transactFileWrites") = some (.ref h.lw) ∧
    Fields.get fs ("Cbact04c$Result", "accountFileRewrites") = some (.ref h.lr) ∧
    Fields.get fs ("Cbact04c$Result", "abended") = some (.int 0)

/-- The display list holds the lines `d`. -/
def DispAt (σ : State) (ld : Addr) (d : List (List Nat)) : Prop :=
  ∃ xs m, σ.heap ld = some (.list .arrayList xs m) ∧ Forall2 (JStrAt σ) xs (d.map jline)

/-- A list of record objects of class `cls` holding `vals`, none of them at the addresses `M`. -/
def RecsAt (s : Schema) (cls : ClassName) (σ : State) (l : Addr) (vals : List (List FV))
    (M : List Addr) : Prop :=
  ∃ xs m, σ.heap l = some (.list .arrayList xs m) ∧ Forall2 (JRecAt s cls σ) xs vals ∧
    ∀ v ∈ xs, ∀ a, v = .ref a → a ∉ M

/-- The copy of the account table holds `accts`, none of its objects at the addresses `M`. -/
def TableAt (σ : State) (A : Addr) (accts : List (List FV)) (M : List Addr) : Prop :=
  ∃ xs, σ.heap A = some (.array (.cls "Cbact04c$AccountRecord") xs) ∧
    Forall2 (JRecAt AccountRecord "Cbact04c$AccountRecord" σ) xs accts ∧
    ∀ v ∈ xs, ∀ a, v = .ref a → a ∉ M

/-- The fields of a transaction record object. -/
def keysTR : List String := ["tranId", "tranTypeCd", "tranCatCd", "tranSource", "tranDesc",
  "tranAmt", "tranMerchantId", "tranMerchantName", "tranMerchantCity", "tranMerchantZip",
  "tranCardNum", "tranOrigTs", "tranProcTs", "filler1"]

/-- The transaction object `T`: every field set; its description is 100 characters ending in 76
spaces, its filler 20 spaces (what `run` reads of it before overwriting the rest). -/
def TranOk (σ : State) (T : Addr) : Prop :=
  ∃ fs, σ.heap T = some (.plain "Cbact04c$TranRecord" fs) ∧
    (∀ k ∈ keysTR, ∃ v, Fields.get fs ("Cbact04c$TranRecord", k) = some v) ∧
    (∃ d s, Fields.get fs ("Cbact04c$TranRecord", "tranDesc") = some (.ref d) ∧
      σ.heap d = some (.str s) ∧ s.length = 100 ∧ s.drop 24 = spJ 76) ∧
    (∃ f, Fields.get fs ("Cbact04c$TranRecord", "filler1") = some (.ref f) ∧
      σ.heap f = some (.str (spJ 20)))

/-- `WS-LAST-ACCT-NUM`: spaces before the first record, then the last account id's digits. -/
def lastText : Option Int → JStr
  | none => spJ 11
  | some id => zpadJ id.natAbs 11

/-- The address of a reference (for the distinctness of record objects). -/
def addrOf : Value → List Addr
  | .ref a => [a]
  | _ => []

/-- `run`'s objects are fresh (allocated by `run`) and the three lists distinct. -/
def Fresh (σ0 : State) (h : Hp) : Prop :=
  σ0.next ≤ h.res ∧ σ0.next ≤ h.ld ∧ σ0.next ≤ h.lw ∧ σ0.next ≤ h.lr ∧ σ0.next ≤ h.A ∧
  σ0.next ≤ h.T ∧ h.ld ≠ h.lw ∧ h.ld ≠ h.lr ∧ h.lw ≠ h.lr

/-- The account object the loop may still write (once a record was read). -/
def curAcct (s : Model.St) (acctV : Value) : List Addr :=
  if s.lastId.isSome then addrOf acctV else []

/-- The heap the loop keeps, for the outputs and account table of the model state `s`; `M` are the
account objects the loop may still write. -/
def CoreHeap (g : G) (σ0 σ : State) (h : Hp) (s : Model.St) (M : List Addr) : Prop :=
  Grows σ0 σ ∧ Inits σ ∧ Fresh σ0 h ∧ ResAt σ h ∧ DispAt σ h.ld s.disp ∧
  RecsAt TranRecord "Cbact04c$TranRecord" σ h.lw s.writes [h.T] ∧
  RecsAt AccountRecord "Cbact04c$AccountRecord" σ h.lr s.rewrites M ∧
  TableAt σ h.A s.accts M ∧ TranOk σ h.T ∧
  JStrAt σ h.parmV (cp037Str g.parm) ∧ JStrAt σ h.clkV (cp037Str g.clk)

/-- The heap at the loop head, for the model state `s`: `CoreHeap`, and the current account and
cross-reference objects hold `s.acct` and `s.xref` (once a record was read), `lastV` the text of
the last account id; the account object is one `run` allocated (it writes it). -/
def LoopHeap (g : G) (σ0 σ : State) (h : Hp) (s : Model.St) (acctV xrefV lastV : Value) : Prop :=
  CoreHeap g σ0 σ h s (curAcct s acctV) ∧
  (s.lastId.isSome → JRecAt AccountRecord "Cbact04c$AccountRecord" σ acctV s.acct) ∧
  (s.lastId.isSome → JRecAt CardXrefRecord "Cbact04c$CardXrefRecord" σ xrefV s.xref) ∧
  JStrAt σ lastV (lastText s.lastId) ∧
  (s.lastId.isSome → ∀ a, acctV = .ref a → σ0.next ≤ a)

/-- The locals that hold the same values throughout the read loop. -/
def Locs (g : G) (h : Hp) (fr : Frame) : Prop :=
  fr.get 1 = some (.ref g.a1) ∧ fr.get 36 = some (.ref g.a2) ∧ fr.get 40 = some (.ref g.a3) ∧
  fr.get 8 = some (.ref g.a4) ∧ fr.get 37 = some (.ref g.p1) ∧ fr.get 10 = some (.ref h.res) ∧
  fr.get 19 = some (.int (BitVec.ofNat 32 g.tcat.length)) ∧
  fr.get 20 = some (.int (BitVec.ofNat 32 g.xrefs.length)) ∧
  fr.get 21 = some (.int (BitVec.ofNat 32 g.discs.length)) ∧ fr.get 41 = some (.ref h.A) ∧
  fr.get 38 = some (.ref h.T) ∧ fr.get 26 = some h.parmV ∧ fr.get 24 = some h.clkV

/-- **The read loop's head (statement 85)**: after `i` category records, the locals and the heap
hold the model state `g.st i`. -/
def J85 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (acctV xrefV lastV : Value),
    0 ≤ i.toInt ∧ i.toInt ≤ g.tcat.length ∧ Locs g h fr ∧ fr.get 22 = some (.int i) ∧
    fr.get 12 = some (.long (BitVec.ofInt 64 (g.st i.toInt.toNat).total)) ∧
    fr.get 3 = some (.int (if (g.st i.toInt.toNat).lastId.isSome then 0#32 else 1#32)) ∧
    fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)) ∧
    fr.get 25 = some lastV ∧ fr.get 16 = some acctV ∧ fr.get 17 = some xrefV ∧
    fr.get 4 = some (.int 0#32) ∧ fr.get 5 = some (.int 0#32) ∧
    Hide (LoopHeap g σ0 σ h (g.st i.toInt.toNat) acctV xrefV lastV)

/-- Statement 10: the `Result` is built and the start line displayed. -/
def J10 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (res ld lw lr : Addr) (sv : Addr),
    fr.get 1 = some (.ref g.a1) ∧ fr.get 36 = some (.ref g.a2) ∧ fr.get 40 = some (.ref g.a3) ∧
    fr.get 8 = some (.ref g.a4) ∧ fr.get 37 = some (.ref g.p1) ∧ fr.get 24 = some (.ref g.cs) ∧
    fr.get 10 = some (.ref res) ∧
    Hide (ResAt σ ⟨res, ld, lw, lr, 0, 0, .null, .null⟩) ∧
    σ.heap ld = some (.list .arrayList [.ref sv] 1) ∧
    σ.heap sv = some (.str (JStr.ofString "START OF EXECUTION OF PROGRAM CBACT04C")) ∧
    σ.heap lw = some (.list .arrayList [] 0) ∧ σ.heap lr = some (.list .arrayList [] 0) ∧
    σ0.next ≤ res ∧ σ0.next ≤ ld ∧ σ0.next ≤ lw ∧ σ0.next ≤ lr ∧
    ld ≠ lw ∧ ld ≠ lr ∧ lw ≠ lr ∧ Grows σ0 σ ∧ Inits σ

/-- **The account-table copy loop (statement 28)**: the first `j` accounts are copied. -/
def J28 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (j : I32) (res ld lw lr A : Addr) (cxs : List Value),
    fr.get 1 = some (.ref g.a1) ∧ fr.get 36 = some (.ref g.a2) ∧ fr.get 40 = some (.ref g.a3) ∧
    fr.get 8 = some (.ref g.a4) ∧ fr.get 37 = some (.ref g.p1) ∧ fr.get 24 = some (.ref g.cs) ∧
    fr.get 10 = some (.ref res) ∧
    fr.get 19 = some (.int (BitVec.ofNat 32 g.tcat.length)) ∧
    fr.get 20 = some (.int (BitVec.ofNat 32 g.xrefs.length)) ∧
    fr.get 21 = some (.int (BitVec.ofNat 32 g.discs.length)) ∧
    fr.get 22 = some (.int (BitVec.ofNat 32 g.accts.length)) ∧
    fr.get 41 = some (.ref A) ∧ fr.get 18 = some (.int j) ∧
    0 ≤ j.toInt ∧ j.toInt ≤ g.accts.length ∧ cxs.length = j.toInt.toNat ∧
    σ.heap A = some (.array (.cls "Cbact04c$AccountRecord")
      (cxs ++ List.replicate (g.accts.length - j.toInt.toNat) .null)) ∧
    Hide (Forall2 (JRecAt AccountRecord "Cbact04c$AccountRecord" σ) cxs
      (g.accts.take j.toInt.toNat)) ∧
    Hide (ResAt σ ⟨res, ld, lw, lr, A, 0, .null, .null⟩) ∧
    Hide (DispAt σ ld (Model.init g.accts).disp) ∧
    σ.heap lw = some (.list .arrayList [] 0) ∧ σ.heap lr = some (.list .arrayList [] 0) ∧
    σ0.next ≤ res ∧ σ0.next ≤ ld ∧ σ0.next ≤ lw ∧ σ0.next ≤ lr ∧ σ0.next ≤ A ∧
    ld ≠ lw ∧ ld ≠ lr ∧ lw ≠ lr ∧ Grows σ0 σ ∧ Inits σ

/-- Between the copy loop and the read loop: the locals that hold the inputs, the `Result`, the
account table copy (complete). -/
def InitAt (g : G) (σ0 : State) (fr : Frame) (σ : State) (res ld lw lr A : Addr) : Prop :=
  fr.get 1 = some (.ref g.a1) ∧ fr.get 36 = some (.ref g.a2) ∧ fr.get 40 = some (.ref g.a3) ∧
  fr.get 8 = some (.ref g.a4) ∧ fr.get 37 = some (.ref g.p1) ∧ fr.get 24 = some (.ref g.cs) ∧
  fr.get 10 = some (.ref res) ∧
  fr.get 19 = some (.int (BitVec.ofNat 32 g.tcat.length)) ∧
  fr.get 20 = some (.int (BitVec.ofNat 32 g.xrefs.length)) ∧
  fr.get 21 = some (.int (BitVec.ofNat 32 g.discs.length)) ∧ fr.get 41 = some (.ref A) ∧
  Hide (TableAt σ A g.accts []) ∧ Hide (ResAt σ ⟨res, ld, lw, lr, A, 0, .null, .null⟩) ∧
  Hide (DispAt σ ld (Model.init g.accts).disp) ∧
  Hide (RecsAt TranRecord "Cbact04c$TranRecord" σ lw [] []) ∧
  Hide (RecsAt AccountRecord "Cbact04c$AccountRecord" σ lr [] []) ∧
  σ0.next ≤ res ∧ σ0.next ≤ ld ∧ σ0.next ≤ lw ∧ σ0.next ≤ lr ∧ σ0.next ≤ A ∧
  ld ≠ lw ∧ ld ≠ lr ∧ lw ≠ lr ∧ Grows σ0 σ ∧ Inits σ

/-- Statements 38, 47: the copy loop is done (the record objects being built are not read). -/
def JI (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ res ld lw lr A, InitAt g σ0 fr σ res ld lw lr A

/-- Statements 42, 47: also local 17 (the cross-reference object) holds a value. -/
def JI42 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ res ld lw lr A, InitAt g σ0 fr σ res ld lw lr A ∧ ∃ v, fr.get 17 = some v

/-- Statement 57: the account object `r105` exists. -/
def JI57 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ res ld lw lr A acctV, InitAt g σ0 fr σ res ld lw lr A ∧ fr.get 16 = some acctV ∧
    ∃ v, fr.get 17 = some v

/-- Statement 63: the transaction object is allocated (all fields at their defaults), local 28
holds 100 spaces. -/
def JI63 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ res ld lw lr A acctV T d, InitAt g σ0 fr σ res ld lw lr A ∧ fr.get 16 = some acctV ∧
    fr.get 38 = some (.ref T) ∧ σ0.next ≤ T ∧
    (∃ fs, σ.heap T = some (.plain "Cbact04c$TranRecord" fs) ∧
      ∀ k ∈ keysTR, ∃ v, Fields.get fs ("Cbact04c$TranRecord", k) = some v) ∧
    fr.get 28 = some (.ref d) ∧ σ.heap d = some (.str (spJ 100)) ∧
    (∃ v, fr.get 25 = some v) ∧ (∃ v, fr.get 26 = some v) ∧ (∃ v, fr.get 27 = some v) ∧
    (∃ v, fr.get 29 = some v) ∧ ∃ v, fr.get 17 = some v

/-- Statement 70: the transaction object is built. -/
def JI70 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ res ld lw lr A acctV T, InitAt g σ0 fr σ res ld lw lr A ∧ fr.get 16 = some acctV ∧
    fr.get 38 = some (.ref T) ∧ σ0.next ≤ T ∧ Hide (TranOk σ T) ∧ ∃ v, fr.get 17 = some v

/-! ## Inside an iteration of the read loop -/

/-- The model state after the display of record `t`. -/
def disp1 (s : Model.St) (t : List FV) : Model.St :=
  { s with disp := s.disp ++ [TranCatBalRecord.textS t] }

/-- The model state after the rewrite of the previous account (if any), before the new account is
read. -/
def stRw (s : Model.St) (t : List FV) : Model.St :=
  let s1 := disp1 s t
  let p := Model.posted s1.acct s1.total
  if s1.lastId.isSome then
    { s1 with accts := Model.replaceFirst (fun a => Model.aId a == Model.aId s1.acct) p s1.accts,
              rewrites := s1.rewrites ++ [p] }
  else s1

/-- The model state after the new account is read (the cross-reference not yet). -/
def stAcct (s : Model.St) (t : List FV) : Model.St :=
  { stRw s t with lastId := some (Model.tAcct t), total := 0,
                  acct := Model.findAcct (stRw s t).accts (Model.tAcct t) }

/-- The model state after the account part of record `t` (the same account, or the rewrite of the
previous account and the new account and cross-reference read). -/
def stSel (xrefs : List (List FV)) (s : Model.St) (t : List FV) : Model.St :=
  if s.lastId = some (Model.tAcct t) then disp1 s t
  else { stAcct s t with xref := Model.findXref xrefs (Model.tAcct t) }

/-- The interest part of record `t` from the state `s2` (rate `rate`). -/
def stFin (parm clk : List UInt8) (rate : Int) (s2 : Model.St) (t : List FV) : Model.St :=
  if rate = 0 then s2
  else
    let amt := Int.tmod (Int.tdiv (Model.tBal t * rate) 120000) (10 ^ 11)
    let k := (s2.k + 1) % 1000000
    { s2 with total := Int.tmod (s2.total + amt) (10 ^ 11), k,
              writes := s2.writes ++ [Model.tranVals parm clk k (Model.aId s2.acct) (Model.xCard s2.xref) amt] }

/-- The facts shared inside iteration `i` (record `t = g.tcat[i]` read into the object `tcbV`). -/
def Body (g : G) (fr : Frame) (σ : State) (i : I32) (h : Hp) (tcbV : Value) : Prop :=
  i.toInt.toNat < g.tcat.length ∧ 0 ≤ i.toInt ∧ Locs g h fr ∧
    fr.get 22 = some (.int (i + 1#32)) ∧ fr.get 6 = some tcbV ∧
    fr.get 4 = some (.int 0#32) ∧ fr.get 5 = some (.int 0#32) ∧
    Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ tcbV (g.trec i.toInt.toNat))

/-- Statement 90: record `i` read (copied into `tcbV`), not yet displayed. -/
def J89 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV acctV xrefV lastV : Value),
    Body g fr σ i h tcbV ∧
    fr.get 12 = some (.long (BitVec.ofInt 64 (g.st i.toInt.toNat).total)) ∧
    fr.get 3 = some (.int (if (g.st i.toInt.toNat).lastId.isSome then 0#32 else 1#32)) ∧
    fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)) ∧
    fr.get 25 = some lastV ∧ fr.get 16 = some acctV ∧ fr.get 17 = some xrefV ∧
    Hide (LoopHeap g σ0 σ h (g.st i.toInt.toNat) acctV xrefV lastV)

/-- Statement 97: record `i` displayed. -/
def J97 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV acctV xrefV lastV : Value),
    Body g fr σ i h tcbV ∧
    fr.get 12 = some (.long (BitVec.ofInt 64 (g.st i.toInt.toNat).total)) ∧
    fr.get 3 = some (.int (if (g.st i.toInt.toNat).lastId.isSome then 0#32 else 1#32)) ∧
    fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)) ∧
    fr.get 25 = some lastV ∧ fr.get 16 = some acctV ∧ fr.get 17 = some xrefV ∧
    Hide (LoopHeap g σ0 σ h (disp1 (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) acctV xrefV lastV)

/-- Statement 102: another account than the previous record's; the previous account is to be
posted. -/
def J102 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV acctV xrefV lastV : Value),
    Body g fr σ i h tcbV ∧
    (g.st i.toInt.toNat).lastId.isSome ∧
    (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)) ∧
    fr.get 3 = some (.int 0#32) ∧
    fr.get 12 = some (.long (BitVec.ofInt 64 (g.st i.toInt.toNat).total)) ∧
    fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)) ∧
    fr.get 16 = some acctV ∧
    Hide (LoopHeap g σ0 σ h (disp1 (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) acctV xrefV lastV)

/-- Statement 108: the previous account posted in its object `acctV` (not yet stored). -/
def J108 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV acctV : Value),
    Body g fr σ i h tcbV ∧
    (g.st i.toInt.toNat).lastId.isSome ∧
    (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)) ∧
    fr.get 3 = some (.int 0#32) ∧
    fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)) ∧
    fr.get 16 = some acctV ∧
    Hide (CoreHeap g σ0 σ h (disp1 (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) (addrOf acctV)) ∧
    Hide (JRecAt AccountRecord "Cbact04c$AccountRecord" σ acctV
      (Model.posted (g.st i.toInt.toNat).acct (g.st i.toInt.toNat).total))

/-- The model state after the posted account is stored into the table (statement 112), before it
is appended to the rewrites. -/
def stRw1 (s : Model.St) (t : List FV) : Model.St :=
  { disp1 s t with
    accts := (Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
      (Model.posted s.acct s.total) s.accts) }

/-- Statement 113: the posted account stored into the table copy. -/
def J113 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV : Value) (ac : Addr),
    Body g fr σ i h tcbV ∧
    (g.st i.toInt.toNat).lastId.isSome ∧
    (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)) ∧
    fr.get 3 = some (.int 0#32) ∧
    fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)) ∧
    fr.get 16 = some (.ref ac) ∧
    Hide (CoreHeap g σ0 σ h (stRw1 (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) []) ∧
    Hide (JRecAt AccountRecord "Cbact04c$AccountRecord" σ (.ref ac)
      (Model.posted (g.st i.toInt.toNat).acct (g.st i.toInt.toNat).total))

/-- Statement 125: before the new account is read; the rewrite (if any) done. -/
def J125 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV : Value),
    Body g fr σ i h tcbV ∧
    (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)) ∧
    fr.get 3 = some (.int 0#32) ∧
    fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)) ∧
    Hide (CoreHeap g σ0 σ h (stRw (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) [])

/-- Statement 129: the new account id's text computed (`fmtU`), the account not yet read. -/
def J129 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV lastV : Value),
    Body g fr σ i h tcbV ∧
    (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)) ∧
    fr.get 3 = some (.int 0#32) ∧ fr.get 12 = some (.long 0#64) ∧
    fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)) ∧
    fr.get 11 = some (.long (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)))) ∧
    fr.get 25 = some lastV ∧
    Hide (JStrAt σ lastV (lastText (some (Model.tAcct (g.trec i.toInt.toNat))))) ∧
    Hide (CoreHeap g σ0 σ h (stRw (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) [])

/-- The `xrefAcctId` of the cross-reference object `v`. -/
def xrefIdOf (σ : State) (v : Value) : Option I64 :=
  match v with
  | .ref a => match σ.heap a with
    | some (.plain _ fs) => match Fields.get fs ("Cbact04c$CardXrefRecord", "xrefAcctId") with
      | some (.long n) => some n
      | _ => none
    | _ => none
  | _ => none

/-- Statement 148: the cross-reference search, no match among the first `k` records. -/
def J148 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV acctV lastV : Value) (k : I32),
    Body g fr σ i h tcbV ∧
    (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)) ∧
    fr.get 3 = some (.int 0#32) ∧ fr.get 12 = some (.long 0#64) ∧
    fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)) ∧
    fr.get 25 = some lastV ∧ fr.get 16 = some acctV ∧
    fr.get 13 = some (.long (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)))) ∧
    fr.get 18 = some (.int (-1#32)) ∧ fr.get 23 = some (.int k) ∧ 0 ≤ k.toInt ∧
    k.toInt ≤ g.xrefs.length ∧
    (∀ et xs, σ.heap g.a2 = some (.array et xs) →
      ∀ x ∈ xs.take k.toInt.toNat,
        xrefIdOf σ x ≠ some (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)))) ∧
    Hide (CoreHeap g σ0 σ h (stAcct (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) (addrOf acctV)) ∧
    Hide (JRecAt AccountRecord "Cbact04c$AccountRecord" σ acctV
      (stAcct (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).acct) ∧
    Hide (JStrAt σ lastV (lastText (some (Model.tAcct (g.trec i.toInt.toNat))))) ∧
    (∀ a, acctV = .ref a → σ0.next ≤ a)

/-- Statement 172: the account part of record `i` done (model state `stSel`). -/
def J172 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV acctV xrefV lastV : Value),
    Body g fr σ i h tcbV ∧
    fr.get 3 = some (.int 0#32) ∧
    fr.get 12 = some (.long (BitVec.ofInt 64
      (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).total)) ∧
    fr.get 14 = some (.long (BitVec.ofNat 64
      (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).k)) ∧
    fr.get 25 = some lastV ∧ fr.get 16 = some acctV ∧ fr.get 17 = some xrefV ∧
    Hide (LoopHeap g σ0 σ h (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
      acctV xrefV lastV)

/-- The disclosure group record of record `t` in the model state `s` (the first one of the
account's group with the record's type and category: `Model.findRate`'s). -/
def discOf (g : G) (s : Model.St) (t : List FV) : List FV :=
  (g.discs.find? (fun d => Model.dGrp d == Model.aGrp s.acct && Model.dType d == Model.tType t &&
    Model.dCat d == Model.tCat t)).getD []

/-- Statement 196: the account part of record `i` done (`stSel`), its disclosure group record
copied into `disV`. -/
def J196 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV acctV xrefV lastV disV : Value),
    Body g fr σ i h tcbV ∧
    fr.get 3 = some (.int 0#32) ∧
    fr.get 12 = some (.long (BitVec.ofInt 64
      (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).total)) ∧
    fr.get 14 = some (.long (BitVec.ofNat 64
      (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).k)) ∧
    fr.get 25 = some lastV ∧ fr.get 16 = some acctV ∧ fr.get 17 = some xrefV ∧
    fr.get 7 = some disV ∧
    Hide (LoopHeap g σ0 σ h (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
      acctV xrefV lastV) ∧
    Hide (JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ disV
      (discOf g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) (g.trec i.toInt.toNat)))

/-- Statement 199: a nonzero interest rate (the record's interest is computed and written). -/
def J199 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV acctV xrefV lastV disV : Value),
    Body g fr σ i h tcbV ∧
    fr.get 3 = some (.int 0#32) ∧
    fr.get 12 = some (.long (BitVec.ofInt 64
      (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).total)) ∧
    fr.get 14 = some (.long (BitVec.ofNat 64
      (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).k)) ∧
    fr.get 25 = some lastV ∧ fr.get 16 = some acctV ∧ fr.get 17 = some xrefV ∧
    fr.get 7 = some disV ∧
    Hide (LoopHeap g σ0 σ h (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
      acctV xrefV lastV) ∧
    Hide (JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ disV
      (discOf g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) (g.trec i.toInt.toNat))) ∧
    Model.dRate (discOf g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
      (g.trec i.toInt.toNat)) ≠ 0

/-! ## The interest part of record `n` (statements 199–245) -/

/-- The model state after the account part of record `n`. -/
def sel (g : G) (n : Nat) : Model.St := stSel g.xrefs (g.st n) (g.trec n)
/-- The interest rate of record `n`. -/
def rateOf (g : G) (n : Nat) : Int := Model.dRate (discOf g (sel g n) (g.trec n))
/-- The monthly interest of record `n`. -/
def amtOf (g : G) (n : Nat) : Int :=
  Int.tmod (Int.tdiv (Model.tBal (g.trec n) * rateOf g n) 120000) (10 ^ 11)
/-- The transaction suffix and the total after record `n` (nonzero rate). -/
def kOf (g : G) (n : Nat) : Nat := ((sel g n).k + 1) % 1000000
def totOf (g : G) (n : Nat) : Int := Int.tmod ((sel g n).total + amtOf g n) (10 ^ 11)
/-- The interest transaction of record `n`. -/
def tvals (g : G) (n : Nat) : List FV :=
  Model.tranVals g.parm g.clk (kOf g n) (Model.aId (sel g n).acct) (Model.xCard (sel g n).xref)
    (amtOf g n)

/-- The first `m` fields of the transaction object `T` hold `vals`. -/
def TranSet (σ : State) (T : Addr) (m : Nat) (vals : List FV) : Prop :=
  ∃ fs, σ.heap T = some (.plain "Cbact04c$TranRecord" fs) ∧
    Forall2 (fun f val => jFieldAt σ "Cbact04c$TranRecord" fs f val) (TranRecord.fields.take m)
      (vals.take m)

/-- What the interest part keeps: the record, the locals, the heap of the account part's state. -/
def IntAt (g : G) (σ0 : State) (fr : Frame) (σ : State) (i : I32) (h : Hp) (tcbV acctV xrefV lastV : Value) :
    Prop :=
  Body g fr σ i h tcbV ∧ fr.get 3 = some (.int 0#32) ∧
    fr.get 11 = some (.long (BitVec.ofInt 64 (amtOf g i.toInt.toNat))) ∧
    fr.get 12 = some (.long (BitVec.ofInt 64 (totOf g i.toInt.toNat))) ∧
    fr.get 14 = some (.long (BitVec.ofNat 64 (kOf g i.toInt.toNat))) ∧
    fr.get 25 = some lastV ∧ fr.get 16 = some acctV ∧ fr.get 17 = some xrefV ∧
    Hide (LoopHeap g σ0 σ h (sel g i.toInt.toNat) acctV xrefV lastV) ∧ rateOf g i.toInt.toNat ≠ 0

/-- Statement 210: the interest computed, the transaction id in local 27. -/
def J210 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV acctV xrefV lastV tidV : Value),
    IntAt g σ0 fr σ i h tcbV acctV xrefV lastV ∧ fr.get 27 = some tidV ∧
    Hide (JStrAt σ tidV (cp037Str g.parm ++ zpadJ (kOf g i.toInt.toNat) 6))

/-- Statement 217: id, type, category, source set; the description's head in local 27. -/
def J217 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV acctV xrefV lastV headV : Value),
    IntAt g σ0 fr σ i h tcbV acctV xrefV lastV ∧ fr.get 27 = some headV ∧
    Hide (JStrAt σ headV (JStr.ofString "Int. for a/c " ++
      zpadJ (Model.aId (sel g i.toInt.toNat).acct).natAbs 11)) ∧
    Hide (TranSet σ h.T 4 (tvals g i.toInt.toNat))

/-- Statement 224: also description, amount, merchant id set. -/
def J224 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV acctV xrefV lastV : Value),
    IntAt g σ0 fr σ i h tcbV acctV xrefV lastV ∧ Hide (TranSet σ h.T 7 (tvals g i.toInt.toNat))

/-- Statement 232: also merchant name, city, zip, card number set. -/
def J232 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV acctV xrefV lastV : Value),
    IntAt g σ0 fr σ i h tcbV acctV xrefV lastV ∧ Hide (TranSet σ h.T 11 (tvals g i.toInt.toNat))

/-- Statement 242: also both timestamps set (the transaction object complete). -/
def J242 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (h : Hp) (tcbV acctV xrefV lastV : Value),
    IntAt g σ0 fr σ i h tcbV acctV xrefV lastV ∧ Hide (TranSet σ h.T 13 (tvals g i.toInt.toNat))

/-! ## The callee contracts and the cut points -/

def spacesSig : MethodSig :=
  { cls := "Cbact04c", ret := .cls "java.lang.String", name := "spaces", params := [.prim .int] }
def fixLenSig : MethodSig :=
  { cls := "Cbact04c", ret := .cls "java.lang.String", name := "fixLen",
    params := [.cls "java.lang.String", .prim .int] }
def truncSig : MethodSig :=
  { cls := "Cbact04c", ret := .prim .long, name := "trunc", params := [.prim .long, .prim .int] }
def displayTcbSig : MethodSig :=
  { cls := "Cbact04c", ret := .cls "java.lang.String", name := "displayTcb",
    params := [.cls "Cbact04c$TranCatBalRecord"] }
def findAcctSig : MethodSig :=
  { cls := "Cbact04c", ret := .prim .int, name := "findAcct",
    params := [.array (.cls "Cbact04c$AccountRecord"), .prim .long] }
def findDiscSig : MethodSig :=
  { cls := "Cbact04c", ret := .prim .int, name := "findDisc",
    params := [.array (.cls "Cbact04c$DisGroupRecord"), .prim .int, .cls "java.lang.String",
      .cls "java.lang.String", .prim .long] }

/-- The contracts of `run`'s callees. -/
def runC : Contracts :=
  [(spacesSig, spacesSpec), (fixLenSig, fixLenF), (fmtUSig, fmtUSpec), (truncSig, truncSpec),
   (displayTcbSig, displayTcbF), (findAcctSig, findAcctF), (findDiscSig, findDiscF),
   (copyTcbSig, copyF "Cbact04c$TranCatBalRecord" keysTC),
   (copyXrefSig, copyF "Cbact04c$CardXrefRecord" keysXC),
   (copyAcctSig, copyF "Cbact04c$AccountRecord" keysAC),
   (copyDisSig, copyF "Cbact04c$DisGroupRecord" keysDC),
   (copyTranSig, copyF "Cbact04c$TranRecord" keysRC),
   (ctorTCSig, ctorTCF), (ctorXCSig, ctorXCF), (ctorACSig, ctorACF),
   (ctorDCSig, ctorDCF), (ctorRCSig, ctorRCF)]

abbrev runBody := Gen.Cbact04c.«run(Cbact04c$TranCatBalRecord[],Cbact04c$CardXrefRecord[],Cbact04c$AccountRecord[],Cbact04c$DisGroupRecord[],Cbact04c$ExternalParms,java.lang.String)»

/-- The cut points of `run`. -/
def runInv (g : G) : Invariants :=
  [(10, J10 g), (28, J28 g), (38, JI g), (42, JI42 g), (47, JI42 g), (57, JI57 g),
   (63, JI63 g), (70, JI70 g), (85, J85 g), (90, J89 g), (97, J97 g), (102, J102 g), (108, J108 g), (113, J113 g), (125, J125 g),
   (129, J129 g), (148, J148 g), (172, J172 g), (196, J196 g), (199, J199 g), (210, J210 g),
   (217, J217 g), (224, J224 g), (232, J232 g), (242, J242 g)]

/-- Symbolic execution of `run`'s body from `pc` (callees by their contracts). -/
def RunWP (g : G) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog runC.env 1) runBody ((runInv g).inst g.args σ0)
    ((runSpecG g).post g.args σ0) 60 pc fr σ

/- `RunWP` is unfolded explicitly (`unfold RunWP`) in each segment. -/
attribute [irreducible] RunWP

/-- Symbolic execution of `run`'s body from `pc` against a cut list `cuts` given only by its
lookups at the statements a segment visits (hypotheses `cuts.lookup pc = …` of the segment):
`simp` then evaluates the cut list at those statements only, never under binders. -/
def RunWPc (g : G) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog runC.env 1) runBody cuts ((runSpecG g).post g.args σ0) 60 pc fr σ

attribute [irreducible] RunWPc

theorem runWP_eq (g : G) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) :
    RunWP g σ0 pc fr σ = RunWPc g σ0 ((runInv g).inst g.args σ0) pc fr σ := by
  unfold RunWP RunWPc
  rfl

end EquivLean.Modernize.Cbact04c.Java
