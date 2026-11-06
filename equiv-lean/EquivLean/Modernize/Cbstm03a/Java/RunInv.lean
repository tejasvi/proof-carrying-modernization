import EquivLean.Modernize.Cbstm03a.Java.JRun

/-!
# CBSTM03A → Java: the contract of `run` against `jRunR`, and its cut points

`runSpecG g`: for the input arrays `g.a1 … g.a4` holding the records `g.trs … g.ars` (as `TrnxAtN` … describe
them), with the `CP037` table in place and `Cbstm03a$Result` initialized, `run` returns a `Result` holding
`jRunR`'s outputs (`g.F`).

The cut points (statement indices of `run`'s Jimple, `cbstm03a/run_numbered.txt`) and their invariants:
* 12, 24, 37, 52: the four loops building `trnxTexts`, `xrefTexts`, `custKeys`/`custTexts`, `acctTexts`;
* 80 (`label19`): the load loop (record `k` in `cn`, the table holding the load state `s`);
* 117 (`label24`): the cross-reference loop (`j` records done, the `Result` holding `o`);
* 140, 153: the searches of the customer keys and of the account texts for record `j`;
* 168: the cards loop of record `j` (card number `crJmp`, running total, `n` cards left);
* 179: the transactions loop of card number `crJmp` (transaction `trJmp` of `cnt`).
Every invariant states the remaining computation as an equation with `g.F`.

Locals of `run` (index: name): 1 `trnxSt`, 2 `tCard#70` (`xrefSt`), 3 `tId`, 5 `tId#71_2` (the end flag),
6 `acctFile`, 7 `res`, 9 `custFile`, 10 `trnxFile`, 11 `trnxTexts`, 12 `xrefTexts`, 13 `custKeys`, 14 `custTexts`,
15 `acctTexts`, 16 `i#28` (the table memory), 17 `crJmp` (`trCnt` in the load loop), 18 `crCnt`, 19 `cnt`,
20 `amt`, 21 `i#79` (the total), 22 `trJmp`, 23 `xrefFile`, 24 `trct`, 26 `i#78`, 27 `$i20` (a count; the
customers' from the CUSTFILE loop on), 28 `i` (the TRNXFILE loop's index; the accounts' count from statement 49
on), 29 `i#9`, 30 `i#16`, 32 `tRest` (`saveCard`; the card number of record `j`), 33 `cn` (the record; the
account id of record `j`), 34 `xrefCustId` (the customer id of record `j`), 36 `trest`, 37 `custRec#75`,
38 `i#77` (the account text).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

abbrev runBodyA : Body :=
  Gen.Cbstm03a.«run(Cbstm03a$TrnxRecord[],Cbstm03a$CardXrefRecord[],Cbstm03a$CustomerRecord[],Cbstm03a$AccountRecord[])»
abbrev runRefA : MethodRef :=
  Gen.Cbstm03a.«run(Cbstm03a$TrnxRecord[],Cbstm03a$CardXrefRecord[],Cbstm03a$CustomerRecord[],Cbstm03a$AccountRecord[])».ref

/-! ## The contract -/

/-- An input file: an array (of `int` length) whose elements are records with the values `ts`. -/
def RecsAt {α : Type} (R : State → Value → Option α → Prop) (σ : State) (a : Addr) (ts : List α) : Prop :=
  ∃ et xs, σ.heap a = some (.array et xs) ∧ xs.length < 2147483648 ∧
    Forall2 (fun v t => R σ v (some t)) xs ts

/-- The ghost values of a run: the input arrays and the records they hold. -/
structure RunG where
  a1 : Addr
  a2 : Addr
  a3 : Addr
  a4 : Addr
  trs : List TrnxR
  xrs : List XrefR
  crs : List CustR
  ars : List AcctR

namespace RunG

/-- The texts of the four files, the customer keys, the records the load reads, `run`'s outputs. -/
def T1 (g : RunG) : List JStr := g.trs.map trnxTextR
def T2 (g : RunG) : List JStr := g.xrs.map xrefTextR
def T3 (g : RunG) : List JStr := g.crs.map custTextR
def K3 (g : RunG) : List JStr := g.T3.map (sub · 0 9)
def T4 (g : RunG) : List JStr := g.ars.map acctTextR
def R1 (g : RunG) : List JStr := g.T1.map (recOf · 350)
def F (g : RunG) : JOut := jRunR g.trs g.xrs g.crs g.ars

end RunG

/-- The entry facts of `run` for the ghost values `g`. -/
def RunPre (g : RunG) (args : List Value) (σ : State) : Prop :=
  args = [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] ∧
  RecsAt TrnxAtN σ g.a1 g.trs ∧ RecsAt XrefAtN σ g.a2 g.xrs ∧ RecsAt CustAtN σ g.a3 g.crs ∧
  RecsAt AcctAtN σ g.a4 g.ars ∧ CP037At σ ∧ σ.initOf "Cbstm03a$Result" = .done

/-- **The contract of `run` for the ghost values `g`**: the `Result` holds `jRunR`'s outputs. -/
def runSpecG (g : RunG) : Spec := Spec.of (RunPre g)
  (fun _ _ r σ' => ∃ res, r = some (.ref res) ∧ ResAt σ' res g.F.disp g.F.stmt g.F.html g.F.ab)

/-- The contracts `run` calls. -/
def runCallees : Contracts :=
  [(trnxTextSig, trnxTextSpec), (xrefTextSig, xrefTextSpec), (custTextSig, custTextSpec),
   (acctTextSig, acctTextSpec), (spacesSig, spacesSpecI), (fixSig, fixSpecI), (repeatSig, repeatSpec),
   (seqReadSig, seqReadSpec), (setTrctSig, setTrctSpec), (getTrctSig, getTrctSpec), (cardOffSig, cardOffSpec),
   (tranOffSig, tranOffSpec), (memWriteSig, memWriteSpec), (memReadSig, memReadSpec), (abendSig, abendSpec),
   (createStatementSig, createStatementSpec), (writeTransSig, writeTransSpec), (stmtSig, stmtSpec),
   (htmlSig, htmlSpec), (ebcCompareSig, ebcCompareSpec), (decodeZonedSig, decodeZonedSpec),
   (trunc11Sig, trunc11Spec), (fmtZSig, fmtZSpec)]

/-! ## Parts of the invariants -/

/-- The `String[]` at `a`: strings with the texts `ts`, then `n` nulls. -/
def TextsAt (σ : State) (a : Addr) (ts : List JStr) (n : Nat) : Prop :=
  ∃ xs, σ.heap a = some (.array (.cls "java.lang.String") (xs ++ List.replicate n .null)) ∧
    Forall2 (JStrAt σ) xs ts

/-- Local `i` holds a string with the text `s`. -/
def StrLoc (σ : State) (fr : Frame) (i : Nat) (s : JStr) : Prop :=
  ∃ x, fr.get i = some (.ref x) ∧ σ.heap x = some (.str s)

/-- At every cut point: the parameters in their locals; the `Result` object (fresh) holding `o`; the objects of
the entry state unchanged; class states and statics unchanged. -/
def RunBase (g : RunG) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh : Addr) (o : JOut) : Prop :=
  fr.get 10 = some (.ref g.a1) ∧ fr.get 23 = some (.ref g.a2) ∧ fr.get 9 = some (.ref g.a3) ∧
  fr.get 6 = some (.ref g.a4) ∧ fr.get 7 = some (.ref res) ∧
  ResAtL σ res ld ls lh o.disp o.stmt o.html o.ab ∧
  σ0.next ≤ res ∧ σ0.next ≤ ld ∧ σ0.next ≤ ls ∧ σ0.next ≤ lh ∧
  Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics

/-- After the four text loops: `trnxTexts`, `xrefTexts`, `custKeys`, `custTexts`, `acctTexts` (fresh, allocated
in this order), the customers' count in `$i20` and the accounts' in `i`. -/
def RunTexts (g : RunG) (σ0 : State) (fr : Frame) (σ : State) (t1 t2 t3k t3 t4 : Addr) : Prop :=
  fr.get 11 = some (.ref t1) ∧ fr.get 12 = some (.ref t2) ∧ fr.get 13 = some (.ref t3k) ∧
  fr.get 14 = some (.ref t3) ∧ fr.get 15 = some (.ref t4) ∧
  (∃ n3 : I32, fr.get 27 = some (.int n3) ∧ n3.toInt = g.crs.length) ∧
  (∃ n4 : I32, fr.get 28 = some (.int n4) ∧ n4.toInt = g.ars.length) ∧
  TextsAt σ t1 g.T1 0 ∧ TextsAt σ t2 g.T2 0 ∧ TextsAt σ t3k g.K3 0 ∧ TextsAt σ t3 g.T3 0 ∧
  TextsAt σ t4 g.T4 0 ∧
  σ0.next ≤ t1 ∧ t1 < t2 ∧ t2 < t3k ∧ t3k < t3 ∧ t3 < t4

/-- The table memory and the counts array in their locals, holding the load state `s`. -/
def LoadAt (σ : State) (fr : Frame) (mem trct : Addr) (s : LdSt) : Prop :=
  fr.get 16 = some (.ref mem) ∧ fr.get 24 = some (.ref trct) ∧
  SlotsAt σ mem s.m ∧ σ.heap trct = some (.array (.prim .long) s.trct) ∧ s.trct.length = 51

/-- The counters stay in `0 … 9999` (they are kept modulo 10000), and so do the stored counts. -/
def LdBounded (s : LdSt) : Prop :=
  0 ≤ s.cr.toInt ∧ s.cr.toInt < 10000 ∧ 0 ≤ s.tr.toInt ∧ s.tr.toInt < 10000 ∧
  ∀ v ∈ s.trct, ∃ c : I64, v = .long c ∧ 0 ≤ c.toInt ∧ c.toInt < 10000

/-- The cross-reference loop's state: the text arrays, the loaded table `L` (memory after the text arrays, then
the counts array, then `xrefSt`), `xrefSt` = `{j', 0}`, the end flags clear, `crCnt` = `L.cr`; the `Result`
holds `oc`. -/
def XCtx (g : RunG) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh : Addr) (oc : JOut) (L : LdSt)
    (j' : Nat) : Prop :=
  ∃ t1 t2 t3k t3 t4 mem trct st2,
    RunBase g σ0 fr σ res ld ls lh oc ∧ RunTexts g σ0 fr σ t1 t2 t3k t3 t4 ∧ LoadAt σ fr mem trct L ∧
    fr.get 2 = some (.ref st2) ∧ σ.heap st2 = some (.array (.prim .int) [.int (BitVec.ofNat 32 j'), .int 0]) ∧
    t4 < mem ∧ mem < trct ∧ trct < st2 ∧
    fr.get 5 = some (.int 0) ∧ fr.get 3 = some (.int 0) ∧ fr.get 18 = some (.long L.cr) ∧ LdBounded L

/-- Record `x`'s card number, customer id and account id in `tRest`, `xrefCustId`, `cn`. -/
def XrecLocs (σ : State) (fr : Frame) (x : JStr) : Prop :=
  StrLoc σ fr 32 (sub (fixStr x 1000) 0 16) ∧ StrLoc σ fr 34 (sub (fixStr x 1000) 16 25) ∧
  StrLoc σ fr 33 (sub (fixStr x 1000) 25 36)

/-- A total kept to 11 digits. -/
def TotOk (t : I64) : Prop := -100000000000 < t.toInt ∧ t.toInt < 100000000000

/-! ## The invariants -/

/-- Statement 12: the TRNXFILE texts loop, `i` texts stored. -/
def inv12 (g : RunG) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (res ld ls lh t1 : Addr) (n i : I32), RunBase g σ0 fr σ res ld ls lh JOut.init ∧
    fr.get 11 = some (.ref t1) ∧ fr.get 27 = some (.int n) ∧ fr.get 28 = some (.int i) ∧
    n.toInt = g.trs.length ∧ 0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧
    TextsAt σ t1 (g.T1.take i.toInt.toNat) (g.trs.length - i.toInt.toNat) ∧ σ0.next ≤ t1

/-- Statement 24: the XREFFILE texts loop. -/
def inv24 (g : RunG) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (res ld ls lh t1 t2 : Addr) (n i : I32), RunBase g σ0 fr σ res ld ls lh JOut.init ∧
    fr.get 11 = some (.ref t1) ∧ fr.get 12 = some (.ref t2) ∧ fr.get 27 = some (.int n) ∧
    fr.get 29 = some (.int i) ∧ n.toInt = g.xrs.length ∧ 0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧
    TextsAt σ t1 g.T1 0 ∧ TextsAt σ t2 (g.T2.take i.toInt.toNat) (g.xrs.length - i.toInt.toNat) ∧
    σ0.next ≤ t1 ∧ t1 < t2

/-- Statement 37: the CUSTFILE loop (`custTexts[i]` and its first 9 characters `custKeys[i]`). -/
def inv37 (g : RunG) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (res ld ls lh t1 t2 t3k t3 : Addr) (n i : I32), RunBase g σ0 fr σ res ld ls lh JOut.init ∧
    fr.get 11 = some (.ref t1) ∧ fr.get 12 = some (.ref t2) ∧ fr.get 13 = some (.ref t3k) ∧
    fr.get 14 = some (.ref t3) ∧ fr.get 27 = some (.int n) ∧ fr.get 30 = some (.int i) ∧
    n.toInt = g.crs.length ∧ 0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧
    TextsAt σ t1 g.T1 0 ∧ TextsAt σ t2 g.T2 0 ∧
    TextsAt σ t3k (g.K3.take i.toInt.toNat) (g.crs.length - i.toInt.toNat) ∧
    TextsAt σ t3 (g.T3.take i.toInt.toNat) (g.crs.length - i.toInt.toNat) ∧
    σ0.next ≤ t1 ∧ t1 < t2 ∧ t2 < t3k ∧ t3k < t3

/-- Statement 52: the ACCTFILE loop (index `i#78`; the customers' count in `$i20`, the accounts' in `i`). -/
def inv52 (g : RunG) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (res ld ls lh t1 t2 t3k t3 t4 : Addr) (n3 n i : I32), RunBase g σ0 fr σ res ld ls lh JOut.init ∧
    fr.get 11 = some (.ref t1) ∧ fr.get 12 = some (.ref t2) ∧ fr.get 13 = some (.ref t3k) ∧
    fr.get 14 = some (.ref t3) ∧ fr.get 15 = some (.ref t4) ∧ fr.get 27 = some (.int n3) ∧
    fr.get 28 = some (.int n) ∧ fr.get 26 = some (.int i) ∧
    n3.toInt = g.crs.length ∧ n.toInt = g.ars.length ∧ 0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧
    TextsAt σ t1 g.T1 0 ∧ TextsAt σ t2 g.T2 0 ∧ TextsAt σ t3k g.K3 0 ∧ TextsAt σ t3 g.T3 0 ∧
    TextsAt σ t4 (g.T4.take i.toInt.toNat) (g.ars.length - i.toInt.toNat) ∧
    σ0.next ≤ t1 ∧ t1 < t2 ∧ t2 < t3k ∧ t3k < t3 ∧ t3 < t4

/-- Statement 80 (`label19`): the load loop. Record `k` of `R1` is in `cn` (read: `trnxSt` = `{k + 1, 0}`),
`tRest` holds `saveCard`, `crCnt` and `crJmp` (`trCnt`) the counters of `s`; the table holds `s`; loading the
records from `k` on, then the cross-reference loop, gives `run`'s outputs. -/
def inv80 (g : RunG) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (res ld ls lh t1 t2 t3k t3 t4 mem trct st1 : Addr) (s : LdSt) (k : Nat),
    RunBase g σ0 fr σ res ld ls lh JOut.init ∧ RunTexts g σ0 fr σ t1 t2 t3k t3 t4 ∧ LoadAt σ fr mem trct s ∧
    fr.get 1 = some (.ref st1) ∧
    σ.heap st1 = some (.array (.prim .int) [.int (BitVec.ofNat 32 (k + 1)), .int 0]) ∧
    t4 < mem ∧ mem < trct ∧ trct < st1 ∧
    k < g.R1.length ∧ StrLoc σ fr 33 (g.R1.getD k []) ∧ StrLoc σ fr 32 s.save ∧
    fr.get 18 = some (.long s.cr) ∧ fr.get 17 = some (.long s.tr) ∧ LdBounded s ∧
    xrefAll g.K3 g.T3 g.T4 (ldFin (ldAll s (g.R1.drop k))) JOut.init g.T2 = g.F

/-- Statement 117 (`label24`): the cross-reference loop, records `0 … j - 1` done. -/
def inv117 (g : RunG) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (res ld ls lh : Addr) (L : LdSt) (o : JOut) (j : Nat), XCtx g σ0 fr σ res ld ls lh o L j ∧
    j ≤ g.T2.length ∧ xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F

/-- Statement 140 (`label28`): record `j` read; the search of the customer keys, `custRec` still `null`, keys
`0 … i - 1` differ from its customer id. -/
def inv140 (g : RunG) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (res ld ls lh : Addr) (L : LdSt) (o : JOut) (j : Nat) (i : I32), XCtx g σ0 fr σ res ld ls lh o L (j + 1) ∧
    j < g.T2.length ∧ xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F ∧ XrecLocs σ fr (g.T2.getD j []) ∧
    fr.get 37 = some .null ∧ fr.get 26 = some (.int i) ∧ 0 ≤ i.toInt ∧ i.toInt ≤ g.crs.length ∧
    ∀ k, k < i.toInt.toNat → g.K3.getD k [] ≠ sub (fixStr (g.T2.getD j []) 1000) 16 25

/-- Statement 153 (`label32`): the customer text `crec` found; the search of the account texts, `i#77` still
`null`, texts `0 … i - 1` do not start with the account id. -/
def inv153 (g : RunG) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (res ld ls lh : Addr) (L : LdSt) (o : JOut) (j : Nat) (i : I32) (crec : JStr),
    XCtx g σ0 fr σ res ld ls lh o L (j + 1) ∧
    j < g.T2.length ∧ xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F ∧ XrecLocs σ fr (g.T2.getD j []) ∧
    StrLoc σ fr 37 crec ∧ custFind g.K3 g.T3 (sub (fixStr (g.T2.getD j []) 1000) 16 25) = some crec ∧
    fr.get 38 = some .null ∧ fr.get 26 = some (.int i) ∧ 0 ≤ i.toInt ∧ i.toInt ≤ g.ars.length ∧
    ∀ k, k < i.toInt.toNat → sub (g.T4.getD k []) 0 11 ≠ sub (fixStr (g.T2.getD j []) 1000) 25 36

/-- Statement 168 (`label36`): the cards loop of record `j` at card number `crJmp` (`n` cards left), the `Result`
holding `oc` and the running total `total`; the loop's result `pF`, then the statement's tail and the records
after `j`, give `run`'s outputs. -/
def inv168 (g : RunG) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (res ld ls lh : Addr) (L : LdSt) (oc : JOut) (j : Nat) (crJmp total : I64) (n : Nat) (pF : JOut × I64),
    XCtx g σ0 fr σ res ld ls lh oc L (j + 1) ∧ j < g.T2.length ∧
    xrefAll g.K3 g.T3 g.T4 L (tailOf pF.1 pF.2) (g.T2.drop (j + 1)) = g.F ∧
    StrLoc σ fr 32 (sub (fixStr (g.T2.getD j []) 1000) 0 16) ∧
    fr.get 17 = some (.long crJmp) ∧ fr.get 21 = some (.long total) ∧ TotOk total ∧
    1 ≤ crJmp.toInt ∧ crJmp.toInt + n = L.cr.toInt + 1 ∧
    cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) n crJmp (oc, total) = pF

/-- Statement 179 (`label37`): the transactions loop of card number `crJmp` (`cnt` transactions, `trJmp` next);
`acc0` the outputs and total before the card. -/
def inv179 (g : RunG) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (res ld ls lh : Addr) (L : LdSt) (oc : JOut) (j : Nat) (crJmp total : I64) (n : Nat) (pF : JOut × I64)
    (cnt trJmp : I64) (acc0 : JOut × I64),
    XCtx g σ0 fr σ res ld ls lh oc L (j + 1) ∧ j < g.T2.length ∧
    xrefAll g.K3 g.T3 g.T4 L (tailOf pF.1 pF.2) (g.T2.drop (j + 1)) = g.F ∧
    StrLoc σ fr 32 (sub (fixStr (g.T2.getD j []) 1000) 0 16) ∧
    fr.get 17 = some (.long crJmp) ∧ fr.get 21 = some (.long total) ∧ TotOk total ∧
    1 ≤ crJmp.toInt ∧ crJmp.toInt ≤ L.cr.toInt ∧ crJmp.toInt + n = L.cr.toInt + 1 ∧
    fr.get 19 = some (.long cnt) ∧ trctGet L.trct crJmp = .long cnt ∧
    fr.get 22 = some (.long trJmp) ∧ 1 ≤ trJmp.toInt ∧ trJmp.toInt ≤ cnt.toInt + 1 ∧
    (oc, total) = transOf L.m crJmp (trJmp.toInt.toNat - 1) acc0 ∧
    cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) (n - 1) (crJmp + 1)
      (transOf L.m crJmp cnt.toInt.toNat acc0) = pF

/-- The invariants of `run`. -/
def runInv (g : RunG) : Invariants :=
  [(12, inv12 g), (24, inv24 g), (37, inv37 g), (52, inv52 g), (80, inv80 g), (117, inv117 g),
   (140, inv140 g), (153, inv153 g), (168, inv168 g), (179, inv179 g)]

/-- The paths of `run` from statement `pc`. -/
@[irreducible] def runWP (g : RunG) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA ((runInv g).inst args σ0) ((runSpecG g).post args σ0)
    300 pc fr σ

/-! ## The verification conditions, by segment (proved in `CbARun.*`) -/

/-- The entry path (statements 0 … 12). -/
def RunEntryVC (g : RunG) : Prop :=
  ∀ args σ0, RunPre g args σ0 → runWP g args σ0 0 (Frame.init true args) σ0

/-- The paths from cut point `pc` with invariant `I`. -/
def RunCutVC (g : RunG) (pc : Nat) (I : RunG → List Value → State → Frame → State → Prop) : Prop :=
  ∀ args σ0, RunPre g args σ0 → ∀ fr σ, I g args σ0 fr σ → runWP g args σ0 pc fr σ

end EquivLean.Modernize.Cbstm03a.Java
