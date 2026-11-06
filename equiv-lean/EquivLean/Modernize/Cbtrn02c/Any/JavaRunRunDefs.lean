import EquivLean.Modernize.Cbtrn02c.Any.JavaRunW
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVR

/-!
# CBTRN02C → Java: `run` with fixed inputs

`G`: the argument objects and the field values they hold; `runSpecG g`: `runSpec` for these
inputs.  `G.st g n`: the model state after the first `n` daily transactions.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

abbrev FV := EquivLean.Cobol.Rec.FVal

/-- The inputs of `run`: the argument objects and the field values they hold. -/
structure G where
  a1 : Addr
  a2 : Addr
  a3 : Addr
  a4 : Addr
  cs : Addr
  trans : List (List FV)
  xrefs : List (List FV)
  accts : List (List FV)
  cats : List (List FV)
  clk : List UInt8

namespace G

def args (g : G) : List Value := [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4, .ref g.cs]
def step (g : G) : Model.St → List FV → Model.St := Model.step g.xrefs g.clk
/-- The model state after the first `n` daily transactions. -/
def st (g : G) (n : Nat) : Model.St := (g.trans.take n).foldl g.step (Model.init g.accts g.cats)
/-- What the model outputs. -/
def out (g : G) : Model.Out := Model.run g.trans g.xrefs g.accts g.cats g.clk
/-- The `n`-th daily transaction. -/
def trec (g : G) (n : Nat) : List FV := g.trans.getD n []

end G

/-- The classes `run` uses are initialized. -/
def Inits (σ : State) : Prop :=
  σ.initOf "Cbtrn02c" = .done ∧ σ.initOf "Cbtrn02c$Result" = .done ∧
  σ.initOf "Cbtrn02c$AccountRecord" = .done ∧ σ.initOf "Cbtrn02c$CardXrefRecord" = .done ∧
  σ.initOf "Cbtrn02c$DalytranRecord" = .done ∧ σ.initOf "Cbtrn02c$TranCatBalRecord" = .done ∧
  σ.initOf "Cbtrn02c$RejectRecord" = .done ∧ σ.initOf "Cbtrn02c$TranRecord" = .done

/-- The precondition of `run` with fixed inputs. -/
def RunPreG (g : G) (args : List Value) (σ : State) : Prop :=
  args = g.args ∧ RunIn g.args σ g.trans g.xrefs g.accts g.cats g.clk ∧ Inits σ

/-- The postcondition of `run` (the body of `runSpec`'s) with fixed inputs. -/
def RunPostG (g : G) (r : Option Value) (σ' : State) : Prop :=
  ∃ res fs l k xs mods, r = some (.ref res) ∧
    σ'.heap res = some (.plain "Cbtrn02c$Result" fs) ∧
    Fields.get fs ("Cbtrn02c$Result", "displays") = some (.ref l) ∧
    σ'.heap l = some (.list k xs mods) ∧ Forall2 (JStrAt σ') xs (g.out.disp.map jline) ∧
    ListOf σ' fs "transactFileWrites" TranRecord "Cbtrn02c$TranRecord" g.out.tranW ∧
    ListOf σ' fs "dalyrejsFileWrites" RejectRecord "Cbtrn02c$RejectRecord" g.out.rejW ∧
    ListOf σ' fs "tcatbalFileWrites" TranCatBalRecord "Cbtrn02c$TranCatBalRecord" g.out.catW ∧
    ListOf σ' fs "accountFileRewrites" AccountRecord "Cbtrn02c$AccountRecord" g.out.acctRW ∧
    ListOf σ' fs "tcatbalFileRewrites" TranCatBalRecord "Cbtrn02c$TranCatBalRecord" g.out.catRW ∧
    Fields.get fs ("Cbtrn02c$Result", "returnCode") = some (.int (BitVec.ofInt 32 g.out.rc)) ∧
    Fields.get fs ("Cbtrn02c$Result", "abended") = some (.int 0)

def runSpecG (g : G) : Spec := Spec.of (RunPreG g) (fun _ _ r σ' => RunPostG g r σ')

/-! ## The heap of `run` -/

/-- The inputs in the heap: the daily transactions and cross-references as arrays of record
objects (none of them a work-storage object), the clock text. -/
def Inp (σ : State) (g : G) (A : Addrs) : Prop :=
  ARec σ g.a1 DalytranRecord "Cbtrn02c$DalytranRecord" A.ws g.trans ∧
  ARec σ g.a2 CardXrefRecord "Cbtrn02c$CardXrefRecord" A.ws g.xrefs ∧
  JStrAt σ (.ref g.cs) (cp037Str g.clk)

/-- What the model keeps valid: the account and category records, the `FILLER` length. -/
def MV (s : Model.St) : Prop :=
  (∀ a ∈ s.accts, AccountRecord.Valid a) ∧ (∀ c ∈ s.cats, TranCatBalRecord.Valid c) ∧
  s.catFill.length = 22

/-- The locals of the main loop. -/
def Locs65 (g : G) (A : Addrs) (fr : Frame) : Prop :=
  fr.get 32 = some (.ref g.a1) ∧ fr.get 0 = some (.ref g.a2) ∧ fr.get 16 = some (.ref g.cs) ∧
  fr.get 31 = some (.ref A.r) ∧ fr.get 8 = some (.ref A.aD) ∧ fr.get 11 = some (.ref A.lC) ∧
  fr.get 12 = some (.ref A.lK) ∧ fr.get 6 = some (.ref A.wX) ∧ fr.get 13 = some (.ref A.wA) ∧
  fr.get 29 = some (.ref A.wC) ∧ fr.get 28 = some (.ref A.wT)

/-- **The main loop** (statement 65): `k` transactions processed, the counters, the state holds
the model state after them. -/
def J65 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (A : Addrs) (k : Nat) (next z : I32) (tx rej : I64) (et : JType) (xsD : List Value),
    Locs65 g A fr ∧ fr.get 14 = some (.int next) ∧ fr.get 4 = some (.int z) ∧
    fr.get 9 = some (.long tx) ∧ fr.get 10 = some (.long rej) ∧
    σ.heap g.a1 = some (.array et xsD) ∧ xsD.length = g.trans.length ∧
    next.toInt = k ∧ k ≤ g.trans.length ∧ (z = 0#32 ∨ (z = 1#32 ∧ k = g.trans.length)) ∧
    tx = BitVec.ofNat 64 (k % 1000000000) ∧ rej = BitVec.ofNat 64 ((g.st k).rejects % 1000000000) ∧
    Hide (W σ A (g.st k) ∧ Inp σ g A ∧ MV (g.st k)) ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics ∧ σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c"

/-- After `validateTran` (statement 75): the transaction `k` is `d`, its reject reason `c`; when
it is valid, `xrefWs` and `acctWs` hold its cross-reference and account. -/
def J75 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (A : Addrs) (k : Nat) (next c : I32) (tx rej : I64) (et : JType) (xsD : List Value) (d : Addr),
    Locs65 g A fr ∧ fr.get 14 = some (.int next) ∧ fr.get 9 = some (.long tx) ∧
    fr.get 10 = some (.long rej) ∧ fr.get 30 = some (.ref d) ∧ fr.get 15 = some (.int c) ∧
    σ.heap g.a1 = some (.array et xsD) ∧ xsD.length = g.trans.length ∧ xsD[k]? = some (.ref d) ∧
    k < g.trans.length ∧ next.toInt = k + 1 ∧
    tx = BitVec.ofNat 64 ((k + 1) % 1000000000) ∧ rej = BitVec.ofNat 64 ((g.st k).rejects % 1000000000) ∧
    c = BitVec.ofInt 32 (vreason g.xrefs (g.st k).accts (g.trec k)) ∧
    Hide (W σ A (g.st k) ∧ Inp σ g A ∧ MV (g.st k) ∧
      (vreason g.xrefs (g.st k).accts (g.trec k) = 0 → ∃ x a,
        Model.findXref g.xrefs (Model.tCard (g.trec k)) = some x ∧
        Model.findAcct (g.st k).accts (Model.xAcct x) = some a ∧
        JRecAt CardXrefRecord "Cbtrn02c$CardXrefRecord" σ (.ref A.wX) x ∧
        JRecAt AccountRecord "Cbtrn02c$AccountRecord" σ (.ref A.wA) a)) ∧
    Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c"

/-! ## Before the main loop -/

/-- The `Result` at `σ0.next` with its six fresh lists, the start line displayed. -/
def ResInit (σ0 σ : State) : Prop :=
  ∃ fs, σ.heap σ0.next = some (.plain "Cbtrn02c$Result" fs) ∧
    Fields.get fs ("Cbtrn02c$Result", "displays") = some (.ref (σ0.next + 1)) ∧
    Fields.get fs ("Cbtrn02c$Result", "transactFileWrites") = some (.ref (σ0.next + 2)) ∧
    Fields.get fs ("Cbtrn02c$Result", "dalyrejsFileWrites") = some (.ref (σ0.next + 3)) ∧
    Fields.get fs ("Cbtrn02c$Result", "tcatbalFileWrites") = some (.ref (σ0.next + 4)) ∧
    Fields.get fs ("Cbtrn02c$Result", "accountFileRewrites") = some (.ref (σ0.next + 5)) ∧
    Fields.get fs ("Cbtrn02c$Result", "tcatbalFileRewrites") = some (.ref (σ0.next + 6)) ∧
    Fields.get fs ("Cbtrn02c$Result", "returnCode") = some (.int 0) ∧
    Fields.get fs ("Cbtrn02c$Result", "abended") = some (.int 0)

/-- The display list holds the start line; the other output lists are empty. -/
def ListsInit (σ0 σ : State) : Prop :=
  (∃ m, σ.heap (σ0.next + 1) = some (.list .arrayList [.ref (σ0.next + 7)] m)) ∧
  σ.heap (σ0.next + 7) = some (.str (jline (Model.txt "START OF EXECUTION OF PROGRAM CBTRN02C"))) ∧
  (∃ m, σ.heap (σ0.next + 2) = some (.list .arrayList [] m)) ∧
  (∃ m, σ.heap (σ0.next + 3) = some (.list .arrayList [] m)) ∧
  (∃ m, σ.heap (σ0.next + 4) = some (.list .arrayList [] m)) ∧
  (∃ m, σ.heap (σ0.next + 5) = some (.list .arrayList [] m)) ∧
  (∃ m, σ.heap (σ0.next + 6) = some (.list .arrayList [] m))

/-- The account table at `σ0.next + 8`: the copies of the first `i` accounts, then `null`s. -/
def TabInit (g : G) (σ0 σ : State) (i : Nat) : Prop :=
  ∃ ys, σ.heap (σ0.next + 8) = some (.array (.cls "Cbtrn02c$AccountRecord")
      (ys ++ List.replicate (g.accts.length - i) .null)) ∧
    Forall2 (JRecAt AccountRecord "Cbtrn02c$AccountRecord" σ) ys (g.accts.take i) ∧
    ∀ v ∈ ys, ∀ a, v = .ref a → σ0.next + 9 ≤ a

/-- The account copy loop (statement 12). -/
def J12 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ i : I32, fr.get 32 = some (.ref g.a1) ∧ fr.get 0 = some (.ref g.a2) ∧
    fr.get 7 = some (.ref g.a3) ∧ fr.get 2 = some (.ref g.a4) ∧ fr.get 16 = some (.ref g.cs) ∧
    fr.get 31 = some (.ref σ0.next) ∧ fr.get 8 = some (.ref (σ0.next + 8)) ∧
    fr.get 15 = some (.int i) ∧ 0 ≤ i.toInt ∧ i.toInt ≤ g.accts.length ∧
    Hide (ResInit σ0 σ ∧ ListsInit σ0 σ ∧ TabInit g σ0 σ i.toInt.toNat) ∧
    σ0.next + 9 ≤ σ.next ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c"

/-- The category copy loop (statement 22): the account table complete, the category list at
`c` holds copies of the first `i` category records. -/
def J22 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (c : Addr), fr.get 32 = some (.ref g.a1) ∧ fr.get 0 = some (.ref g.a2) ∧
    fr.get 2 = some (.ref g.a4) ∧ fr.get 16 = some (.ref g.cs) ∧
    fr.get 31 = some (.ref σ0.next) ∧ fr.get 8 = some (.ref (σ0.next + 8)) ∧
    fr.get 11 = some (.ref c) ∧ fr.get 15 = some (.int i) ∧ 0 ≤ i.toInt ∧ i.toInt ≤ g.cats.length ∧
    Hide (ResInit σ0 σ ∧ ListsInit σ0 σ ∧ TabInit g σ0 σ g.accts.length ∧
      (∃ xs m, σ.heap c = some (.list .arrayList xs m) ∧
        Forall2 (JRecAt TranCatBalRecord "Cbtrn02c$TranCatBalRecord" σ) xs (g.cats.take i.toInt.toNat) ∧
        ∀ v ∈ xs, ∀ a, v = .ref a → σ0.next + 9 ≤ a) ∧ σ0.next + 9 ≤ c) ∧
    σ0.next + 9 ≤ σ.next ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c"

end EquivLean.Modernize.Cbtrn02c.Java
