import EquivLean.Demo.Gen.Jimple.Cbact04c

/-!
# CBACT04C in Java: what the code computes, and the contracts of its methods

`examples/java/cbact04c/Cbact04c.java` (javac + Soot, imported as `Cb.Gen`). This file has

* `JCat`/`JAcct`/`JDisc`: the records as the Java code sees them (Java `long`/`int` values and
  strings), and `CatAt`/`AcctAt`/`DiscAt`: such a record as an object of the heap;
* `jStep`/`jRun`: one iteration of the main loop of `run` and the whole loop, over the records,
  with Java's arithmetic (`BitVec.sdiv`/`srem`, i.e. `/` and `%` on `long`);
* the contracts `readAccountSpec`, `readRateSpec`, `postSpec`, `runSpec`: `run` returns the
  rewrites and the transaction count of `jRun`.
-/

open Jimple

namespace EquivLean.Demo.Cbact04c

/-- Two lists related element by element. -/
def Pairs {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as1, b :: bs1 => R a b ∧ Pairs R as1 bs1
  | _, _ => False

/-! ## Records -/

/-- A category-balance record (TRAN-CAT-BAL-RECORD). -/
structure JCat where
  acct : I64
  ty : JStr
  cat : I32
  bal : I64
  deriving Inhabited

/-- An account record: the fields the program reads or changes. -/
structure JAcct where
  id : I64
  bal : I64
  cc : I64
  cd : I64
  grp : JStr
  deriving Inhabited

/-- A disclosure-group record. -/
structure JDisc where
  grp : JStr
  ty : JStr
  cat : I32
  rate : I64
  deriving Inhabited

/-- `v` is a reference to a `String` holding `s`. -/
def StrAt (σ : State) (v : Value) (s : JStr) : Prop :=
  ∃ x, v = .ref x ∧ σ.heap x = some (.str s)

def CatAt (σ : State) (v : Value) (c : JCat) : Prop :=
  ∃ x fs t, v = .ref x ∧ σ.heap x = some (.plain "Cbact04c$Cat" fs) ∧
    Fields.get fs ("Cbact04c$Cat", "acctId") = some (.long c.acct) ∧
    Fields.get fs ("Cbact04c$Cat", "typeCd") = some t ∧ StrAt σ t c.ty ∧
    Fields.get fs ("Cbact04c$Cat", "catCd") = some (.int c.cat) ∧
    Fields.get fs ("Cbact04c$Cat", "bal") = some (.long c.bal)

def AcctAt (σ : State) (v : Value) (a : JAcct) : Prop :=
  ∃ x fs g, v = .ref x ∧ σ.heap x = some (.plain "Cbact04c$Account" fs) ∧
    Fields.get fs ("Cbact04c$Account", "id") = some (.long a.id) ∧
    Fields.get fs ("Cbact04c$Account", "bal") = some (.long a.bal) ∧
    Fields.get fs ("Cbact04c$Account", "cycCredit") = some (.long a.cc) ∧
    Fields.get fs ("Cbact04c$Account", "cycDebit") = some (.long a.cd) ∧
    Fields.get fs ("Cbact04c$Account", "groupId") = some g ∧ StrAt σ g a.grp

def DiscAt (σ : State) (v : Value) (d : JDisc) : Prop :=
  ∃ x fs g t, v = .ref x ∧ σ.heap x = some (.plain "Cbact04c$Disc" fs) ∧
    Fields.get fs ("Cbact04c$Disc", "groupId") = some g ∧ StrAt σ g d.grp ∧
    Fields.get fs ("Cbact04c$Disc", "typeCd") = some t ∧ StrAt σ t d.ty ∧
    Fields.get fs ("Cbact04c$Disc", "catCd") = some (.int d.cat) ∧
    Fields.get fs ("Cbact04c$Disc", "rate") = some (.long d.rate)

/-! ## The main loop of `run` -/

/-- State of the main loop: the rewrites so far (in order), the transaction count, `firstTime`,
`lastAcct`, `totalInt` and the current account. -/
structure JState where
  rewrites : List JAcct
  tx : I32
  first : Bool
  last : I64
  total : I64
  acct : JAcct

/-- `post(a, t)`: interest posted, cycle credit and debit zero (`S9(10)V99`: `% 10^12`). -/
def jPost (a : JAcct) (t : I64) : JAcct :=
  ⟨a.id, (a.bal + t).srem 1000000000000, 0, 0, a.grp⟩

/-- One iteration on the record `c`, with the account and rate lookups `acctOf`, `rateOf`. -/
def jStep (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64) (s : JState) (c : JCat) :
    JState :=
  let s1 : JState :=
    if s.first || c.acct != s.last then
      { rewrites := if s.first then s.rewrites else s.rewrites ++ [jPost s.acct s.total],
        tx := s.tx, first := false, last := c.acct, total := 0, acct := acctOf c.acct }
    else s
  let r := rateOf s1.acct.grp c.ty c.cat
  if r = 0 then s1
  else { s1 with total := (s1.total + ((c.bal * r).sdiv 120000).srem 100000000000).srem 100000000000,
                 tx := s1.tx + 1 }

def jInit : JState := ⟨[], 0, true, 0, 0, default⟩

/-- The loop over all records. -/
def jRun (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64) (cs : List JCat) : JState :=
  cs.foldl (jStep acctOf rateOf) jInit

/-! ## Contracts -/

/-- The `id` of an `Account` object. -/
def idOf (σ : State) (v : Value) : Option I64 :=
  match v with
  | .ref a =>
    match σ.heap a with
    | some (.plain "Cbact04c$Account" fs) =>
      match Fields.get fs ("Cbact04c$Account", "id") with
      | some (.long i) => some i
      | _ => none
    | _ => none
  | _ => none

/-- `readAccount(accounts, id)` on an array of accounts with exactly one account `a` with key
`id` (the keyed READ finds it): returns that object; the state is unchanged. -/
def readAccountSpec : Spec := Spec.of
  (fun args σ => ∃ aa id et xs a, args = [.ref aa, .long id] ∧ σ.heap aa = some (.array et xs) ∧
     xs.length < 2147483647 ∧ (∀ x ∈ xs, ∃ b, AcctAt σ x b) ∧
     (∃ x ∈ xs, AcctAt σ x a) ∧ a.id = id ∧ ∀ x ∈ xs, idOf σ x = some id → AcctAt σ x a)
  (fun args σ r σ' => ∀ aa id et xs a, args = [.ref aa, .long id] → σ.heap aa = some (.array et xs) →
     (∃ x ∈ xs, AcctAt σ x a) → a.id = id → (∀ x ∈ xs, idOf σ x = some id → AcctAt σ x a) →
     ∃ v, r = some v ∧ AcctAt σ v a ∧ σ' = σ)

/-- `readRate(discs, group, type, cat)` when some record has this key and every record with
this key has rate `rate`: returns `rate`; the state is unchanged. -/
def readRateSpec : Spec := Spec.of
  (fun args σ => ∃ da g t gs ts cat rate et xs, args = [.ref da, .ref gs, .ref ts, .int cat] ∧
     σ.heap gs = some (.str g) ∧ σ.heap ts = some (.str t) ∧
     σ.heap da = some (.array et xs) ∧ xs.length < 2147483647 ∧ (∀ x ∈ xs, ∃ d, DiscAt σ x d) ∧
     (∃ x ∈ xs, DiscAt σ x ⟨g, t, cat, rate⟩) ∧
     ∀ x ∈ xs, ∀ d, DiscAt σ x d → d.grp = g → d.ty = t → d.cat = cat → d.rate = rate)
  (fun args σ r σ' => ∀ da g t gs ts cat rate et xs, args = [.ref da, .ref gs, .ref ts, .int cat] →
     σ.heap gs = some (.str g) → σ.heap ts = some (.str t) → σ.heap da = some (.array et xs) →
     (∃ x ∈ xs, DiscAt σ x ⟨g, t, cat, rate⟩) →
     (∀ x ∈ xs, ∀ d, DiscAt σ x d → d.grp = g → d.ty = t → d.cat = cat → d.rate = rate) →
     r = some (.long rate) ∧ σ' = σ)

/-- The heap only grows: existing objects are unchanged. -/
def Grows (σ σ' : State) : Prop := σ.next ≤ σ'.next ∧ ∀ x, x < σ.next → σ'.heap x = σ.heap x

/-- `post(a, t)`: a new account object with the fields of `jPost a t`. -/
def postSpec : Spec := Spec.of
  (fun args σ => ∃ v t a, args = [v, .long t] ∧ AcctAt σ v a ∧ σ.initOf "Cbact04c$Account" = .done)
  (fun args σ r σ' => ∀ v t a, args = [v, .long t] → AcctAt σ v a →
     ∃ w, r = some w ∧ AcctAt σ' w (jPost a t) ∧ Grows σ σ' ∧
       σ'.initOf "Cbact04c$Account" = .done ∧ σ'.initOf "Cbact04c$Result" = σ.initOf "Cbact04c$Result" ∧
       σ'.initOf "Cbact04c" = σ.initOf "Cbact04c")

/-- The inputs of `run`: the category records `cs` (an array `ca`), the accounts (array `aa`) with
the account `acctOf c.acct` for each record (unique keys), the disclosure groups (array `da`) with
a record of key `(acctOf c.acct).grp, c.ty, c.cat` and rate `rateOf …` for each record. -/
def RunPre (σ : State) (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) : Prop :=
  (∃ et xs, σ.heap ca = some (.array et xs) ∧ Pairs (CatAt σ) xs cs) ∧
  cs.length < 2147483647 ∧
  (∃ et xs, σ.heap aa = some (.array et xs) ∧ xs.length < 2147483647 ∧
    (∀ x ∈ xs, ∃ b, AcctAt σ x b) ∧
    ∀ c ∈ cs, (acctOf c.acct).id = c.acct ∧ (∃ x ∈ xs, AcctAt σ x (acctOf c.acct)) ∧
      ∀ x ∈ xs, idOf σ x = some c.acct → AcctAt σ x (acctOf c.acct)) ∧
  (∃ et xs, σ.heap da = some (.array et xs) ∧ xs.length < 2147483647 ∧
    (∀ x ∈ xs, ∃ d, DiscAt σ x d) ∧
    ∀ c ∈ cs,
      (∃ x ∈ xs, DiscAt σ x ⟨(acctOf c.acct).grp, c.ty, c.cat, rateOf (acctOf c.acct).grp c.ty c.cat⟩) ∧
      ∀ x ∈ xs, ∀ d, DiscAt σ x d → d.grp = (acctOf c.acct).grp → d.ty = c.ty → d.cat = c.cat →
        d.rate = rateOf (acctOf c.acct).grp c.ty c.cat) ∧
  σ.initOf "Cbact04c$Account" = .done ∧ σ.initOf "Cbact04c$Result" = .done ∧
  σ.initOf "Cbact04c" = .done

/-- `run(cats, accounts, discs)` returns a `Result` holding the rewrites of `jRun` (an
`ArrayList` of new account objects, in order) and its transaction count. -/
def runSpec : Spec := Spec.of
  (fun args σ => ∃ ca aa da acctOf rateOf cs, args = [.ref ca, .ref aa, .ref da] ∧
     RunPre σ ca aa da acctOf rateOf cs)
  (fun args σ r σ' => ∀ ca aa da acctOf rateOf cs, args = [.ref ca, .ref aa, .ref da] →
     RunPre σ ca aa da acctOf rateOf cs →
     ∃ res fs l k xs mods, r = some (.ref res) ∧ σ'.heap res = some (.plain "Cbact04c$Result" fs) ∧
       Fields.get fs ("Cbact04c$Result", "rewrites") = some (.ref l) ∧
       Fields.get fs ("Cbact04c$Result", "transactions") = some (.int (jRun acctOf rateOf cs).tx) ∧
       σ'.heap l = some (.list k xs mods) ∧ Pairs (AcctAt σ') xs (jRun acctOf rateOf cs).rewrites)

end EquivLean.Demo.Cbact04c
