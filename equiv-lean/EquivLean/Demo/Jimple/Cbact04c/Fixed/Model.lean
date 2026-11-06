import EquivLean.Demo.Jimple.Cbact04c.Model
import EquivLean.Demo.Gen.Jimple.Cbact04cFixed

/-!
# CBACT04C in Java, the fixed port: contracts

`examples/java/cbact04c_fixed/Cbact04cFixed.java` (javac + Soot, imported as `EquivLean.Demo.Cbact04c.GenF`) is
`Cbact04c` renamed, with the last account posted after the main loop (CardDemo issue #64).
Its classes are `Cbact04cFixed`, `Cbact04cFixed$Cat`, … instead of `Cbact04c`, `Cbact04c$Cat`, …,
so the representation predicates of `Cbact04c/Model.lean` are stated here for any class name (`CatAtC`,
`AcctAtC`, `DiscAtC`, `idOfC`; those of `Cbact04c/Model.lean` are their instances, `catAt_eq` …), and the
contracts of `Cbact04c/Model.lean` are restated for the new classes (`readAccountSpecF`, `readRateSpecF`,
`postSpecF`, `RunPreF`). `runFixSpec`: `run` returns the rewrites `jRunFix` (those of `jRun` and
the last account posted) and the transaction count of `jRun`.
-/

open Jimple

namespace EquivLean.Demo.Cbact04c

/-! ## Representation predicates for any class names -/

/-- `CatAt` for the record class `C`. -/
def CatAtC (C : ClassName) (σ : State) (v : Value) (c : JCat) : Prop :=
  ∃ x fs t, v = .ref x ∧ σ.heap x = some (.plain C fs) ∧
    Fields.get fs (C, "acctId") = some (.long c.acct) ∧
    Fields.get fs (C, "typeCd") = some t ∧ StrAt σ t c.ty ∧
    Fields.get fs (C, "catCd") = some (.int c.cat) ∧
    Fields.get fs (C, "bal") = some (.long c.bal)

/-- `AcctAt` for the record class `A`. -/
def AcctAtC (A : ClassName) (σ : State) (v : Value) (a : JAcct) : Prop :=
  ∃ x fs g, v = .ref x ∧ σ.heap x = some (.plain A fs) ∧
    Fields.get fs (A, "id") = some (.long a.id) ∧
    Fields.get fs (A, "bal") = some (.long a.bal) ∧
    Fields.get fs (A, "cycCredit") = some (.long a.cc) ∧
    Fields.get fs (A, "cycDebit") = some (.long a.cd) ∧
    Fields.get fs (A, "groupId") = some g ∧ StrAt σ g a.grp

/-- `DiscAt` for the record class `D`. -/
def DiscAtC (D : ClassName) (σ : State) (v : Value) (d : JDisc) : Prop :=
  ∃ x fs g t, v = .ref x ∧ σ.heap x = some (.plain D fs) ∧
    Fields.get fs (D, "groupId") = some g ∧ StrAt σ g d.grp ∧
    Fields.get fs (D, "typeCd") = some t ∧ StrAt σ t d.ty ∧
    Fields.get fs (D, "catCd") = some (.int d.cat) ∧
    Fields.get fs (D, "rate") = some (.long d.rate)

/-- `idOf` for the record class `A`. -/
def idOfC (A : ClassName) (σ : State) (v : Value) : Option I64 :=
  match v with
  | .ref a =>
    match σ.heap a with
    | some (.plain c fs) =>
      if c = A then
        match Fields.get fs (A, "id") with
        | some (.long i) => some i
        | _ => none
      else none
    | _ => none
  | _ => none

theorem catAt_eq : CatAt = CatAtC "Cbact04c$Cat" := rfl
theorem acctAt_eq : AcctAt = AcctAtC "Cbact04c$Account" := rfl
theorem discAt_eq : DiscAt = DiscAtC "Cbact04c$Disc" := rfl

/-! ## The fixed port -/

/-- The rewrites of the fixed port: those of `jRun`, then the current account posted (if any
record was read). -/
def jRunFix (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64) (cs : List JCat) :
    List JAcct :=
  let s := jRun acctOf rateOf cs
  if s.first then s.rewrites else s.rewrites ++ [jPost s.acct s.total]

/-- `readAccountSpec` for `Cbact04cFixed`. -/
def readAccountSpecF : Spec := Spec.of
  (fun args σ => ∃ aa id et xs a, args = [.ref aa, .long id] ∧ σ.heap aa = some (.array et xs) ∧
     xs.length < 2147483647 ∧ (∀ x ∈ xs, ∃ b, AcctAtC "Cbact04cFixed$Account" σ x b) ∧
     (∃ x ∈ xs, AcctAtC "Cbact04cFixed$Account" σ x a) ∧ a.id = id ∧
     ∀ x ∈ xs, idOfC "Cbact04cFixed$Account" σ x = some id → AcctAtC "Cbact04cFixed$Account" σ x a)
  (fun args σ r σ' => ∀ aa id et xs a, args = [.ref aa, .long id] → σ.heap aa = some (.array et xs) →
     (∃ x ∈ xs, AcctAtC "Cbact04cFixed$Account" σ x a) → a.id = id →
     (∀ x ∈ xs, idOfC "Cbact04cFixed$Account" σ x = some id → AcctAtC "Cbact04cFixed$Account" σ x a) →
     ∃ v, r = some v ∧ AcctAtC "Cbact04cFixed$Account" σ v a ∧ σ' = σ)

/-- `readRateSpec` for `Cbact04cFixed`. -/
def readRateSpecF : Spec := Spec.of
  (fun args σ => ∃ da g t gs ts cat rate et xs, args = [.ref da, .ref gs, .ref ts, .int cat] ∧
     σ.heap gs = some (.str g) ∧ σ.heap ts = some (.str t) ∧
     σ.heap da = some (.array et xs) ∧ xs.length < 2147483647 ∧
     (∀ x ∈ xs, ∃ d, DiscAtC "Cbact04cFixed$Disc" σ x d) ∧
     (∃ x ∈ xs, DiscAtC "Cbact04cFixed$Disc" σ x ⟨g, t, cat, rate⟩) ∧
     ∀ x ∈ xs, ∀ d, DiscAtC "Cbact04cFixed$Disc" σ x d → d.grp = g → d.ty = t → d.cat = cat →
       d.rate = rate)
  (fun args σ r σ' => ∀ da g t gs ts cat rate et xs, args = [.ref da, .ref gs, .ref ts, .int cat] →
     σ.heap gs = some (.str g) → σ.heap ts = some (.str t) → σ.heap da = some (.array et xs) →
     (∃ x ∈ xs, DiscAtC "Cbact04cFixed$Disc" σ x ⟨g, t, cat, rate⟩) →
     (∀ x ∈ xs, ∀ d, DiscAtC "Cbact04cFixed$Disc" σ x d → d.grp = g → d.ty = t → d.cat = cat →
       d.rate = rate) →
     r = some (.long rate) ∧ σ' = σ)

/-- `postSpec` for `Cbact04cFixed`. -/
def postSpecF : Spec := Spec.of
  (fun args σ => ∃ v t a, args = [v, .long t] ∧ AcctAtC "Cbact04cFixed$Account" σ v a ∧
     σ.initOf "Cbact04cFixed$Account" = .done)
  (fun args σ r σ' => ∀ v t a, args = [v, .long t] → AcctAtC "Cbact04cFixed$Account" σ v a →
     ∃ w, r = some w ∧ AcctAtC "Cbact04cFixed$Account" σ' w (jPost a t) ∧ Grows σ σ' ∧
       σ'.initOf "Cbact04cFixed$Account" = .done ∧
       σ'.initOf "Cbact04cFixed$Result" = σ.initOf "Cbact04cFixed$Result" ∧
       σ'.initOf "Cbact04cFixed" = σ.initOf "Cbact04cFixed")

/-- `RunPre` for `Cbact04cFixed`. -/
def RunPreF (σ : State) (ca aa da : Addr) (acctOf : I64 → JAcct)
    (rateOf : JStr → JStr → I32 → I64) (cs : List JCat) : Prop :=
  (∃ et xs, σ.heap ca = some (.array et xs) ∧ Pairs (CatAtC "Cbact04cFixed$Cat" σ) xs cs) ∧
  cs.length < 2147483647 ∧
  (∃ et xs, σ.heap aa = some (.array et xs) ∧ xs.length < 2147483647 ∧
    (∀ x ∈ xs, ∃ b, AcctAtC "Cbact04cFixed$Account" σ x b) ∧
    ∀ c ∈ cs, (acctOf c.acct).id = c.acct ∧
      (∃ x ∈ xs, AcctAtC "Cbact04cFixed$Account" σ x (acctOf c.acct)) ∧
      ∀ x ∈ xs, idOfC "Cbact04cFixed$Account" σ x = some c.acct →
        AcctAtC "Cbact04cFixed$Account" σ x (acctOf c.acct)) ∧
  (∃ et xs, σ.heap da = some (.array et xs) ∧ xs.length < 2147483647 ∧
    (∀ x ∈ xs, ∃ d, DiscAtC "Cbact04cFixed$Disc" σ x d) ∧
    ∀ c ∈ cs,
      (∃ x ∈ xs, DiscAtC "Cbact04cFixed$Disc" σ x
        ⟨(acctOf c.acct).grp, c.ty, c.cat, rateOf (acctOf c.acct).grp c.ty c.cat⟩) ∧
      ∀ x ∈ xs, ∀ d, DiscAtC "Cbact04cFixed$Disc" σ x d → d.grp = (acctOf c.acct).grp →
        d.ty = c.ty → d.cat = c.cat → d.rate = rateOf (acctOf c.acct).grp c.ty c.cat) ∧
  σ.initOf "Cbact04cFixed$Account" = .done ∧ σ.initOf "Cbact04cFixed$Result" = .done ∧
  σ.initOf "Cbact04cFixed" = .done

/-- `run(cats, accounts, discs)` of the fixed port returns a `Result` holding the rewrites
`jRunFix` (an `ArrayList` of new account objects, in order) and the transaction count of
`jRun`. -/
def runFixSpec : Spec := Spec.of
  (fun args σ => ∃ ca aa da acctOf rateOf cs, args = [.ref ca, .ref aa, .ref da] ∧
     RunPreF σ ca aa da acctOf rateOf cs)
  (fun args σ r σ' => ∀ ca aa da acctOf rateOf cs, args = [.ref ca, .ref aa, .ref da] →
     RunPreF σ ca aa da acctOf rateOf cs →
     ∃ res fs l k xs mods, r = some (.ref res) ∧
       σ'.heap res = some (.plain "Cbact04cFixed$Result" fs) ∧
       Fields.get fs ("Cbact04cFixed$Result", "rewrites") = some (.ref l) ∧
       Fields.get fs ("Cbact04cFixed$Result", "transactions") =
         some (.int (jRun acctOf rateOf cs).tx) ∧
       σ'.heap l = some (.list k xs mods) ∧
       Pairs (AcctAtC "Cbact04cFixed$Account" σ') xs (jRunFix acctOf rateOf cs))

end EquivLean.Demo.Cbact04c
