import Cobol
import EquivLean.Bridge.Cobol.Behaves
import EquivLean.Bridge.Cobol.Corr
import EquivLean.Bridge.Jimple.Behaves
import EquivLean.Bridge.Jimple.Corr
import EquivLean.Demo.Jimple.AcctIntJava

/-!
# COBOL → Java migration: ACCTINT ≡ `AcctInt.accrue` (javac + Soot + JimpleLean)

* **Source**: the COBOL program `ACCTINT` (`examples/cobol/acctint/ACCTINT.cob` + `ACCTREC.cpy`),
  loaded by coblean's `cobol_program` from its surface IR (the same JSON as eq-cobol's demos,
  under a different program name).  Its meaning is `EquivLean.Cobol.run AcctIntCobJ {} 20 …`
  (`Bridge/Cobol/Behaves.lean`: deterministic, total).
* **Target**: `AcctInt.accrue(char, BigDecimal, BigDecimal, int)` of
  `examples/java/acctint/AcctInt.java` (a rewrite without records), compiled by
  `javac --release 17`, converted by Soot 4.7.1, imported by `jimple_import`; its meaning is
  JimpleLean's big-step `MExec` (`Bridge/Jimple/Behaves.lean`: partial correctness).
* **Outcome relation** `AcctRelJ`: the Java method returns normally an `AcctInt$Result` whose
  `balance` and `interest` fields are `BigDecimal`s with the values (`Corr BigDec Decimal`) of the
  decimals held by the COBOL fields `ACCT-BALANCE` and `WS-INTEREST` (`fieldDec`, shared
  `Decimal` model), and whose `status` character is the CP037 code of the `WS-STATUS` byte; the
  COBOL run ends with `GOBACK`.

Main results: `acctint_java_sim` (valid balance) and `acctint_java_sim_lowvalues` (the balance
field holds LOW-VALUES and Java receives `null`):
`Sim AcctRelJ (Java call) (COBOL run)`: on every terminating execution, the Java method returns
what the COBOL program stores (partial correctness on the Java side).

Proof chain (each step a theorem of this file or of its imports):
1. Java (real Jimple) satisfies a `BigDecimal` reference `accrueD`: `AcctIntJava.accrue_sat`,
   `accrue_null_sat` (JimpleLean's VC generator, `jvc`).
2. `accrueD` on the record's decimals = coblean's transcription of the Java code over its own
   `BigDecimal` model (`link`): the only arithmetic is `Cobol.units` (JimpleLean's rounding) =
   `Cobol.divRound .nearestAwayFromZero` (coblean's), through the shared `Decimal.roundRat`
   (`EquivLean.Jimple.units_eq_divRound`).
3. COBOL program = coblean's transcription (`acctint_cob`, coblean's own proof of
   `Examples/AcctInt.lean`, re-run here on the copied program: `cobol_equiv`, `cobol_sym`).
-/

open Cobol

cobol_program AcctIntCobJ from "../../../examples/cobol/acctint/acctint.ir.json"

namespace EquivLean.Demo.AcctIntMigration

open EquivLean.Jimple EquivLean.Demo.AcctIntJava
open EquivLean.Cobol (fieldDec)

/-! ## Step 3: ACCTINT ≡ coblean's transcription of the Java code (coblean `Examples/AcctInt.lean`) -/

namespace CobJava
open Java

structure Result where
  balance : BigDecimal
  interest : BigDecimal
  status : Char

def ZERO2 : BigDecimal := BigDecimal.valueOf 0 2

/-- `AcctInt.accrue` over coblean's `BigDecimal` model (`balance = none`: LOW-VALUES). -/
def accrue (type : Char) (balance : Option BigDecimal) (rate : BigDecimal) (days : Int32) :
    Except ArithmeticException Result :=
  let bal := balance.getD ZERO2
  if days = 0 ∨ (type ≠ 'S' ∧ type ≠ 'C') then .ok ⟨bal, ZERO2, 'Z'⟩ else
  match rate.divide (BigDecimal.valueOf 365) 8 Java.RoundingMode.HALF_UP with
  | .error e => .error e
  | .ok daily =>
    match ((bal.multiply daily).multiply (BigDecimal.valueOf days.toInt)).setScale 2
        Java.RoundingMode.HALF_UP with
    | .error e => .error e
    | .ok interest =>
      if interest.abs.compareTo (BigDecimal.valueOf 1000000000) ≥ 0 then .ok ⟨bal, ZERO2, 'E'⟩
      else
        let newBal := bal.add interest
        if newBal.abs.compareTo (BigDecimal.valueOf 100000000000) ≥ 0 then
          .ok ⟨bal, interest, 'E'⟩
        else .ok ⟨newBal, interest, 'K'⟩

end CobJava

open AcctIntCobJ in
/-- What the COBOL run produces: new balance, interest (both scale 2) and status byte. -/
def cobolObs (r : Sem.Res) : Option (Int × Int × List UInt8) :=
  if r.1 = .stop .goback then
    match decodeNum {} ACCT_BALANCE.fmt (r.2.mem.field ACCT_BALANCE),
          decodeNum {} WS_INTEREST.fmt (r.2.mem.field WS_INTEREST) with
    | some b, some i => some (b, i, r.2.mem.field WS_STATUS)
    | _, _ => none
  else none

/-- The same observation of the transcription's result. -/
def javaObs : Except Java.ArithmeticException CobJava.Result → Option (Int × Int × List UInt8)
  | .ok res => (Codepage.cp037Byte res.status).map fun b =>
      (res.balance.valueAt 2, res.interest.valueAt 2, [b])
  | .error _ => none

/-- COBOL's two roundings of the daily rate equal Java's one (coblean). -/
theorem daily_rate_eq (rate : Int) :
    divRound .nearestAwayFromZero (divRound .truncation (rate * 10000) 365) 10 =
      divRound .nearestAwayFromZero (rate * 1000) 365 := by
  cobol_arith

open AcctIntCobJ in
theorem acctint_cob (m : Mem) (hm : m.size = 33) (ty : UInt8) (bal rate : Int) (days : Int32)
    (hty : m.field ACCT_TYPE = [ty])
    (hbal : decodeNum {} ACCT_BALANCE.fmt (m.field ACCT_BALANCE) = some bal)
    (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate)
    (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some days.toInt) :
    cobolObs (AcctIntCobJ.run {} 20 (AcctIntCobJ.initState m)) =
      javaObs (CobJava.accrue (Codepage.cp037Char ty) (some (.valueOf bal 2))
        (.valueOf rate 5) days) := by
  cobol_ranges
  have hz : ¬ m.field ACCT_BAL_RAW = [0, 0, 0, 0, 0, 0, 0] := by
    intro h; cobol_sym [h] at hbal
  have := daily_rate_eq rate
  cobol_equiv [cobolObs, javaObs, hm, hty, hbal, hrate, hdays, hz,
    CobJava.accrue, CobJava.ZERO2]

open AcctIntCobJ in
theorem acctint_cob_lowvalues (m : Mem) (hm : m.size = 33) (ty : UInt8) (rate : Int)
    (days : Int32)
    (hty : m.field ACCT_TYPE = [ty])
    (hraw : m.field ACCT_BAL_RAW = [0, 0, 0, 0, 0, 0, 0])
    (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate)
    (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some days.toInt) :
    cobolObs (AcctIntCobJ.run {} 20 (AcctIntCobJ.initState m)) =
      javaObs (CobJava.accrue (Codepage.cp037Char ty) none (.valueOf rate 5) days) := by
  cobol_ranges
  have := daily_rate_eq rate
  cobol_equiv [cobolObs, javaObs, hm, hty, hraw, hrate, hdays, CobJava.accrue,
    CobJava.ZERO2]

/-! ## Step 2: JimpleLean's `BigDecimal` reference = coblean's transcription -/

/-- The Java `char` argument of a character. -/
def charBits (c : Char) : Jimple.I32 := BitVec.ofNat 32 c.toNat

/-- Observation of the reference result (balance and interest at scale 2, status byte). -/
def jObs (q : Jimple.BigDec × Jimple.BigDec × Int) : Option (Int × Int × List UInt8) :=
  (Codepage.cp037Byte (Char.ofNat q.2.2.toNat)).map fun b => (q.1.unscaled, q.2.1.unscaled, [b])

theorem E1 (rate : Int) :
    (⟨rate, 5⟩ : Jimple.BigDec).toRat / (⟨365, 0⟩ : Jimple.BigDec).toRat * Jimple.pow10 8 =
      ((rate * 1000 : Int) : Rat) / ((365 : Int) : Rat) := by
  simp only [Jimple.BigDec.toRat_mk, Jimple.pow10_neg_ofNat, Jimple.pow10_ofNat]
  push_cast
  grind
theorem E2 (bal q d : Int) :
    (((⟨bal, 2⟩ : Jimple.BigDec).mul ⟨q, 8⟩).mul ⟨d, 0⟩).toRat * Jimple.pow10 2 =
      ((bal * q * d : Int) : Rat) / ((100000000 : Int) : Rat) := by
  simp only [Jimple.BigDec.toRat_mul, Jimple.BigDec.toRat_mk, Jimple.pow10_neg_ofNat, Jimple.pow10_ofNat]
  push_cast
  grind
theorem dailyOf_eq (rate : Int) :
    dailyOf ⟨rate, 5⟩ = ⟨Cobol.Sem.quot .nearestAwayFromZero rate 5 365 0 8, 8⟩ := by
  simp only [dailyOf]
  rw [units_eq_divRound (by decide) (E1 rate), ← EquivLean.Cobol.divRound_toCobol]
  simp [Cobol.Sem.quot, Cobol.divRoundZ, EquivLean.Cobol.toCobol]
theorem interestOf_eq (bal rate : Int) (d : Jimple.I32) :
    interestOf ⟨bal, 2⟩ ⟨rate, 5⟩ d =
      ⟨Cobol.rescale .nearestAwayFromZero (bal * Cobol.Sem.quot .nearestAwayFromZero rate 5 365 0 8 * d.toInt) 10 2, 2⟩ := by
  simp only [interestOf, dailyOf_eq]
  rw [units_eq_divRound (by decide) (E2 _ _ _), ← EquivLean.Cobol.divRound_toCobol]
  simp [Cobol.rescale, EquivLean.Cobol.toCobol]

theorem charBits_eq_iff (c d : Char) : charBits c = charBits d ↔ c = d := by
  constructor
  · intro h
    have hc : c.toNat < 2 ^ 32 := by rw [← Char.toNat_val]; exact UInt32.toNat_lt c.val
    have hd : d.toNat < 2 ^ 32 := by rw [← Char.toNat_val]; exact UInt32.toNat_lt d.val
    have := congrArg BitVec.toNat h
    simp only [charBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at this
    exact Char.toNat_inj.mp this
  · rintro rfl; rfl

theorem cmp_cob (u N : Int) :
    (0 ≤ (Java.BigDecimal.abs ⟨u, 2⟩).compareTo ⟨N, 0⟩) ↔ N * 100 ≤ u.natAbs := by
  simp [Java.BigDecimal.abs, Java.BigDecimal.compareTo, Cobol.Sem.align, Int.max_def]
  split <;> (try split) <;> omega
theorem cmp_jim (u N : Int) :
    (0 ≤ (absJ ⟨u, 2⟩).compareTo ⟨N, 0⟩) ↔ N * 100 ≤ u.natAbs := by
  by_cases hu : u < 0
  · simp [absJ, hu, Jimple.BigDec.negate, Jimple.BigDec.compareTo, Jimple.BigDec.upscale,
      Jimple.pow10Int, Int.max_def]
    split <;> (try split) <;> omega
  · simp [absJ, hu, Jimple.BigDec.compareTo, Jimple.BigDec.upscale, Jimple.pow10Int, Int.max_def]
    split <;> (try split) <;> omega
theorem add_cob (b u : Int) : Java.BigDecimal.add ⟨b, 2⟩ ⟨u, 2⟩ = ⟨b + u, 2⟩ := by
  simp [Java.BigDecimal.add, Cobol.Sem.align]
theorem add_jim (b u : Int) : Jimple.BigDec.add ⟨b, 2⟩ ⟨u, 2⟩ = ⟨b + u, 2⟩ := by
  simp [Jimple.BigDec.add, Jimple.BigDec.upscale, Jimple.pow10Int]
theorem days_zero_iff (days : Int32) : days.toBitVec = 0#32 ↔ days = 0 := by
  constructor
  · intro h; exact Int32.toBitVec_inj.mp h
  · intro h; subst h; rfl
theorem charBits_S (c : Char) : charBits c = 83#32 ↔ c = 'S' := charBits_eq_iff c 'S'
theorem charBits_C (c : Char) : charBits c = 67#32 ↔ c = 'C' := charBits_eq_iff c 'C'
theorem valueAt_2 (v : Int) : Java.BigDecimal.valueAt ⟨v, 2⟩ 2 = v := by
  simp [Java.BigDecimal.valueAt, Cobol.rescale]

theorem link (c : Char) (bal rate : Int) (days : Int32) :
    javaObs (CobJava.accrue c (some (.valueOf bal 2)) (.valueOf rate 5) days) =
      jObs (accrueD (charBits c) ⟨bal, 2⟩ ⟨rate, 5⟩ days.toBitVec) := by
  simp only [javaObs, CobJava.accrue, jObs, accrueD, CobJava.ZERO2, Option.getD_some,
    interestOf_eq, charBits_S, charBits_C, days_zero_iff, ne_eq, add_jim,
    cmp_jim]
  simp [Java.BigDecimal.divide, Java.BigDecimal.setScale, Java.BigDecimal.valueOf,
    Java.BigDecimal.multiply, add_cob, add_jim, cmp_cob, cmp_jim, valueAt_2]
  have hz : (days = { toUInt32 := 0 }) ↔ days.toBitVec = 0#32 := (days_zero_iff days).symm
  have hm : Java.RoundingMode.HALF_UP = Cobol.RoundingMode.nearestAwayFromZero := rfl
  have hi : days.toInt = days.toBitVec.toInt := rfl
  simp only [hz, hm, hi]
  generalize Cobol.rescale Cobol.RoundingMode.nearestAwayFromZero
    (bal * Cobol.Sem.quot Cobol.RoundingMode.nearestAwayFromZero rate 5 365 0 8 * days.toBitVec.toInt) 10 2 = U
  by_cases h1 : days.toBitVec = 0#32 ∨ ¬c = 'S' ∧ ¬c = 'C' <;>
    by_cases h2 : (100000000000 : Int) ≤ ↑U.natAbs <;>
    by_cases h3 : (10000000000000 : Int) ≤ ↑(bal + U).natAbs <;>
    simp [h1, h2, h3, valueAt_2] <;> decide

theorem link_none (c : Char) (rate : Int) (days : Int32) :
    javaObs (CobJava.accrue c none (.valueOf rate 5) days) =
      jObs (accrueD (charBits c) ⟨0, 2⟩ ⟨rate, 5⟩ days.toBitVec) :=
  link c 0 rate days

/-- The reference's balance and interest have scale 2. -/
theorem accrueD_scales (c : Char) (bal rate : Int) (days : Int32) :
    (accrueD (charBits c) ⟨bal, 2⟩ ⟨rate, 5⟩ days.toBitVec).1.scale = 2 ∧
      (accrueD (charBits c) ⟨bal, 2⟩ ⟨rate, 5⟩ days.toBitVec).2.1.scale = 2 := by
  simp only [accrueD, interestOf_eq, add_jim]
  constructor <;> split <;> (try split) <;> (try split) <;> rfl

/-! ## The outcome relation and the migration theorems -/

open AcctIntCobJ in
/-- The Java call returns an `AcctInt$Result` whose decimals have the values of the COBOL
fields `ACCT-BALANCE`, `WS-INTEREST` (shared `Decimal` model) and whose status is the CP037
code of `WS-STATUS`; COBOL ends with `GOBACK`. -/
def AcctRelJ : Out → Signal × State → Prop
  | .normal v σ', os =>
      os.1 = .stop .goback ∧
      ∃ c fs b i s B I, v = some (.ref c) ∧ σ'.heap c = some (.plain "AcctInt$Result" fs) ∧
        Jimple.Fields.get fs ("AcctInt$Result", "balance") = some (.ref b) ∧
        σ'.heap b = some (.dec B) ∧
        Jimple.Fields.get fs ("AcctInt$Result", "interest") = some (.ref i) ∧
        σ'.heap i = some (.dec I) ∧
        Jimple.Fields.get fs ("AcctInt$Result", "status") = some (.int s) ∧
        (∃ d, fieldDec {} ACCT_BALANCE.fmt (os.2.mem.field ACCT_BALANCE) = some d ∧ Corr.corr B d) ∧
        (∃ d, fieldDec {} WS_INTEREST.fmt (os.2.mem.field WS_INTEREST) = some d ∧ Corr.corr I d) ∧
        (Codepage.cp037Byte (Char.ofNat s.toInt.toNat)).map (fun x => [x]) =
          some (os.2.mem.field WS_STATUS)
  | .exc _ _, _ => False

open AcctIntCobJ in
/-- From the Java postcondition and the COBOL observation of the same reference result. -/
theorem rel_of_obs {v : Option Jimple.Value} {σ' : Jimple.State} {r : Sem.Res}
    {q : Jimple.BigDec × Jimple.BigDec × Int} (hq1 : q.1.scale = 2) (hq2 : q.2.1.scale = 2)
    (hres : ResultIs σ' v q) (hobs : cobolObs r = jObs q) (hsome : (jObs q).isSome = true) :
    AcctRelJ (.normal v σ') r := by
  obtain ⟨sig, st⟩ := r
  obtain ⟨c, fs, b, i, s, B, I, hv, hc, hb, hB, hi, hI, hs, hBq, hIq, hsq⟩ := hres
  cases hx : Codepage.cp037Byte (Char.ofNat q.2.2.toNat) with
  | none => simp [jObs, hx] at hsome
  | some x =>
    simp only [jObs, hx, Option.map_some] at hobs
    unfold cobolObs at hobs
    by_cases hsig : sig = .stop .goback
    · simp only [hsig, if_true] at hobs
      split at hobs
      · next bv iv hbv hiv =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hobs
        obtain ⟨h1, h2, h3⟩ := hobs
        refine ⟨hsig, c, fs, b, i, s, B, I, hv, hc, hb, hB, hi, hI, hs, ?_, ?_, ?_⟩
        · refine ⟨_, EquivLean.Cobol.fieldDec_of_decode hbv, ?_⟩
          show B.toRat = Decimal.val _
          rw [hBq, ← val_ofBigDec, h1]
          simp only [ofBigDec, hq1]
        · refine ⟨_, EquivLean.Cobol.fieldDec_of_decode hiv, ?_⟩
          show I.toRat = Decimal.val _
          rw [hIq, ← val_ofBigDec, h2]
          simp only [ofBigDec, hq2]
        · rw [← hsq] at hx
          simp [hx, h3]
      · simp at hobs
    · simp [hsig] at hobs

/-- A defined observation means the run ended with `GOBACK`: a safe COBOL outcome. -/
theorem ok_of_obs {r : Sem.Res} (h : (cobolObs r).isSome = true) : EquivLean.Cobol.Ok r := by
  obtain ⟨sig, st⟩ := r
  unfold cobolObs at h
  by_cases hsig : sig = .stop .goback
  · subst hsig; rfl
  · simp [hsig] at h

theorem accrueD_status (t : Jimple.I32) (D R : Jimple.BigDec) (d : Jimple.I32) :
    (accrueD t D R d).2.2 = 90 ∨ (accrueD t D R d).2.2 = 69 ∨ (accrueD t D R d).2.2 = 75 := by
  unfold accrueD
  split
  · simp
  · split
    · simp
    · split <;> simp

theorem jObs_isSome (c : Char) (bal rate : Int) (days : Int32) :
    (jObs (accrueD (charBits c) ⟨bal, 2⟩ ⟨rate, 5⟩ days.toBitVec)).isSome = true := by
  rcases accrueD_status (charBits c) ⟨bal, 2⟩ ⟨rate, 5⟩ days.toBitVec with h | h | h <;>
    simp only [jObs, Option.isSome_map, h] <;> decide

open AcctIntCobJ in
/-- **ACCTINT ⊑ AcctInt.accrue (Java, javac + Soot).**  For every storage whose account
record holds a type byte and a valid balance, rate and day count, and every JVM state in which
the arguments are the `BigDecimal`s `bal × 10⁻²` and `rate × 10⁻⁵` (as the record's COMP-3
fields hold them), every terminating execution of the Java method returns what the COBOL
program stores (`AcctRelJ`), and the method cannot go wrong.  Partial correctness: JimpleLean's
big-step semantics does not see divergence. -/
theorem acctint_java_sim (m : Mem) (hm : m.size = 33) (ty : UInt8) (bal rate : Int)
    (days : Int32)
    (hty : m.field ACCT_TYPE = [ty])
    (hbal : decodeNum {} ACCT_BALANCE.fmt (m.field ACCT_BALANCE) = some bal)
    (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate)
    (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some days.toInt)
    (σ : Jimple.State) (a r : Jimple.Addr)
    (ha : σ.heap a = some (.dec ⟨bal, 2⟩)) (hr : σ.heap r = some (.dec ⟨rate, 5⟩))
    (hinit : σ.initOf "AcctInt$Result" = .done) :
    Sim AcctRelJ
      (Call.mk EquivLean.Gen.AcctIntJ.prog accrueRef
        [.int (charBits (Codepage.cp037Char ty)), .ref a, .ref r, .int days.toBitVec] σ)
      (EquivLean.Cobol.run AcctIntCobJ {} 20 (AcctIntCobJ.initState m)) := by
  have hobs := (acctint_cob m hm ty bal rate days hty hbal hrate hdays).trans
    (link (Codepage.cp037Char ty) bal rate days)
  have hsome := jObs_isSome (Codepage.cp037Char ty) bal rate days
  have hsc := accrueD_scales (Codepage.cp037Char ty) bal rate days
  -- the COBOL run ends with GOBACK: a safe outcome
  have hok : EquivLean.Cobol.Ok (AcctIntCobJ.run {} 20 (AcctIntCobJ.initState m)) :=
    ok_of_obs (hobs ▸ hsome)
  rw [EquivLean.Cobol.run]
  refine sim_of_sat ((EquivLean.Cobol.safe_exec_iff _).2 hok)
    ((EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩) accrue_sat ⟨_, a, r, _, _, _, rfl, ha, hr, hinit⟩ ?_
  intro o ho
  cases o with
  | normal v σ' =>
    exact rel_of_obs hsc.1 hsc.2 (ho _ a r _ _ _ rfl ha hr) hobs hsome
  | exc e σ' => exact ho.elim
  | wrong msg => exact ho.elim

open AcctIntCobJ in
/-- **ACCTINT ⊑ AcctInt.accrue**, LOW-VALUES balance: the COBOL program zeroes the balance
field, the Java method receives `null`. -/
theorem acctint_java_sim_lowvalues (m : Mem) (hm : m.size = 33) (ty : UInt8) (rate : Int)
    (days : Int32)
    (hty : m.field ACCT_TYPE = [ty])
    (hraw : m.field ACCT_BAL_RAW = [0, 0, 0, 0, 0, 0, 0])
    (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate)
    (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some days.toInt)
    (σ : Jimple.State) (r : Jimple.Addr) (hr : σ.heap r = some (.dec ⟨rate, 5⟩))
    (hinit : σ.initOf "AcctInt$Result" = .done) :
    Sim AcctRelJ
      (Call.mk EquivLean.Gen.AcctIntJ.prog accrueRef
        [.int (charBits (Codepage.cp037Char ty)), .null, .ref r, .int days.toBitVec] σ)
      (EquivLean.Cobol.run AcctIntCobJ {} 20 (AcctIntCobJ.initState m)) := by
  have hobs := (acctint_cob_lowvalues m hm ty rate days hty hraw hrate hdays).trans
    (link_none (Codepage.cp037Char ty) rate days)
  have hsome := jObs_isSome (Codepage.cp037Char ty) 0 rate days
  have hsc := accrueD_scales (Codepage.cp037Char ty) 0 rate days
  have hok : EquivLean.Cobol.Ok (AcctIntCobJ.run {} 20 (AcctIntCobJ.initState m)) :=
    ok_of_obs (hobs ▸ hsome)
  rw [EquivLean.Cobol.run]
  refine sim_of_sat ((EquivLean.Cobol.safe_exec_iff _).2 hok)
    ((EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩) accrue_null_sat ⟨_, r, _, _, rfl, hr, hinit⟩ ?_
  intro o ho
  cases o with
  | normal v σ' =>
    exact rel_of_obs hsc.1 hsc.2 (ho _ r _ _ rfl hr) hobs hsome
  | exc e σ' => exact ho.elim
  | wrong msg => exact ho.elim

end EquivLean.Demo.AcctIntMigration

#print axioms EquivLean.Demo.AcctIntMigration.acctint_cob
#print axioms EquivLean.Demo.AcctIntMigration.link
#print axioms EquivLean.Demo.AcctIntMigration.acctint_java_sim
#print axioms EquivLean.Demo.AcctIntMigration.acctint_java_sim_lowvalues
