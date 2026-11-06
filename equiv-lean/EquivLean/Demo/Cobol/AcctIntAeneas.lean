import Cobol
import EquivLean.Bridge.Cobol.Behaves
import EquivLean.Bridge.Cobol.Corr
import EquivLean.Bridge.Cobol.Tactic
import EquivLean.Bridge.Aeneas.Behaves
import EquivLean.Demo.Gen.Aeneas.AcctInt.Funs

/-!
# COBOL → Rust migration: ACCTINT ≡ the Aeneas translation of `acctint.rs`

* **Source**: `examples/cobol/acctint/ACCTINT.cob` (+ `ACCTREC.cpy`), loaded from its surface
  IR `acctint.ir.json` by coblean's `cobol_program` (copied read-only from the pinned coblean
  snapshot).  Its meaning is `Cobol.run AcctIntCob {} 20 (AcctIntCob.initState m)` (bridge:
  `EquivLean.Bridge.Cobol.Behaves`).
* **Target**: `acctint::accrue`, the *real* Aeneas output for `examples/rust/acctint/src/lib.rs`
  (Charon + Aeneas fdebf20, `EquivLean/Demo/Gen/Aeneas/AcctInt/Funs.lean`): a `Result`
  computation over `Std.I64` / `Std.I128` with checked arithmetic (bridge:
  `EquivLean.Bridge.Aeneas.Behaves`, outcomes `Except Error _`, panics are outcomes).
* **Outcome relation** (`AcctRel`), through the shared decimal model: the Rust function
  returns (it does not panic) `(bal, interest, status)`; the COBOL run ends with `GOBACK`; the
  `ACCT-BALANCE` and `WS-INTEREST` fields hold the decimals `scaled 2 bal` and
  `scaled 2 interest` (Rust `i64` cents = `PIC S9(11)V99` / `PIC S9(9)V99` COMP-3); the
  status byte is the CP037 code of the Rust `char`.

Main results: `acctint_sim` (`Sim AcctRel rust cobol`), `acctint_equiv` (both directions),
`acctint_rust_no_panic` (on every valid record the Rust code returns, no panic).

Proof: coblean's symbolic executor runs the COBOL program; the same `simp` pass runs the
Aeneas code, with Aeneas' checked operations stated as rewrite rules (`tryMk_I128`, …) whose
overflow tests are decided by coblean's interval arithmetic from the input ranges
(`cobol_ranges`); the hand-written `div_half_up` folds into `Cobol.divRound` once
(`div_half_up_eq`).  The leaves are closed by `cobol_grind`, with the one arithmetic identity
of the migration (`daily_rate_eq`: COBOL's truncated intermediate quotient then `ROUNDED`
equals Rust's single half-up division).
-/

open Cobol
open Aeneas Aeneas.Std Result

cobol_program AcctIntCob from "../../../examples/cobol/acctint/acctint.ir.json"

namespace EquivLean.Demo.AcctIntAeneas

open EquivLean.Cobol (fieldDec scaled)

/-! ## The external `i128::abs` and the helper `div_half_up`

The checked scalar operations of Aeneas are the `cobol_aeneas` rewrite rules of
`EquivLean.Bridge.Cobol.Tactic` (`tryMk_I128`, `mul_I128`, `div_I128`, casts, …). -/

/-- `i128::abs` (Rust's `#[rustc_inherit_overflow_checks]` negation, `FunsExternal.lean`) away
from `i128::MIN`. -/
theorem abs_I128 (x : I128) (h : -170141183460469231731687303715884105728 < x.val) :
    core.num.I128.abs x = ok (IScalar.ofIntCore (x.val.natAbs : Int) (by
      have := x.hBounds; simp only [IScalarTy.numBits] at this ⊢; omega)) := by
  have hb := x.hBounds
  simp only [IScalarTy.numBits] at hb
  unfold core.num.I128.abs
  by_cases hn : x.val < 0
  · rw [ite_eq_left hn, EquivLean.Cobol.neg_I128, EquivLean.Cobol.tryMk_I128, dite_eq_left (by omega)]
    congr 1; apply IScalar.eq_of_val_eq; simp only [IScalar.ofInt_val_eq]; omega
  · rw [ite_eq_right hn]
    congr 1; apply IScalar.eq_of_val_eq; simp only [IScalar.ofInt_val_eq]; omega

theorem halfUp_bounds {n d : Int} (hd : 0 < d) (hd' : d ≤ 1000000000000000000)
    (hn1 : -1000000000000000000000000000000 ≤ n) (hn2 : n ≤ 1000000000000000000000000000000) :
    -2 ^ (IScalarTy.I128.numBits - 1) ≤ Cobol.divRound .nearestAwayFromZero n d ∧
      Cobol.divRound .nearestAwayFromZero n d < 2 ^ (IScalarTy.I128.numBits - 1) := by
  rw [EquivLean.Cobol.i128_bounds_iff]
  simp only [Cobol.divRound]
  split
  · have h1 := Int.ediv_le_self (2 * d) (show 0 ≤ 2 * n + d by omega)
    have h2 := Int.ediv_nonneg (show 0 ≤ 2 * n + d by omega) (show 0 ≤ 2 * d by omega)
    omega
  · have h1 := Int.ediv_le_self (2 * d) (show 0 ≤ 2 * -n + d by omega)
    have h2 := Int.ediv_nonneg (show 0 ≤ 2 * -n + d by omega) (show 0 ≤ 2 * d by omega)
    omega

/-- **The Rust helper `div_half_up`, as translated by Aeneas, is half-up rounding**
(`Cobol.divRound .nearestAwayFromZero` = `Decimal.divRound .HALF_UP`, see
`EquivLean.Cobol.divRound_cobol`), and does not panic, for operands in range. -/
theorem div_half_up_eq (n d : I128) (hd : 0 < d.val) (hd' : d.val ≤ 1000000000000000000)
    (hn1 : -1000000000000000000000000000000 ≤ n.val)
    (hn2 : n.val ≤ 1000000000000000000000000000000) :
    acctint.div_half_up n d =
      ok (IScalar.ofIntCore (Cobol.divRound .nearestAwayFromZero n.val d.val)
        (halfUp_bounds hd hd' hn1 hn2)) := by
  -- range facts in the form coblean's interval arithmetic reads
  have hn : Cobol.InRange (-1000000000000000000000000000000) 1000000000000000000000000000000
      n.val := ⟨hn1, hn2⟩
  have hdr : Cobol.InRange 1 1000000000000000000 d.val := ⟨by omega, hd'⟩
  unfold acctint.div_half_up
  cobol_sym [cobol_aeneas]
  split
  · rename_i hpos
    congr 1; apply IScalar.eq_of_val_eq
    simp only [IScalar.ofInt_val_eq, Cobol.divRound, hpos, ↓reduceIte,
      show 0 ≤ 2 * n.val + d.val by omega]
  · rename_i hneg
    have he : -Cobol.divRound .truncation (2 * -n.val + d.val) (2 * d.val) =
        Cobol.divRound .nearestAwayFromZero n.val d.val := by
      simp only [Cobol.divRound, hneg, ↓reduceIte, show 0 ≤ 2 * -n.val + d.val by omega]
    have hb := (EquivLean.Cobol.i128_bounds_iff _).1 (halfUp_bounds hd hd' hn1 hn2)
    simp only [he, hb, and_self, ↓reduceDIte]

/-! ## Observations -/

open AcctIntCob in
/-- What the COBOL run produces: new balance, interest (both scale 2) and status byte
(as in coblean's `Examples/AcctInt.lean`). -/
def cobolObs (r : Sem.Res) : Option (Int × Int × List UInt8) :=
  if r.1 = .stop .goback then
    match decodeNum {} ACCT_BALANCE.fmt (r.2.mem.field ACCT_BALANCE),
          decodeNum {} WS_INTEREST.fmt (r.2.mem.field WS_INTEREST) with
    | some b, some i => some (b, i, r.2.mem.field WS_STATUS)
    | _, _ => none
  else none

/-- The same observation of a Rust outcome (a panic observes nothing). -/
def rustObs : Except Error (I64 × I64 × Char) → Option (Int × Int × List UInt8)
  | .ok (b, i, s) => (Codepage.cp037Byte s).map fun x => (b.val, i.val, [x])
  | .error _ => none

/-- COBOL computes `RATE / 365` to 9 places (IBM intermediate rule), truncating, then rounds to
the 8 places of `WS-DAILY-RATE`; Rust rounds the exact quotient once (`div_half_up`).  These
agree (coblean `Examples/AcctInt.lean`). -/
theorem daily_rate_eq (rate : Int) :
    Cobol.divRound .nearestAwayFromZero (Cobol.divRound .truncation (rate * 10000) 365) 10 =
      Cobol.divRound .nearestAwayFromZero (rate * 1000) 365 := by
  cobol_arith

/-! ## The relation between the two runs, through `Decimal` -/

open AcctIntCob in
/-- Rust returns `(bal, interest, status)`; COBOL ends with `GOBACK`, and its balance and
interest fields hold the same scale-2 decimals, its status byte the CP037 code of `status`. -/
def AcctRel : Except Error (I64 × I64 × Char) → Signal × State → Prop
  | .ok (b, i, s), (sig, st) =>
      sig = .stop .goback ∧
      fieldDec {} ACCT_BALANCE.fmt (st.mem.field ACCT_BALANCE) = some (scaled 2 b.val) ∧
      fieldDec {} WS_INTEREST.fmt (st.mem.field WS_INTEREST) = some (scaled 2 i.val) ∧
      (Codepage.cp037Byte s).map (fun x => [x]) = some (st.mem.field WS_STATUS)
  | .error _, _ => False

open AcctIntCob in
/-- Equal observations, the Rust one defined, give the relation. -/
theorem rel_of_obs {ot : Except Error (I64 × I64 × Char)} {r : Sem.Res}
    (h : rustObs ot = cobolObs r) (hs : (rustObs ot).isSome = true) : AcctRel ot r := by
  obtain ⟨sig, st⟩ := r
  cases ot with
  | error e => simp [rustObs] at hs
  | ok v =>
    obtain ⟨b, i, s⟩ := v
    cases hx : Codepage.cp037Byte s with
    | none => simp [rustObs, hx] at hs
    | some x =>
      simp only [rustObs, hx, Option.map_some] at h
      unfold cobolObs at h
      by_cases hsig : sig = .stop .goback
      · simp only [hsig, ↓reduceIte] at h
        split at h
        · rename_i bv iv hb hi
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, hst⟩ := h
          refine ⟨hsig, ?_, ?_, ?_⟩
          · rw [EquivLean.Cobol.fieldDec_of_decode hb]; rfl
          · rw [EquivLean.Cobol.fieldDec_of_decode hi]; rfl
          · rw [hx, Option.map_some, hst]
        · cases h
      · simp [hsig] at h

/-- The relation implies that the COBOL run is a safe outcome. -/
theorem ok_of_rel {ot : Except Error (I64 × I64 × Char)} {r : Sem.Res} (h : AcctRel ot r) :
    EquivLean.Cobol.Ok r := by
  obtain ⟨sig, st⟩ := r
  cases ot with
  | error e => exact h.elim
  | ok v =>
    obtain ⟨b, i, s⟩ := v
    obtain ⟨hsig, -⟩ := h
    subst hsig
    rfl

/-! ## The equivalence -/

open AcctIntCob in
/-- **One symbolic execution of both programs**: on every storage whose account record holds a
type byte and valid balance, rate and day count, the Aeneas code returns (no panic, no
divergence) the same balance, interest and status as the COBOL program. -/
theorem acctint_wp (m : Mem) (hm : m.size = 33) (ty : UInt8) (bal rate : I64) (days : U16)
    (hty : m.field ACCT_TYPE = [ty])
    (hbal : decodeNum {} ACCT_BALANCE.fmt (m.field ACCT_BALANCE) = some bal.val)
    (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate.val)
    (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some (days.val : Int)) :
    wp (acctint.accrue (Codepage.cp037Char ty) (some bal) rate days) (fun ot =>
      rustObs ot = cobolObs (AcctIntCob.run {} 20 (AcctIntCob.initState m)) ∧
      (rustObs ot).isSome = true) := by
  cobol_ranges
  -- a valid packed balance is never LOW-VALUES (the program tests `ACCT-BAL-RAW`)
  have hz : ¬ m.field ACCT_BAL_RAW = [0, 0, 0, 0, 0, 0, 0] := by
    intro h; cobol_sym [h] at hbal
  have := daily_rate_eq rate.val
  simp only [acctint.accrue]
  cobol_rust_equiv [cobolObs, rustObs, hm, hty, hbal, hrate, hdays, hz, div_half_up_eq, abs_I128]

open AcctIntCob in
/-- **ACCTINT ⊑ acctint.rs (Aeneas).**  The real Aeneas translation of the Rust rewrite
simulates the COBOL program on every valid account record, with the outcome relation through
the shared decimal model (`AcctRel`). -/
theorem acctint_sim (m : Mem) (hm : m.size = 33) (ty : UInt8) (bal rate : I64) (days : U16)
    (hty : m.field ACCT_TYPE = [ty])
    (hbal : decodeNum {} ACCT_BALANCE.fmt (m.field ACCT_BALANCE) = some bal.val)
    (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate.val)
    (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some (days.val : Int)) :
    Sim AcctRel (acctint.accrue (Codepage.cp037Char ty) (some bal) rate days)
      (EquivLean.Cobol.run AcctIntCob {} 20 (AcctIntCob.initState m)) := by
  rw [EquivLean.Cobol.run, EquivLean.Cobol.sim_exec_iff]
  intro _
  exact wp_mono (acctint_wp m hm ty bal rate days hty hbal hrate hdays)
    fun _ ⟨h, hs⟩ => rel_of_obs h hs

open AcctIntCob in
/-- **ACCTINT ≈ acctint.rs (Aeneas)**: simulation in both directions (both runs are safe on
valid records, with related outcomes). -/
theorem acctint_equiv (m : Mem) (hm : m.size = 33) (ty : UInt8) (bal rate : I64) (days : U16)
    (hty : m.field ACCT_TYPE = [ty])
    (hbal : decodeNum {} ACCT_BALANCE.fmt (m.field ACCT_BALANCE) = some bal.val)
    (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate.val)
    (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some (days.val : Int)) :
    Equiv AcctRel (acctint.accrue (Codepage.cp037Char ty) (some bal) rate days)
      (EquivLean.Cobol.run AcctIntCob {} 20 (AcctIntCob.initState m)) := by
  have hw := acctint_wp m hm ty bal rate days hty hbal hrate hdays
  have hsim := acctint_sim m hm ty bal rate days hty hbal hrate hdays
  obtain ⟨ot, hot, hpost⟩ := wp_exists hw
  have hrel := rel_of_obs hpost.1 hpost.2
  rw [EquivLean.Cobol.run] at hsim ⊢
  refine ⟨hsim, fun _ => ?_⟩
  rw [EquivLean.Cobol.safe_exec_iff]
  refine ⟨ok_of_rel hrel, fun os hos => ⟨ot, hot, ?_⟩⟩
  obtain ⟨h1, -⟩ := (EquivLean.Cobol.runs_exec_iff _ _).1 hos
  rw [h1]
  exact hrel

open AcctIntCob in
/-- **The Rust code does not panic (and terminates) on valid records.** -/
theorem acctint_rust_no_panic (m : Mem) (hm : m.size = 33) (ty : UInt8) (bal rate : I64)
    (days : U16)
    (hty : m.field ACCT_TYPE = [ty])
    (hbal : decodeNum {} ACCT_BALANCE.fmt (m.field ACCT_BALANCE) = some bal.val)
    (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate.val)
    (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some (days.val : Int)) :
    wp (acctint.accrue (Codepage.cp037Char ty) (some bal) rate days)
      (fun ot => ∃ res, ot = .ok res) :=
  wp_mono (acctint_wp m hm ty bal rate days hty hbal hrate hdays) fun ot ⟨_, hs⟩ => by
    cases ot with
    | ok res => exact ⟨res, rfl⟩
    | error e => simp [rustObs] at hs

open AcctIntCob in
/-- The LOW-VALUES case: the COBOL program zeroes a balance field holding LOW-VALUES, the Rust
function receives `None` (`unwrap_or(0)`). -/
theorem acctint_wp_lowvalues (m : Mem) (hm : m.size = 33) (ty : UInt8) (rate : I64) (days : U16)
    (hty : m.field ACCT_TYPE = [ty])
    (hraw : m.field ACCT_BAL_RAW = [0, 0, 0, 0, 0, 0, 0])
    (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate.val)
    (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some (days.val : Int)) :
    wp (acctint.accrue (Codepage.cp037Char ty) none rate days) (fun ot =>
      rustObs ot = cobolObs (AcctIntCob.run {} 20 (AcctIntCob.initState m)) ∧
      (rustObs ot).isSome = true) := by
  cobol_ranges
  have := daily_rate_eq rate.val
  simp only [acctint.accrue]
  cobol_rust_equiv [cobolObs, rustObs, hm, hty, hraw, hrate, hdays, div_half_up_eq, abs_I128]

open AcctIntCob in
/-- **ACCTINT ≈ acctint.rs (Aeneas)**, LOW-VALUES balance. -/
theorem acctint_equiv_lowvalues (m : Mem) (hm : m.size = 33) (ty : UInt8) (rate : I64)
    (days : U16)
    (hty : m.field ACCT_TYPE = [ty])
    (hraw : m.field ACCT_BAL_RAW = [0, 0, 0, 0, 0, 0, 0])
    (hrate : decodeNum {} ACCT_RATE.fmt (m.field ACCT_RATE) = some rate.val)
    (hdays : decodeNum {} ACCT_DAYS.fmt (m.field ACCT_DAYS) = some (days.val : Int)) :
    Equiv AcctRel (acctint.accrue (Codepage.cp037Char ty) none rate days)
      (EquivLean.Cobol.run AcctIntCob {} 20 (AcctIntCob.initState m)) := by
  have hw := acctint_wp_lowvalues m hm ty rate days hty hraw hrate hdays
  obtain ⟨ot, hot, hpost⟩ := wp_exists hw
  have hrel := rel_of_obs hpost.1 hpost.2
  rw [EquivLean.Cobol.run]
  refine ⟨?_, fun _ => ?_⟩
  · rw [EquivLean.Cobol.sim_exec_iff]
    exact fun _ => wp_mono hw fun _ ⟨h, hs⟩ => rel_of_obs h hs
  · rw [EquivLean.Cobol.safe_exec_iff]
    refine ⟨ok_of_rel hrel, fun os hos => ⟨ot, hot, ?_⟩⟩
    obtain ⟨h1, -⟩ := (EquivLean.Cobol.runs_exec_iff _ _).1 hos
    rw [h1]
    exact hrel

end EquivLean.Demo.AcctIntAeneas

#print axioms EquivLean.Demo.AcctIntAeneas.div_half_up_eq
#print axioms EquivLean.Demo.AcctIntAeneas.acctint_wp
#print axioms EquivLean.Demo.AcctIntAeneas.acctint_sim
#print axioms EquivLean.Demo.AcctIntAeneas.acctint_equiv
#print axioms EquivLean.Demo.AcctIntAeneas.acctint_rust_no_panic
#print axioms EquivLean.Demo.AcctIntAeneas.acctint_equiv_lowvalues
