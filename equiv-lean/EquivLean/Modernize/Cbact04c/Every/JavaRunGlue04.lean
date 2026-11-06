import EquivLean.Modernize.Cbact04c.Every.JavaRunRecFacts
import EquivLean.Modernize.Cbact04c.Every.JavaRunHelpers4
import EquivLean.Modernize.Cbact04c.Every.JavaRunRunDefs

/-!
# CBACT04C → Java: the lines and texts the helpers build are the model's

* `tcbLine_eq`: the line `displayTcb` builds from a valid category record is `jline` of the
  record's text (`TranCatBalRecord.textS`, what `Model.step` displays);
* `zpad`/`zpadJ`, `cp037Str`, the overpunch.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

theorem toInt_ofInt64 {v : Int} (h1 : -9223372036854775808 ≤ v) (h2 : v < 9223372036854775808) :
    (BitVec.ofInt 64 v).toInt = v := by
  rw [BitVec.toInt_ofInt, Int.bmod_def]
  split <;> omega

theorem zpad_jline (n v : Nat) : (zpad n v).map (BitVec.ofNat 16) = zpadJ v n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [zpad, toDigits_succ, List.map_append, List.map_map, List.map_cons, List.map_nil,
      zpadJ] at ih ⊢
    rw [← ih (v / 10)]
    simp [Function.comp_def, digitJ]

theorem cp037Str_eq_map (bs : List UInt8) :
    cp037Str bs = (bs.map cp037Code).map (BitVec.ofNat 16) := by
  simp [cp037Str, cp037Unit, cp037Code, List.map_map, Function.comp_def]

/-- A valid category record, field by field. -/
theorem tcb_shape {t : List EquivLean.Cobol.Rec.FVal} (hv : TranCatBalRecord.Valid t) :
    t = [.num (Model.tAcct t), .str (Model.tType t), .num (Model.tCat t), .num (Model.tBal t),
      .str (tFill t)] := by
  have hlen : t.length = 5 := by
    have := Forall2.length_eq hv
    rw [← this]; decide
  have e0 := (valid_num hv (i := 0) (by decide) (fmt := {digits := 11}) (by decide)).1
  have e1 := (valid_str hv (i := 1) (by decide) (j := false) (by decide)).1
  have e2 := (valid_num hv (i := 2) (by decide) (fmt := {digits := 4}) (by decide)).1
  have e3 := (valid_num hv (i := 3) (by decide) (fmt := {digits := 11, scale := 2, signed := true})
    (by decide)).1
  have e4 := (valid_str hv (i := 4) (by decide) (j := false) (by decide)).1
  match t, hlen with
  | [a0, a1, a2, a3, a4], _ =>
    simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3 e4
    simp only [Model.tAcct, Model.tType, Model.tCat, Model.tBal, tFill, List.getD_cons_zero,
      List.getD_cons_succ]
    rw [← e0, ← e1, ← e2, ← e3, ← e4]

theorem opJ_eq (neg : Bool) (d : Nat) : BitVec.ofNat 16 (overpunch neg d) = opJ neg d := by
  cases neg <;> rfl

/-- The line `displayTcb` builds from field values. -/
theorem tcbLine_eq' (a c b : Int) (ty f : List UInt8)
    (ha1 : -9223372036854775808 ≤ a) (ha2 : a < 9223372036854775808)
    (hc1 : -9223372036854775808 ≤ c) (hc2 : c < 9223372036854775808)
    (hb1 : -9223372036854775808 ≤ b) (hb2 : b < 9223372036854775808) :
    tcbLine (BitVec.ofInt 64 a) (cp037Str ty) (BitVec.ofInt 64 c) (BitVec.ofInt 64 b) (cp037Str f) =
      jline (TranCatBalRecord.textS [.num a, .str ty, .num c, .num b, .str f]) := by
  rw [tcbLine, toInt_ofInt64 ha1 ha2, toInt_ofInt64 hc1 hc2, toInt_ofInt64 hb1 hb2, zonedJ]
  simp only [Schema.textS, List.zip_cons_cons, List.zip_nil_right, List.map_cons,
    List.map_nil, List.flatten_cons, List.flatten_nil, fieldTextS, List.append_nil]
  simp only [↓reduceIte, Bool.false_eq_true, jline, List.map_append, zpad_jline, List.map_cons,
    List.map_nil, opJ_eq, cp037Str_eq_map, List.append_assoc]

/-- **The line `displayTcb` builds is the record's text.** -/
theorem tcbLine_eq {t : List EquivLean.Cobol.Rec.FVal} (hv : TranCatBalRecord.Valid t)
    (ha1 : -9223372036854775808 ≤ Model.tAcct t) (ha2 : Model.tAcct t < 9223372036854775808)
    (hc1 : -9223372036854775808 ≤ Model.tCat t) (hc2 : Model.tCat t < 9223372036854775808)
    (hb1 : -9223372036854775808 ≤ Model.tBal t) (hb2 : Model.tBal t < 9223372036854775808) :
    tcbLine (BitVec.ofInt 64 (Model.tAcct t)) (cp037Str (Model.tType t))
        (BitVec.ofInt 64 (Model.tCat t)) (BitVec.ofInt 64 (Model.tBal t)) (cp037Str (tFill t)) =
      jline (TranCatBalRecord.textS t) := by
  rw [tcbLine_eq' _ _ _ _ _ ha1 ha2 hc1 hc2 hb1 hb2, ← tcb_shape hv]

/-! ## `WS-LAST-ACCT-NUM` against the digits of an account id -/

theorem digitJ_inj {a b : Nat} (ha : a < 10) (hb : b < 10) (h : digitJ a = digitJ b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [digitJ, BitVec.toNat_ofNat] at this
  omega

theorem zpadJ_inj : ∀ (n a b : Nat), a < 10 ^ n → b < 10 ^ n → zpadJ a n = zpadJ b n → a = b
  | 0, a, b, ha, hb, _ => by simp at ha hb; omega
  | n + 1, a, b, ha, hb, h => by
    simp only [zpadJ] at h
    have h1 := List.append_inj' h (by simp)
    simp only [List.cons.injEq, and_true] at h1
    have e1 := digitJ_inj (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) h1.2
    have hpow : 10 ^ (n + 1) = 10 ^ n * 10 := by rw [Nat.pow_succ]
    have e2 := zpadJ_inj n (a / 10) (b / 10) (by rw [hpow] at ha; omega) (by rw [hpow] at hb; omega) h1.1
    omega

theorem zpadJ_ne_spJ (a n : Nat) (hn : 0 < n) : zpadJ a n ≠ spJ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro h
  simp only [zpadJ, spJ_succ] at h
  have h1 := List.append_inj' h (by simp [zpadJ_length, spJ_length])
  simp only [List.cons.injEq, and_true] at h1
  have := congrArg BitVec.toNat h1.2
  simp only [digitJ, space, BitVec.toNat_ofNat] at this
  omega

theorem natAbs_lt_pow11 {x : Int} (h0 : 0 ≤ x) (h1 : x < 100000000000) : x.natAbs < 10 ^ 11 := by
  have : (10 : Nat) ^ 11 = 100000000000 := by decide
  rw [this]; omega

/-- The comparison of `WS-LAST-ACCT-NUM` with the record's account id. -/
theorem lastText_eq_iff {lastId : Option Int} {id : Int} (h0 : 0 ≤ id) (h1 : id < 100000000000)
    (hl : ∀ x, lastId = some x → 0 ≤ x ∧ x < 100000000000) :
    lastText lastId = zpadJ id.natAbs 11 ↔ lastId = some id := by
  cases lastId with
  | none =>
    simp only [lastText, reduceCtorEq, iff_false]
    exact fun h => zpadJ_ne_spJ id.natAbs 11 (by decide) h.symm
  | some x =>
    obtain ⟨hx0, hx1⟩ := hl x rfl
    simp only [lastText, Option.some.injEq]
    constructor
    · intro h
      have := zpadJ_inj 11 x.natAbs id.natAbs (natAbs_lt_pow11 hx0 hx1) (natAbs_lt_pow11 h0 h1) h
      omega
    · intro h; subst h; rfl

end EquivLean.Modernize.Cbact04c.Java
