import EquivLean.Modernize.Cbstm03a.Java.RunInv

/-!
# CBSTM03A → Java: pure facts about the run model, for the segment proofs

Bounds of the load counters (`LdBounded` kept by `ldStep`, `ldFin`), the record-by-record unfolding of the load
(`ldAll_drop`), the counts read back (`trctGet_bounded`), the amounts and totals (`zonedVal_bound`, `TotOk` of
`trunc11Z`, the sums `trunc11` and `writeTrans` receive), the keyed searches (`custFind_of_prefix`,
`custFind_none`, `acctFind_of_prefix`, `acctFind_none`), and the cards loop's steps (`cardsFrom_*`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

/-! ## The load counters -/

theorem bmod64_self {v : Int} (h0 : -9223372036854775808 ≤ v) (h1 : v < 9223372036854775808) :
    v.bmod (2 ^ 64) = v := Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)

theorem i64_one_toInt : (1 : I64).toInt = 1 := by decide

theorem i64_toInt_add_one_small {x : I64} (h0 : 0 ≤ x.toInt) (h1 : x.toInt < 10000) :
    (x + 1).toInt = x.toInt + 1 := by
  rw [BitVec.toInt_add]
  have : (1 : I64).toInt = 1 := by decide
  rw [this]
  exact bmod64_self (by omega) (by omega)

theorem srem10000_bounds {x : I64} (h0 : 0 ≤ x.toInt) (h1 : x.toInt < 10000) :
    0 ≤ ((x + 1).srem 10000).toInt ∧ ((x + 1).srem 10000).toInt < 10000 := by
  rw [BitVec.toInt_srem, i64_toInt_add_one_small h0 h1]
  have e : (10000 : I64).toInt = 10000 := by decide
  rw [e]
  constructor
  · exact Int.tmod_nonneg _ (by omega)
  · exact Int.tmod_lt_of_pos _ (by omega)

theorem trctSet_lengthR (vs : List Value) (cr v : I64) : (trctSet vs cr v).length = vs.length := by
  unfold trctSet; split <;> simp

theorem trctSet_bounded {vs : List Value} {cr v : I64}
    (h : ∀ w ∈ vs, ∃ c : I64, w = .long c ∧ 0 ≤ c.toInt ∧ c.toInt < 10000)
    (hv0 : 0 ≤ v.toInt) (hv1 : v.toInt < 10000) :
    ∀ w ∈ trctSet vs cr v, ∃ c : I64, w = .long c ∧ 0 ≤ c.toInt ∧ c.toInt < 10000 := by
  unfold trctSet
  split
  · intro w hw
    rcases List.mem_or_eq_of_mem_set hw with hw | hw
    · exact h w hw
    · exact ⟨v, hw, hv0, hv1⟩
  · exact h

theorem ld0_bounded (r0 : JStr) : LdBounded (ld0 r0) ∧ (ld0 r0).trct.length = 51 := by
  have e0 : (0 : I64).toInt = 0 := by decide
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by simp [ld0, trct0]⟩
  · show (0 : Int) ≤ (1 : I64).toInt; rw [i64_one_toInt]; omega
  · show (1 : I64).toInt < 10000; rw [i64_one_toInt]; omega
  · show (0 : Int) ≤ (0 : I64).toInt; rw [e0]
  · show (0 : I64).toInt < 10000; rw [e0]; omega
  · intro w hw
    simp only [ld0, trct0, List.mem_replicate] at hw
    exact ⟨0, hw.2, by rw [e0], by rw [e0]; omega⟩

theorem ldStep_bounded {s : LdSt} (r : JStr) (h : LdBounded s) (hl : s.trct.length = 51) :
    LdBounded (ldStep s r) ∧ (ldStep s r).trct.length = 51 := by
  obtain ⟨c0, c1, t0, t1, ht⟩ := h
  unfold ldStep
  by_cases he : s.save = sub r 0 16
  · simp only [he, ite_true]
    have := srem10000_bounds t0 t1
    exact ⟨⟨c0, c1, this.1, this.2, ht⟩, hl⟩
  · simp only [he, ite_false]
    have := srem10000_bounds c0 c1
    have o0 : (0 : Int) ≤ (1 : I64).toInt := by rw [i64_one_toInt]; omega
    have o1 : (1 : I64).toInt < 10000 := by rw [i64_one_toInt]; omega
    refine ⟨⟨this.1, this.2, o0, o1, trctSet_bounded ht t0 t1⟩, ?_⟩
    rw [trctSet_lengthR]; exact hl

theorem ldFin_bounded {s : LdSt} (h : LdBounded s) (hl : s.trct.length = 51) :
    LdBounded (ldFin s) ∧ (ldFin s).trct.length = 51 := by
  obtain ⟨c0, c1, t0, t1, ht⟩ := h
  refine ⟨⟨c0, c1, t0, t1, trctSet_bounded ht t0 t1⟩, ?_⟩
  simp only [ldFin]; rw [trctSet_lengthR]; exact hl

theorem ldAll_drop (s : LdSt) {rs : List JStr} {k : Nat} (hk : k < rs.length) :
    ldAll s (rs.drop k) = ldAll s (rs.drop k) ∧
      ldAll s (rs.drop k) = ldAll (ldStep s (rs.getD k [])) (rs.drop (k + 1)) := by
  refine ⟨rfl, ?_⟩
  rw [List.drop_eq_getElem_cons hk, List.getD_eq_getElem _ _ hk]
  rfl

theorem trctGet_bounded {vs : List Value} (cr : I64)
    (h : ∀ w ∈ vs, ∃ c : I64, w = .long c ∧ 0 ≤ c.toInt ∧ c.toInt < 10000) :
    ∃ c : I64, trctGet vs cr = .long c ∧ 0 ≤ c.toInt ∧ c.toInt < 10000 := by
  unfold trctGet
  split
  · rcases Nat.lt_or_ge (cr.toInt - 1).toNat vs.length with hi | hi
    · rw [List.getD_eq_getElem _ _ hi]
      exact h _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ hi]
      exact ⟨0, rfl, by decide, by decide⟩
  · exact ⟨0, rfl, by decide, by decide⟩

/-! ## Amounts and totals -/

theorem lowDigit_le (c : JChar) : lowDigit c ≤ 9 := by
  unfold lowDigit; omega

theorem zLast_le (c : JChar) (neg : Bool) : (zLast c neg).1 ≤ 9 := by
  unfold zLast
  split
  · simp
  · split
    · rename_i h; have := h.2; simp only; omega
    · split
      · simp
      · split
        · rename_i h; have := h.2; simp only; omega
        · split
          · rename_i h; have := h.2; simp only; omega
          · exact lowDigit_le c

theorem zAcc_lt (s : JStr) : ∀ i, (zAcc s i).1 < 10 ^ i
  | 0 => by simp [zAcc]
  | i + 1 => by
    have ih := zAcc_lt s i
    have hp : 10 ^ (i + 1) = 10 ^ i * 10 := Nat.pow_succ 10 i
    unfold zAcc
    split
    · rename_i h; simp only; have := h.2; omega
    · split
      · have := zLast_le (s.getD i 0) (zAcc s i).2; simp only; omega
      · have := lowDigit_le (s.getD i 0); simp only; omega

/-- A zoned value has fewer digits than the text has characters. -/
theorem zonedVal_bound (s : JStr) :
    -((10 ^ s.length : Nat) : Int) < zonedVal s ∧ zonedVal s < ((10 ^ s.length : Nat) : Int) := by
  have h := zAcc_lt s s.length
  unfold zonedVal
  split <;> constructor <;> omega

theorem trunc11Z_bound (v : Int) : -100000000000 < trunc11Z v ∧ trunc11Z v < 100000000000 := by
  unfold trunc11Z
  have : v.natAbs % 100000000000 < 100000000000 := Nat.mod_lt _ (by decide)
  split <;> constructor <;> omega

theorem i64_ofInt_toInt_small {v : Int} (h0 : -9223372036854775808 ≤ v) (h1 : v < 9223372036854775808) :
    (BitVec.ofInt 64 v).toInt = v := by
  rw [BitVec.toInt_ofInt]
  exact bmod64_self (by omega) (by omega)

/-- The total after `trunc11` stays within 11 digits. -/
theorem totOk_trunc11 (v : Int) : TotOk (BitVec.ofInt 64 (trunc11Z v)) := by
  have h := trunc11Z_bound v
  unfold TotOk
  rw [i64_ofInt_toInt_small (by omega) (by omega)]
  exact h

/-- An amount read from 11 characters is not `Long.MIN_VALUE`, and neither is a total plus such an amount. -/
theorem amt_bounds {s : JStr} (hs : s.length = 11) {total : I64} (ht : TotOk total) :
    -9223372036854775808 < (BitVec.ofInt 64 (zonedVal s)).toInt ∧
      -9223372036854775808 < (total + BitVec.ofInt 64 (zonedVal s)).toInt := by
  have hz := zonedVal_bound s
  rw [hs] at hz
  have e : ((10 ^ 11 : Nat) : Int) = 100000000000 := by norm_num
  rw [e] at hz
  have ha : (BitVec.ofInt 64 (zonedVal s)).toInt = zonedVal s := i64_ofInt_toInt_small (by omega) (by omega)
  refine ⟨by omega, ?_⟩
  unfold TotOk at ht
  rw [BitVec.toInt_add, ha, bmod64_self (by omega) (by omega)]
  omega

/-! ## The keyed searches -/

theorem custFind_of_prefix {keys texts : List JStr} {k : JStr} {i : Nat} (hl : keys.length = texts.length)
    (hi : i < keys.length) (hk : keys.getD i [] = k) (hpre : ∀ j, j < i → keys.getD j [] ≠ k) :
    custFind keys texts k = some (texts.getD i []) := by
  induction keys generalizing texts i with
  | nil => simp at hi
  | cons a rest ih =>
    cases texts with
    | nil => simp at hl
    | cons b bs =>
      cases i with
      | zero =>
        simp only [List.getD_cons_zero] at hk
        simp [custFind, List.zip_cons_cons, List.find?_cons, hk]
      | succ i =>
        have ha : a ≠ k := by simpa using hpre 0 (Nat.succ_pos i)
        have := ih (texts := bs) (i := i) (by simpa using hl) (by simpa using hi) (by simpa using hk)
          (fun j hj => by simpa using hpre (j + 1) (by omega))
        simp only [custFind, List.zip_cons_cons, List.find?_cons, decide_eq_true_eq, ha, ite_false] at this ⊢
        simpa using this

theorem custFind_none {keys texts : List JStr} {k : JStr}
    (hall : ∀ j, j < keys.length → keys.getD j [] ≠ k) : custFind keys texts k = none := by
  induction keys generalizing texts with
  | nil => simp [custFind]
  | cons a rest ih =>
    cases texts with
    | nil => simp [custFind]
    | cons b bs =>
      have ha : a ≠ k := by simpa using hall 0 (Nat.succ_pos _)
      have := ih (texts := bs) (fun j hj => by simpa using hall (j + 1) (by simpa using hj))
      simp only [custFind, List.zip_cons_cons, List.find?_cons, decide_eq_true_eq, ha, ite_false] at this ⊢
      simpa using this

theorem acctFind_of_prefix {texts : List JStr} {k : JStr} {i : Nat} (hi : i < texts.length)
    (hk : sub (texts.getD i []) 0 11 = k) (hpre : ∀ j, j < i → sub (texts.getD j []) 0 11 ≠ k) :
    acctFind texts k = some (texts.getD i []) := by
  induction texts generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at hk
      simp [acctFind, List.find?_cons, hk]
    | succ i =>
      have ha : sub a 0 11 ≠ k := by simpa using hpre 0 (Nat.succ_pos i)
      have := ih (i := i) (by simpa using hi) (by simpa using hk)
        (fun j hj => by simpa using hpre (j + 1) (by omega))
      simp only [acctFind, List.find?_cons, decide_eq_true_eq, ha, ite_false] at this ⊢
      simpa using this

theorem acctFind_none {texts : List JStr} {k : JStr}
    (hall : ∀ j, j < texts.length → sub (texts.getD j []) 0 11 ≠ k) : acctFind texts k = none := by
  induction texts with
  | nil => simp [acctFind]
  | cons a rest ih =>
    have ha : sub a 0 11 ≠ k := by simpa using hall 0 (Nat.succ_pos _)
    have := ih (fun j hj => by simpa using hall (j + 1) (by simpa using hj))
    simp only [acctFind, List.find?_cons, decide_eq_true_eq, ha, ite_false] at this ⊢
    simpa using this

/-! ## The cards loop's steps -/

theorem cardsFrom_past {m : Nat → JChar} {trct : List Value} {crCnt crJmp : I64} {card : JStr} {n : Nat}
    {acc : JOut × I64} (h : crCnt.toInt < crJmp.toInt) : cardsFrom m trct crCnt card n crJmp acc = acc := by
  cases n with
  | zero => rfl
  | succ n => simp [cardsFrom, h]

theorem cardsFrom_break {m : Nat → JChar} {trct : List Value} {crCnt crJmp : I64} {card : JStr} {n : Nat}
    {acc : JOut × I64} (h1 : ¬ crCnt.toInt < crJmp.toInt)
    (h2 : 0 < ebcCmp (memRd m (cardOffJ crJmp).toInt 16) card) :
    cardsFrom m trct crCnt card (n + 1) crJmp acc = acc := by
  simp [cardsFrom, h1, h2]

theorem cardsFrom_skip {m : Nat → JChar} {trct : List Value} {crCnt crJmp : I64} {card : JStr} {n : Nat}
    {acc : JOut × I64} (h1 : ¬ crCnt.toInt < crJmp.toInt)
    (h2 : ¬ 0 < ebcCmp (memRd m (cardOffJ crJmp).toInt 16) card)
    (h3 : card ≠ memRd m (cardOffJ crJmp).toInt 16) :
    cardsFrom m trct crCnt card (n + 1) crJmp acc = cardsFrom m trct crCnt card n (crJmp + 1) acc := by
  simp [cardsFrom, h1, h2, h3]

theorem cardsFrom_match {m : Nat → JChar} {trct : List Value} {crCnt crJmp cnt : I64} {card : JStr} {n : Nat}
    {acc : JOut × I64} (h1 : ¬ crCnt.toInt < crJmp.toInt)
    (h2 : ¬ 0 < ebcCmp (memRd m (cardOffJ crJmp).toInt 16) card)
    (h3 : card = memRd m (cardOffJ crJmp).toInt 16) (h4 : trctGet trct crJmp = .long cnt) :
    cardsFrom m trct crCnt card (n + 1) crJmp acc =
      cardsFrom m trct crCnt card n (crJmp + 1) (transOf m crJmp cnt.toInt.toNat acc) := by
  subst h3
  simp [cardsFrom, h1, h2, h4]

theorem transOf_succ (m : Nat → JChar) (crJmp : I64) (k : Nat) (acc : JOut × I64) :
    transOf m crJmp (k + 1) acc =
      let p := transOf m crJmp k acc
      let trJmp : I64 := BitVec.ofNat 64 (k + 1)
      let tid := memRd m (tranOffJ crJmp trJmp).toInt 16
      let trest := memRd m (tranOffJ crJmp trJmp + 16).toInt 318
      let amt : I64 := BitVec.ofInt 64 (zonedVal (sub trest 116 127))
      (p.1.add (jWriteTrans tid trest amt.toInt), BitVec.ofInt 64 (trunc11Z (p.2 + amt).toInt)) := by
  rfl

theorem xrefAll_cons (custKeys custTexts acctTexts : List JStr) (L : LdSt) (o : JOut) (x : JStr)
    (xs : List JStr) :
    xrefAll custKeys custTexts acctTexts L o (x :: xs) =
      match xrefStep custKeys custTexts acctTexts L o x with
      | .error o' => o'
      | .ok o' => xrefAll custKeys custTexts acctTexts L o' xs := rfl

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.amt_bounds
#print axioms EquivLean.Modernize.Cbstm03a.Java.custFind_of_prefix
#print axioms EquivLean.Modernize.Cbstm03a.Java.ldStep_bounded
#print axioms EquivLean.Modernize.Cbstm03a.Java.cardsFrom_match
