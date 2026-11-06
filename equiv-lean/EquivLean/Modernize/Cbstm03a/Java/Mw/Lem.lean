import EquivLean.Modernize.Cbstm03a.Java.Iface2

/-!
# CBSTM03A → Java: `memWrite`, arithmetic, slot geometry and the written memory (namespace `…Java.Mw`)

The machine-arithmetic facts and the slot geometry are copied from cbA-mem's `CbAMem/{Lem,RdLem,RdDefs,Geo}.lean`
(namespace `…Java.Mem`); `memWr` of a growing prefix of the written text, and `SlotsAt` up to agreement below
`MEM_SZ`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Mw

/-! ## Machine arithmetic -/

theorem msb_false_of_nonneg {n : Nat} (x : BitVec n) (h : 0 ≤ x.toInt) : x.msb = false := by
  have hx := x.isLt
  rw [BitVec.toInt_eq_msb_cond] at h
  cases hm : x.msb
  · rfl
  · rw [hm] at h
    simp only [if_true] at h
    omega

theorem toInt_eq_toNat_of_nonneg {n : Nat} (x : BitVec n) (h : 0 ≤ x.toInt) : x.toInt = x.toNat := by
  have hm := msb_false_of_nonneg x h
  rw [BitVec.toInt_eq_msb_cond, hm]
  simp

theorem toInt_eq_toNat_of_lt {n : Nat} (x : BitVec n) (h : 2 * x.toNat < 2 ^ n) : x.toInt = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond, if_pos h]

theorem bmod32_self {x : Int} (h1 : -2147483648 ≤ x) (h2 : x < 2147483648) : x.bmod (2 ^ 32) = x := by
  unfold Int.bmod
  simp only [Nat.reducePow, Nat.cast_ofNat]
  split <;> omega

theorem bmod64_self {x : Int} (h1 : -9223372036854775808 ≤ x) (h2 : x < 9223372036854775808) :
    x.bmod (2 ^ 64) = x := by
  unfold Int.bmod
  simp only [Nat.reducePow, Nat.cast_ofNat]
  split <;> omega

theorem i2l_toInt (pos : I32) : (JInt.toLong pos).toInt = pos.toInt := by
  unfold JInt.toLong
  rw [BitVec.toInt_signExtend]
  simp only [show min 64 32 = 32 from rfl]
  exact bmod32_self (by have := BitVec.le_toInt (x := pos); omega) (by have := BitVec.toInt_lt (x := pos); omega)

/-- `o = off + (long) pos` without overflow on the invariant's ranges. -/
theorem o_toInt (off : I64) (pos : I32) (h1 : -2147483648 < off.toInt) (h2 : 0 ≤ pos.toInt)
    (h4 : pos.toInt = 0 ∨ off.toInt < 171156) :
    (off + JInt.toLong pos).toInt = off.toInt + pos.toInt := by
  have hol := BitVec.toInt_lt (x := off)
  have hpl := BitVec.toInt_lt (x := pos)
  simp only [Nat.reduceSub] at hol hpl
  rw [BitVec.toInt_add, i2l_toInt]
  exact bmod64_self (by omega) (by rcases h4 with h | h <;> omega)

theorem o_toNat (off : I64) (pos : I32) (h : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt)
    (h0 : 0 ≤ off.toInt + pos.toInt) : (off + JInt.toLong pos).toNat = (off.toInt + pos.toInt).toNat := by
  have e := toInt_eq_toNat_of_nonneg (off + JInt.toLong pos) (by omega)
  omega

/-- `within = (int) (o - slotStart(idx))`. -/
theorem within_toInt (o : I64) (S J : Nat) (hJ : o.toInt = J) (hS : S ≤ J) (hJS : J < 171156) :
    (JLong.toInt (o - BitVec.ofNat 64 S)).toInt = ((J - S : Nat) : Int) := by
  have hS' : (BitVec.ofNat 64 S).toInt = S := by
    rw [toInt_eq_toNat_of_lt _ (by simp only [BitVec.toNat_ofNat]; omega)]
    simp only [BitVec.toNat_ofNat]; omega
  have hd : (o - BitVec.ofNat 64 S).toInt = ((J - S : Nat) : Int) := by
    rw [BitVec.toInt_sub, hJ, hS']
    rw [bmod64_self (by omega) (by omega)]
    omega
  unfold JLong.toInt
  rw [BitVec.toInt_setWidth]
  have e := toInt_eq_toNat_of_nonneg (o - BitVec.ofNat 64 S) (by omega)
  rw [show ((o - BitVec.ofNat 64 S).toNat : Int) = ((J - S : Nat) : Int) by omega]
  exact bmod32_self (by omega) (by omega)

/-- `pos = (int) -off` for `-2^31 < off < 0`. -/
theorem neg_l2i_toInt (off : I64) (h1 : -2147483648 < off.toInt) (h3 : off.toInt < 0) :
    (JLong.toInt (-off)).toInt = -off.toInt := by
  have hol := BitVec.toInt_lt (x := off)
  have hoge := BitVec.le_toInt (x := off)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.cast_ofNat] at hol hoge
  have hs : (-off).toInt = -off.toInt := by
    rw [BitVec.toInt_neg, bmod64_self (by omega) (by omega)]
  unfold JLong.toInt
  rw [BitVec.toInt_setWidth]
  have e := toInt_eq_toNat_of_nonneg (-off) (by omega)
  rw [show ((-off).toNat : Int) = -off.toInt by omega]
  exact bmod32_self (by omega) (by omega)

/-! ## Slot geometry -/

/-- Every position below `MEM_SZ` lies in its slot, one of the 561. -/
theorem slotIdx_spec (j : Nat) (h : j < 171156) :
    slotIdx j < 561 ∧ slotSt (slotIdx j) ≤ j ∧ j < slotSt (slotIdx j) + slotLn (slotIdx j) := by
  unfold slotIdx slotSt slotLn
  split_ifs <;> omega

/-- A position inside slot `i` belongs to slot `i`. -/
theorem slotIdx_of_mem (i j : Nat) (hi : i < 561) (h1 : slotSt i ≤ j) (h2 : j < slotSt i + slotLn i) :
    slotIdx j = i := by
  unfold slotIdx slotSt slotLn at *
  split_ifs at * <;> omega

theorem slot_end_le (i : Nat) (hi : i < 561) : slotSt i + slotLn i ≤ 171156 := by
  unfold slotSt slotLn
  split_ifs <;> omega

theorem slotLn_le (i : Nat) : slotLn i ≤ 334 := by
  unfold slotLn; split_ifs <;> omega

theorem slotLn_pos (i : Nat) : 0 < slotLn i := by
  unfold slotLn; split_ifs <;> omega

/-! ## The written memory -/

theorem getD_take_of_lt {t : JStr} {q k : Nat} (h : k < q) (d : JChar) : (t.take q).getD k d = t.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos h]

/-- Nothing written yet. -/
theorem memWr_take_zero (m : Nat → JChar) (off : Int) (t : JStr) : memWr m off (t.take 0) = m := by
  funext j
  have h0 : (t.take 0).length = 0 := by simp
  unfold memWr
  rw [if_neg (fun h' => by omega)]

/-- All of `t` written. -/
theorem memWr_take_full (m : Nat → JChar) (off : Int) (t : JStr) (p : Nat) (h : t.length ≤ p) :
    memWr m off (t.take p) = memWr m off t := by
  rw [List.take_of_length_le h]

/-- The rest of `t` falls above `MEM_SZ`. -/
theorem memWr_past (m : Nat → JChar) (off : Int) (t : JStr) (p : Nat) (h : 171156 ≤ off + p) :
    memWr m off (t.take p) = memWr m off t := by
  funext j
  have h3 : (t.take p).length = min p t.length := List.length_take
  unfold memWr
  by_cases hj : j < 171156 ∧ off ≤ (j : Int) ∧ (j : Int) < off + t.length
  · rw [if_pos hj, if_pos ⟨hj.1, hj.2.1, by omega⟩]
    exact getD_take_of_lt (by omega) space
  · rw [if_neg hj, if_neg (fun h' => hj ⟨h'.1, h'.2.1, by omega⟩)]

/-- The first `p` characters fall below 0. -/
theorem memWr_neg (m : Nat → JChar) (off : Int) (t : JStr) (p : Nat) (h : off + p ≤ 0) :
    memWr m off (t.take p) = m := by
  funext j
  have h3 : (t.take p).length = min p t.length := List.length_take
  unfold memWr
  rw [if_neg (fun h' => by omega)]

/-- `K` more characters written: positions `[off + P, off + P + K)` below `MEM_SZ` change. -/
theorem memWr_step (m : Nat → JChar) (off : Int) (t : JStr) (P K : Nat) (h : P + K ≤ t.length) (j : Nat) :
    memWr m off (t.take (P + K)) j =
      if off + P ≤ j ∧ (j : Int) < off + P + K ∧ j < 171156 then t.getD (j - off).toNat space
      else memWr m off (t.take P) j := by
  have h1 : (t.take (P + K)).length = P + K := by rw [List.length_take]; omega
  have h2 : (t.take P).length = P := by rw [List.length_take]; omega
  unfold memWr
  rw [h1, h2]
  by_cases hA : off + P ≤ j ∧ (j : Int) < off + P + K ∧ j < 171156
  · rw [if_pos hA, if_pos ⟨hA.2.2, by omega, by omega⟩]
    exact getD_take_of_lt (by omega) space
  · rw [if_neg hA]
    by_cases hB : j < 171156 ∧ off ≤ (j : Int) ∧ (j : Int) < off + (P : Nat)
    · rw [if_pos ⟨hB.1, hB.2.1, by omega⟩, if_pos hB]
      rw [getD_take_of_lt (by omega) space, getD_take_of_lt (by omega) space]
    · rw [if_neg (fun h' => hB ⟨h'.1, h'.2.1, by omega⟩), if_neg hB]

/-! ## `SlotsAt` up to agreement below `MEM_SZ` -/

theorem slotsAt_congr {σ : State} {a : Addr} {M M' : Nat → JChar} (h : SlotsAt σ a M)
    (hMM : ∀ j, j < 171156 → M j = M' j) : SlotsAt σ a M' := by
  obtain ⟨vs, ha, hl, hs⟩ := h
  refine ⟨vs, ha, hl, fun i hi => ?_⟩
  have he := slot_end_le i hi
  rcases hs i hi with ⟨h1, h2⟩ | ⟨x, c, h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1, fun w hw => by rw [← hMM _ (by omega)]; exact h2 w hw⟩
  · exact Or.inr ⟨x, c, h1, h2, h3, fun w hw => by rw [← hMM _ (by omega)]; exact h4 w hw⟩

theorem slotsAt_agree {σ : State} {a : Addr} {M M' : Nat → JChar} (h : SlotsAt σ a M) (h' : SlotsAt σ a M')
    (j : Nat) (hj : j < 171156) : M j = M' j := by
  obtain ⟨vs, ha, hl, hs⟩ := h
  obtain ⟨vs', ha', hl', hs'⟩ := h'
  rw [ha] at ha'
  cases ha'
  obtain ⟨hi, h1, h2⟩ := slotIdx_spec j hj
  have hw : j = slotSt (slotIdx j) + (j - slotSt (slotIdx j)) := by omega
  rcases hs _ hi with ⟨hn, hm⟩ | ⟨x, c, hx, hxc, -, hm⟩ <;>
    rcases hs' _ hi with ⟨hn', hm'⟩ | ⟨x', c', hx', hxc', -, hm'⟩
  · rw [hw, hm _ (by omega), hm' _ (by omega)]
  · rw [hn] at hx'; cases hx'
  · rw [hx] at hn'; cases hn'
  · rw [hx] at hx'
    cases hx'
    rw [hxc] at hxc'
    cases hxc'
    rw [hw, hm _ (by omega), hm' _ (by omega)]

/-- `memWr` keeps agreement below `MEM_SZ`. -/
theorem memWr_agree {m m' : Nat → JChar} (h : ∀ j, j < 171156 → m j = m' j) (off : Int) (s : JStr) (j : Nat)
    (hj : j < 171156) : memWr m off s j = memWr m' off s j := by
  unfold memWr
  split
  · rfl
  · exact h j hj

end EquivLean.Modernize.Cbstm03a.Java.Mw
