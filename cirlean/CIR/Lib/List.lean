import CIR.Logic.Exec

/-!
  List facts that come up when verifying loops over `std::vector` /
  `std::string` contents with an integer index `i` (the C++ index variable,
  an `Int`, used as `i.toNat`). They are `grind` lemmas, so the leftover
  verification conditions of typical loops close automatically.
-/

namespace CIR.Lib

theorem sum_take_succ_toNat (l : List Int) (i : Int) (h0 : 0 ≤ i) (h : i < l.length) :
    (l.take (i + 1).toNat).sum = (l.take i.toNat).sum + l[i.toNat]'(by omega) := by
  have : (i + 1).toNat = i.toNat + 1 := by omega
  rw [this, List.take_add_one, List.sum_append]
  simp [List.getElem?_eq_getElem (show i.toNat < l.length by omega)]

theorem take_toNat_of_length_le (l : List Int) (i : Int) (h : (l.length : Int) ≤ i) :
    l.take i.toNat = l :=
  List.take_of_length_le (by omega)

theorem sum_take_toNat_of_length_le (l : List Int) (i : Int) (h : (l.length : Int) ≤ i) :
    (l.take i.toNat).sum = l.sum := by
  rw [take_toNat_of_length_le l i h]

attribute [grind =] sum_take_succ_toNat
attribute [grind] sum_take_toNat_of_length_le take_toNat_of_length_le

/-- The prefix sums of `l` stay in a range. -/
def PrefixSumsIn (lo hi : Int) (l : List Int) : Prop :=
  ∀ j ≤ l.length, lo ≤ (l.take j).sum ∧ (l.take j).sum ≤ hi

theorem PrefixSumsIn.succ {lo hi : Int} {l : List Int} (h : PrefixSumsIn lo hi l) (i : Int)
    (h0 : 0 ≤ i) (hi' : i < l.length) :
    lo ≤ (l.take i.toNat).sum + l[i.toNat]'(by omega) ∧
      (l.take i.toNat).sum + l[i.toNat]'(by omega) ≤ hi := by
  rw [← sum_take_succ_toNat l i h0 hi']
  exact h _ (by omega)

/-! Counting and searching. -/

theorem count_take_succ_toNat (l : List Int) (a : Int) (i : Int) (h0 : 0 ≤ i) (h : i < l.length) :
    (l.take (i + 1).toNat).count a =
      (l.take i.toNat).count a + (if l[i.toNat]'(by omega) = a then 1 else 0) := by
  have : (i + 1).toNat = i.toNat + 1 := by omega
  rw [this, List.take_add_one, List.count_append]
  simp [List.getElem?_eq_getElem (show i.toNat < l.length by omega), List.count_singleton]

theorem count_take_le (l : List Int) (a : Int) (n : Nat) : (l.take n).count a ≤ n :=
  Nat.le_trans (List.count_le_length) (List.length_take_le n l)

theorem count_take_toNat_of_length_le (l : List Int) (a : Int) (i : Int) (h : (l.length : Int) ≤ i) :
    (l.take i.toNat).count a = l.count a := by
  rw [take_toNat_of_length_le l i h]

attribute [grind =] count_take_succ_toNat
attribute [grind] count_take_toNat_of_length_le

/-- No element of `l` before position `i` is `a`. -/
def NoneBefore (l : List Int) (a : Int) (i : Nat) : Prop := ∀ j (h : j < l.length), j < i → l[j] ≠ a

theorem findIdx?_of_noneBefore_eq (l : List Int) (a : Int) (i : Nat) (h : i < l.length)
    (hn : NoneBefore l a i) (hi : l[i] = a) : l.findIdx? (· == a) = some i := by
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨h, by simp [hi], fun j hj => ?_⟩
  have := hn j (by omega) hj
  simpa using this

theorem findIdx?_of_noneBefore_none (l : List Int) (a : Int) (i : Nat) (h : l.length ≤ i)
    (hn : NoneBefore l a i) : l.findIdx? (· == a) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have := hn j hj (by omega)
  simpa using this

theorem noneBefore_succ (l : List Int) (a : Int) (i : Nat) (hn : NoneBefore l a i)
    (h : i < l.length) (hi : l[i] ≠ a) : NoneBefore l a (i + 1) := by
  intro j hj hji
  by_cases hji' : j = i
  · subst hji'; exact hi
  · exact hn j hj (by omega)

theorem noneBefore_zero (l : List Int) (a : Int) : NoneBefore l a 0 := by
  intro j _ h; omega

/-! `Int` loop-index versions (to be used explicitly). -/

theorem noneBefore_succ_toNat (l : List Int) (a : Int) (i : Int) (hn : NoneBefore l a i.toNat)
    (h0 : 0 ≤ i) (h : i < l.length) (hi : l[i.toNat]'(by omega) ≠ a) :
    NoneBefore l a (i + 1).toNat := by
  have : (i + 1).toNat = i.toNat + 1 := by omega
  rw [this]
  exact noneBefore_succ l a i.toNat hn (by omega) hi

theorem findIdx?_eq_toNat (l : List Int) (a : Int) (i : Int) (hn : NoneBefore l a i.toNat)
    (h0 : 0 ≤ i) (h : i < l.length) (hi : l[i.toNat]'(by omega) = a) :
    l.findIdx? (· == a) = some i.toNat :=
  findIdx?_of_noneBefore_eq l a i.toNat (by omega) hn hi

theorem findIdx?_none_toNat (l : List Int) (a : Int) (i : Int) (hn : NoneBefore l a i.toNat)
    (h : (l.length : Int) ≤ i) : l.findIdx? (· == a) = none :=
  findIdx?_of_noneBefore_none l a i.toNat (by omega) hn

attribute [grind] noneBefore_zero

/-! Element-index (`Nat`) versions, for loops over iterators (range-`for`). -/

theorem sum_take_succ (l : List Int) (i : Nat) (h : i < l.length) :
    (l.take (i + 1)).sum = (l.take i).sum + l[i] := by
  rw [List.take_add_one, List.sum_append]
  simp [List.getElem?_eq_getElem h]

theorem sum_take_of_length_le (l : List Int) (i : Nat) (h : l.length ≤ i) :
    (l.take i).sum = l.sum := by
  rw [List.take_of_length_le h]

attribute [grind =] sum_take_succ
attribute [grind] sum_take_of_length_le

theorem count_take_succ (l : List Int) (a : Int) (i : Nat) (h : i < l.length) :
    (l.take (i + 1)).count a = (l.take i).count a + (if l[i] = a then 1 else 0) := by
  rw [List.take_add_one, List.count_append]
  simp [List.getElem?_eq_getElem h, List.count_singleton]

theorem count_take_of_length_le (l : List Int) (a : Int) (i : Nat) (h : l.length ≤ i) :
    (l.take i).count a = l.count a := by
  rw [List.take_of_length_le h]

attribute [grind =] count_take_succ
attribute [grind] count_take_of_length_le
grind_pattern count_take_le => (l.take n).count a

attribute [grind →] noneBefore_succ findIdx?_of_noneBefore_eq findIdx?_of_noneBefore_none

/-- `[0, 1, …, n-1]` as integers (the values pushed by a counting loop). -/
def iotaInt (n : Nat) : List Int := (List.range n).map fun (j : Nat) => (j : Int)

theorem iotaInt_succ_toNat (i : Int) (h : 0 ≤ i) :
    iotaInt (i + 1).toNat = iotaInt i.toNat ++ [i] := by
  have : (i + 1).toNat = i.toNat + 1 := by omega
  rw [this, iotaInt, List.range_succ, List.map_append]
  simp [iotaInt]
  omega

theorem iotaInt_zero : iotaInt 0 = [] := by simp [iotaInt]

attribute [grind =] iotaInt_succ_toNat
attribute [grind] iotaInt_zero

theorem PrefixSumsIn.succNat {lo hi : Int} {l : List Int} (h : PrefixSumsIn lo hi l) (i : Nat)
    (hi' : i < l.length) :
    lo ≤ (l.take i).sum + l[i] ∧ (l.take i).sum + l[i] ≤ hi := by
  rw [← sum_take_succ l i hi']
  exact h _ (by omega)

end CIR.Lib
