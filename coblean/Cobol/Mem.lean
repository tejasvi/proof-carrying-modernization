/-
# Byte storage

All data-division storage of a program is one flat byte array.  Every record (01 / 77
level) has an offset assigned by the layout; `REDEFINES`, `RENAMES` and reference
modification are simply overlapping byte ranges.  This is the single source of truth: the
typed view of a field is `decodeNum` / raw bytes of the slice `read off len`.

The lemmas `read_write_same`, `read_write_disjoint`, `read_write_within` and
`read_write_overlap` are the field-level reasoning principles used by the symbolic
execution simp set: a read either sees the last write to the same field, skips a disjoint
write, or sees bytes of an overlapping write (`REDEFINES` views).
-/

namespace Cobol

/-- Program storage. -/
structure Mem where
  bytes : Array UInt8
  deriving Inhabited, DecidableEq, Repr

namespace Mem

/-- Number of bytes of storage. -/
def size (m : Mem) : Nat := m.bytes.size

/-- Byte at address `i` (`0` outside the storage). -/
def get (m : Mem) (i : Nat) : UInt8 := m.bytes.getD i 0

/-- The `len` bytes at offset `off`. -/
def read (m : Mem) (off len : Nat) : List UInt8 :=
  (List.range len).map (fun i => m.get (off + i))

/-- Write `bs` at offset `off`; bytes beyond the end of storage are dropped. -/
def write (m : Mem) (off : Nat) (bs : List UInt8) : Mem := ⟨go m.bytes off bs⟩
where
  go (a : Array UInt8) (i : Nat) : List UInt8 → Array UInt8
    | [] => a
    | b :: bs => go (a.setIfInBounds i b) (i + 1) bs

/-- Storage of `n` bytes, all `b`. -/
def fill (n : Nat) (b : UInt8) : Mem := ⟨Array.replicate n b⟩

theorem size_go (a : Array UInt8) (i : Nat) (bs : List UInt8) :
    (write.go a i bs).size = a.size := by
  induction bs generalizing a i with
  | nil => rfl
  | cons b bs ih => simp [write.go, ih]

@[simp] theorem size_write (m : Mem) (off : Nat) (bs : List UInt8) :
    (m.write off bs).size = m.size := size_go _ _ _

theorem getD_setIfInBounds (a : Array UInt8) (i j : Nat) (b : UInt8) :
    (a.setIfInBounds i b).getD j 0 = if i = j ∧ i < a.size then b else a.getD j 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · subst h; by_cases h2 : i < a.size <;> simp [h2]
  · simp [h]

theorem getD_go (a : Array UInt8) (i : Nat) (bs : List UInt8) (j : Nat) :
    (write.go a i bs).getD j 0 =
      if i ≤ j ∧ j < i + bs.length ∧ j < a.size then bs.getD (j - i) 0 else a.getD j 0 := by
  induction bs generalizing a i with
  | nil => simp [write.go]; omega
  | cons b bs ih =>
    simp only [write.go]
    rw [ih, Array.size_setIfInBounds, getD_setIfInBounds]
    simp only [List.length_cons]
    by_cases hij : i = j
    · subst hij
      have h0 : ¬ (i + 1 ≤ i) := by omega
      by_cases hs : i < a.size
      · simp [h0, hs]
      · simp [h0, hs]
    · by_cases h1 : i + 1 ≤ j ∧ j < i + 1 + bs.length ∧ j < a.size
      · have h2 : i ≤ j ∧ j < i + (bs.length + 1) ∧ j < a.size := by omega
        have : j - i = (j - (i + 1)) + 1 := by omega
        simp only [h1, h2, and_self, ↓reduceIte, this, List.getD_cons_succ]
      · have h2 : ¬ (i ≤ j ∧ j < i + (bs.length + 1) ∧ j < a.size) := by omega
        simp only [h1, h2, hij, false_and, ↓reduceIte]

theorem get_write (m : Mem) (off : Nat) (bs : List UInt8) (j : Nat) :
    (m.write off bs).get j =
      if off ≤ j ∧ j < off + bs.length ∧ j < m.size then bs.getD (j - off) 0 else m.get j :=
  getD_go _ _ _ _

@[simp] theorem length_read (m : Mem) (off len : Nat) : (m.read off len).length = len := by
  simp [read]

theorem getElem_read (m : Mem) (off len i : Nat) (h : i < (m.read off len).length) :
    (m.read off len)[i] = m.get (off + i) := by
  simp [read]

theorem read_write_same (m : Mem) (off len : Nat) (bs : List UInt8) (hl : bs.length = len)
    (hs : off + len ≤ m.size) : (m.write off bs).read off len = bs := by
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    rw [getElem_read, get_write]
    simp only [length_read] at h1
    rw [ite_eq_left (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem read_write_disjoint (m : Mem) (off1 off2 len2 : Nat) (bs : List UInt8)
    (h : off2 + len2 ≤ off1 ∨ off1 + bs.length ≤ off2) :
    (m.write off1 bs).read off2 len2 = m.read off2 len2 := by
  apply List.ext_getElem
  · simp
  · intro i h1 _
    simp only [length_read] at h1
    rw [getElem_read, getElem_read, get_write, ite_eq_right (by omega)]

theorem read_write_within (m : Mem) (off1 off2 len2 : Nat) (bs : List UInt8)
    (h1 : off1 ≤ off2) (h2 : off2 + len2 ≤ off1 + bs.length) (hs : off1 + bs.length ≤ m.size) :
    (m.write off1 bs).read off2 len2 = (bs.drop (off2 - off1)).take len2 := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi _
    simp only [length_read] at hi
    rw [getElem_read, get_write, ite_eq_left (by omega)]
    simp only [List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    congr 1; omega

/-- General overlap: each byte comes from the write if it is in range, else from `m`. -/
theorem read_write_overlap (m : Mem) (off1 off2 len2 : Nat) (bs : List UInt8) :
    (m.write off1 bs).read off2 len2 =
      (List.range len2).map (fun i =>
        if off1 ≤ off2 + i ∧ off2 + i < off1 + bs.length ∧ off2 + i < m.size
        then bs.getD (off2 + i - off1) 0 else m.get (off2 + i)) := by
  simp only [read, get_write]

theorem read_append (m : Mem) (off a b : Nat) :
    m.read off (a + b) = m.read off a ++ m.read (off + a) b := by
  apply List.ext_getElem
  · simp
  · intro i h1 _
    simp only [length_read] at h1
    rw [getElem_read, List.getElem_append]
    by_cases hi : i < a
    · rw [dite_eq_left (by simpa using hi), getElem_read]
    · rw [dite_eq_right (by simpa using hi), getElem_read]; congr 1; simp; omega

/-- Extensionality: storages with the same size and bytes are equal. -/
theorem ext_get {m1 m2 : Mem} (hs : m1.size = m2.size)
    (h : ∀ i, i < m1.size → m1.get i = m2.get i) : m1 = m2 := by
  cases m1 with
  | mk a1 =>
  cases m2 with
  | mk a2 =>
  simp only [size] at hs h
  simp only [Mem.mk.injEq]
  apply Array.ext hs
  intro i h1 h2
  have := h i h1
  simp only [get, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2, Option.getD_some] at this
  exact this

theorem write_write_same (m : Mem) (off : Nat) (bs cs : List UInt8) (hl : bs.length = cs.length) :
    (m.write off bs).write off cs = m.write off cs := by
  apply ext_get (by simp)
  intro i _
  simp only [get_write, size_write]
  by_cases h : off ≤ i ∧ i < off + cs.length ∧ i < m.size
  · simp only [ite_eq_left h]
  · have h' : ¬ (off ≤ i ∧ i < off + bs.length ∧ i < m.size) := by omega
    simp only [ite_eq_right h, ite_eq_right h']

theorem write_comm (m : Mem) (o1 o2 : Nat) (bs cs : List UInt8)
    (h : o1 + bs.length ≤ o2 ∨ o2 + cs.length ≤ o1) :
    (m.write o1 bs).write o2 cs = (m.write o2 cs).write o1 bs := by
  apply ext_get (by simp)
  intro i _
  simp only [get_write, size_write]
  by_cases ha : o1 ≤ i ∧ i < o1 + bs.length ∧ i < m.size <;>
    by_cases hb : o2 ≤ i ∧ i < o2 + cs.length ∧ i < m.size
  · exfalso; omega
  · simp only [ite_eq_left ha, ite_eq_right hb]
  · simp only [ite_eq_right ha, ite_eq_left hb]
  · simp only [ite_eq_right ha, ite_eq_right hb]

/-- Writing back what is there changes nothing (also beyond the end: those bytes are dropped
by `write` and read as `0`). -/
theorem write_read_self (m : Mem) (o n : Nat) : m.write o (m.read o n) = m := by
  apply ext_get (by simp)
  intro i _
  simp only [get_write, length_read]
  split
  · rename_i h
    simp only [read, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
      show i - o < n by omega, Option.map_some, Option.getD_some]
    congr 1; omega
  · rfl

/-- An `IF` that writes a field in one branch only: write in both, the old value in the other. -/
theorem ite_write_left (c : Prop) [Decidable c] (X Y : Mem) (o : Nat) (a : List UInt8) :
    (if c then X.write o a else Y) = (if c then X else Y).write o (if c then a else Y.read o a.length) := by
  split
  · rfl
  · rw [write_read_self]

theorem ite_write_right (c : Prop) [Decidable c] (X Y : Mem) (o : Nat) (b : List UInt8) :
    (if c then X else Y.write o b) = (if c then X else Y).write o (if c then X.read o b.length else b) := by
  split
  · rw [write_read_self]
  · rfl

theorem ite_write_write (c : Prop) [Decidable c] (X Y : Mem) (o : Nat) (a b : List UInt8) :
    (if c then X.write o a else Y.write o b) = (if c then X else Y).write o (if c then a else b) := by
  split <;> rfl

/-- Writes in increasing offset order, bottom to top (a canonical order for disjoint writes). -/
theorem write_swap (m : Mem) (o1 o2 : Nat) (a b : List UInt8) (h : o2 + b.length ≤ o1) :
    (m.write o1 a).write o2 b = (m.write o2 b).write o1 a :=
  write_comm m o1 o2 a b (Or.inr h)

end Mem
end Cobol
