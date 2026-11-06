import EquivLean.Bridge.TS.Behaves

/-!
# StrictTS bridge: representation correspondences

How TypeScript values stand for the shared mathematical models.

* `number` ↔ `Int`: `NumInt x n` (`x` is the double of the safe integer `n`, |n| ≤ 2^53); the
  arithmetic of safe integers is exact (`numInt_add`, `numInt_sub`, `numInt_mul`, comparisons).
  This is the default `Corr F64 Int`.
* `number` ↔ `BitVec 32`: the two int32 views of a double, `NumU32 x b` (`x = ofUint32 b`, the
  result of `… >>> 0`) and `NumI32 x b` (`x = ofInt32 b`, the result of `| 0`, `^`, `&`,
  `Math.imul`).  The int32 operators compute on the views (`bxor_ofUint32_ofNat`,
  `imul_ofInt32_ofNat`, `shr_zero_ofInt32`, …), so a loop over uint32 hashes is a loop over
  `BitVec 32`.  `Corr F64 (BitVec 32)` is the unsigned view.
* arrays ↔ `List`: `ArrHolds w a l` (the `T[]` at address `a` holds `l`), `TArrHolds w k a l`
  for typed arrays (`Uint8Array` ↔ `List (BitVec 8)`, …).
* `Map` ↔ finite maps: `MapHolds w a eq f` (lookups under the key equality `eq` agree with
  `f : K → Option V`) and `MapList w a l` (the live entries, in insertion order, are `l`, the
  association list that iteration observes).
* `arr.filter(f)` with a pure callback is `Array.filter` (`arrFilter_pure`, completing
  StrictTS's `arrReduce_pure'`/`arrMap_pure'`).

The number lemmas reuse `StrictTS.Num.F64Lemmas` and `StrictTS.Proof.Numbers`.
-/

namespace EquivLean.TS
open StrictTS

variable {TT : TypeTable}

/-! ## `number` ↔ `Int` (safe integers) -/

/-- `x` is the double holding the safe integer `n`. -/
def NumInt (x : F64) (n : Int) : Prop := F64.Safe n ∧ x = F64.ofInt n

instance : Corr F64 Int := ⟨NumInt⟩

theorem numInt_ofNat {n : Nat} (h : n ≤ 2 ^ 53) : NumInt (F64.ofNat n) n :=
  ⟨by simp only [F64.Safe]; omega, F64.ofNat_eq_ofInt n⟩

theorem numInt_add {x y : F64} {a b : Int} (hx : NumInt x a) (hy : NumInt y b)
    (hab : F64.Safe (a + b)) : NumInt (x + y) (a + b) := by
  obtain ⟨ha, rfl⟩ := hx; obtain ⟨hb, rfl⟩ := hy
  exact ⟨hab, F64.add_ofInt ha hb hab⟩

theorem numInt_sub {x y : F64} {a b : Int} (hx : NumInt x a) (hy : NumInt y b)
    (hab : F64.Safe (a - b)) : NumInt (x - y) (a - b) := by
  obtain ⟨ha, rfl⟩ := hx; obtain ⟨hb, rfl⟩ := hy
  exact ⟨hab, F64.sub_ofInt ha hb hab⟩

/-- Products need `a * b ≠ 0`: a zero product of a negative and a positive integer is `-0`. -/
theorem numInt_mul {x y : F64} {a b : Int} (hx : NumInt x a) (hy : NumInt y b)
    (hab : F64.Safe (a * b)) (hnz : a * b ≠ 0) : NumInt (x * y) (a * b) := by
  obtain ⟨ha, rfl⟩ := hx; obtain ⟨hb, rfl⟩ := hy
  exact ⟨hab, F64.mul_ofInt ha hb hab hnz⟩

theorem numInt_lt {x y : F64} {a b : Int} (hx : NumInt x a) (hy : NumInt y b) :
    x.lt y = decide (a < b) := by
  obtain ⟨ha, rfl⟩ := hx; obtain ⟨hb, rfl⟩ := hy
  exact F64.lt_ofInt ha hb

theorem numInt_le {x y : F64} {a b : Int} (hx : NumInt x a) (hy : NumInt y b) :
    x.le y = decide (a ≤ b) := by
  obtain ⟨ha, rfl⟩ := hx; obtain ⟨hb, rfl⟩ := hy
  exact F64.le_ofInt ha hb

/-- Two doubles holding safe integers are equal iff the integers are. -/
theorem numInt_inj {x y : F64} {a b : Int} (hx : NumInt x a) (hy : NumInt y b) :
    x = y ↔ a = b := by
  obtain ⟨ha, rfl⟩ := hx; obtain ⟨hb, rfl⟩ := hy
  exact F64.ofInt_inj_iff ha hb

/-! ## `number` ↔ `BitVec 32` (int32 idioms) -/

/-- `x` is the uint32 `b` as a double (the result of `>>> 0`). -/
def NumU32 (x : F64) (b : BitVec 32) : Prop := x = F64.ofUint32 b

/-- `x` is the int32 `b` as a double (the result of `| 0`, `^`, `&`, `Math.imul`). -/
def NumI32 (x : F64) (b : BitVec 32) : Prop := x = F64.ofInt32 b

instance : Corr F64 (BitVec 32) := ⟨NumU32⟩

theorem toInt32_ofNat {n : Nat} (h : n ≤ 2 ^ 53) : (F64.ofNat n).toInt32 = BitVec.ofNat 32 n := by
  rw [F64.ofNat_eq_ofInt, F64.toInt32_ofInt (by simp only [F64.Safe]; omega)]
  simp

/-- A typed-array element read as a number (`Uint8Array`, `Uint16Array`, `Uint32Array`). -/
theorem ofUintN_eq_ofNat {n : Nat} (b : BitVec n) : F64.ofUintN b = F64.ofNat b.toNat := by
  simp only [F64.ofUintN, F64.ofNat_eq_ofInt]

theorem ofUint32_eq_ofNat (b : BitVec 32) : F64.ofUint32 b = F64.ofNat b.toNat := by
  simp only [F64.ofUint32, F64.ofNat_eq_ofInt]

/-- `h ^ n` on a uint32 `h` and a small natural number `n`. -/
theorem bxor_ofUint32_ofNat (x : BitVec 32) {n : Nat} (h : n ≤ 2 ^ 53) :
    (F64.ofUint32 x).bxor (F64.ofNat n) = F64.ofInt32 (x ^^^ BitVec.ofNat 32 n) := by
  simp only [F64.bxor, F64.toInt32_ofUint32, toInt32_ofNat h]

theorem bxor_ofInt32_ofNat (x : BitVec 32) {n : Nat} (h : n ≤ 2 ^ 53) :
    (F64.ofInt32 x).bxor (F64.ofNat n) = F64.ofInt32 (x ^^^ BitVec.ofNat 32 n) := by
  simp only [F64.bxor, F64.toInt32_ofInt32, toInt32_ofNat h]

/-- `Math.imul(y, n)` on an int32 `y` and a natural number constant `n`. -/
theorem imul_ofInt32_ofNat (y : BitVec 32) {n : Nat} (h : n ≤ 2 ^ 53) :
    (F64.ofInt32 y).imul (F64.ofNat n) = F64.ofInt32 (y * BitVec.ofNat 32 n) := by
  simp only [F64.imul, F64.toInt32_ofInt32, toInt32_ofNat h]

theorem imul_ofUint32_ofNat (y : BitVec 32) {n : Nat} (h : n ≤ 2 ^ 53) :
    (F64.ofUint32 y).imul (F64.ofNat n) = F64.ofInt32 (y * BitVec.ofNat 32 n) := by
  simp only [F64.imul, F64.toInt32_ofUint32, toInt32_ofNat h]

/-- `y >>> 0` turns the int32 view into the uint32 view. -/
theorem shr_zero_ofInt32 (y : BitVec 32) : (F64.ofInt32 y).shr (F64.ofNat 0) = F64.ofUint32 y := by
  simp only [F64.shr, F64.toInt32_ofInt32, toInt32_ofNat (n := 0) (by omega)]
  simp

theorem shr_zero_ofUint32 (y : BitVec 32) : (F64.ofUint32 y).shr (F64.ofNat 0) = F64.ofUint32 y := by
  simp only [F64.shr, F64.toInt32_ofUint32, toInt32_ofNat (n := 0) (by omega)]
  simp

/-! ## Arrays, typed arrays and maps -/

/-- The array `T[]` at address `a` holds the list `l`. -/
def ArrHolds (w : World TT) {t : Ty} (a : Nat) (l : List (Val TT t)) : Prop :=
  w.heap.get? (.arr t, a) = some l.toArray

/-- The typed array of kind `k` at address `a` holds the list `l` (`Uint8Array` ↔ bytes). -/
def TArrHolds (w : World TT) (k : TAKind) (a : Nat) (l : List (BitVec k.width)) : Prop :=
  w.heap.get? (.tarr k, a) = some l.toArray

/-- The `Map` at address `a` agrees with the finite map `f` under the key equality `eq`
(`SameValueZero` for the interpreter's maps). -/
def MapHolds (w : World TT) {k v : Ty} (a : Nat) (eq : Val TT k → Val TT k → Bool)
    (f : Val TT k → Option (Val TT v)) : Prop :=
  ∃ m, w.heap.get? (.map k v, a) = some m ∧ ∀ key, m.get? eq key = f key

/-- The live entries of the `Map` at address `a`, in insertion order, are `l`. -/
def MapList (w : World TT) {k v : Ty} (a : Nat) (l : List (Val TT k × Val TT v)) : Prop :=
  ∃ m, w.heap.get? (.map k v, a) = some m ∧ m.toList = l

/-- Writing a cell of another kind keeps an array's contents. -/
theorem ArrHolds.insert_kind_ne {w : World TT} {t : Ty} {a : Nat} {l : List (Val TT t)}
    (h : ArrHolds w a l) {k : HKind} (b : Nat) (c : k.Cell TT) (hk : k ≠ .arr t) :
    ArrHolds { w with heap := w.heap.insert (k, b) c } a l := by
  unfold ArrHolds at *
  rw [JS.heap_get_insert_kind_ne _ _ _ _ hk]; exact h

/-- Writing a cell at another address keeps an array's contents. -/
theorem ArrHolds.insert_addr_ne {w : World TT} {t : Ty} {a : Nat} {l : List (Val TT t)}
    (h : ArrHolds w a l) {k : HKind} {b : Nat} (c : k.Cell TT) (hb : b ≠ a) :
    ArrHolds { w with heap := w.heap.insert (k, b) c } a l := by
  unfold ArrHolds at *
  rw [JS.heap_get_insert_addr_ne _ _ _ _ hb]; exact h

theorem ArrHolds.size {w : World TT} {t : Ty} {a : Nat} {l : List (Val TT t)}
    (h : ArrHolds w a l) : ∃ xs, w.heap.get? (.arr t, a) = some xs ∧ xs.size = l.length :=
  ⟨_, h, List.size_toArray⟩

/-- A safe source map lookup agrees with the model after `set` (any key equivalence). -/
theorem mapHolds_set {k v : Ty} {eq : Val TT k → Val TT k → Bool} (hE : JSMap.Equiv eq)
    (m : JSMap (Val TT k) (Val TT v)) (f : Val TT k → Option (Val TT v))
    (hm : ∀ key, m.get? eq key = f key) (key : Val TT k) (val : Val TT v) :
    ∀ key', (m.set eq key val).get? eq key' = if eq key key' then some val else f key' := by
  intro key'
  rw [JSMap.get?_set hE, hm]

/-! ## Array library: `filter` with a pure callback

StrictTS proves `reduce`/`map` with pure callbacks (`arrReduce_pure'`, `arrMap_pure'`); this is
the same for `filter`. -/

section
open JS

/-- Folding a filtering `push` over a list. -/
theorem foldl_push_filter {α : Type} (L : List α) (g : α → Bool) (init : Array α) :
    (L.foldl (fun acc x => if g x then acc.push x else acc) init).toList =
      init.toList ++ L.filter g := by
  induction L generalizing init with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldl_cons, List.filter_cons]
    rw [ih]
    cases g x <;> simp

/-- The pushes of a `filter`-style loop over positions build `Array.filter`. -/
theorem foldl_range_filter {α : Type} (xs : Array α) (g : α → Bool) :
    (List.range xs.size).foldl
      (fun acc k => if h : k < xs.size then (if g xs[k] then acc.push xs[k] else acc) else acc) #[]
      = xs.filter g := by
  have h1 := foldl_range_dite xs.toList (fun acc x _ => if g x then acc.push x else acc)
    (#[] : Array α)
  simp only [Array.length_toList, Array.getElem_toList] at h1
  rw [h1]
  apply Array.ext'
  have h2 : xs.toList.zipIdx.foldl (fun acc p => if g p.1 then acc.push p.1 else acc) #[]
      = (xs.toList.zipIdx.map Prod.fst).foldl (fun acc x => if g x then acc.push x else acc) #[] := by
    rw [List.foldl_map]
  rw [h2, foldl_push_filter]
  simp [List.zipIdx_map_fst]

/-- `arr.filter(f)` with a pure Boolean callback allocates `arr.filter g` at the next free
address. -/
theorem arrFilter_pure (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool))
    (g : Val TT t → Bool) (hf : PureFn I P f (fun vs => .bool (g vs.a0))) (w : World TT)
    (hw : w.heap.get? (.arr t, a) = some xs) (ha : a ≠ w.next) :
    exec (evalBuiltin I P (.arrFilter t) (.cons (.arr a) (.cons f .nil))) w =
      some (.ok (.arr w.next), { w with
        heap := w.heap.insert (.arr t, w.next) (xs.filter g),
        next := w.next + 1 }) := by
  rw [evalBuiltin.eq_def]
  simp only [exec_bind, exec_readArr, hw, Vals.a0_cons, Vals.a1_cons, Val.arrAddr_arr, exec_alloc]
  have hw1 : (w.heap.insert (.arr t, w.next) (#[] : Array (Val TT t))).get? (.arr t, a) = some xs := by
    rw [heap_get_insert_addr_ne _ _ _ _ (Ne.symm ha), hw]
  rw [foldlM_pure (List.range xs.size) _
    (fun acc k => if h : k < xs.size then (if g xs[k] then acc.push xs[k] else acc) else acc) _]
  · simp only [exec_writeArr, foldl_range_filter xs g, heap_insert_insert, exec_pure]
  · intro acc k _
    simp only [exec_bind, exec_readArr, hw1]
    split
    · rw [exec_bind, hf]; rfl
    · rfl

end

end EquivLean.TS
