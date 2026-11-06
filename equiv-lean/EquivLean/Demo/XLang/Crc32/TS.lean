import EquivLean.Bridge.TS.Tactic
import EquivLean.Bridge.TS.Corr
import EquivLean.Demo.Gen.TS.PakoCrc32
import EquivLean.Demo.XLang.Crc32.Spec
import StrictTS.Proof.Summarize
import StrictTS.Proof.AsyncRace

/-!
# Demo: pako's CRC-32 (TypeScript) computes zlib's CRC-32

* TypeScript: `examples/ts/pako_crc32.ts`, pako 1.0.11's `lib/zlib/crc32.js` with types,
  translated by the pinned StrictTS front end to `EquivLean/Demo/Gen/TS/PakoCrc32.lean`:
  `makeTable` builds the table with two nested counted `for` loops and `push`, the module body
  stores it in the global `crcTable`, and `crc32(crc, buf, len, pos)` runs
  `crc = (crc >>> 8) ^ t[(crc ^ buf[i]) & 0xFF]` over `pos ≤ i < pos + len` between two
  `crc ^ -1`.
* Specification: `Demo/XLang/Crc32/Spec.lean` (`Crc32.entry`, `Crc32.step`, `Crc32.crc32`).

Results, for every `Impl`:

* `makeTable_spec`: `makeTable()` allocates one fresh array, at `w.next`, holding `crcTable`, and
  changes nothing else.  `crcTable` holds the 256 numbers `F64.ofInt32 (entry n)`: the signed
  32-bit values, as in JavaScript, where `0xEDB88320 ^ x` is negative (`tableVal_two`).
* `init_spec`: the module body's first statement, `const crcTable = makeTable()` (`initStmt`,
  `mainBlock_eq`), leaves the world `initWorld w`, whose global `crcTable` refers to that array
  (`initWorld_global`, `initWorld_table`); `mainBlock_run`: the whole module body is that
  statement followed by the rest from `initWorld w`.
* `crc32_spec`: in every world whose global `crcTable` refers to an array cell holding exactly
  `crcTable`, for a `Uint8Array` cell holding `bytes`, natural numbers `pos`, `len` (passed as
  doubles) with `pos + len ≤ bytes.size < 2^32`, and **every** number `crc` (NaN, infinities,
  fractions and negative numbers included), `crc32(crc, buf, len, pos)` returns
  `F64.ofInt32 (Crc32.crc32 (F64.toInt32 crc) (bytes.extract pos (pos + len)).toList)` and leaves
  the world unchanged.  `F64.toInt32 crc` is the bit pattern of `ToInt32(crc)`, which is also
  that of `ToUint32(crc)`; the result is an int32 double (`NumI32`, `crc32_numI32`) because
  pako returns `crc ^ -1` without `>>> 0`.
* `crc32_after_init`: the two composed: after the first statement, `crc32` computes zlib's CRC-32
  of any `Uint8Array` of the world.
* `program_output`: the whole program (module body, then the event loop) prints `907060870`, as
  Node does, for every `Impl`.

Proof method.  Both loops are counted `for` loops; StrictTS's counted-loop theorems
(`evalLoop_count_pure`, `evalLoop_count_cells`, the lemmas behind `ts_summarize`) turn each into
a left fold over the positions, given one symbolic iteration: no invariant and no variant.  The
iterations are computed by `ts_sym` and int32 lemmas on doubles (below); the register is kept as
`F64.ofInt32 c` with `c : BitVec 32`, so the folds are folds of `Crc32.entryStep` and
`Crc32.step` on bit vectors.  The 2048 double operations of the table are never evaluated: the
inner loop is `Nat.repeat entryStep 8` for a symbolic entry index.  (`ts_summarize` itself
stops on the `crc32` loop with an internal error, `unknown free variable`, at the pinned
StrictTS a15926a.)
-/

open StrictTS EquivLean.TS EquivLean.Demo.Gen.TS

namespace EquivLean.Demo.Crc32.TS

abbrev TT := PakoCrc32.TT

/-! ## int32 lemmas on doubles -/

/-- A natural number below `2^31` read as an int32 is itself. -/
theorem ofInt32_ofNat_of_lt {n : Nat} (h : n < 2147483648) :
    F64.ofInt32 (BitVec.ofNat 32 n) = F64.ofNat n := by
  rw [F64.ofInt32_eq, F64.ofNat_eq_ofInt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  have h1 : n % 2 ^ 32 = n := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  split
  · rfl
  · omega

/-- The uint32 and int32 views agree below `2^31`. -/
theorem ofUint32_eq_ofInt32 {y : BitVec 32} (h : y.toNat < 2147483648) :
    F64.ofUint32 y = F64.ofInt32 y := by
  rw [F64.ofUint32_eq, F64.ofInt32_eq, BitVec.toInt_eq_toNat_cond]
  split
  · rfl
  · omega

/-- `===` on safe integers. -/
theorem numEq_ofInt {a b : Int} (ha : F64.Safe a) (hb : F64.Safe b) :
    Conv.numEq (F64.ofInt a) (F64.ofInt b) = decide (a = b) := by
  obtain ⟨x, hx, -, hxm, -, -⟩ := F64.ofInt_fin a ha
  obtain ⟨y, hy, -, hym, -, -⟩ := F64.ofInt_fin b hb
  have hx0 : x.man = 0 ↔ a = 0 := by
    rw [← Fin64.mag_eq_zero_iff, hxm]
    constructor
    · intro h
      rcases Nat.mul_eq_zero.1 h with h | h
      · omega
      · exact absurd h (Nat.ne_of_gt (Nat.two_pow_pos 1074))
    · intro h; subst h; simp only [Int.natAbs_zero, Nat.zero_mul]
  have hy0 : y.man = 0 ↔ b = 0 := by
    rw [← Fin64.mag_eq_zero_iff, hym]
    constructor
    · intro h
      rcases Nat.mul_eq_zero.1 h with h | h
      · omega
      · exact absurd h (Nat.ne_of_gt (Nat.two_pow_pos 1074))
    · intro h; subst h; simp only [Int.natAbs_zero, Nat.zero_mul]
  rw [hx, hy]
  simp only [Conv.numEq]
  by_cases hab : a = b
  · subst hab
    have : x = y := F64.fin.inj (hx.symm.trans hy)
    subst this
    simp
  · have hxy : x ≠ y := by
      intro e; subst e
      exact hab (F64.ofInt_inj ha hb (hx.trans hy.symm))
    have : ¬ (x.man = 0 ∧ y.man = 0) := by
      rintro ⟨h1, h2⟩; exact hab ((hx0.1 h1).trans (hy0.1 h2).symm)
    simp only [hab, hxy, decide_false, Bool.or_false]
    simpa using this

/-- `(x & 1) !== 0` reads the int32 `x &&& 1`: `x === 0` on int32 doubles. -/
theorem numEq_ofInt32_zero (x : BitVec 32) :
    Conv.numEq (F64.ofInt32 x) (F64.ofNat 0) = decide (x = 0) := by
  rw [F64.ofInt32_eq, F64.ofNat_eq_ofInt,
    numEq_ofInt (F64.safe_toInt x) (by simp only [F64.Safe]; omega)]
  simp only [Int.natCast_zero]
  exact decide_eq_decide.2
    ⟨fun h => BitVec.toInt_inj.1 (h.trans BitVec.toInt_zero.symm), fun h => h ▸ BitVec.toInt_zero⟩

theorem band_ofInt32_ofNat (x : BitVec 32) {n : Nat} (h : n ≤ 2 ^ 53) :
    (F64.ofInt32 x).band (F64.ofNat n) = F64.ofInt32 (x &&& BitVec.ofNat 32 n) := by
  simp only [F64.band, F64.toInt32_ofInt32, toInt32_ofNat h]

theorem shr_ofInt32_ofNat (x : BitVec 32) {n : Nat} (h : n < 32) :
    (F64.ofInt32 x).shr (F64.ofNat n) = F64.ofUint32 (x >>> n) := by
  simp only [F64.shr, F64.toInt32_ofInt32, toInt32_ofNat (n := n) (by omega), BitVec.toNat_ofNat]
  congr 2
  rw [Nat.mod_eq_of_lt (by omega : n < 2 ^ 32), Nat.mod_eq_of_lt h]

theorem bxor_ofNat_ofUint32 {n : Nat} (h : n ≤ 2 ^ 53) (y : BitVec 32) :
    (F64.ofNat n).bxor (F64.ofUint32 y) = F64.ofInt32 (BitVec.ofNat 32 n ^^^ y) := by
  simp only [F64.bxor, F64.toInt32_ofUint32, toInt32_ofNat h]

theorem bxor_ofUint32_ofInt32 (x y : BitVec 32) :
    (F64.ofUint32 x).bxor (F64.ofInt32 y) = F64.ofInt32 (x ^^^ y) := by
  simp only [F64.bxor, F64.toInt32_ofUint32, F64.toInt32_ofInt32]

/-- `x ^ -1` for any number `x` (NaN and infinities included): the complement of `ToInt32 x`. -/
theorem bxor_negOne (x : F64) : x.bxor (F64.ofInt (-1)) = F64.ofInt32 (~~~ x.toInt32) := by
  simp only [F64.bxor]
  rw [F64.toInt32_ofInt (by simp only [F64.Safe]; omega)]
  have : BitVec.ofInt 32 (-1) = BitVec.allOnes 32 := by decide
  rw [this, BitVec.xor_allOnes]

theorem ofNat_add_ofNat {a b : Nat} (h : a + b ≤ 2 ^ 53) :
    F64.ofNat a + F64.ofNat b = F64.ofNat (a + b) := by
  simp only [F64.ofNat_eq_ofInt]
  rw [F64.add_ofInt (by simp only [F64.Safe]; omega) (by simp only [F64.Safe]; omega)
    (by simp only [F64.Safe]; omega)]
  simp

/-- A typed-array element of at most 31 bits read as a number is an int32 (its zero
extension). -/
theorem ofUintN_eq_ofInt32 {n : Nat} (b : BitVec n) (h : n ≤ 31) :
    F64.ofUintN b = F64.ofInt32 (b.setWidth 32) := by
  have hb := b.isLt
  have hp : 2 ^ n ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) h
  have h1 : (b.setWidth 32).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  rw [F64.ofUintN, F64.ofInt32_eq, BitVec.toInt_eq_toNat_cond, h1]
  split
  · rfl
  · omega

/-- A `Uint8Array` element as a number.  (Stated at `BitVec TAKind.u8.width`, the type of the
heap cell's elements, which `simp` does not identify with `BitVec 8`.) -/
theorem ofUintN_u8 (x : BitVec TAKind.u8.width) : F64.ofUintN x = F64.ofInt32 (x.setWidth 32) :=
  ofUintN_eq_ofInt32 x (by decide)

/-- An int32 below `2^31` used as an array index. -/
theorem arrayIndex?_ofInt32 {u : BitVec 32} (h : u.toNat < 2147483648) :
    Conv.arrayIndex? (F64.ofInt32 u) = some u.toNat := by
  rw [← ofUint32_eq_ofInt32 h, ofUint32_eq_ofNat, Conv.arrayIndex?_ofNat (by omega)]

theorem toNat_and_ofNat_255_lt (v : BitVec 32) : (v &&& BitVec.ofNat 32 255).toNat < 256 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- `(…) & 0xFF` as an array index. -/
theorem arrayIndex?_and255 (v : BitVec 32) :
    Conv.arrayIndex? (F64.ofInt32 (v &&& BitVec.ofNat 32 255)) =
      some (v &&& BitVec.ofNat 32 255).toNat :=
  arrayIndex?_ofInt32 (by have := toNat_and_ofNat_255_lt v; omega)

theorem and255_lt (v : BitVec 32) : ((v &&& BitVec.ofNat 32 255).toNat < 256) = True :=
  eq_true (toNat_and_ofNat_255_lt v)

theorem shr1_lt (x : BitVec 32) : (x >>> 1).toNat < 2147483648 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-! ## Folds -/

theorem repeat_succ' {α : Type} (f : α → α) (n : Nat) (x : α) :
    Nat.repeat f n (f x) = f (Nat.repeat f n x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat, ih]

theorem foldl_const_eq_repeat {α β : Type} (f : α → α) (l : List β) (x : α) :
    l.foldl (fun s _ => f s) x = Nat.repeat f l.length x := by
  induction l generalizing x with
  | nil => rfl
  | cons b l ih => simp only [List.foldl_cons, List.length_cons, ih, repeat_succ', Nat.repeat]

theorem foldl_pair_snd {α β γ : Type} (G : γ → α → β → α) (H : γ → β → β) (l : List γ)
    (s : α) (c : β) :
    (l.foldl (fun p i => (G i p.1 p.2, H i p.2)) (s, c)).2 = l.foldl (fun c i => H i c) c := by
  induction l generalizing s c with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons, ih]

theorem foldl_push_toList {α β : Type} (f : α → β) (l : List α) (acc : Array β) :
    (l.foldl (fun c i => c.push (f i)) acc).toList = acc.toList ++ l.map f := by
  induction l generalizing acc with
  | nil => simp
  | cons i l ih => simp only [List.foldl_cons, ih, Array.toList_push, List.map_cons]; simp

theorem foldl_push_finRange {β : Type} {n : Nat} (f : Fin n → β) :
    (List.finRange n).foldl (fun c i => c.push (f i)) #[] = Array.ofFn f := by
  apply Array.toList_inj.1
  rw [foldl_push_toList, Array.toList_ofFn]
  simp [List.finRange, List.map_ofFn]
  rfl

/-- The positions `p … n-1` of an array, read in order, are `xs.extract p n`. -/
theorem foldl_drop_finRange {α β : Type} (xs : Array β) (n p : Nat) (hn : n ≤ xs.size)
    (F : α → β → α) (s0 : α) :
    ((List.finRange n).drop p).foldl (fun s i => F s (xs[i.val]'(Nat.lt_of_lt_of_le i.isLt hn)))
      s0 = (xs.extract p n).toList.foldl F s0 := by
  have h : ((List.finRange n).drop p).map (fun i => xs[i.val]'(Nat.lt_of_lt_of_le i.isLt hn)) =
      (xs.extract p n).toList := by
    apply List.ext_getElem
    · simp; omega
    · intro j h1 h2
      simp
  rw [← h, List.foldl_map]

/-! ## The table -/

/-- Entry `n` of pako's table: the signed 32-bit value of zlib's `entry n`, as a double. -/
def tableVal (n : Nat) : Val TT .num := .num (F64.ofInt32 (Crc32.entry n))

/-- The 256 numbers of pako's `crcTable`. -/
def crcTable : Array (Val TT .num) := Array.ofFn (n := 256) fun i => tableVal i.val

theorem crcTable_size : crcTable.size = 256 := Array.size_ofFn

theorem crcTable_getElem (n : Nat) (h : n < crcTable.size) : crcTable[n] = tableVal n := by
  simp only [crcTable, Array.getElem_ofFn]

/-- Each element is the int32 double of zlib's entry (`NumI32`). -/
theorem crcTable_numI32 (n : Nat) (h : n < crcTable.size) :
    ∃ x, crcTable[n] = .num x ∧ NumI32 x (Crc32.entry n) :=
  ⟨_, crcTable_getElem n h, rfl⟩

/-- The sign is JavaScript's: zlib's entry 2 is `0xEE0E612C`, which pako stores as
`-301047508`. -/
theorem tableVal_two : tableVal 2 = .num (F64.ofInt (-301047508)) := by
  have h1 : Crc32.entry 2 = 0xEE0E612C := by decide
  have h2 : (0xEE0E612C : BitVec 32).toInt = -301047508 := by decide
  rw [tableVal, F64.ofInt32_eq, h1, h2]

/-! ## `makeTable()` -/

/-- `makeTable`'s outer loop environment: `n`, `table`, `c`. -/
def outerEnv (a k : Nat) (x : F64) :
    Env TT [⟨.num, true⟩, ⟨.arr .num, false⟩, ⟨.num, true⟩] :=
  .cons (.num (F64.ofNat k)) (.cons (.arr a) (.cons (.num x) .nil))

/-- The inner loop environment: `k`, `n`, `table`, `c` (an int32). -/
def innerEnv (a n k : Nat) (x : BitVec 32) :
    Env TT [⟨.num, true⟩, ⟨.num, true⟩, ⟨.arr .num, false⟩, ⟨.num, true⟩] :=
  .cons (.num (F64.ofNat k)) (.cons (.num (F64.ofNat n)) (.cons (.arr a)
    (.cons (.num (F64.ofInt32 x)) .nil)))

/-- The world with the fresh array at `w.next` holding `c`. -/
def tblWorld (w : World TT) (c : Array (Val TT .num)) : World TT :=
  { w with heap := w.heap.insert (.arr .num, w.next) c, next := w.next + 1 }

theorem entryStep_eq (x : BitVec 32) :
    Crc32.entryStep x =
      if x &&& BitVec.ofNat 32 1 = 0 then x >>> 1 else BitVec.ofNat 32 3988292384 ^^^ (x >>> 1) :=
  rfl

/-- The eight iterations of the inner loop, from `n`. -/
theorem inner_fold (n : Nat) :
    List.foldl (fun s (_ : Fin 8) => Crc32.entryStep s) (BitVec.ofNat 32 n)
      (List.drop 0 (List.finRange 8)) = Crc32.entry n := by
  rw [foldl_const_eq_repeat]; rfl

/-- **`makeTable()`** allocates one fresh array, at `w.next`, holding `crcTable`, and changes
nothing else. -/
theorem makeTable_spec (I : Impl) (w : World TT) :
    JS.exec (callFun I PakoCrc32.program PakoCrc32.makeTableRef .nil) w =
      some (.ok (.arr w.next),
        { w with heap := w.heap.insert (.arr .num, w.next) crcTable, next := w.next + 1 }) := by
  rw [PakoCrc32.makeTable_call]
  simp only [PakoCrc32.makeTableDef, ts_sym, F64.lit_eq_ofNat]
  rw [evalLoop_count_cells I PakoCrc32.program _ _ _ (σ := F64) (κ := Array (Val TT .num))
    (fun k x => outerEnv w.next k x) (fun c => tblWorld w c) 256 (by omega)
    (fun _ _ _ => .normal) (fun i _ _ => F64.ofInt32 (Crc32.entry i))
    (fun i _ c => c.push (tableVal i)) 0 (F64.ofNat 0) #[] _ ?henv (by omega) _ ?hw0 ?hcond ?hF
    (fun _ _ _ => rfl) ?hstep]
  case henv => rfl
  case hw0 => rfl
  case hcond =>
    intro k s c hk
    simp only [outerEnv, tblWorld, ts_sym]
  case hstep =>
    intro i s c hi
    simp (disch := omega) only [outerEnv, tblWorld, ts_sym, ofNat_add_one]
  case hF =>
    intro i s c
    simp only [outerEnv, tblWorld, ts_sym]
    rw [evalLoop_count_pure I PakoCrc32.program _ _ _ (fun k x => innerEnv w.next i k x) 8
      (by omega) (fun _ _ => .normal) (fun _ x => Crc32.entryStep x) 0 (BitVec.ofNat 32 i) _
      ?henv2 (by omega) _ ?hcond2 ?hF2 (fun _ _ => rfl) ?hstep2]
    case henv2 =>
      simp only [innerEnv, ofInt32_ofNat_of_lt (by have := i.isLt; omega : i.val < 2147483648)]
    case hcond2 =>
      intro k x hk
      simp only [innerEnv, ts_sym]
    case hstep2 =>
      intro j x hj
      simp (disch := omega) only [innerEnv, ts_sym, ofNat_add_one]
    case hF2 =>
      intro j x
      simp (disch := omega) only [innerEnv, ts_sym, band_ofInt32_ofNat, numEq_ofInt32_zero,
        shr_ofInt32_ofNat]
      by_cases h : x &&& BitVec.ofNat 32 1 = 0
      · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ts_sym,
          ofUint32_eq_ofInt32 (shr1_lt x), entryStep_eq]
      · simp (disch := omega) only [h, decide_false, Bool.not_false, ts_sym, bxor_ofNat_ofUint32,
          entryStep_eq]
    simp only [innerEnv, ts_sym, inner_fold, tableVal]
  rw [foldl_pair_snd
    (fun (i : Fin 256) (_ : F64) (_ : Array (Val TT .num)) => F64.ofInt32 (Crc32.entry i.val))
    (fun (i : Fin 256) (c : Array (Val TT .num)) => c.push (tableVal i.val))]
  simp only [List.drop_zero, foldl_push_finRange, outerEnv, tblWorld, ts_sym]
  rfl

/-! ## The module body's first statement -/

/-- `const crcTable = makeTable();`, the first statement of the module body. -/
def initStmt : Stmt TT [] .undef := .gset PakoCrc32.g_crcTable (.call PakoCrc32.makeTableRef .nil)

/-- The rest of the module body. -/
def mainRest : Block TT [] .undef :=
  match PakoCrc32.mainBlock with
  | .seq _ rest => rest
  | b => b

theorem mainBlock_eq : PakoCrc32.mainBlock = .seq initStmt mainRest := rfl

/-- The world after `initStmt`: the table at `w.next`, the global `crcTable` (the module
variable's box) referring to it. -/
def initWorld (w : World TT) : World TT :=
  { w with
    heap := (w.heap.insert (.arr .num, w.next) crcTable).insert
      (.box (.arr .num), PakoCrc32.g_crcTable.idx) (some (.arr w.next))
    next := w.next + 1 }

theorem init_spec (I : Impl) (w : World TT) :
    JS.exec (evalS I PakoCrc32.program initStmt .nil) w =
      some (.ok (.normal, .nil), initWorld w) := by
  simp only [initStmt, ts_sym, makeTable_spec]
  rfl

theorem mainBlock_run (I : Impl) (w : World TT) :
    JS.exec (evalB I PakoCrc32.program PakoCrc32.mainBlock .nil) w =
      JS.exec (evalB I PakoCrc32.program mainRest .nil) (initWorld w) := by
  rw [mainBlock_eq]
  simp only [ts_sym, init_spec]

theorem initWorld_global (w : World TT) :
    (initWorld w).heap.get? (.box (.arr .num), PakoCrc32.g_crcTable.idx) =
      some (some (.arr w.next)) := by
  simp only [initWorld, ts_sym]

theorem initWorld_table (w : World TT) :
    (initWorld w).heap.get? (.arr .num, w.next) = some crcTable := by
  simp only [initWorld]
  rw [JS.heap_get_insert_kind_ne _ _ _ _ (by decide), JS.heap_get_insert_self]

/-- Typed arrays are untouched by `initStmt`. -/
theorem initWorld_tarr (w : World TT) (k : TAKind) (b : Nat) :
    (initWorld w).heap.get? (.tarr k, b) = w.heap.get? (.tarr k, b) := by
  simp only [initWorld]
  rw [JS.heap_get_insert_kind_ne _ _ _ _ (by intro h; cases h),
    JS.heap_get_insert_kind_ne _ _ _ _ (by intro h; cases h)]

/-! ## `crc32(crc, buf, len, pos)` -/

/-- The environment of `crc32`'s loop at counter `k` with register `c` (an int32): `i`, `end`,
`t`, `crc`, `buf`, `len`, `pos`. -/
def loopEnv (ta b len pos e k : Nat) (c : BitVec 32) :
    Env TT [⟨.num, true⟩, ⟨.num, false⟩, ⟨.arr .num, false⟩, ⟨.num, true⟩, ⟨.tarr .u8, false⟩,
      ⟨.num, false⟩, ⟨.num, false⟩] :=
  .cons (.num (F64.ofNat k)) (.cons (.num (F64.ofNat e)) (.cons (.arr ta)
    (.cons (.num (F64.ofInt32 c)) (.cons (.tarr b) (.cons (.num (F64.ofNat len))
      (.cons (.num (F64.ofNat pos)) .nil))))))

theorem step_eq (s : BitVec 32) (x : BitVec 8) :
    s >>> 8 ^^^ Crc32.entry ((s ^^^ x.setWidth 32) &&& BitVec.ofNat 32 255).toNat =
      Crc32.step s x := by
  rw [Crc32.step, BitVec.xor_comm]; rfl

theorem step_eq_u8 (s : BitVec 32) (x : BitVec TAKind.u8.width) :
    s >>> 8 ^^^ Crc32.entry ((s ^^^ x.setWidth 32) &&& BitVec.ofNat 32 255).toNat =
      Crc32.step s x :=
  step_eq s x

/-- **`crc32(crc, buf, len, pos)`** computes zlib's CRC-32 of `bytes[pos : pos + len]` from the
register `ToUint32(crc)`, for every number `crc`, as an int32 double, and leaves the world
unchanged. -/
theorem crc32_spec (I : Impl) (w : World TT) (crc : F64) (ta b : Nat)
    (bytes : Array (BitVec 8)) (len pos : Nat)
    (hg : w.heap.get? (.box (.arr .num), PakoCrc32.g_crcTable.idx) = some (some (.arr ta)))
    (ht : w.heap.get? (.arr .num, ta) = some crcTable)
    (hb : w.heap.get? (.tarr .u8, b) = some bytes)
    (hpl : pos + len ≤ bytes.size) (hsz : bytes.size < 4294967296) :
    JS.exec (callFun I PakoCrc32.program PakoCrc32.crc32Ref
        (.cons (.num crc) (.cons (.tarr b) (.cons (.num (F64.ofNat len))
          (.cons (.num (F64.ofNat pos)) .nil))))) w =
      some (.ok (.num (F64.ofInt32
        (Crc32.crc32 crc.toInt32 (bytes.extract pos (pos + len)).toList))), w) := by
  rw [PakoCrc32.crc32_call]
  simp only [PakoCrc32.crc32Def, ts_sym, hg]
  rw [ofNat_add_ofNat (by omega), bxor_negOne]
  rw [evalLoop_count_pure I PakoCrc32.program _ _ _
    (fun k c => loopEnv ta b len pos (pos + len) k c)
    (pos + len) (by omega) (fun _ _ => .normal)
    (fun i c => Crc32.step c (bytes[i.val]'(Nat.lt_of_lt_of_le i.isLt hpl))) pos (~~~ crc.toInt32) _
    ?henv (by omega) w ?hcond ?hF (fun _ _ => rfl) ?hstep]
  case henv => rfl
  case hcond =>
    intro k s hk
    simp only [loopEnv, ts_sym]
  case hF =>
    intro i s
    have hi : i.val < @Array.size (BitVec TAKind.u8.width) bytes :=
      Nat.lt_of_lt_of_le i.isLt hpl
    simp (disch := omega) only [loopEnv, ts_sym, evalE_taGet_u8, hb, ht, hi, F64.lit_eq_ofNat,
      Conv.arrayIndex?_ofNat, ofUintN_u8, F64.bxor_ofInt32, band_ofInt32_ofNat, arrayIndex?_and255,
      crcTable_size, and255_lt, crcTable_getElem, tableVal, shr_ofInt32_ofNat,
      bxor_ofUint32_ofInt32, step_eq_u8]
    rfl
  case hstep =>
    intro i s hi
    simp (disch := omega) only [loopEnv, ts_sym, F64.lit_eq_ofNat, ofNat_add_one]
  simp only [loopEnv, ts_sym, bxor_negOne, F64.toInt32_ofInt32]
  rw [foldl_drop_finRange bytes (pos + len) pos hpl Crc32.step]
  rfl

/-- The result through the bridge's int32 view (`NumI32`). -/
theorem crc32_numI32 (I : Impl) (w : World TT) (crc : F64) (ta b : Nat)
    (bytes : Array (BitVec 8)) (len pos : Nat)
    (hg : w.heap.get? (.box (.arr .num), PakoCrc32.g_crcTable.idx) = some (some (.arr ta)))
    (ht : w.heap.get? (.arr .num, ta) = some crcTable)
    (hb : w.heap.get? (.tarr .u8, b) = some bytes)
    (hpl : pos + len ≤ bytes.size) (hsz : bytes.size < 4294967296) :
    ∃ x, JS.exec (callFun I PakoCrc32.program PakoCrc32.crc32Ref
        (.cons (.num crc) (.cons (.tarr b) (.cons (.num (F64.ofNat len))
          (.cons (.num (F64.ofNat pos)) .nil))))) w = some (.ok (.num x), w) ∧
      NumI32 x (Crc32.crc32 crc.toInt32 (bytes.extract pos (pos + len)).toList) :=
  ⟨_, crc32_spec I w crc ta b bytes len pos hg ht hb hpl hsz, rfl⟩

/-- **After the module's first statement**, `crc32` computes zlib's CRC-32 of every
`Uint8Array` of the world. -/
theorem crc32_after_init (I : Impl) (w : World TT) (crc : F64) (b : Nat)
    (bytes : Array (BitVec 8)) (len pos : Nat)
    (hb : w.heap.get? (.tarr .u8, b) = some bytes)
    (hpl : pos + len ≤ bytes.size) (hsz : bytes.size < 4294967296) :
    JS.exec (callFun I PakoCrc32.program PakoCrc32.crc32Ref
        (.cons (.num crc) (.cons (.tarr b) (.cons (.num (F64.ofNat len))
          (.cons (.num (F64.ofNat pos)) .nil))))) (initWorld w) =
      some (.ok (.num (F64.ofInt32
        (Crc32.crc32 crc.toInt32 (bytes.extract pos (pos + len)).toList))), initWorld w) :=
  crc32_spec I (initWorld w) crc w.next b bytes len pos (initWorld_global w) (initWorld_table w)
    (by rw [initWorld_tarr]; exact hb) hpl hsz

/-! ## The whole program -/

theorem program_main : PakoCrc32.program.main = PakoCrc32.mainBlock := rfl
theorem program_globals : PakoCrc32.program.globals = [.arr .num] := rfl

/-- `new Uint8Array([…])`: the array literal has type `number[]` but is used at
`TAKind.u8.elem[]`, and the cells hold `BitVec 8` values at type `BitVec TAKind.u8.width`; `simp`
does not identify these types, so the interpreter equation and the heap lemmas below are stated
with the literal's own types. -/
theorem evalE_arrOf_u8elem (I : Impl) (P : Program TT) {Γ : Ctx} {n : Nat}
    (args : Args TT Γ (List.replicate n .num)) (env : Env TT Γ) :
    evalE I P (t := .arr TAKind.u8.elem) (Expr.builtin (Builtin.arrOf .num n) args) env =
      (do let vs ← evalArgs I P args env; JS.allocArr TAKind.u8.elem (Vals.toList vs).toArray) := by
  rw [evalE.eq_def]; rfl

theorem exec_allocArr_u8elem (c : Array (Val TT .num)) (w : World TT) :
    JS.exec (JS.allocArr (TT := TT) TAKind.u8.elem c) w =
      some (.ok (.arr w.next),
        { w with heap := w.heap.insert (.arr TAKind.u8.elem, w.next) c, next := w.next + 1 }) := rfl

theorem heap_get_insert_self_u8elem (h : Heap TT) (a : Nat) (c : Array (Val TT .num)) :
    (h.insert (HKind.arr TAKind.u8.elem, a) c).get? (HKind.arr TAKind.u8.elem, a) = some c :=
  Std.ExtDHashMap.get?_insert_self

theorem map_toElem_u8 (l : List (Val TT .num)) :
    Array.map (TAKind.toElem (TT := TT) .u8) l.toArray =
      (l.map (fun v => F64.toBitsN 8 v.toNum)).toArray := by
  show Array.map (fun v : Val TT .num => F64.toBitsN 8 v.toNum) l.toArray = _
  exact List.map_toArray

theorem exec_alloc_tarr_u8 (c : Array (BitVec 8)) (w : World TT) :
    JS.exec (JS.alloc (HKind.tarr .u8) c) w =
      some (.ok w.next,
        { w with heap := w.heap.insert (.tarr .u8, w.next) c, next := w.next + 1 }) := rfl

theorem heap_get_insert_u8elem_ne (h : Heap TT) {k' : HKind} {a a' : Nat} (c : Array (Val TT .num))
    (hne : (HKind.arr TAKind.u8.elem, a) ≠ (k', a')) :
    (h.insert (HKind.arr TAKind.u8.elem, a) c).get? (k', a') = h.get? (k', a') :=
  JS.heap_get_insert_ne (k := HKind.arr TAKind.u8.elem) (k' := k') (a := a) (a' := a') h c hne

theorem heap_get_insert_tarr_u8_ne (h : Heap TT) {k' : HKind} {a a' : Nat} (c : Array (BitVec 8))
    (hne : (HKind.tarr .u8, a) ≠ (k', a')) :
    (h.insert (HKind.tarr .u8, a) c).get? (k', a') = h.get? (k', a') :=
  JS.heap_get_insert_ne (k := HKind.tarr .u8) (k' := k') (a := a) (a' := a') h c hne

theorem heap_get_insert_self_tarr_u8 (h : Heap TT) (a : Nat) (c : Array (BitVec 8)) :
    (h.insert (HKind.tarr .u8, a) c).get? (HKind.tarr .u8, a) = some c :=
  Std.ExtDHashMap.get?_insert_self

set_option maxRecDepth 100000 in
/-- **The whole program**: for every implementation of the host functions, running
`pako_crc32.ts` (module body, then the event loop) prints `907060870`, as Node does:
`crc32(0, new Uint8Array([104, 101, 108, 108, 111]), 5, 0) >>> 0`, zlib's `0x3610a686`. -/
theorem program_output (I : Impl) :
    runOutput I PakoCrc32.program = some (.ok (), [JSStr.ofString "907060870"]) := by
  rw [runOutput_eq]
  simp only [runProgram, program_globals, program_main, World.init, ts_sym, List.forIn_cons,
    List.forIn_nil]
  rw [mainBlock_run]
  simp only [mainRest, PakoCrc32.mainBlock, ts_sym, F64.lit_eq_ofNat, evalE_arrOf_u8elem,
    exec_allocArr_u8elem, Vals.toList, heap_get_insert_self_u8elem, map_toElem_u8, List.map_cons,
    List.map_nil, exec_alloc_tarr_u8, initWorld]
  rw [crc32_spec I _ (F64.ofNat 0) (0 + 1) (0 + 1 + 1 + 1) #[104, 101, 108, 108, 111] 5 0
    ?hg ?ht ?hb (by decide) (by decide)]
  case hg =>
    rw [heap_get_insert_tarr_u8_ne _ _ (by decide), heap_get_insert_u8elem_ne _ _ (by decide),
      JS.heap_get_insert_self]
  case ht =>
    rw [heap_get_insert_tarr_u8_ne _ _ (by decide), heap_get_insert_u8elem_ne _ _ (by decide),
      JS.heap_get_insert_kind_ne _ _ _ _ (by decide), JS.heap_get_insert_self]
  case hb =>
    rw [heap_get_insert_self_tarr_u8]
    exact congrArg some (by decide)
  simp only [ts_sym, shr_zero_ofInt32, eventLoop_eq, exec_drain_mk_nil, exec_eventLoopTail_mk,
    earliestTimer, List.nil_append, List.foldl_nil, Option.map_some]
  have hc : Crc32.crc32 (F64.ofNat 0).toInt32
      ((#[104, 101, 108, 108, 111] : Array (BitVec 8)).extract 0 (0 + 5)).toList = 0x3610a686 := by
    decide
  have hs : NumFormat.toJSString (F64.ofUint32 0x3610a686) = JSStr.ofString "907060870" := by decide
  rw [hc, hs]

end EquivLean.Demo.Crc32.TS
