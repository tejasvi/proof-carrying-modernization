/-
StrictTS proof layer: library facts behind common refactorings, stated in `simp` normal form
(numeric literals as `F64.ofNat n`, `x >= y` as `y.le x`).

* **`Math.min` / `Math.max` are commutative** on every double, NaN and `±0` included
  (`F64.min_comm`, `F64.max_comm`). They are not `@[simp]`: as permutation lemmas they made every
  `simp` over large `Math.min`/`Math.max` arguments order those arguments (`acLt`), which cost
  `ts_auto`'s final `simp` its whole heartbeat budget; pass them to `simp` where needed.
* **`Math.floor(y / 2) = y >> 1`** for every int32 value `y` (the result of `|`, `&`, `^`, `>>`,
  …), negative ones included (`F64.floor_div_two_ofInt32`, `F64.floor_div_two_bor`).
* **`s.indexOf(p, k) >= 0` is `s.includes(p, k)`** (`JSStr.zero_le_indexOf`).
* **`s.slice(0, p.length) === p` is `s.startsWith(p)`** (`JSStr.slice_length_beq`), with
  `Prim.intArg_ofNat` / `Prim.posArg_ofNat` for the position arguments. The length argument
  reduces only when `p.length ≤ 2^53`: for a longer pattern `F64.ofNat p.length` rounds, the slice
  can be shorter than `p`, and the two expressions differ in the model.
* **Dangling arrays panic at the first read**: a `for … of` loop (`evalForOf_dangling`, also over
  maps and sets) or an array method with a callback (`evalBuiltin_arrReduce_dangling`, …) whose
  array cell is missing throws the panic `"dangling reference"` with the world unchanged, so two
  versions of a refactoring that read the same missing cell first reach the same result. These
  are conditional `simp` lemmas: the hypothesis `w.heap.get? (.arr t, a) = none` must be in the
  `simp` set (e.g. `simp [*]`).
-/
import StrictTS.Proof.Unfold
import StrictTS.Proof.Numbers
import StrictTS.Proof.F64Order
import StrictTS.Str.Lemmas

namespace StrictTS
namespace F64

/-! ### `Math.min` and `Math.max` are commutative -/

theorem sval_eq_zero_iff (x : Fin64) : x.sval = 0 ↔ x.man = 0 := by
  rw [← Fin64.mag_eq_zero_iff]; unfold Fin64.sval; split <;> omega

/-- A finite double is determined by its value and its sign (the sign matters only for zeros). -/
theorem fin_eq_of_sval_eq {x y : Fin64} (h : x.sval = y.sval) (hs : x.neg = y.neg) : x = y := by
  by_cases hx : x.man = 0
  · have hy : y.man = 0 := (sval_eq_zero_iff y).1 (h ▸ (sval_eq_zero_iff x).2 hx)
    have ex := Fin64.exp_of_man_lt (x := x) (by omega)
    have ey := Fin64.exp_of_man_lt (x := y) (by omega)
    cases x; cases y
    simp only [Fin64.mk.injEq]
    simp_all
  · have hy : y.man ≠ 0 := fun hy => hx ((sval_eq_zero_iff x).1 (h ▸ (sval_eq_zero_iff y).2 hy))
    have e : F64.fin x = F64.fin y := by rw [fin_eq_round_sval x hx, fin_eq_round_sval y hy, h]
    exact F64.fin.inj e

/-- Two non-NaN doubles neither of which is below the other are equal if they have the same sign
bit (otherwise they are `+0` and `-0`). -/
theorem eq_of_not_lt_of_not_lt {x y : F64} (hx : x ≠ .nan) (hy : y ≠ .nan) (h1 : x.lt y = false)
    (h2 : y.lt x = false) (hs : x.signBit = y.signBit) : x = y := by
  match x, y, hx, hy, h1, h2, hs with
  | .nan, _, hx, _, _, _, _ => exact absurd rfl hx
  | _, .nan, _, hy, _, _, _ => exact absurd rfl hy
  | .inf a, .inf b, _, _, h1, h2, _ => cases a <;> cases b <;> simp_all [lt]
  | .inf a, .fin _, _, _, h1, h2, _ => cases a <;> simp_all [lt]
  | .fin _, .inf b, _, _, h1, h2, _ => cases b <;> simp_all [lt]
  | .fin x, .fin y, _, _, h1, h2, hs =>
    rw [lt_fin_fin] at h1 h2
    simp only [decide_eq_false_iff_not] at h1 h2
    simp only [signBit] at hs
    exact congrArg F64.fin (fin_eq_of_sval_eq (by omega) hs)

theorem isNaN_eq_false {x : F64} (h : x ≠ .nan) : x.isNaN = false := by
  cases x <;> simp_all [isNaN]

/-- `Math.min` is commutative, NaN and `±0` included. -/
theorem min_comm (x y : F64) : x.min y = y.min x := by
  unfold min
  by_cases hx : x = .nan
  · subst hx; simp [isNaN]
  by_cases hy : y = .nan
  · subst hy; simp [isNaN]
  simp only [isNaN_eq_false hx, isNaN_eq_false hy, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  cases h1 : x.lt y <;> cases h2 : y.lt x <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · by_cases hs : x.signBit = y.signBit
    · rw [eq_of_not_lt_of_not_lt hx hy h1 h2 hs]
    · cases hxs : x.signBit <;> cases hys : y.signBit <;> simp_all
  · exact absurd h2 (by rw [not_lt_of_le (le_of_lt h1)]; decide)

/-- `Math.max` is commutative, NaN and `±0` included. -/
theorem max_comm (x y : F64) : x.max y = y.max x := by
  unfold max
  by_cases hx : x = .nan
  · subst hx; simp [isNaN]
  by_cases hy : y = .nan
  · subst hy; simp [isNaN]
  simp only [isNaN_eq_false hx, isNaN_eq_false hy, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  cases h1 : x.lt y <;> cases h2 : y.lt x <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · by_cases hs : x.signBit = y.signBit
    · rw [eq_of_not_lt_of_not_lt hx hy h1 h2 hs]
    · cases hxs : x.signBit <;> cases hys : y.signBit <;> simp_all
  · exact absurd h2 (by rw [not_lt_of_le (le_of_lt h1)]; decide)

/-! ### `Math.floor(y / 2) = y >> 1` on int32 values -/

/-- `Math.floor(y / 2) = y >> 1` for every int32 value `y` (arithmetic shift rounds down). -/
@[simp] theorem floor_div_two_ofInt32 (b : BitVec 32) : (ofInt32 b / ofNat 2).floor = (ofInt32 b).sar (ofNat 1) := by
  rw [show ofNat 1 = ofInt32 1 from rfl, sar_ofInt32, show ofNat 2 = ofInt 2 from rfl, ofInt32_eq, ofInt32_eq,
    floor_div_ofInt (safe_toInt b) (by simp only [Safe]; omega) (by decide) (Or.inr (by decide))]
  congr 1
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, Int.fdiv_eq_ediv]
  simp

/-- `Math.floor((x | y) / 2) = (x | y) >> 1` (e.g. `y = 0`: the int32 idiom `x | 0`). -/
@[simp] theorem floor_div_two_bor (x y : F64) : (x.bor y / ofNat 2).floor = (x.bor y).sar (ofNat 1) :=
  floor_div_two_ofInt32 _

/-! ### Rounded naturals are `≥ 0` -/

theorem mkFin_sign (neg : Bool) (man : Nat) (exp : Int) :
    mkFin neg man exp = .nan ∨ ∃ x : Fin64, x.neg = neg ∧ mkFin neg man exp = .fin x := by
  unfold mkFin; split
  · exact .inr ⟨_, rfl, rfl⟩
  · exact .inl rfl

/-- `round` gives the infinity or a finite double of the requested sign. -/
theorem round_sign (neg : Bool) (m : Nat) (e : Int) :
    round neg m e = .inf neg ∨ ∃ x : Fin64, x.neg = neg ∧ round neg m e = .fin x := by
  have hne := round_ne_nan neg m e false (Or.inr rfl)
  suffices key : round neg m e = .inf neg ∨ ∃ man exp, round neg m e = mkFin neg man exp by
    rcases key with h | ⟨man, exp, h⟩
    · exact .inl h
    · rcases mkFin_sign neg man exp with h' | ⟨x, hx, h'⟩
      · exact absurd (h.trans h') hne
      · exact .inr ⟨x, hx, h.trans h'⟩
  by_cases h0 : m = 0
  · subst h0; exact .inr ⟨_, _, round_zero neg e⟩
  rw [round_eq _ _ _ _ (by simp [h0])]
  unfold pack
  repeat' split
  all_goals first | exact .inl rfl | exact .inr ⟨_, _, rfl⟩

theorem ofNat_zero_eq : ofNat 0 = .fin ⟨false, 0, -1074, Or.inr ⟨by decide, rfl⟩⟩ := by
  show round false 0 0 = _
  rw [round_zero, mkFin_eq]

theorem zero_le_round (m : Nat) (e : Int) : (ofNat 0).le (round false m e) = true := by
  rcases round_sign false m e with h | ⟨x, hx, h⟩ <;> rw [h, ofNat_zero_eq]
  · rfl
  · rw [le_fin_fin, decide_eq_true_eq,
      show (⟨false, 0, -1074, Or.inr ⟨by decide, rfl⟩⟩ : Fin64).sval = 0 by simp [Fin64.sval, Fin64.mag]]
    unfold Fin64.sval
    simp only [hx, Bool.false_eq_true, ↓reduceIte]
    omega

/-- Every natural number converts to a double `≥ 0` (`+Infinity` beyond the finite range). -/
@[simp] theorem zero_le_ofInt_natCast (n : Nat) : (ofNat 0).le (ofInt (n : Int)) = true := by
  have : ofInt (n : Int) = round false n 0 := by unfold ofInt; congr 1 <;> simp
  rw [this]; exact zero_le_round n 0

end F64

/-! ### Strings -/

/-- A position argument that is a natural number up to `2^53` (`slice`, `substring`, …). -/
@[simp] theorem Prim.intArg_ofNat {n : Nat} (len : Nat) (h : n ≤ 2 ^ 53) :
    Prim.intArg (F64.ofNat n) len = n := by
  simp [Prim.intArg, Conv.toIntegerOrInf_ofNat h]

/-- A clamped position argument that is a natural number up to `2^53` (`indexOf`, `includes`,
`startsWith`, …). -/
@[simp] theorem Prim.posArg_ofNat {n : Nat} (len : Nat) (h : n ≤ 2 ^ 53) :
    Prim.posArg (F64.ofNat n) len = min n len := by
  simp [Prim.posArg, Conv.toIntegerOrInf_ofNat h]

namespace JSStr

/-- `s.indexOf(p, k) >= 0` is `s.includes(p, k)`. -/
@[simp] theorem zero_le_indexOf (s p : JSStr) (k : Nat) :
    (F64.ofNat 0).le (F64.ofInt (s.indexOf p k)) = s.includes p k := by
  unfold JSStr.indexOf JSStr.includes
  split
  · rename_i i heq
    rw [heq, Option.isSome_some]
    exact F64.zero_le_ofInt_natCast i
  · rename_i heq
    rw [heq]
    decide

/-- The same, in the form a `>=` test leaves (`F64.ge` is not unfolded by `simp`). -/
@[simp] theorem indexOf_ge_zero (s p : JSStr) (k : Nat) :
    (F64.ofInt (s.indexOf p k)).ge (F64.ofNat 0) = s.includes p k := by
  rw [F64.ge_eq_le]; exact zero_le_indexOf s p k

/-- `s.slice(0, p.length) === p` is `s.startsWith(p)`. -/
@[simp] theorem slice_length_beq (s p : JSStr) : (s.slice 0 p.length == p) = s.startsWith p 0 := by
  cases s with
  | mk su =>
  cases p with
  | mk pu =>
  have hc : ¬ ((pu.length : Int) < 0) := by omega
  simp only [slice, sub, relIndex, startsWith, length, hc, Int.reduceLT, ↓reduceIte, Int.toNat_zero,
    Int.toNat_natCast, Nat.zero_min, List.drop_zero, Nat.sub_zero]
  rw [Bool.eq_iff_iff, beq_iff_eq, mk.injEq, List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take,
    List.take_eq_take_iff.2 (show min (min pu.length su.length) su.length = min pu.length su.length by omega)]
  exact eq_comm

end JSStr

/-! ### Dangling arrays: the first read panics -/

open JS

variable {TT : TypeTable}

/-- `for (const x of arr)` over a missing array cell panics with the world unchanged. -/
@[simp] theorem evalForOf_dangling (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty} (a i : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT)
    (h : w.heap.get? (.arr t, a) = none) :
    exec (evalForOf I P a i body env) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalForOf.eq_1]; simp only [exec_bind, exec_readArr, h]

/-- `for (const [k, v] of map)` over a missing map cell panics with the world unchanged. -/
@[simp] theorem evalForOfMap_dangling (I : Impl) (P : Program TT) {Γ : Ctx} {ρ k v : Ty} (a i : Nat)
    (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT)
    (h : w.heap.get? (.map k v, a) = none) :
    exec (evalForOfMap I P a i body env) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalForOfMap.eq_1]; simp only [exec_bind, exec_readMap, h]

/-- `for (const x of set)` over a missing set cell panics with the world unchanged. -/
@[simp] theorem evalForOfSet_dangling (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty} (a i : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (env : Env TT Γ) (w : World TT)
    (h : w.heap.get? (.set t, a) = none) :
    exec (evalForOfSet I P a i body env) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalForOfSet.eq_1]; simp only [exec_bind, exec_readSet, h]

/-! Array methods with a callback read the array first. -/

@[simp] theorem evalBuiltin_arrSort_dangling (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (rest : Vals TT _)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrSort t) (.cons (.arr a) rest)) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalBuiltin.eq_def]; simp only [exec_bind, exec_readArr, Vals.a0_cons, Val.arrAddr_arr, h]

@[simp] theorem evalBuiltin_arrMap_dangling (I : Impl) (P : Program TT) {t u : Ty} (a : Nat) (rest : Vals TT _)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrMap t u) (.cons (.arr a) rest)) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalBuiltin.eq_def]; simp only [exec_bind, exec_readArr, Vals.a0_cons, Val.arrAddr_arr, h]

@[simp] theorem evalBuiltin_arrFilter_dangling (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (rest : Vals TT _)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrFilter t) (.cons (.arr a) rest)) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalBuiltin.eq_def]; simp only [exec_bind, exec_readArr, Vals.a0_cons, Val.arrAddr_arr, h]

@[simp] theorem evalBuiltin_arrForEach_dangling (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (rest : Vals TT _)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrForEach t) (.cons (.arr a) rest)) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalBuiltin.eq_def]; simp only [exec_bind, exec_readArr, Vals.a0_cons, Val.arrAddr_arr, h]

@[simp] theorem evalBuiltin_arrFind_dangling (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (rest : Vals TT _)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrFind t) (.cons (.arr a) rest)) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalBuiltin.eq_def]; simp only [exec_bind, exec_readArr, Vals.a0_cons, Val.arrAddr_arr, h]

@[simp] theorem evalBuiltin_arrFindIndex_dangling (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (rest : Vals TT _)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrFindIndex t) (.cons (.arr a) rest)) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalBuiltin.eq_def]; simp only [exec_bind, exec_readArr, Vals.a0_cons, Val.arrAddr_arr, h]

@[simp] theorem evalBuiltin_arrFindLast_dangling (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (rest : Vals TT _)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrFindLast t) (.cons (.arr a) rest)) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalBuiltin.eq_def]; simp only [exec_bind, exec_readArr, Vals.a0_cons, Val.arrAddr_arr, h]

@[simp] theorem evalBuiltin_arrFindLastIndex_dangling (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (rest : Vals TT _)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrFindLastIndex t) (.cons (.arr a) rest)) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalBuiltin.eq_def]; simp only [exec_bind, exec_readArr, Vals.a0_cons, Val.arrAddr_arr, h]

@[simp] theorem evalBuiltin_arrSome_dangling (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (rest : Vals TT _)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrSome t) (.cons (.arr a) rest)) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalBuiltin.eq_def]; simp only [exec_bind, exec_readArr, Vals.a0_cons, Val.arrAddr_arr, h]

@[simp] theorem evalBuiltin_arrEvery_dangling (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (rest : Vals TT _)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrEvery t) (.cons (.arr a) rest)) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalBuiltin.eq_def]; simp only [exec_bind, exec_readArr, Vals.a0_cons, Val.arrAddr_arr, h]

@[simp] theorem evalBuiltin_arrFlatMap_dangling (I : Impl) (P : Program TT) {t u : Ty} (a : Nat) (rest : Vals TT _)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrFlatMap t u) (.cons (.arr a) rest)) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalBuiltin.eq_def]; simp only [exec_bind, exec_readArr, Vals.a0_cons, Val.arrAddr_arr, h]

@[simp] theorem evalBuiltin_arrReduce_dangling (I : Impl) (P : Program TT) {t u : Ty} (a : Nat) (rest : Vals TT _)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrReduce t u) (.cons (.arr a) rest)) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalBuiltin.eq_def]; simp only [exec_bind, exec_readArr, Vals.a0_cons, Val.arrAddr_arr, h]

@[simp] theorem evalBuiltin_arrReduce1_dangling (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (rest : Vals TT _)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrReduce1 t) (.cons (.arr a) rest)) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalBuiltin.eq_def]; simp only [exec_bind, exec_readArr, Vals.a0_cons, Val.arrAddr_arr, h]

@[simp] theorem evalBuiltin_arrReduceRight_dangling (I : Impl) (P : Program TT) {t u : Ty} (a : Nat) (rest : Vals TT _)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrReduceRight t u) (.cons (.arr a) rest)) w = some (.error (.panic "dangling reference"), w) := by
  rw [evalBuiltin.eq_def]; simp only [exec_bind, exec_readArr, Vals.a0_cons, Val.arrAddr_arr, h]

/-! ## Bench lemmas (difftool block, 10-24)

### String literals

A comparison of two string literals (`JSStr.ofString "sub" == JSStr.ofString "div"`, also as a
proposition) is evaluated: the UTF-16 encodings are compared by the kernel, as by `decide`. The
narrowing of a string-literal union (`enumToStr` of a concrete enum value, then `===` against the
members of the narrower union) leaves exactly such comparisons. -/

/-! ### Position arguments of strings within the ECMAScript maximum length

A String has at most `2^53 - 1` code units (ECMA-262 6.1.4); the allocated-arguments statement of
strictts-diff states it for string arguments (`hl : s.length < 2 ^ 53`). These forms of
`Prim.intArg_ofNat` / `Prim.posArg_ofNat` let `simp` discharge their side condition with that
hypothesis. -/

@[simp] theorem Prim.intArg_ofNat_lt {n : Nat} (len : Nat) (h : n < 2 ^ 53) :
    Prim.intArg (F64.ofNat n) len = n :=
  Prim.intArg_ofNat len (Nat.le_of_lt h)

@[simp] theorem Prim.posArg_ofNat_lt {n : Nat} (len : Nat) (h : n < 2 ^ 53) :
    Prim.posArg (F64.ofNat n) len = min n len :=
  Prim.posArg_ofNat len (Nat.le_of_lt h)

/-- The position of an element of an explicit list, when it reduces to a numeral (`ts_enum_cases`
leaves `["add", "div"].get ⟨0 + 1, _⟩`, which `simp` turns into `["add", "div"][↑1]`). -/
def listLitIndex? (l i : Lean.Expr) : Lean.Meta.MetaM (Option Lean.Expr) := do
  let some (_, elems) := l.listLit? | return none
  -- `simp` runs at reducible transparency; the position (`Fin.val` of a numeral) needs instances
  let some k := (← Lean.Meta.withDefault (Lean.Meta.reduce i)).rawNatLit? | return none
  return elems[k]?

open Lean Meta Simp in
simproc [simp, ts_sym] reduceListGetLit (List.get _ _) := fun e => do
  let_expr List.get _ l i := e | return .continue
  let some r ← listLitIndex? l (← mkAppM ``Fin.val #[i]) | return .continue
  return .done { expr := r }

open Lean Meta Simp in
simproc [simp, ts_sym] reduceListGetElemLit (@GetElem.getElem (List _) Nat _ _ _ _ _ _) := fun e => do
  let_expr GetElem.getElem _ _ _ _ _ l i _ := e | return .continue
  let some r ← listLitIndex? l i | return .continue
  return .done { expr := r }

open Lean Meta Simp in
simproc [simp, ts_sym] reduceOfStringBEq (@BEq.beq JSStr _ (JSStr.ofString _) (JSStr.ofString _)) := fun e => do
  let_expr BEq.beq _ _ x y := e | return .continue
  let_expr JSStr.ofString a := x | return .continue
  let_expr JSStr.ofString b := y | return .continue
  let .lit (.strVal sa) := a | return .continue
  let .lit (.strVal sb) := b | return .continue
  let r := toExpr (JSStr.ofString sa == JSStr.ofString sb)
  return .done { expr := r, proof? := some (← mkDecideProof (← mkEq e r)) }

open Lean Meta Simp in
simproc [simp, ts_sym] reduceOfStringEq (@Eq JSStr (JSStr.ofString _) (JSStr.ofString _)) := fun e => do
  let_expr Eq _ x y := e | return .continue
  let_expr JSStr.ofString a := x | return .continue
  let_expr JSStr.ofString b := y | return .continue
  let .lit (.strVal sa) := a | return .continue
  let .lit (.strVal sb) := b | return .continue
  if JSStr.ofString sa == JSStr.ofString sb then
    return .done { expr := mkConst ``True, proof? := some (← mkEqTrue (← mkDecideProof e)) }
  else
    return .done { expr := mkConst ``False, proof? := some (← mkEqFalse (← mkDecideProof (mkNot e))) }

/-! ### Flag loops (`found = false; for (x of xs) if (p x) found = true` is `xs.some(p)`)

`ts_summarize` turns such a loop into an `Array.foldl` whose step sets the flag. `Arrays.lean` has
the folds for a Boolean test (`if p x = true`); these are for a decidable proposition (`simp` turns
a string `===` into `x.toStr = s`). `Conv.svz_*` give the comparison behind `includes` for the
types where SameValueZero is strict equality. -/

theorem foldl_flag_true_dec_list {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] (b : Bool) :
    l.foldl (fun s x => if p x then Val.bool (TT := TT) true else s) (Val.bool b) =
      Val.bool (b || l.any fun x => decide (p x)) := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.any_cons]
    by_cases h : p x
    · simp only [h, ↓reduceIte, decide_true, Bool.true_or, Bool.or_true]
      rw [ih]; simp
    · simp only [h, ↓reduceIte, decide_false, Bool.false_or]
      exact ih b

/-- A loop that sets a flag when an element satisfies `p` computes `xs.some(p)`. -/
@[simp] theorem foldl_flag_true_dec {α : Type} (xs : Array α) (p : α → Prop) [DecidablePred p] (b : Bool) :
    xs.foldl (fun s x => if p x then Val.bool (TT := TT) true else s) (Val.bool b) =
      Val.bool (b || xs.any fun x => decide (p x)) := by
  rw [← Array.foldl_toList, foldl_flag_true_dec_list, Array.any_toList]

theorem foldl_flag_false_dec_list {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] (b : Bool) :
    l.foldl (fun s x => if p x then Val.bool (TT := TT) false else s) (Val.bool b) =
      Val.bool (b && l.all fun x => !decide (p x)) := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.all_cons]
    by_cases h : p x
    · simp only [h, ↓reduceIte, decide_true, Bool.not_true, Bool.false_and, Bool.and_false]
      rw [ih]; simp
    · simp only [h, ↓reduceIte, decide_false, Bool.not_false, Bool.true_and]
      exact ih b

/-- A loop that clears a flag when an element satisfies `p` computes `xs.every(x => !p(x))`. -/
@[simp] theorem foldl_flag_false_dec {α : Type} (xs : Array α) (p : α → Prop) [DecidablePred p] (b : Bool) :
    xs.foldl (fun s x => if p x then Val.bool (TT := TT) false else s) (Val.bool b) =
      Val.bool (b && xs.all fun x => !decide (p x)) := by
  rw [← Array.foldl_toList, foldl_flag_false_dec_list, Array.all_toList]

/-- The flag loops with an equality test, stated with `==` (the form of `includes` and `===`
after `Conv.svz_*` / `Conv.strictEq_*`). -/
@[simp high] theorem foldl_flag_true_eq {α β : Type} [DecidableEq β] (xs : Array α) (f : α → β) (c : β)
    (b : Bool) :
    xs.foldl (fun s x => if f x = c then Val.bool (TT := TT) true else s) (Val.bool b) =
      Val.bool (b || xs.any fun x => f x == c) :=
  foldl_flag_true_dec xs (fun x => f x = c) b

@[simp high] theorem foldl_flag_false_eq {α β : Type} [DecidableEq β] (xs : Array α) (f : α → β) (c : β)
    (b : Bool) :
    xs.foldl (fun s x => if f x = c then Val.bool (TT := TT) false else s) (Val.bool b) =
      Val.bool (b && xs.all fun x => !(f x == c)) :=
  foldl_flag_false_dec xs (fun x => f x = c) b

/-- SameValueZero (`includes`, `Map`/`Set` keys) is strict equality on strings, booleans and
bigints. -/
@[simp, ts_sym] theorem Conv.svz_str (x y : Val TT .str) : Conv.svz .str x y = (x.toStr == y.toStr) := rfl
@[simp, ts_sym] theorem Conv.svz_bool (x y : Val TT .bool) : Conv.svz .bool x y = (x.toBool == y.toBool) := rfl
@[simp, ts_sym] theorem Conv.svz_bigint (x y : Val TT .bigint) : Conv.svz .bigint x y = (x.toBig == y.toBig) := rfl

/-! ### Loop fusion (`for (x of xs) a = f(a, x); for (x of xs) b = g(b, x)` is one loop)

Two summarized loops over the same array, or one loop updating two variables, leave folds over
pairs of accumulators in which each component reads only its own accumulator. `foldlPairSplit`
(a simproc) splits such a fold into a pair of folds, so that the fused and the separate loops
reach the same terms. -/

theorem foldl_pair_split {α β γ : Type} (xs : Array α) (f : β → α → β) (g : γ → α → γ) (a : β) (b : γ) :
    xs.foldl (fun s x => (f s.1 x, g s.2 x)) (a, b) = (xs.foldl f a, xs.foldl g b) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList, ← Array.foldl_toList]
  generalize xs.toList = l
  induction l generalizing a b with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons]; exact ih (f a x) (g b x)

/-- A fold whose step keeps the accumulator is the initial value. -/
@[simp] theorem foldl_keep {α β : Type} (xs : Array α) (c : β) : xs.foldl (fun s _ => s) c = c := by
  rw [← Array.foldl_toList]
  generalize xs.toList = l
  induction l with
  | nil => rfl
  | cons x l ih => simpa using ih

open Lean Meta Simp in
/-- `xs.foldl (fun s x => (A, B)) (a, b)` with `A` mentioning `s` only as `s.1` and `B` only as
`s.2` is `(xs.foldl (fun s₁ x => A) a, xs.foldl (fun s₂ x => B) b)` (`foldl_pair_split`). -/
simproc [simp] foldlPairSplit (Array.foldl _ (Prod.mk _ _) _ _ _) := fun e => do
  let_expr Array.foldl α βγ f init xs start stop := e | return .continue
  let_expr Prod β γ := βγ | return .continue
  let_expr Prod.mk _ _ a b := init | return .continue
  unless (← isDefEq start (mkNatLit 0)) do return .continue
  unless (← isDefEq stop (← mkAppM ``Array.size #[xs])) do return .continue
  let .lam _ _ (.lam _ _ _ _) _ := f | return .continue
  let some (f', g') ← lambdaTelescope f fun ps body => do
      let #[s, x] := ps | return none
      let_expr Prod.mk _ _ A B := body | return none
      let piece (proj : Name) (ty : Lean.Expr) (C : Lean.Expr) : MetaM (Option Lean.Expr) :=
        withLocalDeclD `acc ty fun acc => do
          let C' := C.replace fun t =>
            if t.isAppOfArity proj 3 && t.appArg! == s then some acc else none
          if C'.containsFVar s.fvarId! then return none
          return some (← mkLambdaFVars #[acc, x] C')
      let some f' ← piece ``Prod.fst β A | return none
      let some g' ← piece ``Prod.snd γ B | return none
      return some (f', g')
    | return .continue
  let pf ← mkAppM ``foldl_pair_split #[xs, f', g', a, b]
  let size ← mkAppM ``Array.size #[xs]
  let rhs ← mkAppM ``Prod.mk #[← mkAppM ``Array.foldl #[f', a, xs, mkNatLit 0, size],
    ← mkAppM ``Array.foldl #[g', b, xs, mkNatLit 0, size]]
  let _ := α
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint pf (← mkEq e rhs)) }

/-! ### Counted join loops (`for (i = 0; i < xs.length; i++) { if (i > 0) s += sep; s += xs[i] }`)

`ts_summarize` turns the counted loop into a fold over `List.finRange xs.length` with a string
accumulator `Val.str …`, the element read as `Val.toStr.match_1 … xs[i] …` and the test `i > 0`
as a double comparison. `foldl_val_str` takes the accumulator out of `Val.str`,
`toStr_match_ite` pushes the read into the `if`, `F64.ofNat_fin_gt_zero` turns the test into
`0 < i` (indices of arrays shorter than `2^32`), `foldl_finRange_sep` is the separator loop, and
`ofFn_toStr_getElem` its list of parts, the one `join` reads. -/

/-- A fold whose accumulator is always a string value. -/
@[simp] theorem foldl_val_str {α : Type} (l : List α) (f : Val TT .str → α → JSStr) (t : JSStr) :
    l.foldl (fun s i => Val.str (f s i)) (Val.str t) = Val.str (l.foldl (fun t i => f (Val.str t) i) t) := by
  induction l generalizing t with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons]; exact ih (f (Val.str t) x)

/-- Reading the string of an `if`: the read of each branch. -/
@[simp] theorem toStr_match_ite (c : Prop) [Decidable c] (a b : Val TT .str) :
    Val.toStr.match_1 (fun _ => JSStr) (if c then a else b) (fun s => s) =
      if c then Val.toStr.match_1 (fun _ => JSStr) a (fun s => s)
      else Val.toStr.match_1 (fun _ => JSStr) b (fun s => s) := by
  by_cases h : c <;> simp only [h, ↓reduceIte]

/-- `i > 0` for an index `i` of an array shorter than `2^32`. -/
@[simp] theorem F64.ofNat_fin_gt_zero {n : Nat} (i : Fin n) (hn : n < 2 ^ 32) :
    (F64.ofNat (i : Nat)).gt (F64.ofNat 0) = decide (0 < (i : Nat)) := by
  have hi := i.isLt
  show (F64.ofNat 0).lt (F64.ofNat (i : Nat)) = _
  rw [F64.ofNat_eq_ofInt, F64.ofNat_eq_ofInt, F64.lt_ofInt (by simp only [Safe]; omega)
    (by simp only [Safe]; omega)]
  simp

theorem foldl_ofFn {α β : Type} {n : Nat} (g : Fin n → α) (F : β → α → β) (a : β) :
    (List.ofFn g).foldl F a = (List.finRange n).foldl (fun t i => F t (g i)) a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.finRange_succ, List.foldl_cons, List.foldl_cons, List.foldl_map]
    exact ih (fun i => g i.succ) (F a (g 0))

/-- The separator loop: the parts `g 0, …, g (n - 1)` joined by `sep`, as `join` computes it. -/
@[simp] theorem foldl_finRange_sep {n : Nat} (g : Fin n → JSStr) (sep : JSStr) :
    (List.finRange n).foldl (fun t (i : Fin n) => (if 0 < i.val then t ++ sep else t) ++ g i) JSStr.empty =
      match List.ofFn g with
      | [] => JSStr.empty
      | p :: ps => ps.foldl (fun acc q => acc ++ sep ++ q) p := by
  cases n with
  | zero => simp
  | succ n =>
    rw [List.finRange_succ, List.foldl_cons, List.foldl_map, List.ofFn_succ]
    simp only [Fin.val_zero, Nat.lt_irrefl, ↓reduceIte, JSStr.empty_append, Fin.val_succ,
      Nat.zero_lt_succ]
    rw [foldl_ofFn]

open Lean Meta Simp in
/-- `List.ofFn f` over `Fin n` with `n` reducing to `0` (e.g. the size of the empty array literal,
which `simp` cannot rewrite inside the type of `f`) is `[]`. -/
simproc [simp] reduceOfFnZero (List.ofFn _) := fun e => do
  let_expr List.ofFn α n _ := e | return .continue
  unless (← withDefault (reduce n)).rawNatLit? == some 0 do return .continue
  return .done { expr := ← mkAppOptM ``List.nil #[α] }

/-- The parts of an array of strings, read by position, are the parts `join` reads (a `↓` lemma:
it must see the reads `c[i]` before `simp` rewrites them). -/
@[simp ↓] theorem ofFn_toStr_getElem (c : Array (Val TT .str)) :
    List.ofFn (fun i : Fin c.size => Val.toStr.match_1 (fun _ => JSStr) c[(i : Nat)] (fun s => s)) =
      c.toList.map Val.toStr := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_ofFn, List.getElem_map, Array.getElem_toList]

/-! ### Integral values in a small range -/

namespace F64

/-- The magnitude of an integral finite double, as its integer part times `2^1074`. -/
theorem mag_eq_intMag_mul {x : Fin64} (h : x.fracMag = 0) : x.mag = x.intMag * 2 ^ 1074 := by
  rw [Fin64.intMag_eq]
  exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ((Fin64.fracMag_eq_zero_iff x).1 h))).symm

/-- An integral double `n` with `¬ (n < 0)` and `¬ (n > m)` (`m ≤ 2^53`) is `-0` or one of
`0, …, m`: input validation `Number.isInteger(n) && n >= 0 && n <= m` leaves `m + 2` concrete
cases. -/
theorem int_range_cases {n : F64} {m : Nat} (hm : m ≤ 2 ^ 53) (h1 : n.isInteger = true)
    (h2 : n.lt (ofNat 0) = false) (h3 : (ofNat m).lt n = false) :
    n = zero true ∨ ∃ k, k ≤ m ∧ n = ofNat k := by
  rcases n with _ | b | x
  · simp [isInteger, toInt?] at h1
  · simp [isInteger, toInt?] at h1
  have hf : x.fracMag = 0 := by
    simp only [isInteger, toInt?] at h1
    by_cases hne : x.fracMag = 0
    · exact hne
    · simp [hne] at h1
  have hmag := mag_eq_intMag_mul hf
  have hpos : (0 : Int) < ((2 ^ 1074 : Nat) : Int) := pow1074_pos
  obtain ⟨ym, hym, hymn, hymm⟩ := ofInt_spec (m : Int) (by simp only [Safe]; omega)
  rw [ofNat_eq_ofInt, hym, lt_fin_fin, decide_eq_false_iff_not, Fin64.sval_eq ym m hymn hymm] at h3
  rw [ofNat_zero_eq, lt_fin_fin, decide_eq_false_iff_not,
    show (⟨false, 0, -1074, Or.inr ⟨by decide, rfl⟩⟩ : Fin64).sval = 0 by simp [Fin64.sval, Fin64.mag]] at h2
  have hsv : x.sval = (if x.neg then -((x.intMag : Int) * ((2 ^ 1074 : Nat) : Int))
      else (x.intMag : Int) * ((2 ^ 1074 : Nat) : Int)) := by
    simp only [Fin64.sval, hmag, Int.natCast_mul]
  cases hneg : x.neg
  · simp only [hneg, Bool.false_eq_true, ↓reduceIte] at hsv
    rw [hsv] at h3
    have hk : x.intMag ≤ m := by
      have := (Int.mul_le_mul_right hpos).1 (Int.not_lt.1 h3)
      omega
    right
    refine ⟨x.intMag, hk, ?_⟩
    obtain ⟨yk, hyk, hykn, hykm⟩ := ofInt_spec (x.intMag : Int) (by simp only [Safe]; omega)
    rw [ofNat_eq_ofInt, hyk]
    congr 1
    apply fin_eq_of_sval_eq
    · rw [Fin64.sval_eq yk _ hykn hykm, hsv]
    · rw [hneg, hykn]; simp
  · simp only [hneg, ↓reduceIte] at hsv
    rw [hsv] at h2
    have h0 : x.intMag = 0 := by
      by_cases hne : x.intMag = 0
      · exact hne
      · have : (0 : Int) < (x.intMag : Int) * ((2 ^ 1074 : Nat) : Int) :=
          Int.mul_pos (by omega) hpos
        omega
    left
    have hman : x.man = 0 := (Fin64.mag_eq_zero_iff x).1 (by simp only [hmag, h0, Nat.zero_mul])
    have hexp := Fin64.exp_of_man_lt (x := x) (by omega)
    show F64.fin x = mkFin true 0 (-1074)
    rw [mkFin_eq (Or.inr ⟨by decide, rfl⟩)]
    congr 1
    apply fin_eq_of_sval_eq
    · rw [hsv, h0]; simp only [Fin64.sval, Fin64.mag, Nat.zero_mul, Int.natCast_zero, Int.zero_mul, Int.neg_zero, ite_self]
    · exact hneg


/-! ### Starts of counted loops (block of partial, item 3)

The start of a counted loop that is not a literal, such as `Math.min(Math.floor(n), 50)` or a
validated argument, is `ofNat` of its value when the loop's condition holds there (`natVal`,
`eq_ofNat_natVal` from `int_range_cases`, `floor_min_gt`); `ts_summarize` splits on the
condition at the start (`evalLoop_start_split`). -/

/-- The natural number an integral double in `[0, 2^53]` denotes (`0` for the other doubles). -/
def natVal (x : F64) : Nat := (x.toInt?.getD 0).toNat

theorem natVal_ofNat {k : Nat} (h : k ≤ 2 ^ 53) : (ofNat k).natVal = k := by
  simp [natVal, ofNat_eq_ofInt, toInt?_ofInt (show Safe (k : Int) by simp only [Safe]; omega)]

/-- An integral double in `[0, m]` (`m ≤ 2^53`) other than `-0` is `ofNat` of its value. -/
theorem eq_ofNat_natVal {x : F64} {m : Nat} (hm : m ≤ 2 ^ 53) (h1 : x.isInteger = true)
    (h2 : x.lt (ofNat 0) = false) (h3 : (ofNat m).lt x = false) (h0 : x ≠ zero true) :
    x = ofNat x.natVal ∧ x.natVal ≤ m := by
  rcases int_range_cases hm h1 h2 h3 with h | ⟨k, hk, rfl⟩
  · exact absurd h h0
  · rw [natVal_ofNat (by omega)]
    exact ⟨rfl, hk⟩

theorem intMag_lt_of_fracMag_ne {x : Fin64} (h : x.fracMag ≠ 0) : x.intMag < 2 ^ 53 := by
  have hv := x.valid
  unfold Fin64.fracMag at h
  unfold Fin64.intMag
  split
  · exfalso
    apply h
    have : (-x.exp).toNat = 0 := by omega
    simp [this]
  · have : x.man >>> (-x.exp).toNat ≤ x.man := Nat.shiftRight_le _ _
    omega

theorem isInteger_ofInt {n : Int} (h : Safe n) : (ofInt n).isInteger = true := by
  simp [isInteger, toInt?_ofInt h]

/-- `Math.floor` of a finite double is integral. -/
theorem isInteger_floor_fin (x : Fin64) : (floor (.fin x)).isInteger = true := by
  by_cases h : x.fracMag = 0
  · simp [floor, h, isInteger, toInt?]
  · have hb := intMag_lt_of_fracMag_ne h
    by_cases hn : x.neg = true
    · have : floor (.fin x) = ofInt (-((x.intMag + 1 : Nat) : Int)) := by
        simp only [floor, h, hn, ofInt, ite_false, ite_true]
        congr 1
        simp
      rw [this]
      exact isInteger_ofInt (by simp only [Safe]; omega)
    · have : floor (.fin x) = ofInt (x.intMag : Int) := by
        rw [← ofNat_eq_ofInt]
        simp [floor, h, hn, ofNat]
      rw [this]
      exact isInteger_ofInt (by simp only [Safe]; omega)

theorem isInteger_ofNat {m : Nat} (hm : m ≤ 2 ^ 53) : (ofNat m).isInteger = true := by
  rw [ofNat_eq_ofInt]
  exact isInteger_ofInt (by simp only [Safe]; omega)

theorem zero_lt_negZero : (ofNat 0).lt (zero true) = false := by decide

theorem lt_nan_right (x : F64) : x.lt .nan = false := by cases x <;> rfl
theorem lt_negInf_right (x : F64) : x.lt (.inf true) = false := by
  cases x with
  | nan => rfl
  | inf a => cases a <;> rfl
  | fin _ => rfl

theorem floor_min_key {x : F64} {m c : Nat} (hm : m ≤ 2 ^ 53)
    (h : (ofNat c).lt ((floor x).min (ofNat m)) = true) :
    ((floor x).min (ofNat m)).isInteger = true ∧ (ofNat m).lt ((floor x).min (ofNat m)) = false := by
  obtain ⟨y, hy, -, -⟩ := ofInt_spec (m : Int) (by simp only [Safe]; omega)
  have hy' : ofNat m = .fin y := by rw [ofNat_eq_ofInt]; exact hy
  have hiy : (F64.fin y).isInteger = true := hy' ▸ isInteger_ofNat hm
  rw [hy'] at h ⊢
  have hyn : (F64.fin y).isNaN = false := rfl
  rcases x with _ | b | x
  · -- NaN: the minimum is NaN, never above `c`
    simp only [floor, F64.min] at h
    simp [isNaN, lt_nan_right] at h
  · cases b
    · -- `+∞`: the minimum is `m`
      have hl1 : (F64.inf false).lt (.fin y) = false := rfl
      have hl2 : (F64.fin y).lt (.inf false) = true := rfl
      have hin : (F64.inf false).isNaN = false := rfl
      simp only [floor, F64.min, hin, hyn, Bool.or_false, Bool.false_eq_true, ite_false, hl1, hl2, ite_true]
      exact ⟨hiy, lt_irrefl _⟩
    · -- `-∞`: the minimum is `-∞`, never above `c`
      have hl : (F64.inf true).lt (.fin y) = true := rfl
      have hin : (F64.inf true).isNaN = false := rfl
      simp only [floor, F64.min, hin, hyn, Bool.or_false, Bool.false_eq_true, ite_false, hl, ite_true] at h
      rw [lt_negInf_right] at h
      exact absurd h (by decide)
  · -- finite: the floor is integral
    have hi := isInteger_floor_fin x
    have hfn : (floor (.fin x)).isNaN = false := by
      cases e : floor (.fin x) with
      | nan => rw [e] at hi; simp [isInteger, toInt?] at hi
      | _ => rfl
    simp only [F64.min, hfn, hyn, Bool.or_false, Bool.false_eq_true, ite_false]
    by_cases hl : (floor (.fin x)).lt (.fin y) = true
    · simp only [hl, ite_true]
      exact ⟨hi, not_lt_of_le (le_of_lt hl)⟩
    · simp only [hl, Bool.false_eq_true, ite_false]
      by_cases hl' : (F64.fin y).lt (floor (.fin x)) = true
      · simp only [hl', ite_true]
        exact ⟨hiy, lt_irrefl _⟩
      · simp only [hl', Bool.false_eq_true, ite_false]
        split
        · exact ⟨hi, by simpa using hl'⟩
        · exact ⟨hiy, lt_irrefl _⟩

/-- `Math.min(Math.floor(x), m)` above a natural `c`: an integral double, so `ofNat` of its value,
at most `m` (the start of `for (let i = Math.min(Math.floor(n), m); i > c; i--)`). -/
theorem floor_min_gt {x : F64} {m c : Nat} (hm : m ≤ 2 ^ 53) (hc : c ≤ 2 ^ 53)
    (h : (ofNat c).lt ((floor x).min (ofNat m)) = true) :
    (floor x).min (ofNat m) = ofNat ((floor x).min (ofNat m)).natVal ∧
      ((floor x).min (ofNat m)).natVal ≤ m := by
  have h0 : (ofNat 0).lt ((floor x).min (ofNat m)) = true :=
    lt_of_le_of_lt (by rw [le_ofNat (by omega) hc]; simp) h
  have hneg : ((floor x).min (ofNat m)).lt (ofNat 0) = false := not_lt_of_le (le_of_lt h0)
  have hz : (floor x).min (ofNat m) ≠ zero true := by
    intro e
    rw [e, zero_lt_negZero] at h0
    exact absurd h0 (by decide)
  have key := floor_min_key hm h
  exact eq_ofNat_natVal hm key.1 hneg key.2 hz


/-- `floor_min_gt` with the bound folded in: the start is `ofNat (min k m)`, so a loop from it has
at most `m + 1` positions without a separate bound. -/
theorem floor_min_eq_ofNat_min {x : F64} {m c : Nat} (hm : m ≤ 2 ^ 53) (hc : c ≤ 2 ^ 53)
    (h : (ofNat c).lt ((floor x).min (ofNat m)) = true) :
    (floor x).min (ofNat m) = ofNat (Min.min ((floor x).min (ofNat m)).natVal m) := by
  have h' := floor_min_gt hm hc h
  rw [Nat.min_eq_left h'.2]
  exact h'.1

end F64

/-! ### Heap lookups past a write to a cell of another kind

`heap_get_insert_kind_ne` has the side condition `k ≠ k'`, which `simp only [ts_sym]` cannot
discharge (it lacks `ne_eq`/`not_false_eq_true`), so a read of an object after a write to an array
stayed stuck in symbolic execution (`this.items.push(x)` then `this.items`). The simproc decides
the side condition on the constructors (`decide`; the arguments of different constructors are
never compared). -/

open Lean Meta Simp in
simproc [simp, ts_sym] heapGetInsertKindNe (Std.ExtDHashMap.get? (Std.ExtDHashMap.insert _ _ _) _) := fun e => do
  let n := e.getAppNumArgs
  unless e.isAppOf ``Std.ExtDHashMap.get? && n ≥ 2 do return .continue
  let m := e.getArg! (n - 2)
  let key := e.getArg! (n - 1)
  let nm := m.getAppNumArgs
  unless m.isAppOf ``Std.ExtDHashMap.insert && nm ≥ 3 do return .continue
  let h := m.getArg! (nm - 3)
  let kIns := m.getArg! (nm - 2)
  let c := m.getArg! (nm - 1)
  let_expr Prod.mk _ _ k a := kIns | return .continue
  let_expr Prod.mk _ _ k' a' := key | return .continue
  let some ck := k.getAppFn.constName? | return .continue
  let some ck' := k'.getAppFn.constName? | return .continue
  unless ck != ck' && (ck.getPrefix == ``HKind) && (ck'.getPrefix == ``HKind) do return .continue
  let hk ← mkDecideProof (← mkAppM ``Ne #[k, k'])
  let pf ← mkAppOptM ``heap_get_insert_kind_ne #[none, h, k, k', a, a', c, hk]
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  return .visit { expr := rhs, proof? := some pf }

/-! ### Counted loop over an array after a `push`

`this.items.push(x)` followed by `for (i = 0; i < this.items.length; i++) … this.items[i]`: the
summary folds over the positions `0 … c.size` of `c.push x` (the bound reaches the summary as
`c.size + 1`); that fold is the fold over `c` followed by one step on `x`, the form the `for … of`
summary of the same array takes. -/

theorem foldl_finRange_push {α β : Type} (c : Array β) (x : β) (F : α → β → α) (s0 : α) :
    (List.finRange (c.size + 1)).foldl
        (fun s (i : Fin (c.size + 1)) => F s ((c.push x)[(i : Nat)]'(by simp [Array.size_push]))) s0 =
      F (c.foldl F s0) x := by
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [Fin.val_castSucc, Fin.val_last, Array.getElem_push_eq, List.foldl_cons, List.foldl_nil]
  congr 1
  have h : ∀ (i : Fin c.size), (c.push x)[(i : Nat)]'(by simp [Array.size_push]; omega) = c[(i : Nat)] :=
    fun i => Array.getElem_push_lt i.isLt
  simp only [h]
  have hm : (List.finRange c.size).map (fun (i : Fin c.size) => c[(i : Nat)]) = c.toList := by
    apply List.ext_getElem <;> simp
  rw [← Array.foldl_toList, ← hm, List.foldl_map]

open Lean Meta Simp in
/-- `foldl_finRange_push` for a step that reads the array at the position anywhere in its body
(the step's function is read off by abstracting the reads `(c.push x)[i]`). -/
simproc [simp] foldlFinRangePush (List.foldl _ _ (List.finRange _)) := fun e => do
  let_expr List.foldl _ _ f s0 l := e | return .continue
  let_expr List.finRange n := l | return .continue
  let_expr HAdd.hAdd _ _ _ _ sz one := n | return .continue
  unless (← instantiateMVars one).nat? == some 1 || one.rawNatLit? == some 1 do return .continue
  let_expr Array.size _ c := sz | return .continue
  let .lam _ _ (.lam _ _ _ _) _ := f | return .continue
  let some (F, x) ← lambdaTelescope f fun ps body => do
      let #[s, i] := ps | return none
      -- the reads `(c.push x)[↑i]`
      let isRead (t : Lean.Expr) : Bool :=
        t.isAppOfArity ``GetElem.getElem 8 && (t.getArg! 5).isAppOfArity ``Array.push 3 &&
          (t.getArg! 5).getArg! 1 == c && (t.getArg! 6).isAppOfArity ``Fin.val 2 && (t.getArg! 6).getArg! 1 == i
      let some rd := body.find? isRead | return none
      let x := (rd.getArg! 5).getArg! 2
      let elemTy ← inferType rd
      withLocalDeclD `y elemTy fun y => do
        let body' := body.replace fun t => if isRead t then some y else none
        if body'.containsFVar i.fvarId! then return none
        return some (← mkLambdaFVars #[s, y] body', x)
    | return .continue
  let pf ← mkAppM ``foldl_finRange_push #[c, x, F, s0]
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  let rhs ← Core.betaReduce rhs
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint pf (← mkEq e rhs)) }

/-! ### Maps with explicit entries (a `Map` literal) evaluate

`new Map([["s", 1], …])` builds its entries with `JSMap.set`; on explicit entry lists `set` and
`get?` run by these equations (an abstract map is untouched: the left-hand sides need explicit
entries), the key comparisons by `Conv.svz_*` and the literal simprocs. -/

namespace JSMap
variable {K V : Type}

@[simp] theorem get?_mk_nil (eq : K → K → Bool) (k : K) : (⟨[]⟩ : JSMap K V).get? eq k = none := rfl

@[simp] theorem get?_mk_cons_none (eq : K → K → Bool) (rest : List (Option (K × V))) (k : K) :
    (⟨none :: rest⟩ : JSMap K V).get? eq k = (⟨rest⟩ : JSMap K V).get? eq k := rfl

@[simp] theorem get?_mk_cons_some (eq : K → K → Bool) (k' : K) (v : V) (rest : List (Option (K × V))) (k : K) :
    (⟨some (k', v) :: rest⟩ : JSMap K V).get? eq k = if eq k' k = true then some v else (⟨rest⟩ : JSMap K V).get? eq k :=
  rfl

@[simp] theorem updAux_nil (eq : K → K → Bool) (k : K) (v : V) : updAux eq k v [] = none := rfl

@[simp] theorem updAux_cons_none (eq : K → K → Bool) (k : K) (v : V) (rest : List (Option (K × V))) :
    updAux eq k v (none :: rest) = (updAux eq k v rest).map (none :: ·) := rfl

@[simp] theorem updAux_cons_some (eq : K → K → Bool) (k : K) (v : V) (k' : K) (v' : V) (rest : List (Option (K × V))) :
    updAux eq k v (some (k', v') :: rest) =
      if eq k' k = true then some (some (k', v) :: rest) else (updAux eq k v rest).map (some (k', v') :: ·) := rfl

/-- `set` on explicit entries: an update in place, or an entry appended. -/
@[simp] theorem set_mk_of_updAux_none (eq : K → K → Bool) (l : List (Option (K × V))) (k : K) (v : V)
    (h : updAux eq k v l = none) : (⟨l⟩ : JSMap K V).set eq k v = ⟨l ++ [some (k, v)]⟩ := by
  simp [set, h]

@[simp] theorem set_mk_of_updAux_some (eq : K → K → Bool) (l l' : List (Option (K × V))) (k : K) (v : V)
    (h : updAux eq k v l = some l') : (⟨l⟩ : JSMap K V).set eq k v = ⟨l'⟩ := by
  simp [set, h]

end JSMap

/-! ### Reversing a string: `s.split("").reverse().join("")` against a backwards `charAt` loop

The backwards loop's summary is a fold over the positions with the loop's only mutable slot in a
pair `(Val.str …, ())`, which `simp` turns into `List.foldr` (`List.foldl_reverse`).
`foldrFstUnit` (a simproc, `foldr_fst_unit`) takes the slot out of the pair and `foldr_val_str`
the string out of `Val.str`. `join` of the reversed parts is `ps.foldl (· ++ ·) p` once the parts
list is split as `ps.reverse ++ [p]`; `foldl_append_eq_foldr` equates it with the loop's fold.
These are not `@[simp]`: the observational statements of the difftool pass them explicitly. -/

theorem foldr_fst_unit {α β : Type} (G : α → β → β) (a : β) (l : List α) :
    (l.foldr (fun x y => (G x y.1, ())) (a, ())).1 = l.foldr G a := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.foldr_cons, ih]

open Lean Meta Simp in
/-- `(l.foldr (fun x y => (B, ())) (a, ())).1` with `B` reading `y` only as `y.1` is
`l.foldr (fun x z => B[y.1 := z]) a` (`foldr_fst_unit`). -/
simproc_decl foldrFstUnit (Prod.fst (List.foldr _ (Prod.mk _ _) _)) := fun e => do
  let_expr Prod.fst _ _ p := e | return .continue
  let_expr List.foldr _ _ f init l := p | return .continue
  let_expr Prod.mk β _ a u := init | return .continue
  let isUnit (t : Lean.Expr) : MetaM Bool := return (← whnfR t).isConstOf ``PUnit.unit
  unless ← isUnit u do return .continue
  let .lam _ _ (.lam _ _ _ _) _ := f | return .continue
  let some G ← lambdaTelescope f fun ps body => do
      let #[x, y] := ps | return none
      let_expr Prod.mk _ _ B u2 := body | return none
      unless ← isUnit u2 do return none
      withLocalDeclD `acc β fun acc => do
        let B' := B.replace fun t => if t.isAppOfArity ``Prod.fst 3 && t.appArg! == y then some acc else none
        if B'.containsFVar y.fvarId! then return none
        return some (← mkLambdaFVars #[x, acc] B')
    | return .continue
  let pf ← mkAppM ``foldr_fst_unit #[G, a, l]
  let rhs ← mkAppM ``List.foldr #[G, a, l]
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint pf (← mkEq e rhs)) }

/-- A right fold whose accumulator is always a string value. -/
theorem foldr_val_str {α : Type} (l : List α) (f : α → Val TT .str → JSStr) (t : JSStr) :
    l.foldr (fun i s => Val.str (f i s)) (Val.str t) = Val.str (l.foldr (fun i t => f i (Val.str t)) t) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.foldr_cons, ih]

/-- `join("")` of the reversed parts `l.map F` (split as `ps.reverse ++ [p]`) appends the parts
from the last to the first. -/
theorem foldl_append_of_map_eq {α : Type} (F : α → JSStr) (l : List α) (p : JSStr) (ps : List JSStr)
    (h : l.map F = ps.reverse ++ [p]) :
    ps.foldl (fun acc q => acc ++ q) p = l.foldr (fun x t => t ++ F x) JSStr.empty := by
  have h2 : (l.map F).reverse = p :: ps := by rw [h]; simp
  have h3 : l.foldr (fun x t => t ++ F x) JSStr.empty =
      ((l.map F).reverse).foldl (fun acc q => acc ++ q) JSStr.empty := by
    simp only [List.foldl_reverse, List.foldr_map]
  rw [h3, h2]
  simp

/-- `foldl_append_of_map_eq` as a rewrite of the equation (all its variables occur on the left;
the hypothesis is discharged from the context). -/
theorem foldl_append_eq_foldr {α : Type} (F : α → JSStr) (l : List α) (p : JSStr) (ps : List JSStr)
    (h : l.map F = ps.reverse ++ [p]) :
    (ps.foldl (fun acc q => acc ++ q) p = l.foldr (fun x t => t ++ F x) JSStr.empty) = True := by
  rw [foldl_append_of_map_eq F l p ps h]; simp

section Tests

/-! The goals of the refactorings, as symbolic execution leaves them (literals as written). -/

example (a b : F64) : a.min b = b.min a ∧ a.max b = b.max a := by simp [F64.min_comm, F64.max_comm]
example (a : F64) : (a.bor 0 / 2).floor = (a.bor 0).sar 1 := by simp
example (s p : JSStr) : (F64.ofInt (s.indexOf p (Prim.posArg 0 s.length))).ge 0 =
    s.includes p (Prim.posArg 0 s.length) := by simp [F64.ge_eq_le]
example (s p : JSStr) (hp : p.length ≤ 2 ^ 53) :
    (s.slice (Prim.intArg 0 s.length) (Prim.intArg (F64.ofNat p.length) s.length) == p) =
      s.startsWith p (Prim.posArg 0 s.length) := by simp [hp]

/-! `±0` and NaN by evaluation: `Math.min(-0, +0)` is `-0` in either order, `Math.max` `+0`. -/

example : (F64.zero true).min (F64.zero false) = F64.zero true ∧
    (F64.zero false).min (F64.zero true) = F64.zero true := by decide
example : (F64.zero true).max (F64.zero false) = F64.zero false ∧
    (F64.zero false).max (F64.zero true) = F64.zero false := by decide
example : F64.nan.min (F64.ofNat 1) = .nan ∧ (F64.ofNat 1).min .nan = .nan := by decide
example : (F64.ofInt (-3) / 2).floor = F64.ofInt (-2) ∧ (F64.ofInt (-3)).sar 1 = F64.ofInt (-2) := by decide

example (I : Impl) (P : Program TT) {t u : Ty} (a : Nat)
    (f : Val TT (.fn (.cons u (.cons t (.cons .num (.cons (.arr t) .nil)))) u)) (init : Val TT u)
    (w : World TT) (h : w.heap.get? (.arr t, a) = none) :
    exec (evalBuiltin I P (.arrReduce t u) (.cons (.arr a) (.cons f (.cons init .nil)))) w =
      some (.error (.panic "dangling reference"), w) := by simp [h]

example : (JSStr.ofString "sub" == JSStr.ofString "div") = false := by simp
example : (JSStr.ofString "sub" == JSStr.ofString "sub") = true := by simp only [reduceOfStringBEq]

example (h : 0 + 1 + 1 + 1 < 4)
    (h' : JSStr.ofString (["add", "div", "mul", "sub"].get (⟨0 + 1 + 1 + 1, h⟩ : Fin 4)) = JSStr.ofString "div") :
    False := by simp at h'
example (h : 0 + 1 < ["x", "y"].length) : ["x", "y"].get ⟨0 + 1, h⟩ = "y" := by simp

example (s p : JSStr) (hp : p.length < 2 ^ 53) :
    (s.slice (Prim.intArg 0 s.length) (Prim.intArg (F64.ofNat p.length) s.length) == p) =
      s.startsWith p (Prim.posArg 0 s.length) := by simp [hp]

example (xs : Array Nat) : xs.foldl (fun s x => (s.1 + x, s.2 * x)) (0, 1) =
    (xs.foldl (fun a x => a + x) 0, xs.foldl (fun b x => b * x) 1) := by simp only [foldlPairSplit]
example (xs : Array Nat) (c : Nat) : (xs.foldl (fun s x => (s.1 + x, s.2)) (0, c)).2 = c := by simp

example (w : World TT) (b a : Nat) (v : Array (Val TT .num)) :
    (w.heap.insert (HKind.arr .num, b) v).get? (HKind.obj "Cart" [.arr .num, .num], a) =
      w.heap.get? (HKind.obj "Cart" [.arr .num, .num], a) := by simp only [ts_sym]

example (c : Array Nat) (x : Nat) :
    (List.finRange (c.size + 1)).foldl (fun s (i : Fin (c.size + 1)) => s + 2 * (c.push x)[(i : Nat)]'(by simp)) 0 =
      c.foldl (fun s y => s + 2 * y) 0 + 2 * x := by simp only [foldlFinRangePush]

-- bench pair 32 (the goal `ts_auto` leaves for the observational statement)
example {n : Nat} (s : JSStr) (p : JSStr) (ps : List JSStr)
    (h : List.map (Val.toStr ∘ fun (i : Fin n) => (Val.str (s.charAt ↑i) : Val TT .str)) (List.finRange n) =
      ps.reverse ++ [p]) :
    (Val.str (ps.foldl (fun acc q => acc ++ q) p) : Val TT .str) =
      (List.foldr (fun (i : Fin n) (y : Val TT .str × Unit) =>
        (Val.str (Val.toStr.match_1 (fun _ => JSStr) y.1 (fun t => t) ++ s.charAt ↑i), ()))
        (Val.str JSStr.empty, ()) (List.finRange n)).1 := by
  simp_all [foldrFstUnit, foldr_val_str, foldl_append_eq_foldr, Function.comp_def]

end Tests

end StrictTS
