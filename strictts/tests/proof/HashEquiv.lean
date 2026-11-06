import StrictTS.Proof.Tactics

open StrictTS JS

/-!
Int32 refactoring proved with `bv_decide`:

```ts
function stepShift(h: number, c: number): number {
  h = (h ^ c) >>> 0;
  h = (h + (h << 1) + (h << 4) + (h << 7) + (h << 8) + (h << 24)) >>> 0;
  return h;
}
function stepImul(h: number, c: number): number {
  return Math.imul(h ^ c, 16777619) >>> 0;
}
```
Both are FNV-1a steps (16777619 = 2^24 + 2^8 + 2^7 + 2^4 + 2 + 1); they agree on **all** numbers,
including NaN, ±Infinity and non-integers, because every operand goes through ToInt32.
-/

def TT0 : TypeTable := ⟨fun _ => .undef, fun _ => .nil⟩

abbrev N (x : Nat) {Γ : Ctx} : Expr TT0 Γ .num := .lit (.num (F64.ofNat x))
abbrev bin (op : NumBin) {Γ : Ctx} (a b : Expr TT0 Γ .num) : Expr TT0 Γ .num :=
  .prim (.numBin op) (.cons a (.cons b .nil))

abbrev Γh : Ctx := [⟨.num, true⟩, ⟨.num, false⟩]
abbrev hV : Expr TT0 Γh .num := .var .here
abbrev cV : Expr TT0 Γh .num := .var (.there .here)

def stepShiftDef : FunDef TT0 :=
  { name := "stepShift", args := .cons .num (.cons .num .nil), ret := .num,
    lam := .sync Γh rfl
      (.seq (.assign .here (bin .shr (bin .bxor hV cV) (N 0)))
      (.seq (.assign .here (bin .shr
          (bin .add (bin .add (bin .add (bin .add (bin .add hV (bin .shl hV (N 1))) (bin .shl hV (N 4)))
            (bin .shl hV (N 7))) (bin .shl hV (N 8))) (bin .shl hV (N 24))) (N 0)))
      (.seq (.ret hV) .nil))) }

def stepImulDef : FunDef TT0 :=
  { name := "stepImul", args := .cons .num (.cons .num .nil), ret := .num,
    lam := .sync [⟨.num, false⟩, ⟨.num, false⟩] rfl
      (.seq (.ret (bin .shr (bin .imul (bin .bxor (.var .here) (.var (.there .here))) (N 16777619)) (N 0))) .nil) }

def prog : Program TT0 := { funs := [stepShiftDef, stepImulDef], globals := [], main := .nil }
def stepShiftRef : FunRef (.cons .num (.cons .num .nil)) .num := ⟨0, "stepShift"⟩
def stepImulRef : FunRef (.cons .num (.cons .num .nil)) .num := ⟨1, "stepImul"⟩


theorem stepImul_call (I : Impl) (vs : Vals TT0 [.num, .num]) :
    callFun I prog stepImulRef vs = applyLam I prog stepImulDef.lam .nil vs := by
  rw [callFun.eq_1]; rfl
theorem stepShift_call (I : Impl) (vs : Vals TT0 [.num, .num]) :
    callFun I prog stepShiftRef vs = applyLam I prog stepShiftDef.lam .nil vs := by
  rw [callFun.eq_1]; rfl

/-- Bounds that make every intermediate sum an exact (safe) integer. -/
theorem safe_toNat (b : BitVec 32) : F64.Safe (b.toNat : Int) := by
  have := b.isLt; simp only [F64.Safe]; omega
theorem safe_toInt (b : BitVec 32) : F64.Safe b.toInt := F64.safe_toInt b

theorem step_equiv (I : Impl) (h c : F64) (w : World TT0) :
    exec (callFun I prog stepShiftRef (.cons (.num h) (.cons (.num c) .nil))) w =
      exec (callFun I prog stepImulRef (.cons (.num h) (.cons (.num c) .nil))) w := by
  rw [stepShift_call, stepImul_call]
  simp only [ts_sym, stepShiftDef, stepImulDef, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq,
    Val.num.injEq, and_true]
  -- int32 normal form: every operand goes through ToInt32 ...
  generalize hb : F64.toInt32 h ^^^ F64.toInt32 c = b
  simp only [F64.bxor, hb, F64.shr, F64.shl, F64.imul, F64.ofNat_eq_ofInt,
    F64.toInt32_ofInt32, F64.toInt32_ofUint32]
  simp (disch := (simp only [F64.Safe]; omega)) only [F64.toInt32_ofInt]
  simp only [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.zero_mod, BitVec.ushiftRight_zero, F64.ofUint32_eq, F64.ofInt32_eq]
  -- ... the sum of six int32-sized terms is an exact integer below 2^53 ...
  have h0 := b.isLt
  have l1 := BitVec.toInt_lt (x := b <<< 1); have g1 := BitVec.le_toInt (x := b <<< 1)
  have l4 := BitVec.toInt_lt (x := b <<< 4); have g4 := BitVec.le_toInt (x := b <<< 4)
  have l7 := BitVec.toInt_lt (x := b <<< 7); have g7 := BitVec.le_toInt (x := b <<< 7)
  have l8 := BitVec.toInt_lt (x := b <<< 8); have g8 := BitVec.le_toInt (x := b <<< 8)
  have l24 := BitVec.toInt_lt (x := b <<< 24); have g24 := BitVec.le_toInt (x := b <<< 24)
  simp (disch := (simp only [F64.Safe]; omega)) only [F64.add_ofInt, F64.toInt32_ofInt]
  -- ... so both sides are the same 32-bit value
  congr 2
  rw [BitVec.toNat_inj]
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  clear h0 l1 g1 l4 g4 l7 g7 l8 g8 l24 g24 hb
  bv_decide

/-- The same proof with the packaged tactics. -/
theorem step_equiv' (I : Impl) (h c : F64) (w : World TT0) :
    exec (callFun I prog stepShiftRef (.cons (.num h) (.cons (.num c) .nil))) w =
      exec (callFun I prog stepImulRef (.cons (.num h) (.cons (.num c) .nil))) w := by
  rw [stepShift_call, stepImul_call]
  ts_sym [stepShiftDef, stepImulDef]
  ts_int32

#print axioms step_equiv
