import EquivLean.Demo.XLang.TinyRegex.CPartial

/-!
# musl string functions: partial-correctness rules for `for` loops

The `for` counterparts of `holds_while_name` / `holds_while_inv` (`TinyRegex/CPartial.lean`): a
`cir.for` loop in a hypothesis `h : (evalFor ctx c b s cl σ₀).holds K`, by an invariant and no
variant (partial correctness).
-/

namespace EquivLean.Cir

open CIR

/-- Name the state at the head of a `for` loop in a hypothesis. -/
theorem holds_for_name {ctx : Ctx} {c b s : Region} {cl : Option (CleanupKind × Region)} {σ₀ : State}
    {K : Step × State → Prop} (hs : (evalFor ctx c b s cl σ₀).holds K) :
    ∃ t, t = σ₀ ∧ (evalFor ctx c b s cl t).holds K := ⟨σ₀, rfl, hs⟩

/-- A `for` loop in a hypothesis, by an invariant (partial correctness, no variant). -/
theorem holds_for_inv {ctx : Ctx} {c b s : Region} {cl : Option (CleanupKind × Region)} {σ₀ : State}
    {K : Step × State → Prop} (hs : (evalFor ctx c b s cl σ₀).holds K) (Inv : State → Prop)
    (Post : Step × State → Prop) (h0 : Inv σ₀)
    (hstep : ∀ σ, Inv σ → pholds (forIter ctx c b s cl σ) (fun r => match r with
      | .inl o => Post o
      | .inr σ' => Inv σ')) :
    ∃ a, Post a ∧ K a := by
  have hl := pholds_loop (loopShape_for ctx c b s cl) (terminates_for ctx c b s cl) Inv Post
    (fun σ hσ r hr => by have h := hstep σ hσ r hr; cases r <;> exact h) σ₀ h0
  obtain ⟨a, -, hp, hk⟩ := holds_pspec_elim hs hl
  exact ⟨a, hp, hk⟩

open Lean Meta

attribute [cir_exec] Option.isSome_some Option.isSome_none

def addrOfLoc (ctx : Ctx) (m : Mem) (b : Nat) (path : List PathElem) : Int :=
  match (m.blocks b).bind fun blk => ctx.absPos? blk.ty path with
  | some q =>
    if b + 1 < ctx.segLimit ∧ q < 2 ^ ctx.segBits then (b + 1) * 2 ^ ctx.segBits + q
    else ctx.otherAddr b path
  | none => ctx.otherAddr b path

@[cir_exec] theorem addrOf?_loc (ctx : Ctx) (m : Mem) (b : Nat) (path : List PathElem) :
    ctx.addrOf? m (.loc b path) = some (addrOfLoc ctx m b path) := by
  simp only [Ctx.addrOf?, addrOfLoc]
  rcases (m.blocks b).bind fun blk => ctx.absPos? blk.ty path with _ | q
  · rfl
  · by_cases h : b + 1 < ctx.segLimit ∧ q < 2 ^ ctx.segBits <;> simp [h]

theorem intOfAddr_u64_of_ptrBytes8 {ctx : Ctx} (hp : ctx.mod.ptrBytes = 8) (a : Int) :
    ctx.intOfAddr false 64 a = wrap false 64 a := by
  unfold Ctx.intOfAddr
  have hbits : ctx.ptrBits = 64 := by simp [Ctx.ptrBits, hp]
  simp only [hbits, Nat.lt_irrefl, ↓reduceIte, wrap, Bool.false_and, Bool.false_eq_true]
  rw [Int.emod_emod]

simproc ↓ [cir_exec] reduceIntOfAddr (Ctx.intOfAddr _ false 64 _) := fun e => do
  unless e.isAppOfArity ``Ctx.intOfAddr 4 do return .continue
  let ctx := e.getArg! 0
  let a := e.getArg! 3
  let pbe ← mkAppM ``Module.ptrBytes #[← mkAppM ``Ctx.mod #[ctx]]
  let pb ← whnfD pbe
  let some 8 := pb.rawNatLit? | return .continue
  let hp ← mkExpectedTypeHint (← mkEqRefl (mkNatLit 8)) (← mkEq pbe (mkNatLit 8))
  let pf ← mkAppM ``intOfAddr_u64_of_ptrBytes8 #[hp, a]
  let res ← mkAppM ``wrap #[mkConst ``Bool.false, mkNatLit 64, a]
  return .visit { expr := res, proof? := some pf }

def addrOfChar (b i : Nat) : Int :=
  if b + 1 < 2 ^ 29 ∧ i < 2 ^ 32 then ((b : Int) + 1) * 4294967296 + (i : Int)
  else 2 ^ 62 + (((b : Int) + 1) * 4294967296 + ((i : Int) + 1)) % 2 ^ 62

theorem addrOfLoc_char_eq {ctx : Ctx} {m : Mem} {b i : Nat} {kd : BlockKind} {es : Bool} {tlen : Nat} {val : Val}
    (hp : ctx.mod.ptrBytes = 8)
    (hblk : m.blocks b = some ⟨kd, true, .array (.int es 8) tlen, val⟩) :
    addrOfLoc ctx m b [.idx i] = addrOfChar b i := by
  unfold addrOfLoc addrOfChar
  have hpos : ctx.absPos? (.array (.int es 8) tlen) [.idx i] = some i := by
    simp [Ctx.absPos?, Ctx.sizeAlign]
  have hlim : ctx.segLimit = 2 ^ 29 := by simp [Ctx.segLimit, hp]
  have hbits : ctx.segBits = 32 := by simp [Ctx.segBits, hp]
  simp only [hblk, Option.bind_some, hpos, hlim, hbits]
  by_cases h : b + 1 < 2 ^ 29 ∧ i < 2 ^ 32
  · simp only [h, and_self, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte, Ctx.otherAddr, hp, List.foldl, PathElem.index]; omega

simproc ↓ [cir_exec] reduceAddrOfLoc (addrOfLoc _ _ _ _) := fun e => do
  unless e.isAppOfArity ``addrOfLoc 4 do return .continue
  let ctx := e.getArg! 0
  let m := e.getArg! 1
  let b := e.getArg! 2
  let path := e.getArg! 3
  let_expr List.cons _ pe nil := path | return .continue
  unless nil.isAppOfArity ``List.nil 1 do return .continue
  let_expr PathElem.idx i := pe | return .continue
  let pbe ← mkAppM ``Module.ptrBytes #[← mkAppM ``Ctx.mod #[ctx]]
  let pb ← whnfD pbe
  let some 8 := pb.rawNatLit? | return .continue
  let hp ← mkExpectedTypeHint (← mkEqRefl (mkNatLit 8)) (← mkEq pbe (mkNatLit 8))
  let look ← mkAppM ``Mem.blocks #[m, b]
  let (rhs, hblk) ← CIR.simpEqOf look
  let_expr Option.some _ blk := rhs | return .continue
  let_expr MemBlock.mk _ alive ty _ := blk | return .continue
  unless alive.isConstOf ``Bool.true do return .continue
  let_expr Ty.array et _ := ty | return .continue
  let_expr Ty.int _ w := et | return .continue
  let some 8 := (← whnfD w).rawNatLit? | return .continue
  let pf ← mkAppOptM ``addrOfLoc_char_eq #[some ctx, some m, some b, some i, none, none, none, none, some hp, some hblk]
  let res ← mkAppM ``addrOfChar #[b, i]
  return .done { expr := res, proof? := some pf }

theorem tmod8_addrOfChar (b i : Nat) :
    (wrap false 64 (addrOfChar b i)).tmod 8 =
      ((if b + 1 < 2 ^ 29 ∧ i < 2 ^ 32 then i else i + 1 : Nat) : Int) % 8 := by
  unfold addrOfChar
  by_cases h : b + 1 < 2 ^ 29 ∧ i < 2 ^ 32
  · simp only [h, and_self, ↓reduceIte, wrap, Bool.false_and, Bool.false_eq_true]
    have h1 : 0 ≤ (((b : Int) + 1) * 4294967296 + (i : Int)) % (2 : Int) ^ 64 := Int.emod_nonneg _ (by decide)
    rw [Int.tmod_eq_emod_of_nonneg h1, Int.emod_emod_of_dvd _ (by decide : (8 : Int) ∣ 2 ^ 64)]
    omega
  · simp only [h, ↓reduceIte, wrap, Bool.false_and, Bool.false_eq_true]
    have h1 : 0 ≤ (2 ^ 62 + (((b : Int) + 1) * 4294967296 + ((i : Int) + 1)) % 2 ^ 62) % (2 : Int) ^ 64 :=
      Int.emod_nonneg _ (by decide)
    rw [Int.tmod_eq_emod_of_nonneg h1, Int.emod_emod_of_dvd _ (by decide : (8 : Int) ∣ 2 ^ 64)]
    have h2 : (2 ^ 62 + (((b : Int) + 1) * 4294967296 + ((i : Int) + 1)) % 2 ^ 62) % 8 =
        ((((b : Int) + 1) * 4294967296 + ((i : Int) + 1)) % 2 ^ 62) % 8 := by omega
    rw [h2, Int.emod_emod_of_dvd _ (by decide : (8 : Int) ∣ 2 ^ 62)]
    omega

theorem tmod4_addrOfChar_flat {b : Nat} (hb : b + 1 < 2 ^ 29) (i : Nat) (hi : i < 2 ^ 32 := by decide) :
    (wrap false 64 (addrOfChar b i)).tmod 4 = (i : Int) % 4 := by
  unfold addrOfChar
  simp only [hb, hi, and_self, ↓reduceIte, wrap, Bool.false_and, Bool.false_eq_true]
  have h1 : 0 ≤ (((b : Int) + 1) * 4294967296 + (i : Int)) % (2 : Int) ^ 64 := Int.emod_nonneg _ (by decide)
  rw [Int.tmod_eq_emod_of_nonneg h1, Int.emod_emod_of_dvd _ (by decide : (4 : Int) ∣ 2 ^ 64)]
  omega

theorem tmod4_addrOfChar_other {b : Nat} (hb : ¬(b + 1 < 2 ^ 29)) (i : Nat) :
    (wrap false 64 (addrOfChar b i)).tmod 4 = ((i : Int) + 1) % 4 := by
  unfold addrOfChar
  simp only [hb, false_and, ↓reduceIte, wrap, Bool.false_and, Bool.false_eq_true]
  have h1 : 0 ≤ (2 ^ 62 + (((b : Int) + 1) * 4294967296 + ((i : Int) + 1)) % 2 ^ 62) % (2 : Int) ^ 64 :=
    Int.emod_nonneg _ (by decide)
  rw [Int.tmod_eq_emod_of_nonneg h1, Int.emod_emod_of_dvd _ (by decide : (4 : Int) ∣ 2 ^ 64)]
  have h2 : (2 ^ 62 + (((b : Int) + 1) * 4294967296 + ((i : Int) + 1)) % 2 ^ 62) % 4 =
      ((((b : Int) + 1) * 4294967296 + ((i : Int) + 1)) % 2 ^ 62) % 4 := by omega
  rw [h2, Int.emod_emod_of_dvd _ (by decide : (4 : Int) ∣ 2 ^ 62)]
  omega

end EquivLean.Cir
