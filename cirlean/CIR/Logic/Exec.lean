import Lean
import CIR.Logic.WP

/-!
  Rewrite rules for symbolic execution.

  The simp set `cir_exec` contains everything needed to run straight-line
  CIR code on a symbolic state: unfolding of op lists, blocks, regions and
  single operations, the SSA environment, memory, typed loads and stores, and
  integer arithmetic. Loops (`evalFor`, `evalWhile`, `evalDo`) and calls
  (`evalCall`) are left folded; they are handled by `CIR.Logic.Rules`.
-/

namespace CIR

/-! ### Point updates (unfolded only when applied) -/

@[simp] theorem upd_apply {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) (x : α) :
    upd f a b x = if x = a then b else f x := rfl

theorem killRange_apply (lo hi : Nat) (bs : Nat → Option MemBlock) (b : Nat) :
    killRange lo hi bs b = if lo ≤ b ∧ b < hi then
      (match bs b with
       | some blk => if blk.kind = .stack then none else some blk
       | none => none)
    else bs b := rfl

/-! ### Normal form of memory after region exits -/

/-- Nothing was allocated. -/
@[simp] theorem killRange_self (n : Nat) (bs : Nat → Option MemBlock) : killRange n n bs = bs := by
  funext b; simp only [killRange]; split <;> first | omega | rfl

/-- Blocks older than the region are unaffected by its exit. -/
theorem killRange_upd_old {lo hi k : Nat} {bs : Nat → Option MemBlock} {x : Option MemBlock}
    (h : k < lo) : killRange lo hi (upd bs k x) = upd (killRange lo hi bs) k x := by
  funext b; simp only [killRange, upd]
  by_cases hb : b = k
  · subst hb; simp; omega
  · simp [hb]

/-- A block below the range keeps its contents. -/
theorem killRange_of_lt {lo hi : Nat} {bs : Nat → Option MemBlock} {b : Nat} (h : b < lo) :
    killRange lo hi bs b = bs b := by
  simp [killRange_apply]; omega

/-- A block above the range keeps its contents. -/
theorem killRange_of_ge {lo hi : Nat} {bs : Nat → Option MemBlock} {b : Nat} (h : hi ≤ b) :
    killRange lo hi bs b = bs b := by
  simp [killRange_apply]; omega

/-- A scope exit as a filter on the block looked up (one occurrence of the
lookup: unfolding `killRange` with `killRange_apply` duplicates it). -/
theorem killRange_eq_bind (lo hi : Nat) (bs : Nat → Option MemBlock) (b : Nat) :
    killRange lo hi bs b =
      (bs b).bind fun blk => if lo ≤ b ∧ b < hi ∧ blk.kind = .stack then none else some blk := by
  simp only [killRange]
  cases h : bs b with
  | none => simp
  | some blk =>
    simp only [Option.bind_some]
    by_cases h1 : lo ≤ b ∧ b < hi
    · by_cases h2 : blk.kind = .stack <;> simp [h1, h2]
    · simp [h1]; intro h2 h3; exact absurd ⟨h2, h3⟩ h1

/-- The initial memory has no block from `next` on. -/
theorem killRange_base {m : Mem} {lo hi : Nat} (hwf : m.WF) (h : m.next ≤ lo) :
    killRange lo hi m.blocks = m.blocks := by
  funext b; simp only [killRange]
  split
  · rename_i hb; rw [hwf b (by omega)]
  · rfl

/-! ### Scope exits pushed into the writes (keeping memory terms small)

After a region exits, its stack blocks are dead: a write to one of them can
be forgotten (`none`), other writes stay, and below a well-formed memory the
exit has no effect. `normKillRange` and `dropDeadNone`
(`CIR/Tactic/Simprocs.lean`) apply these to the state, so that later lookups
do not pass through the exits of every region and callee. -/

theorem killRange_upd_hi {lo hi k : Nat} {bs : Nat → Option MemBlock} {x : Option MemBlock}
    (h : hi ≤ k) : killRange lo hi (upd bs k x) = upd (killRange lo hi bs) k x := by
  funext b; simp only [killRange, upd]
  by_cases hb : b = k
  · subst hb; simp; omega
  · simp [hb]

theorem killRange_upd_stack {lo hi k : Nat} {bs : Nat → Option MemBlock} {a : Bool} {t : Ty} {x : Val}
    (h1 : lo ≤ k) (h2 : k < hi) :
    killRange lo hi (upd bs k (some ⟨.stack, a, t, x⟩)) = upd (killRange lo hi bs) k none := by
  funext b; simp only [killRange, upd]
  by_cases hb : b = k
  · subst hb; simp [h1, h2]
  · simp [hb]

theorem killRange_upd_keep {lo hi k : Nat} {bs : Nat → Option MemBlock} {kd : BlockKind} {a : Bool}
    {t : Ty} {x : Val} (hk : kd ≠ .stack) :
    killRange lo hi (upd bs k (some ⟨kd, a, t, x⟩)) = upd (killRange lo hi bs) k (some ⟨kd, a, t, x⟩) := by
  funext b; simp only [killRange, upd]
  by_cases hb : b = k
  · subst hb; simp [hk]
  · simp [hb]

theorem killRange_upd_none {lo hi k : Nat} {bs : Nat → Option MemBlock} :
    killRange lo hi (upd bs k none) = upd (killRange lo hi bs) k none := by
  funext b; simp only [killRange, upd]
  by_cases hb : b = k
  · subst hb; simp
  · simp [hb]

/-- Forgetting a block that was not there. -/
theorem upd_none_eq {f : Nat → Option MemBlock} {k : Nat} (h : f k = none) : upd f k none = f := by
  funext x; simp only [upd]; split
  · subst_vars; exact h.symm
  · rfl

/-- Keys at different offsets of one base differ (`h` by evaluation). -/
theorem add_ne_add_of_beq {t a b : Nat} (h : Nat.beq a b = false) : t + a ≠ t + b := by
  intro he
  exact Nat.ne_of_beq_eq_false h (Nat.add_left_cancel he)

theorem self_ne_add_of_beq {t b : Nat} (h : Nat.beq b 0 = false) : t ≠ t + b := by
  intro he
  exact Nat.ne_of_beq_eq_false h (by omega)

theorem add_ne_self_of_beq {t a : Nat} (h : Nat.beq a 0 = false) : t + a ≠ t := by
  intro he
  exact Nat.ne_of_beq_eq_false h (by omega)

theorem upd_apply_ne {α β : Type} [DecidableEq α] {f : α → β} {k k' : α} {v : β} (h : k ≠ k') :
    upd f k' v k = f k := by simp [upd, h]

theorem upd_apply_same {α β : Type} [DecidableEq α] (f : α → β) (k : α) (v : β) :
    upd f k v k = v := by simp [upd]

/-! ### In-place update of an existing key -/

theorem upd_upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (x y : β) :
    upd (upd f a x) a y = upd f a y := by
  funext z; simp only [upd]; split <;> rfl

theorem upd_comm {α β : Type} [DecidableEq α] (f : α → β) {a c : α} (x y : β) (h : a ≠ c) :
    upd (upd f c x) a y = upd (upd f a y) c x := by
  funext z; simp only [upd]
  by_cases h₁ : z = a <;> by_cases h₂ : z = c <;> simp_all

/-! ### The SSA environment -/

namespace State
variable (σ : State)

/-- Canonical form `⟨mem, env⟩` of states (used by `cir_exec`): superseded
memories and environments do not accumulate in the goal. -/
theorem set_eq (v : VId) (x : Val) : σ.set v x = ⟨σ.mem, upd σ.env v (some x), σ.names⟩ := rfl
theorem withMem_eq (m : Mem) : σ.withMem m = ⟨m, σ.env, σ.names⟩ := rfl

@[simp] theorem set_env (v : VId) (x : Val) : (σ.set v x).env = upd σ.env v (some x) := rfl
@[simp] theorem set_mem (v : VId) (x : Val) : (σ.set v x).mem = σ.mem := rfl
@[simp] theorem withMem_mem (m : Mem) : (σ.withMem m).mem = m := rfl
@[simp] theorem withMem_env (m : Mem) : (σ.withMem m).env = σ.env := rfl
@[simp] theorem mk_mem (m : Mem) (e : VId → Option Val) (n : List (String × Nat)) :
    (State.mk m e n).mem = m := rfl
@[simp] theorem mk_env (m : Mem) (e : VId → Option Val) (n : List (String × Nat)) :
    (State.mk m e n).env = e := rfl
@[simp] theorem mk_names (m : Mem) (e : VId → Option Val) (n : List (String × Nat)) :
    (State.mk m e n).names = n := rfl
@[simp] theorem set_names (v : VId) (x : Val) : (σ.set v x).names = σ.names := rfl
@[simp] theorem withMem_names (m : Mem) : (σ.withMem m).names = σ.names := rfl

@[simp] theorem get_eq (v : VId) : σ.get v = Res.ofOption "use of undefined SSA value" (σ.env v) := rfl

theorem getPtr_eq (v : VId) : σ.getPtr v = (σ.get v >>= fun x => match x with
    | .ptr p => pure p
    | _ => .ub "expected a pointer") := rfl
theorem getInt_eq (v : VId) : σ.getInt v = (σ.get v >>= fun x => match x with
    | .int i => pure i
    | _ => .ub "expected an integer") := rfl
theorem getBool_eq (v : VId) : σ.getBool v = (σ.get v >>= fun x => match x with
    | .bool b => pure b
    | _ => .ub "expected a bool") := rfl

@[simp] theorem bindArgs_nil : σ.bindArgs [] [] = .ok σ := rfl
@[simp] theorem bindArgs_cons (v : VId) (vs : List VId) (x : Val) (xs : List Val) :
    σ.bindArgs (v :: vs) (x :: xs) = (σ.set v x).bindArgs vs xs := rfl
/-- The variadic arguments of a call: a fresh block named `__va_args`. -/
@[simp] theorem bindArgs_extra (x : Val) (xs : List Val) :
    σ.bindArgs [] (x :: xs) =
      .ok { σ with
        mem := { blocks := upd σ.mem.blocks σ.mem.next
                   (some ⟨.stack, true, .array (.int true 64) (x :: xs).length, .arr (x :: xs)⟩),
                 next := σ.mem.next + 1 },
        names := ("__va_args", σ.mem.next) :: σ.names } := rfl
@[simp] theorem setResults_none : σ.setResults none [] = .ok σ := rfl
@[simp] theorem setResults_some (r : VId) (x : Val) : σ.setResults (some r) [x] = .ok (σ.set r x) := rfl

end State

/-! ### Memory and values -/

namespace Mem
variable (m : Mem)

@[simp] theorem alloc_eq (k : BlockKind) (ty : Ty) (v : Val) :
    m.alloc k ty v = (m.next, { blocks := upd m.blocks m.next (some ⟨k, true, ty, v⟩),
                                next := m.next + 1 }) := rfl
theorem setBlock_eq (b : Nat) (blk : MemBlock) : m.setBlock b blk = ⟨upd m.blocks b (some blk), m.next⟩ := rfl
theorem endScope_eq (lo : Nat) : m.endScope lo = ⟨killRange lo m.next m.blocks, m.next⟩ := rfl

@[simp] theorem setBlock_blocks (b : Nat) (blk : MemBlock) :
    (m.setBlock b blk).blocks = upd m.blocks b (some blk) := rfl
@[simp] theorem setBlock_next (b : Nat) (blk : MemBlock) : (m.setBlock b blk).next = m.next := rfl
@[simp] theorem mk_blocks (bs : Nat → Option MemBlock) (n : Nat) : (Mem.mk bs n).blocks = bs := rfl
@[simp] theorem mk_next (bs : Nat → Option MemBlock) (n : Nat) : (Mem.mk bs n).next = n := rfl
@[simp] theorem endScope_next (lo : Nat) : (m.endScope lo).next = m.next := rfl
@[simp] theorem endScope_blocks (lo : Nat) : (m.endScope lo).blocks = killRange lo m.next m.blocks := rfl

theorem live?_eq (b : Nat) : m.live? b = (match m.blocks b with
    | some blk => if blk.alive then some blk else none
    | none => none) := rfl

theorem read?_loc (b : Nat) (p : List PathElem) :
    m.read? (.loc b p) = (match m.live? b with
      | some blk => blk.val.get? p
      | none => none) := rfl

theorem write?_loc (b : Nat) (p : List PathElem) (w : Val) :
    m.write? (.loc b p) w = (match m.live? b with
      | some blk =>
        if blk.kind = .readonly then
          if (blk.val.get? p).all (Val.initBy · w) then
            match blk.val.set? p w with
            | some v' => some (m.setBlock b { blk with val := v' })
            | none => none
          else none
        else match blk.val.set? p w with
          | some v' => some (m.setBlock b { blk with val := v' })
          | none => none
      | none => none) := rfl

@[simp] theorem read?_null : m.read? .null = none := rfl
@[simp] theorem write?_null (w : Val) : m.write? .null w = none := rfl

end Mem

attribute [simp] Val.get? Val.set?
attribute [simp] List.mapM_cons List.mapM_nil

/-! ### Block ids

Fresh blocks are numbered `next`, `next + 1`, ... Offsets are normalised to
`n + k` with a literal `k`, so comparisons between block ids are decided by
simp without an arithmetic oracle. -/

attribute [simp] Nat.add_assoc

@[simp] theorem nat_self_eq_add (n k : Nat) : (n = n + k) ↔ k = 0 := by omega
@[simp] theorem nat_add_eq_self (n k : Nat) : (n + k = n) ↔ k = 0 := by omega
@[simp] theorem nat_add_le_self (n k : Nat) : (n + k ≤ n) ↔ k = 0 := by omega
@[simp] theorem nat_self_le_add (n k : Nat) : n ≤ n + k := by omega
@[simp] theorem nat_not_add_lt_self (n k : Nat) : ¬ (n + k < n) := by omega
@[simp] theorem nat_self_lt_add (n k : Nat) : (n < n + k) ↔ 0 < k := by omega

/-! ### Typed memory access and arithmetic -/

attribute [simp] loadTy storeTy fitsTy Ty.isScalar Mem.punnedAccess Ty.atPath Ty.accessCompatible
  Ctx.punnedMember Ctx.typedLoad Ctx.typedStore Ty.isChar Ty.isVoid Ty.hasBytes Ty.isAggregate Ctx.reachIn
  Ctx.reach? Ctx.castAligned Ctx.castCheck splitByte Ctx.reachTypeNone Ctx.reachNone

/-- Range checks are decided by an arithmetic discharger (see `cir_disch`). -/
theorem inRange_of_bounds {s : Bool} {w : Nat} {x : Int}
    (h : intMin s w ≤ x ∧ x ≤ intMax s w) : inRange s w x = true := by
  simp [inRange, h.1, h.2]
theorem not_inRange_of_bounds {s : Bool} {w : Nat} {x : Int}
    (h : x < intMin s w ∨ intMax s w < x) : inRange s w x = false := by
  simp only [inRange, Bool.and_eq_false_iff, decide_eq_false_iff_not, Int.not_le]
  exact h

/-- Conversions that keep the value (it is representable in the target type). -/
theorem wrap_of_bounds {s : Bool} {w : Nat} {x : Int} (hw : 0 < w)
    (h : intMin s w ≤ x ∧ x ≤ intMax s w) : wrap s w x = x := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  have hp : (2:Int) ^ (k + 1) = 2 ^ k * 2 := Int.pow_succ 2 k
  have hpos : (0:Int) < 2 ^ k := Int.pow_pos (by decide)
  simp only [intMin, intMax, Nat.add_sub_cancel] at h
  unfold wrap
  cases s with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h
    simp only [Bool.false_and, Bool.false_eq_true, ite_false]
    exact Int.emod_eq_of_lt h.1 (by omega)
  | true =>
    simp only [ite_true] at h
    simp only [Nat.add_sub_cancel, Bool.true_and, decide_eq_true_eq]
    by_cases hx : 0 ≤ x
    · rw [Int.emod_eq_of_lt hx (by omega)]
      split <;> omega
    · have hm : x % 2 ^ (k + 1) = x + 2 ^ (k + 1) := by
        rw [Int.emod_eq_add_self_emod]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [hm]
      split <;> omega

/-- A wrapped value is representable (so the range check of a store after
unsigned arithmetic always passes). -/
theorem inRange_wrap {s : Bool} {w : Nat} (x : Int) (hw : 0 < w) :
    inRange s w (wrap s w x) = true := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  have hp : (2:Int) ^ (k + 1) = 2 ^ k * 2 := Int.pow_succ 2 k
  have hpos : (0:Int) < 2 ^ k := Int.pow_pos (by decide)
  have h1 : 0 ≤ x % 2 ^ (k + 1) := Int.emod_nonneg _ (by omega)
  have h2 : x % 2 ^ (k + 1) < 2 ^ (k + 1) := Int.emod_lt_of_pos _ (by omega)
  unfold inRange wrap intMin intMax
  cases s with
  | false =>
    simp only [Bool.false_and, Bool.false_eq_true, ite_false, Bool.and_eq_true, decide_eq_true_eq]
    omega
  | true =>
    simp only [Nat.add_sub_cancel, Bool.true_and, decide_eq_true_eq, ite_true, Bool.and_eq_true]
    split <;> omega

/-- The result of a bitwise operation is representable. -/
theorem inRange_bitwise {s : Bool} {w : Nat} (f : BitVec w → BitVec w → BitVec w) (x y : Int)
    (hw : 0 < w) : inRange s w (bitwise s w f x y) = true := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  unfold inRange bitwise intMin intMax
  cases s with
  | false =>
    simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true, decide_eq_true_eq]
    have := BitVec.isLt (f (BitVec.ofInt (k + 1) x) (BitVec.ofInt (k + 1) y))
    constructor
    · exact Int.natCast_nonneg _
    · have h2 : ((2 ^ (k + 1) : Nat) : Int) = (2 : Int) ^ (k + 1) := by norm_cast
      omega
  | true =>
    simp only [ite_true, Nat.add_sub_cancel, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨BitVec.le_toInt _, by have := BitVec.toInt_lt (x := f (BitVec.ofInt (k + 1) x)
      (BitVec.ofInt (k + 1) y)); simp at this ⊢; omega⟩

theorem inRange_eq_true_iff {s : Bool} {w : Nat} {x : Int} :
    inRange s w x = true ↔ intMin s w ≤ x ∧ x ≤ intMax s w := by
  simp [inRange]
theorem inRange_eq_false_iff {s : Bool} {w : Nat} {x : Int} :
    inRange s w x = false ↔ x < intMin s w ∨ intMax s w < x := by
  simp only [inRange, Bool.and_eq_false_iff, decide_eq_false_iff_not, Int.not_le]

@[simp] theorem intMin_s8 : intMin true 8 = -128 := rfl
@[simp] theorem intMax_s8 : intMax true 8 = 127 := rfl
@[simp] theorem intMin_s16 : intMin true 16 = -32768 := rfl
@[simp] theorem intMax_s16 : intMax true 16 = 32767 := rfl
@[simp] theorem intMin_s32 : intMin true 32 = -2147483648 := rfl
@[simp] theorem intMax_s32 : intMax true 32 = 2147483647 := rfl
@[simp] theorem intMin_s64 : intMin true 64 = -9223372036854775808 := rfl
@[simp] theorem intMax_s64 : intMax true 64 = 9223372036854775807 := rfl
@[simp] theorem intMin_u (w : Nat) : intMin false w = 0 := rfl
@[simp] theorem intMax_u8 : intMax false 8 = 255 := rfl
@[simp] theorem intMax_u16 : intMax false 16 = 65535 := rfl
@[simp] theorem intMax_u32 : intMax false 32 = 4294967295 := rfl
@[simp] theorem intMax_u64 : intMax false 64 = 18446744073709551615 := rfl
attribute [simp] evalBinop evalUnop evalShift cmpInt evalCmp evalCast caseMatches runsCleanup finishRegion
attribute [simp] Ctx.initVal Ctx.constVal

/-! ### Deciding branch conditions

`ite_pos'` / `ite_neg'` are conditional rewrite rules: with an arithmetic
discharger (`simp (disch := omega) [ite_pos', ite_neg']`) every overflow and
range check whose outcome follows from the hypotheses is resolved during
symbolic execution. -/

/-- `if True then a else b = a` for any decidability instance. The core
lemmas `ite_true`/`ite_false` fix the instance and are proved by `rfl`, so
`simp` uses them as definitional steps: the kernel then has to evaluate the
instance actually present in the term (the original condition's, e.g. a
range check on a large literal), which can be arbitrarily expensive. These
versions are generic in the instance, so no evaluation is ever needed. -/
theorem ite_true_inst {α : Sort _} {inst : Decidable True} (a b : α) :
    @ite α True inst a b = a := match inst with
  | .isTrue _ => rfl
  | .isFalse h => absurd trivial h

theorem ite_false_inst {α : Sort _} {inst : Decidable False} (a b : α) :
    @ite α False inst a b = b := match inst with
  | .isTrue h => absurd h id
  | .isFalse _ => rfl

theorem ite_pos' {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]
theorem ite_neg' {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]
theorem dite_pos' {α : Sort _} {c : Prop} [Decidable c] {t : c → α} {e : ¬c → α} (h : c) :
    dite c t e = t h := by simp [h]
theorem dite_neg' {α : Sort _} {c : Prop} [Decidable c] {t : c → α} {e : ¬c → α} (h : ¬c) :
    dite c t e = e h := by simp [h]

/-- Data-dependent region choice (`cir.if`, `cir.ternary`). -/
@[simp] theorem evalRegion_ite (ctx : Ctx) {c : Prop} [Decidable c] (r₁ r₂ : Region) (args : List Val)
    (σ : State) :
    evalRegion ctx (if c then r₁ else r₂) args σ =
      if c then evalRegion ctx r₁ args σ else evalRegion ctx r₂ args σ := by
  split <;> rfl

attribute [simp] Res.holds_ite

/-! ### Unfolding the interpreter (loops and calls stay folded) -/

attribute [simp] evalSimple missingAggCheck endLifetime
attribute [simp] evalOps.eq_1 evalOps.eq_2 evalRegion.eq_1 evalRegion.eq_2 Exit.leaveMem

@[simp] theorem evalBlock_zero (ctx : Ctx) (params : List VId) (ops : List Op) (bs : List Block)
    (args : List Val) (σ : State) :
    evalBlock ctx (.mk params ops :: bs) 0 args σ = (do
      let σ ← σ.bindArgs params args
      let (s, σ) ← evalOps ctx ops σ
      match s with
      | .exit (.goto l) =>
        match labelBlock? l (.mk params ops :: bs) with
        | some j => evalBlock ctx (.mk params ops :: bs) j [] σ
        | none => pure (.goto l, σ)
      | .exit e => pure (e, σ)
      | .jump j vs => evalBlock ctx (.mk params ops :: bs) j vs σ
      | .next => .ub "fell off the end of a block") := by
  rw [evalBlock.eq_1]; rfl

/-- Calling a function with a body (and no library model) that is no destructor. -/
theorem evalCall_body {ctx : Ctx} {sym : String} {fd : FuncDecl} {body : Region} {args : List Val}
    {m : Mem} (hf : ctx.mod.findFunc? sym = some fd) (hm : fd.model = none)
    (hb : fd.body = some body) (hs : fd.special ≠ .dtor) :
    evalCall ctx sym args m = (do
      let (e, σ) ← evalRegion ctx body args ⟨m, fun _ => none, []⟩
      match e with
      | .ret v => pure (.ret v, σ.mem)
      | .exn x => if fd.nothrow then .ub "exception escaped a noexcept function" else pure (.exn x, σ.mem)
      | .halt n => pure (.halt n, σ.mem)
      | .longjmp t v => pure (.longjmp t v, σ.mem)
      | _ => .ub "function body exited without cir.return") := by
  rw [evalCall.eq_1, hf]; simp only [hm, hb, hs, if_false]; rfl

/-- Calling a destructor with a body: its return ends the object's lifetime (`endLifetime`). -/
theorem evalCall_dtor {ctx : Ctx} {sym : String} {fd : FuncDecl} {body : Region} {args : List Val}
    {m : Mem} (hf : ctx.mod.findFunc? sym = some fd) (hm : fd.model = none)
    (hb : fd.body = some body) (hs : fd.special = .dtor) :
    evalCall ctx sym args m = (do
      let (e, σ) ← evalRegion ctx body args ⟨m, fun _ => none, []⟩
      match e with
      | .ret v => pure (.ret v, endLifetime ctx args σ.mem)
      | .exn x => if fd.nothrow then .ub "exception escaped a noexcept function" else pure (.exn x, σ.mem)
      | .halt n => pure (.halt n, σ.mem)
      | .longjmp t v => pure (.longjmp t v, σ.mem)
      | _ => .ub "function body exited without cir.return") := by
  rw [evalCall.eq_1, hf]; simp only [hm, hb, hs, if_true]; rfl

/-- Calling a function with a library model. -/
theorem evalCall_model {ctx : Ctx} {sym : String} {fd : FuncDecl} {mdl : Model} {args : List Val}
    {m : Mem} (hf : ctx.mod.findFunc? sym = some fd) (hm : fd.model = some mdl) :
    evalCall ctx sym args m = Std.runModel ctx mdl args m := by
  rw [evalCall.eq_1, hf]; simp only [hm]

open Lean Elab Tactic in
/-- Discharge `P l[i]` from a hypothesis `∀ x ∈ l, P x` (element facts of
lists, e.g. the range of the integers stored in a `std::vector`). -/
elab "cir_mem_disch" : tactic => do
  let g ← getMainGoal
  g.withContext do
    for d in (← getLCtx) do
      if d.isImplementationDetail || d.userName.hasMacroScopes then continue
      -- only hypotheses `∀ x, x ∈ l → …`
      let t ← Meta.whnfR d.type
      let .forallE _ _ body _ := t | continue
      let .forallE _ hyp _ _ := body | continue
      unless hyp.isAppOf ``Membership.mem do continue
      let s ← Tactic.saveState
      try
        withoutRecover <| evalTactic (← `(tactic| exact $(mkIdent d.userName) _ (List.getElem_mem _)))
        return
      catch _ =>
        s.restore
    throwError "cir_mem_disch: no element hypothesis applies"

/-- `omega` with the facts `∀ k (h : k < l.length), Q k` instantiated at the
list elements of the goal (`CIR/Tactic/Simprocs.lean`). -/
syntax "cir_idx_omega" : tactic

/-- A negation or membership goal from a quantified hypothesis, instantiated
by unification, its other premises by assumption or `omega`
(`CIR/Tactic/Simprocs.lean`). -/
syntax "cir_hyp_apply" : tactic

/-- The discharger used during symbolic execution: an assumption, or integer
type bounds as literals (and list non-membership as disequalities), then
`omega`. -/
macro "cir_disch" : tactic => `(tactic| first
  | assumption
  | (simp (config := {failIfUnchanged := false}) only [intMin_s8, intMax_s8, intMin_s16, intMax_s16,
      intMin_s32, intMax_s32, intMin_s64, intMax_s64, intMin_u, intMax_u8, intMax_u16, intMax_u32,
      intMax_u64, List.mem_cons, List.not_mem_nil, not_or, ne_eq, not_false_eq_true, and_true,
      true_and, List.length_map]
     omega)
  | (simp (config := {failIfUnchanged := false}) only [inRange_eq_true_iff, intMin_s8, intMax_s8,
      intMin_s16, intMax_s16, intMin_s32, intMax_s32, intMin_s64, intMax_s64, intMin_u, intMax_u8,
      intMax_u16, intMax_u32, intMax_u64]
     cir_mem_disch)
  | (simp (config := {failIfUnchanged := false}) only [List.mem_cons, List.not_mem_nil, not_or,
      ne_eq, not_false_eq_true, and_true, true_and, List.length_map]
     cir_idx_omega)
  | cir_hyp_apply)

end CIR

namespace CIR

/-! ### Head-only structural steps (used by `cir_vcg`) -/

theorem holds_evalOps_cons {ctx : Ctx} {op : Op} {ops : List Op} {σ : State} {Q : Step × State → Prop}
    (h : (evalOp ctx op σ >>= fun x => match x with
      | (s, σ) => match s with
        | .next => evalOps ctx ops σ
        | s => pure (s, σ)).holds Q) :
    (evalOps ctx (op :: ops) σ).holds Q := by
  rw [evalOps.eq_2]; exact h

theorem holds_evalOps_nil {ctx : Ctx} {σ : State} {Q : Step × State → Prop}
    (h : Q (.exit (.yield []), σ)) : (evalOps ctx [] σ).holds Q := by
  rw [evalOps.eq_1]; exact h

theorem holds_evalRegion_cons {ctx : Ctx} {b : Block} {bs : List Block} {args : List Val} {σ : State}
    {Q : Exit × State → Prop}
    (h : (evalBlock ctx (b :: bs) 0 args σ >>= fun x => match x with
      | (e, σ') => pure (e, { mem := e.leaveMem σ'.mem σ.mem.next, env := σ.env, names := σ.names })).holds Q) :
    (evalRegion ctx (.mk (b :: bs)) args σ).holds Q := by
  rw [evalRegion.eq_2]; exact h

theorem holds_evalRegion_nil {ctx : Ctx} {args : List Val} {σ : State} {Q : Exit × State → Prop}
    (h : Q (.yield [], σ)) : (evalRegion ctx (.mk []) args σ).holds Q := by
  rw [evalRegion.eq_1]; exact h

/-! `switch` bodies: the selected case and the ones it falls through to. -/

theorem evalCases_nil (ctx : Ctx) (σ : State) : evalCases ctx [] σ = .ok (.next, σ) := by
  rw [evalCases.eq_1]

theorem evalCases_case (ctx : Ctx) (k : CaseKind) (vs : List Int) (r : Region) (ops : List Op)
    (σ : State) : evalCases ctx (.case k vs r :: ops) σ = (do
      let (e, σ) ← evalRegion ctx r [] σ
      match e with
      | .yield [] => evalCases ctx ops σ
      | .brk => pure (.next, σ)
      | .yield _ => .ub "case region yields values"
      | .cond _ => .ub "cir.condition in a case region"
      | e => pure (.exit e, σ)) := by
  rw [evalCases.eq_def]; rfl

theorem evalCases_yield (ctx : Ctx) (ops : List Op) (σ : State) :
    evalCases ctx (.yield [] :: ops) σ = .ok (.next, σ) := by
  rw [evalCases.eq_def]

theorem int_beq_eq_decide (a b : Int) : (a == b) = decide (a = b) := Bool.beq_eq_decide_eq a b

theorem holds_evalBlock_zero {ctx : Ctx} {params : List VId} {ops : List Op} {bs : List Block}
    {args : List Val} {σ : State} {Q : Exit × State → Prop}
    (h : (do
      let σ ← σ.bindArgs params args
      let (s, σ) ← evalOps ctx ops σ
      match s with
      | .exit (.goto l) =>
        match labelBlock? l (.mk params ops :: bs) with
        | some j => evalBlock ctx (.mk params ops :: bs) j [] σ
        | none => pure (.goto l, σ)
      | .exit e => pure (e, σ)
      | .jump j vs => evalBlock ctx (.mk params ops :: bs) j vs σ
      | .next => .ub "fell off the end of a block").holds Q) :
    (evalBlock ctx (.mk params ops :: bs) 0 args σ).holds Q := by
  rw [evalBlock_zero]; exact h

/-- Entering the block at index `i` (a jump, or a `goto` to a labelled block). -/
theorem holds_evalBlock_at {ctx : Ctx} {blocks : List Block} {i : BlockId} {params : List VId}
    {ops : List Op} {args : List Val} {σ : State} {Q : Exit × State → Prop}
    (hb : blocks[i]? = some (.mk params ops))
    (h : (do
      let σ ← σ.bindArgs params args
      let (s, σ) ← evalOps ctx ops σ
      match s with
      | .exit (.goto l) =>
        match labelBlock? l blocks with
        | some j => evalBlock ctx blocks j [] σ
        | none => pure (.goto l, σ)
      | .exit e => pure (e, σ)
      | .jump j vs => evalBlock ctx blocks j vs σ
      | .next => .ub "fell off the end of a block").holds Q) :
    (evalBlock ctx blocks i args σ).holds Q := by
  rw [evalBlock.eq_1, hb]; exact h

theorem holds_ok_intro {α : Type} {a : α} {Q : α → Prop} (h : Q a) : (Res.ok a).holds Q := h
theorem holds_pure_intro {α : Type} {a : α} {Q : α → Prop} (h : Q a) : (pure a : Res α).holds Q := h
theorem holds_bind_intro {α β : Type} {x : Res α} {f : α → Res β} {Q : β → Prop}
    (h : x.holds fun a => (f a).holds Q) : (x >>= f).holds Q := Res.holds_bind.mpr h
/-- The decidability instance is an ordinary implicit argument: it is taken
from the goal by unification and never re-synthesized (re-synthesis followed
by a defeq check can evaluate arithmetic on large literals). -/
theorem holds_ite_intro {α : Type} {c : Prop} {inst : Decidable c} {x y : Res α} {Q : α → Prop}
    (h₁ : c → x.holds Q) (h₂ : ¬c → y.holds Q) : (@ite _ c inst x y).holds Q :=
  Res.holds_ite.mpr ⟨h₁, h₂⟩

end CIR
