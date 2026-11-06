import EquivLean.Bridge.Cir.Behaves

/-!
# cirlean bridge: observable behaviour of a call

Two implementations of a C++ function may allocate different numbers of local variables, so
their final memories differ in the blocks they allocated (the stack blocks of a call are
erased at its return, but ids are not reused and `next` differs).  What the caller can
observe is the `Exit` (returned value or escaping exception) and the blocks that existed
before the call:

    ObsEq m₀ (e₁, m₁) (e₂, m₂)  :=  e₁ = e₂ ∧ ∀ b < m₀.next, m₁.blocks b = m₂.blocks b

`EquivOn Bad ctxNew fNew ctxOld fOld`: on every call (argument values and initial memory)
outside `Bad`, the new function is safe exactly when the old one is, and then they have the
same observable outcome.  Choosing `Bad` as the inputs on which the old version has undefined
behaviour states that a patch changed behaviour only where the old code was wrong.
-/

namespace EquivLean.Cir

open CIR

/-- Same `Exit` and same contents of every block that existed before the call (`m₀`). -/
def ObsEq (m₀ : Mem) (o₁ o₂ : Exit × Mem) : Prop :=
  o₁.1 = o₂.1 ∧ ∀ b, b < m₀.next → o₁.2.blocks b = o₂.2.blocks b

/-- The new function agrees with the old one on every call outside `Bad`. -/
def EquivOn (Bad : List Val → Mem → Prop) (ctxNew : Ctx) (fNew : String) (ctxOld : Ctx)
    (fOld : String) : Prop :=
  ∀ args m, ¬ Bad args m → Equiv (ObsEq m) (evalCall ctxNew fNew args m) (evalCall ctxOld fOld args m)

theorem obsEq_def (m₀ : Mem) (e₁ e₂ : Exit) (m₁ m₂ : Mem) :
    ObsEq m₀ (e₁, m₁) (e₂, m₂) ↔ e₁ = e₂ ∧ ∀ b, b < m₀.next → m₁.blocks b = m₂.blocks b :=
  Iff.rfl

theorem ObsEq.refl (m₀ : Mem) (o : Exit × Mem) : ObsEq m₀ o o := ⟨rfl, fun _ _ => rfl⟩

theorem ObsEq.symm {m₀ : Mem} {o₁ o₂ : Exit × Mem} (h : ObsEq m₀ o₁ o₂) : ObsEq m₀ o₂ o₁ :=
  ⟨h.1.symm, fun b hb => (h.2 b hb).symm⟩

theorem ObsEq.trans {m₀ : Mem} {o₁ o₂ o₃ : Exit × Mem} (h₁ : ObsEq m₀ o₁ o₂)
    (h₂ : ObsEq m₀ o₂ o₃) : ObsEq m₀ o₁ o₃ :=
  ⟨h₁.1.trans h₂.1, fun b hb => (h₁.2 b hb).trans (h₂.2 b hb)⟩

/-- The relation of the reversed simulation in an `Equiv` is `ObsEq` again. -/
theorem obsEq_flip (m₀ : Mem) : (fun o₂ o₁ => ObsEq m₀ o₁ o₂) = ObsEq m₀ := by
  funext o₂ o₁; exact propext ⟨ObsEq.symm, ObsEq.symm⟩

/-- `EquivOn` from the two simulations (each direction is proved with the tactic). -/
theorem EquivOn.intro {Bad : List Val → Mem → Prop} {ctxNew ctxOld : Ctx} {fNew fOld : String}
    (h₁ : ∀ args m, ¬ Bad args m →
      Sim (ObsEq m) (evalCall ctxNew fNew args m) (evalCall ctxOld fOld args m))
    (h₂ : ∀ args m, ¬ Bad args m →
      Sim (ObsEq m) (evalCall ctxOld fOld args m) (evalCall ctxNew fNew args m)) :
    EquivOn Bad ctxNew fNew ctxOld fOld :=
  fun args m hb => ⟨h₁ args m hb, by rw [obsEq_flip]; exact h₂ args m hb⟩

/-- `EquivOn` bounds the calls on which the two versions differ. -/
theorem EquivOn.changed_subset {Bad : List Val → Mem → Prop} {ctxNew ctxOld : Ctx}
    {fNew fOld : String} (h : EquivOn Bad ctxNew fNew ctxOld fOld) (args : List Val) (m : Mem)
    (hne : ¬ Equiv (ObsEq m) (evalCall ctxNew fNew args m) (evalCall ctxOld fOld args m)) :
    Bad args m :=
  Classical.byContradiction fun hb => hne (h args m hb)

/-- The core `EquivLean.EquivOn` over the pair (arguments, memory) is the same statement. -/
theorem equivOn_iff_core {Bad : List Val → Mem → Prop} {ctxNew ctxOld : Ctx} {fNew fOld : String}
    (m : Mem) :
    (∀ args, ¬ Bad args m → Equiv (ObsEq m) (evalCall ctxNew fNew args m)
      (evalCall ctxOld fOld args m)) ↔
    EquivLean.EquivOn (fun args => Bad args m) (ObsEq m) (fun args => evalCall ctxNew fNew args m)
      (fun args => evalCall ctxOld fOld args m) :=
  Iff.rfl

/-! ### Up to container generations

A container's generation (`Val.vec gen _`, and `PathElem.vel gen i` in element pointers) is
drawn from the counter of block ids (`CIR.Std.fresh`), so two implementations that allocate
different numbers of locals give a rebuilt container different generations.  `ObsEqGen`
compares the exit and the caller's blocks after setting every generation to `0`.  It is
coarser than `ObsEq`: it also identifies a stale element pointer with a valid one, so use it
for results whose containers the caller reads through the container itself. -/

def eraseGenElem : PathElem → PathElem
  | .vel _ i => .vel 0 i
  | e => e

def eraseGenPtr : Ptr → Ptr
  | .loc b path => .loc b (path.map eraseGenElem)
  | p => p

mutual
/-- A value with the generation numbers of containers and element pointers set to `0`. -/
def eraseGen : Val → Val
  | .ptr p => .ptr (eraseGenPtr p)
  | .agg fs => .agg (eraseGenList fs)
  | .arr xs => .arr (eraseGenList xs)
  | .vec _ xs => .vec 0 (eraseGenList xs)
  | .opt o => .opt (eraseGenOpt o)
  | .tok e => .tok { e with obj := eraseGenPtr e.obj }
  | v => v
def eraseGenList : List Val → List Val
  | [] => []
  | v :: vs => eraseGen v :: eraseGenList vs
def eraseGenOpt : Option Val → Option Val
  | none => none
  | some v => some (eraseGen v)
end

def eraseGenExit : Exit → Exit
  | .ret v => .ret (eraseGenOpt v)
  | .exn x => .exn { x with obj := eraseGenPtr x.obj }
  | e => e

def eraseGenBlock (blk : MemBlock) : MemBlock := { blk with val := eraseGen blk.val }

/-- `ObsEq` up to container generations. -/
def ObsEqGen (m₀ : Mem) (o₁ o₂ : Exit × Mem) : Prop :=
  eraseGenExit o₁.1 = eraseGenExit o₂.1 ∧
    ∀ b, b < m₀.next → (o₁.2.blocks b).map eraseGenBlock = (o₂.2.blocks b).map eraseGenBlock

theorem ObsEq.toGen {m₀ : Mem} {o₁ o₂ : Exit × Mem} (h : ObsEq m₀ o₁ o₂) : ObsEqGen m₀ o₁ o₂ :=
  ⟨congrArg eraseGenExit h.1, fun b hb => congrArg (Option.map eraseGenBlock) (h.2 b hb)⟩

theorem ObsEqGen.symm {m₀ : Mem} {o₁ o₂ : Exit × Mem} (h : ObsEqGen m₀ o₁ o₂) :
    ObsEqGen m₀ o₂ o₁ :=
  ⟨h.1.symm, fun b hb => (h.2 b hb).symm⟩

theorem ObsEqGen.trans {m₀ : Mem} {o₁ o₂ o₃ : Exit × Mem} (h₁ : ObsEqGen m₀ o₁ o₂)
    (h₂ : ObsEqGen m₀ o₂ o₃) : ObsEqGen m₀ o₁ o₃ :=
  ⟨h₁.1.trans h₂.1, fun b hb => (h₁.2 b hb).trans (h₂.2 b hb)⟩

theorem obsEqGen_flip (m₀ : Mem) : (fun o₂ o₁ => ObsEqGen m₀ o₁ o₂) = ObsEqGen m₀ := by
  funext o₂ o₁; exact propext ⟨ObsEqGen.symm, ObsEqGen.symm⟩

/-- `EquivOn` up to container generations. -/
def EquivOnGen (Bad : List Val → Mem → Prop) (ctxNew : Ctx) (fNew : String) (ctxOld : Ctx)
    (fOld : String) : Prop :=
  ∀ args m, ¬ Bad args m →
    Equiv (ObsEqGen m) (evalCall ctxNew fNew args m) (evalCall ctxOld fOld args m)

theorem EquivOn.toGen {Bad : List Val → Mem → Prop} {ctxNew ctxOld : Ctx} {fNew fOld : String}
    (h : EquivOn Bad ctxNew fNew ctxOld fOld) : EquivOnGen Bad ctxNew fNew ctxOld fOld :=
  fun args m hb => (h args m hb).mono fun _ _ => ObsEq.toGen

end EquivLean.Cir
