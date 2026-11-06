import CIR.Semantics.Init
import CIR.Memory

/-!
  The initial memory of a module: block `i` holds global `i`, alive unless the
  module only declares it, and the read-only globals stay as they were when the
  memory changed only at blocks that are not read-only
  (`Module.RoGlobals.frame`).
-/

namespace CIR

/-- A `for` loop over a list in `Id` whose body always yields is a left fold. -/
private theorem forIn_id_eq_foldl {α β : Type} (l : List α) (f : α → β → Id (ForInStep β))
    (g : α → β → β) (hf : ∀ a b, f a b = pure (ForInStep.yield (g a b))) (init : β) :
    (forIn l init f).run = l.foldl (fun b a => g a b) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    rw [List.forIn_cons, hf]
    exact ih (g a init)

/-- One step of `Module.initMem`: allocate global `g` with initial value `val g`. -/
private def allocGlobal (val : GlobalDecl → Val) (m : Mem) (g : GlobalDecl) : Mem :=
  (m.allocAs g.blockKind g.init.isSome g.ty (val g)).2

private theorem allocGlobal_next (val : GlobalDecl → Val) (m : Mem) (g : GlobalDecl) :
    (allocGlobal val m g).next = m.next + 1 := rfl

private theorem allocGlobal_blocks (val : GlobalDecl → Val) (m : Mem) (g : GlobalDecl) (b : Nat) :
    (allocGlobal val m g).blocks b = if b = m.next then
      some ⟨g.blockKind, g.init.isSome, g.ty, val g⟩ else m.blocks b := rfl

/-- `Module.initMem` allocates the globals in order, each with its initial value. -/
private theorem initMem_eq_foldl (M : Module) :
    ∃ val, M.initMem = M.globals.foldl (allocGlobal val) Mem.empty :=
  ⟨_, forIn_id_eq_foldl M.globals _ _ (fun _ _ => rfl) Mem.empty⟩

/-- Allocating the globals `l` one after another from `m0`: global `j` lands in
block `m0.next + j`, and the other blocks are unchanged. -/
private theorem foldl_allocGlobal (val : GlobalDecl → Val) (l : List GlobalDecl) (m0 : Mem) :
    (l.foldl (allocGlobal val) m0).next = m0.next + l.length ∧
    (∀ j g, l[j]? = some g → (l.foldl (allocGlobal val) m0).blocks (m0.next + j) =
      some ⟨g.blockKind, g.init.isSome, g.ty, val g⟩) ∧
    (∀ b, b < m0.next ∨ m0.next + l.length ≤ b →
      (l.foldl (allocGlobal val) m0).blocks b = m0.blocks b) := by
  induction l generalizing m0 with
  | nil =>
    refine ⟨rfl, fun j g hj => ?_, fun b _ => rfl⟩
    simp at hj
  | cons g l ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih (allocGlobal val m0 g)
    rw [allocGlobal_next] at ih1 ih2 ih3
    rw [List.foldl_cons, List.length_cons]
    refine ⟨by rw [ih1]; omega, fun j g' hj => ?_, fun b hb => ?_⟩
    · cases j with
      | zero =>
        rw [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, ih3 m0.next (Or.inl (by omega)), allocGlobal_blocks, ite_eq_left rfl]
      | succ j =>
        rw [List.getElem?_cons_succ] at hj
        rw [show m0.next + (j + 1) = m0.next + 1 + j by omega]
        exact ih2 j g' hj
    · rw [ih3 b (by omega), allocGlobal_blocks, ite_eq_right (show b ≠ m0.next by omega)]

theorem Module.initMem_next (M : Module) : M.initMem.next = M.globals.length := by
  obtain ⟨val, hval⟩ := initMem_eq_foldl M
  rw [hval, (foldl_allocGlobal _ _ _).1]
  exact Nat.zero_add _

theorem Module.initMem_blocks {M : Module} {i : Nat} {g : GlobalDecl} (h : M.globals[i]? = some g) :
    ∃ v, M.initMem.blocks i =
      some ⟨g.blockKind, g.init.isSome, g.ty, v⟩ := by
  obtain ⟨val, hval⟩ := initMem_eq_foldl M
  refine ⟨val g, ?_⟩
  have := (foldl_allocGlobal val M.globals Mem.empty).2.1 i g h
  rw [hval]
  rwa [show Mem.empty.next + i = i from Nat.zero_add i] at this

/-- No block of the initial memory lies at or above `next`. -/
theorem Module.initMem_wf (M : Module) : M.initMem.WF := by
  intro b hb
  rw [Module.initMem_next] at hb
  obtain ⟨val, hval⟩ := initMem_eq_foldl M
  rw [hval, (foldl_allocGlobal val M.globals Mem.empty).2.2 b
    (Or.inr (show 0 + M.globals.length ≤ b by omega))]
  rfl

/-- The read-only globals stay as they were when the memory changed only at
blocks that are not read-only (a well-formed memory holds every constant global
below `next`; a constant one the module only declares has a read-only block too). -/
theorem Module.RoGlobals.frame {M : Module} {m m' : Mem} (h : M.RoGlobals m) (hwf : m.WF)
    (hag : ∀ i, i < m.next → (∀ blk, m.blocks i = some blk → blk.kind = .readonly) →
      m'.blocks i = m.blocks i) :
    M.RoGlobals m' := by
  intro i g hi hc
  obtain ⟨v, hv⟩ := Module.initMem_blocks hi
  have hm : m.blocks i = some ⟨g.blockKind, g.init.isSome, g.ty, v⟩ := by
    rw [h i g hi hc, hv]
  have hk : g.blockKind = .readonly := by
    simp [GlobalDecl.blockKind, hc]
  have hlt : i < m.next := by
    rcases Nat.lt_or_ge i m.next with hlt | hge
    · exact hlt
    · rw [hwf i hge] at hm
      cases hm
  rw [hag i hlt (fun blk hblk => by rw [hm] at hblk; cases hblk; exact hk)]
  exact h i g hi hc

end CIR

