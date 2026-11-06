/-
# `MOVE` between numeric items, by rewriting

Symbolic execution unfolds `Sem.execStmt`, `Sem.lift`, `Sem.move` and `Sem.srcVal` with
definitional (`rfl`) equations, so the kernel has to re-check those unfoldings when it composes
the proof.  For a `COMP-5` receiver the check runs into `fitBin`'s range test `v < 2 ^ 32` on a
symbolic value, which the kernel reduces through `Nat.sub` in unary ("deep recursion").
`execStmt_move_num_num` is the whole `MOVE` of a numeric item to a numeric item (no subscripts,
no reference modification), proved once for every state; used as a `↓` lemma it rewrites the
statement before those definitions are unfolded.
-/
import Cobol

namespace Cobol.Stm

theorem execStmt_move_num_num (P : Program) (env : Env) (rec : Nat → State → Sem.Res)
    (fuel : Nat) (st : State) (i1 o1 l1 i2 o2 l2 : Nat) (f g : NumFmt)
    (hov : Sem.badOverlap ⟨o1, l1, .num f⟩ ⟨o2, l2, .num g⟩ = false) :
    Sem.execStmt P env rec fuel
        (.move (.ref ⟨i1, ⟨o1, l1, .num f⟩, [], none⟩) [⟨i2, ⟨o2, l2, .num g⟩, [], none⟩]) st =
      match decodeNum P.cfg f (st.mem.read o1 l1) with
      | some v =>
        if (Sem.fitNum P.cfg g (rescale .truncation v f.scale g.scale)).1 &&
            Sem.overflowUndefined P.cfg g then (.fault .sizeUndefined, st)
        else (.normal,
          { st with mem := st.mem.write o2 (encodeNum P.cfg g (Sem.fitNum P.cfg g (rescale .truncation v f.scale g.scale)).2) })
      | none => (.fault .invalidData, st) := by
  rw [Sem.execStmt.eq_1]
  cases hd : decodeNum P.cfg f (st.mem.read o1 l1) with
  | none =>
    simp [Sem.lift, Sem.move, Sem.srcVal, Sem.resolve, Sem.readBytes, Sem.moveList, hov,
      Sem.moveInto, hd]
  | some v =>
    simp only [Sem.lift, Sem.move, Sem.srcVal, Sem.resolve, Sem.readBytes, Sem.moveList, hov,
      Sem.moveInto, Sem.numInto, Sem.storeMove, Sem.writeBytes, hd, Bool.false_eq_true,
      ↓reduceIte]
    cases h1 : (Sem.fitNum P.cfg g (rescale .truncation v f.scale g.scale)).1 <;>
      cases h2 : Sem.overflowUndefined P.cfg g <;> simp [h1, h2]

end Cobol.Stm
