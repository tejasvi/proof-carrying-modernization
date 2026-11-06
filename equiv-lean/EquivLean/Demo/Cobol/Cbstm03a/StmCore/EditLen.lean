/-
# Numeric editing of `CBSTM03A`'s two pictures: always defined, 13 bytes

`ST-CURR-BAL` (`9(9).99-`) and `ST-TRANAMT` / `ST-TOTAL-TRAMT` (`Z(9).99-`): for every value,
`Edit.edit` returns 13 bytes (`edit9_spec`, `editZ_spec`), so `MOVE`s into them never fault and
write exactly the item.
-/
import Cobol
open Cobol

namespace Cobol.StmCore

/-- `9(9).99-`. -/
def pic9 : List ESym := [.nine, .nine, .nine, .nine, .nine, .nine, .nine, .nine, .nine, .dot, .nine,
  .nine, .minus]

/-- `Z(9).99-`. -/
def picZ : List ESym := [.z, .z, .z, .z, .z, .z, .z, .z, .z, .dot, .nine, .nine, .minus]

/-- Printed width of an editing position. -/
def posLen (c : Config) (neg : Bool) : Edit.Pos → Nat
  | .digit _ => 1
  | .floatHead => 1
  | .insert _ => 1
  | .point => 1
  | .implied => 0
  | .fixed s => (Edit.fixedBytes c s neg).length

theorem length_gen (c : Config) (i : Nat) (ds : List Nat) (neg : Bool) (sk : Option ESym) (k0 : Nat) :
    ∀ (j : Nat) (ps : List Edit.Pos),
      (Edit.editOpt.gen c i ds neg sk k0 j ps).length = (ps.map (posLen c neg)).sum
  | _, [] => rfl
  | j, p :: ps => by
    cases p <;> simp [Edit.editOpt.gen, length_gen, posLen, Nat.add_comm]

theorem classify_pic9 : Edit.classify pic9 = some [.digit none, .digit none, .digit none,
    .digit none, .digit none, .digit none, .digit none, .digit none, .digit none, .point,
    .digit none, .digit none, .fixed .minus] := by decide

theorem classify_picZ : Edit.classify picZ = some [.digit (some .z), .digit (some .z),
    .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z),
    .digit (some .z), .digit (some .z), .point, .digit none, .digit none, .fixed .minus] := by decide

theorem edit9_spec (v : Int) : ∃ bs, Edit.edit {} pic9 false v 2 = some bs ∧ bs.length = 13 := by
  unfold Edit.edit Edit.editOpt
  have hf : Edit.floatSym pic9 = none := by decide
  have hb : Edit.floatBeforePoint [Edit.Pos.digit none, .digit none, .digit none, .digit none,
    .digit none, .digit none, .digit none, .digit none, .digit none, .point, .digit none, .digit none,
    .fixed .minus] = true := by decide
  have ha : [Edit.Pos.digit none, .digit none, .digit none, .digit none, .digit none, .digit none,
    .digit none, .digit none, .digit none, .point, .digit none, .digit none, .fixed .minus].all
    (fun p => p != Edit.Pos.digit none) = false := by decide
  simp only [classify_pic9, Option.bind_eq_bind, Option.bind_some, hf, hb, ha, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.false_and]
  refine ⟨_, rfl, ?_⟩
  rw [List.length_map, length_gen]
  cases (decide (v < 0)) <;> rfl

theorem editZ_spec (v : Int) : ∃ bs, Edit.edit {} picZ false v 2 = some bs ∧ bs.length = 13 := by
  unfold Edit.edit Edit.editOpt
  have hf : Edit.floatSym picZ = none := by decide
  have hb : Edit.floatBeforePoint [Edit.Pos.digit (some .z), .digit (some .z), .digit (some .z),
    .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z),
    .digit (some .z), .point, .digit none, .digit none, .fixed .minus] = true := by decide
  have ha : [Edit.Pos.digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z),
    .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z), .point,
    .digit none, .digit none, .fixed .minus].all (fun p => p != Edit.Pos.digit none) = false := by
    decide
  simp only [classify_picZ, Option.bind_eq_bind, Option.bind_some, hf, hb, ha, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.false_and]
  refine ⟨_, rfl, ?_⟩
  rw [List.length_map, length_gen]
  cases (decide (v < 0)) <;> rfl

/-- The edited balance (`ST-CURR-BAL`). -/
def edit9 (v : Int) : List UInt8 := (Edit.edit {} pic9 false v 2).getD []

/-- An edited amount (`ST-TRANAMT`, `ST-TOTAL-TRAMT`). -/
def editZ (v : Int) : List UInt8 := (Edit.edit {} picZ false v 2).getD []

theorem edit9_eq (v : Int) : Edit.edit {} pic9 false v 2 = some (edit9 v) := by
  obtain ⟨bs, h, -⟩ := edit9_spec v; simp [edit9, h]

theorem editZ_eq (v : Int) : Edit.edit {} picZ false v 2 = some (editZ v) := by
  obtain ⟨bs, h, -⟩ := editZ_spec v; simp [editZ, h]

theorem length_edit9 (v : Int) : (edit9 v).length = 13 := by
  obtain ⟨bs, h, hl⟩ := edit9_spec v; simp [edit9, h, hl]

theorem length_editZ (v : Int) : (editZ v).length = 13 := by
  obtain ⟨bs, h, hl⟩ := editZ_spec v; simp [editZ, h, hl]

end Cobol.StmCore
