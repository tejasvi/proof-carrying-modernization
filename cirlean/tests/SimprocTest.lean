import CIR
open CIR

example (m : Mem) (b1 b2 : Option MemBlock) :
    upd (upd m.blocks m.next b1) (m.next + 6) b2 m.next = b1 := by
  simp only [CIR.Tactic.reduceUpd]

example (m : Mem) (b1 b2 : Option MemBlock) :
    upd (upd m.blocks (m.next + 1) b1) (m.next + 6) b2 (m.next + 1) = b1 := by
  simp only [CIR.Tactic.reduceUpd]

example (f : Nat → Option Val) (x y : Option Val) :
    upd (upd f 0 x) 3 y 0 = x := by
  simp only [CIR.Tactic.reduceUpd]
