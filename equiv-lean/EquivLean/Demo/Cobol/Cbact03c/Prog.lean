-- Copied unchanged from coblean (frozen snapshot ~/coblean_snapshots/coblean-20261024T0857Z,
-- Examples/Cbact03c.lean); only the IR path differs. coblean and JimpleLean both have a library
-- named `Examples`, so equiv-lean cannot import the original module next to JimpleLean.
/-
# CardDemo CBACT03C (cross-reference file listing), extracted by the front end

`examples/carddemo/cbact03c.ir.json` is the output of `tools/cobolfe` on
`app/cbl/CBACT03C.cbl` of AWS CardDemo (commit 59cc6c2f, Apache-2.0), unchanged.
-/
import Cobol
open Cobol

namespace CardDemo

cobol_program Cbact03c from "../../../../examples/cobol/carddemo/cbact03c.ir.json"

namespace Cbact03c

def displays (st : State) : List (List UInt8) :=
  st.out.reverse.filterMap fun | .display bs => some bs | _ => none


/-- `START OF EXECUTION OF PROGRAM CBACT03C` in EBCDIC (`startMsg_eq`). -/
def startMsg : List UInt8 := [226, 227, 193, 217, 227, 64, 214, 198, 64, 197, 231, 197, 195, 228, 227, 201, 214, 213, 64, 214, 198, 64, 215, 217, 214, 199, 217, 193, 212, 64, 195, 194, 193, 195, 227, 240, 243, 195]

/-- `END OF EXECUTION OF PROGRAM CBACT03C` in EBCDIC (`endMsg_eq`). -/
def endMsg : List UInt8 := [197, 213, 196, 64, 214, 198, 64, 197, 231, 197, 195, 228, 227, 201, 214, 213, 64, 214, 198, 64, 215, 217, 214, 199, 217, 193, 212, 64, 195, 194, 193, 195, 227, 240, 243, 195]

theorem startMsg_eq : Codepage.encode037 "START OF EXECUTION OF PROGRAM CBACT03C" = some startMsg := by
  decide +kernel

theorem endMsg_eq : Codepage.encode037 "END OF EXECUTION OF PROGRAM CBACT03C" = some endMsg := by
  decide +kernel

/-- Loop invariant of `PERFORM UNTIL END-OF-FILE = 'Y'`, with `rest` = the outcomes of the
remaining `READ`s (`some r`: record `r`, `none`: end of file): the records `done` have been
displayed (twice each), the file is positioned after them. -/
def Inv (recs : List (List UInt8)) (rest : List (Option (List UInt8))) (st : State) : Prop :=
  ∃ done todo, recs = done ++ todo ∧
    st.idx = [] ∧ st.slots = [] ∧ st.active = [] ∧ st.clockN = 0 ∧
    st.out = (done.flatMap fun r => [r, r]).reverse.map Event.display ++ [.display startMsg] ∧
    st.inp = [(1, recs)] ∧
    (∃ c, st.files = [(1, { mode := some .input, recs, pos := done.length, eof := rest.isEmpty,
                            cur := c })]) ∧
    st.mem.size = 123 ∧
    ((rest = [] ∧ todo = [] ∧ st.mem.field END_OF_FILE = [0xE8]) ∨
     (rest = todo.map some ++ [none] ∧ st.mem.field END_OF_FILE = [0xD5]))

theorem getElem?_append_length {α : Type} (l : List α) (x : α) (xs : List α) :
    (l ++ x :: xs)[l.length]? = some x := by simp

theorem getElem?_length_self {α : Type} (l : List α) : l[l.length]? = none := by simp

/-- **CBACT03C lists the card file.**  For every card file (any number of 50-byte records)
and any initial storage, when the file opens, the program ends with `GOBACK` and its
`DISPLAY` output is the start message, every record twice in file order (`GET-NEXT`
displays it after the `READ`, the main loop again), and the end message. -/
theorem cbact03c_lists (m : Mem) (hm : m.size = 123) (recs : List (List UInt8)) (n : Nat)
    (hrecs : ∀ r ∈ recs, r.length = 50) (hn : recs.length < n) :
    let r := Cbact03c.run {} (n + 20) (Cbact03c.initState m [(1, recs)])
    r.1 = .stop .goback ∧ displays r.2 = [startMsg] ++ recs.flatMap (fun r => [r, r]) ++ [endMsg] := by
  intro r
  simp only [r]
  cobol_sym [hm]
  cobol_loop (Inv recs) (recs.map some ++ [none])
  · -- after the loop: CLOSE, DISPLAY, GOBACK
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := loopState
    obtain ⟨done, todo, hd, rfl, rfl, rfl, rfl, rfl, rfl, ⟨c, rfl⟩, hsz, hcase⟩ := hloopInv
    obtain ⟨-, rfl, heof⟩ | ⟨h, -⟩ := hcase
    · simp only [List.append_nil] at hd
      subst hd
      cobol_sym [hsz, heof]
      simp [displays, startMsg, endMsg, List.filterMap_map, Function.comp_def]
    · simp at h
  · -- before the loop: nothing displayed but the start message, file at its start
    refine ⟨[], recs, by simp, rfl, rfl, rfl, rfl, by simp [startMsg], rfl, ⟨none, by simp⟩, ?_,
      Or.inr ⟨by simp, ?_⟩⟩ <;> cobol_sym [hm]
  · simp; omega
  · -- the loop ends exactly after the end-of-file READ
    rintro ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨done, todo, -, rfl, rfl, rfl, rfl, rfl, rfl, ⟨c, rfl⟩, -, (⟨-, -, heof⟩ | ⟨h, -⟩)⟩
    · cobol_sym [heof]
    · simp at h
  · -- one iteration: READ the next record and DISPLAY it, or reach the end of the file
    rintro y ys ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨done, todo, hd, rfl, rfl, rfl, rfl, rfl, rfl, ⟨c, rfl⟩, hsz, (⟨h, -⟩ | ⟨hrest, heof⟩)⟩
    · simp at h
    cases todo with
    | nil =>
      simp at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      simp only [List.append_nil] at hd
      subst hd
      refine ⟨by cobol_sym [heof], ?_⟩
      cobol_sym [hsz, heof, getElem?_length_self]
      refine ⟨recs, [], by simp, rfl, rfl, rfl, rfl, rfl, rfl, ⟨none, by simp⟩, ?_,
        Or.inl ⟨rfl, rfl, ?_⟩⟩ <;> cobol_sym [hsz]
    | cons t todo' =>
      simp at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      subst hd
      have ht : t.length = 50 := hrecs t (by simp)
      refine ⟨by cobol_sym [heof], ?_⟩
      cobol_sym [hsz, heof, ht, getElem?_append_length]
      refine ⟨done ++ [t], todo', by simp, rfl, rfl, rfl, rfl, by simp, rfl,
        ⟨some done.length, by simp⟩, ?_, Or.inr ⟨by simp, ?_⟩⟩ <;> cobol_sym [hsz, heof, ht]

#print axioms cbact03c_lists

end Cbact03c
end CardDemo
