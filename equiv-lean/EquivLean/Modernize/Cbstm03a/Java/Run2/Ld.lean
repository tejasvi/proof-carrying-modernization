import EquivLean.Modernize.Cbstm03a.Java.Run2.Frame

/-!
# CBSTM03A → Java `run`, the load loop: one load step by its counters

The memory after `ldStep s rec` is the three writes at the offsets of its own counters, whichever branch set them;
`saveCard` becomes the card number; the counts array keeps its length.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (fixStr space)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

theorem ldStep_m (s : LdSt) (rec : JStr) :
    (ldStep s rec).m = memWr (memWr (memWr s.m (cardOffJ (ldStep s rec).cr).toInt (sub rec 0 16))
      (tranOffJ (ldStep s rec).cr (ldStep s rec).tr).toInt (sub rec 16 32))
      (tranOffJ (ldStep s rec).cr (ldStep s rec).tr + 16).toInt (sub rec 32 350) := by
  by_cases h : s.save = sub rec 0 16
  · rw [ldStep_same h]
  · rw [ldStep_diff h]

theorem ldStep_save (s : LdSt) (rec : JStr) : (ldStep s rec).save = sub rec 0 16 := by
  by_cases h : s.save = sub rec 0 16
  · rw [ldStep_same h]
  · rw [ldStep_diff h]

theorem ldStep_trct_length (s : LdSt) (rec : JStr) : (ldStep s rec).trct.length = s.trct.length := by
  by_cases h : s.save = sub rec 0 16
  · rw [ldStep_same h]
  · rw [ldStep_diff h]
    exact trctSet_lengthR _ _ _

theorem ldStep_same_cr {s : LdSt} {rec : JStr} (h : s.save = sub rec 0 16) :
    (ldStep s rec).cr = s.cr ∧ (ldStep s rec).tr = (s.tr + 1).srem 10000 ∧ (ldStep s rec).trct = s.trct := by
  rw [ldStep_same h]; exact ⟨rfl, rfl, rfl⟩

theorem ldStep_diff_cr {s : LdSt} {rec : JStr} (h : ¬ s.save = sub rec 0 16) :
    (ldStep s rec).cr = (s.cr + 1).srem 10000 ∧ (ldStep s rec).tr = 1 ∧
      (ldStep s rec).trct = trctSet s.trct s.cr s.tr := by
  rw [ldStep_diff h]; exact ⟨rfl, rfl, rfl⟩

theorem sub_length {rec : JStr} (h : rec.length = 350) :
    (sub rec 0 16).length = 16 ∧ (sub rec 16 32).length = 16 ∧ (sub rec 32 350).length = 318 := by
  simp [sub, h]

end EquivLean.Modernize.Cbstm03a.Java.Seg2
