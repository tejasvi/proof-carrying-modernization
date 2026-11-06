/-
# Ground facts of `CBSTM03A` that symbolic execution does not evaluate

`Edit.edit` (numeric editing) is not unfolded by `cobol_sym`; its values on the constants the
program moves (`INITIALIZE` of the numeric-edited items) are checked by the kernel here.
-/
import Cobol
open Cobol

namespace Cobol.StmCore

set_option maxRecDepth 100000 in
/-- `INITIALIZE` of `ST-CURR-BAL` (`9(9).99-`): `000000000.00 `. -/
theorem edit9_zero : Edit.edit {} [.nine, .nine, .nine, .nine, .nine, .nine, .nine, .nine, .nine,
    .dot, .nine, .nine, .minus] false 0 0 = some [240, 240, 240, 240, 240, 240, 240, 240, 240, 75,
    240, 240, 64] := by decide +kernel

set_option maxRecDepth 100000 in
/-- `INITIALIZE` of `ST-TRANAMT` / `ST-TOTAL-TRAMT` (`Z(9).99-`): `         .00 `. -/
theorem editZ_zero : Edit.edit {} [.z, .z, .z, .z, .z, .z, .z, .z, .z, .dot, .nine, .nine, .minus]
    false 0 0 = some [64, 64, 64, 64, 64, 64, 64, 64, 64, 75, 240, 240, 64] := by decide +kernel

/-- An unsigned `DISPLAY` item holds the digit characters of its value. -/
theorem encodeNum_display_unsigned (w n : Nat) :
    encodeNum {} { digits := w + 1 } (n : Int) = Sem.digitChars {} (w + 1) n := by
  simp [encodeNum, encZoned, Sem.digitChars, Digits.toDigits]

theorem decodeNum_digitChars (w n : Nat) (hw : w + 1 ≤ 18) (hn : n < 10 ^ (w + 1)) :
    decodeNum {} { digits := w + 1 } (Sem.digitChars {} (w + 1) n) = some (n : Int) := by
  rw [← encodeNum_display_unsigned]
  apply decodeNum_encodeNum _ _ _ (by simp) (by simpa using hw)
  unfold NumFmt.Holds NumFmt.fullBinary
  simp only [Int.natAbs_natCast]
  refine ⟨?_, fun _ => by omega⟩
  exact hn

/-- The key `CBSTM03B` builds for `ACCT-FILE` (`MOVE LK-M03B-KEY (1:11) TO FD-ACCT-ID`, a
`PIC 9(11)` item): the digits back again. -/
theorem decodeNum_digitChars11 (n : Nat) (hn : n < 100000000000) :
    decodeNum {} { digits := 11 } (Sem.digitChars {} 11 n) = some (n : Int) :=
  decodeNum_digitChars 10 n (by decide) (by simpa using hn)

theorem encodeNum_digits11 (n : Nat) :
    encodeNum {} { digits := 11 } (n : Int) = Sem.digitChars {} 11 n :=
  encodeNum_display_unsigned 10 n

end Cobol.StmCore
