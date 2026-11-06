/-
# BINCNT: `COMP-5` arithmetic ≡ Java `short` / `int` arithmetic, bit for bit

`examples/binary/BINCNT.cob` adds 1 to a `PIC S9(4) COMP-5` counter (two's-complement
wrap-around at 32767), adds three times the counter to a `PIC S9(9) COMP-5` total (the
counter is sign-extended), and copies the high half of the total through a `REDEFINES` byte
view.  `BinCntJava.update` transcribes `examples/binary/BinCnt.java` (`ByteBuffer` reads and
writes, `short` / `int` arithmetic).

The theorem holds for all 2⁴⁸ contents of the input fields, including every overflow:
symbolic execution produces the stored bytes, `cobol_bits` restates them as `BitVec`
expressions, and `bv_decide` proves the remaining bit-vector identity.
-/
import Cobol
open Cobol

cobol_program BinCnt from "../examples/binary/bincnt.ir.json"

namespace BinCntJava
open Java.Bits

/-- `BinCnt.update` on the eight bytes of the record. -/
def update (c0 c1 t0 t1 t2 t3 : UInt8) : List UInt8 :=
  let cnt : Int16 := getShort c0 c1
  let total : Int32 := getInt t0 t1 t2 t3
  let cnt := cnt + 1
  let total := total + cnt.toInt32 * 3
  match putShort cnt, putInt total with
  | [a0, a1], [b0, b1, b2, b3] => [a0, a1, b0, b1, b2, b3, b0, b1]
  | _, _ => []

end BinCntJava

open BinCnt in
theorem bincnt_equiv (m : Mem) (hm : m.size = 8) (c0 c1 t0 t1 t2 t3 : UInt8)
    (hc : m.field WS_CNT = [c0, c1]) (ht : m.field WS_TOTAL = [t0, t1, t2, t3]) :
    let r := BinCnt.run {} 10 (BinCnt.initState m)
    r.1 = .stop .goback ∧
      r.2.mem.field WS_CNT ++ r.2.mem.field WS_TOTAL ++ r.2.mem.field WS_OUT =
        BinCntJava.update c0 c1 t0 t1 t2 t3 := by
  cobol_bv [hm, hc, ht, BinCntJava.update]

#print axioms bincnt_equiv

/-! ## A wrong rewrite is refuted

Keeping the counter in an `int` (`int cnt = bb.getShort(0); cnt++; …; bb.putShort(0, (short) cnt)`)
stores the same counter bytes, but uses `32768` instead of `-32768` in the total after an
overflow.  `cobol_bv` on this version fails, and `bv_decide` reports a counterexample (counter
bytes `7F FF`); evaluating both programs on it proves the difference. -/

namespace BinCntJava
open Java.Bits

def updateWrong (c0 c1 t0 t1 t2 t3 : UInt8) : List UInt8 :=
  let cnt : Int32 := (getShort c0 c1).toInt32
  let total : Int32 := getInt t0 t1 t2 t3
  let cnt := cnt + 1
  let total := total + cnt * 3
  match putShort cnt.toInt16, putInt total with
  | [a0, a1], [b0, b1, b2, b3] => [a0, a1, b0, b1, b2, b3, b0, b1]
  | _, _ => []

end BinCntJava

open BinCnt in
theorem bincnt_wrong :
    let m : Mem := ⟨#[0x7F, 0xFF, 0, 0, 0, 0, 0, 0]⟩
    let r := BinCnt.run {} 10 (BinCnt.initState m)
    r.2.mem.field WS_CNT ++ r.2.mem.field WS_TOTAL ++ r.2.mem.field WS_OUT ≠
      BinCntJava.updateWrong 0x7F 0xFF 0 0 0 0 := by
  decide +kernel
