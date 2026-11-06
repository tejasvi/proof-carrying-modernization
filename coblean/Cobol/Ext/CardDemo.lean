/-
# External routines of AWS CardDemo, as environment `CALL`s

The batch programs call two routines that are not COBOL: `CEE3ABD` (Language Environment
abend, built into the semantics as an abend) and `COBDATFT` (`app/asm/COBDATFT.asm`, 84 lines of
HLASM), modelled here from its source.

`COBDATFT` reformats the date in its parameter area `CODATECN-REC` (`CODATECN.cpy`, 80 bytes:
input type, input date (20), output type, output date (20), error message (38)):
* input type `1` (`YYYYMMDD`), output type not `2`: the output date's first 10 bytes become
  `YYYY-MM-DD`;
* input type `2` (`YYYY-MM-DD`), output type not `1`: its first 8 bytes become `YYYYMMDD`;
the rest of the area is unchanged.  On every other input (another input type, a type-1 input
with `-` in position 5, a mismatched output type) it moves `'INVALID INPUT'` to the 38-byte error
message with an `MVC` of 38 bytes from a 13-byte literal: the last 25 bytes come from the
routine's literal pool, which the source does not determine.  That path is left out (the call
is `unsupported` there).  The routine returns 0 in R15; the semantics does not set
`RETURN-CODE` after a `CALL`, which agrees with that.
-/
import Cobol.IR
import Cobol.Target.Codepage

namespace Cobol.Ext

/-- A character of the program's character set (the routine compares and stores EBCDIC
characters; under the ASCII profile the same characters in ASCII). -/
def chr (cfg : Config) (c : Char) : UInt8 :=
  match cfg.charset with
  | .ebcdic => (Codepage.encode037 c.toString).getD [0] |>.headD 0
  | .ascii => UInt8.ofNat c.toNat

/-- `COBDATFT` on its parameter area (`none`: the error path, not modelled). -/
def cobdatft (cfg : Config) (area : List UInt8) : Option (List UInt8) :=
  if area.length ≠ 80 then none else
  let ty := area.getD 0 0
  let inp := (area.drop 1).take 20
  let oty := area.getD 21 0
  let out := (area.drop 22).take 20
  let rest := area.drop 42
  let dash := chr cfg '-'
  let put (o : List UInt8) := some ((area.take 22) ++ o ++ rest)
  if ty = chr cfg '1' then
    if inp.getD 4 0 = dash ∨ oty = chr cfg '2' then none
    else put (inp.take 4 ++ [dash] ++ (inp.drop 4).take 2 ++ [dash] ++ (inp.drop 6).take 2 ++
      out.drop 10)
  else if ty = chr cfg '2' then
    if oty = chr cfg '1' then none
    else put (inp.take 4 ++ (inp.drop 5).take 2 ++ (inp.drop 8).take 2 ++ out.drop 8)
  else none

/-- The environment `CALL`s of CardDemo's batch programs. -/
def cardDemoCalls (cfg : Config) : String → List (List UInt8) → Option (List (List UInt8))
  | "COBDATFT", [area] => (cobdatft cfg area).map ([·])
  | _, _ => none

end Cobol.Ext
