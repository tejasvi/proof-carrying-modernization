/-
# Platform and compiler-option profile

Everything that differs between IBM Enterprise COBOL on z/OS and other COBOL systems
(character set, embedded-sign convention, byte order, `TRUNC`, `NUMPROC`, binary sizes,
behaviour of a size error without `ON SIZE ERROR`) is a field of `Config`.  The default
`Config` (`Config.ibm`) is IBM Enterprise COBOL with `TRUNC(STD) NUMPROC(NOPFD)`.
A program's `Config` is part of the IR, so the extractor records the compile options.
-/

namespace Cobol

/-- Character set family. -/
inductive Charset where
  /-- EBCDIC (CP037 / CP1140 family): space `0x40`, digits `0xF0`-`0xF9`. -/
  | ebcdic
  /-- ASCII: space `0x20`, digits `0x30`-`0x39`. -/
  | ascii
  deriving DecidableEq, Repr, Inhabited

/-- Encoding of the operational sign embedded in the zone of a zoned-decimal byte. -/
inductive ZonedSign where
  /-- IBM mainframe: zone nibble `C` (+), `D` (-), `F` (unsigned). -/
  | ebcdic
  /-- ASCII, Micro Focus / GnuCOBOL default: `0x30`-`0x39` (+), `0x70`-`0x79` (-). -/
  | asciiMF
  /-- ASCII with EBCDIC-style overpunch: `{ABCDEFGHI` (+0..+9), `}JKLMNOPQR` (-0..-9). -/
  | asciiOverpunch
  deriving DecidableEq, Repr, Inhabited

/-- The `TRUNC` compiler option (binary data). -/
inductive Trunc where
  /-- `TRUNC(STD)`: binary values are truncated to the `PICTURE` digits on store. -/
  | std
  /-- `TRUNC(OPT)`: the compiler assumes values fit the `PICTURE`; results that do not fit
  are unpredictable (modelled as `unsupported`). -/
  | opt
  /-- `TRUNC(BIN)`: binary items behave like `COMP-5` (full binary range). -/
  | bin
  deriving DecidableEq, Repr, Inhabited

structure Config where
  charset : Charset := .ebcdic
  zonedSign : ZonedSign := .ebcdic
  trunc : Trunc := .std
  /-- `NUMPROC(PFD)`: only preferred signs (`C`, `D`, `F`) are valid.  With the default
  `NUMPROC(NOPFD)` the alternative sign nibbles `A`, `B`, `E` are accepted too, and an
  unsigned item with a sign nibble other than `F` is read as positive. -/
  numprocPfd : Bool := false
  /-- Byte order of `COMP` / `BINARY` / `COMP-4` items (`false` = big-endian, IBM). -/
  binaryLE : Bool := false
  /-- Byte order of `COMP-5` items (`false` = big-endian, IBM). -/
  comp5LE : Bool := false
  /-- Binary items of 1-2 digits occupy one byte (GnuCOBOL `binary-size: 1-2-4-8`);
  IBM uses 2-4-8. -/
  binary1Byte : Bool := false
  /-- Without `ON SIZE ERROR`, a size error stores the high-order-truncated result (IBM
  behaviour).  If `false` the result is treated as undefined (`unsupported`), which is what
  the COBOL standard says. -/
  sizeErrorTruncates : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- IBM Enterprise COBOL for z/OS, `TRUNC(STD) NUMPROC(NOPFD)`. -/
def Config.ibm : Config := {}

/-- GnuCOBOL on x86 with `-std=ibm` style data but ASCII storage. -/
def Config.gnucobol : Config :=
  { charset := .ascii, zonedSign := .asciiMF, comp5LE := true }

namespace Config

/-- A character of the platform character set, by its ASCII code (only the characters COBOL
semantics needs: space, digits, quote, sign and editing characters, letters). -/
def chr (c : Config) (ascii : Nat) : UInt8 :=
  match c.charset with
  | .ascii => UInt8.ofNat ascii
  | .ebcdic =>
    UInt8.ofNat <|
      if 0x30 ≤ ascii ∧ ascii ≤ 0x39 then 0xF0 + (ascii - 0x30)          -- 0-9
      else if 0x41 ≤ ascii ∧ ascii ≤ 0x49 then 0xC1 + (ascii - 0x41)     -- A-I
      else if 0x4A ≤ ascii ∧ ascii ≤ 0x52 then 0xD1 + (ascii - 0x4A)     -- J-R
      else if 0x53 ≤ ascii ∧ ascii ≤ 0x5A then 0xE2 + (ascii - 0x53)     -- S-Z
      else if 0x61 ≤ ascii ∧ ascii ≤ 0x69 then 0x81 + (ascii - 0x61)     -- a-i
      else if 0x6A ≤ ascii ∧ ascii ≤ 0x72 then 0x91 + (ascii - 0x6A)     -- j-r
      else if 0x73 ≤ ascii ∧ ascii ≤ 0x7A then 0xA2 + (ascii - 0x73)     -- s-z
      else match ascii with
        | 0x20 => 0x40 | 0x22 => 0x7F | 0x24 => 0x5B | 0x27 => 0x7D | 0x2A => 0x5C
        | 0x2B => 0x4E | 0x2C => 0x6B | 0x2D => 0x60 | 0x2E => 0x4B | 0x2F => 0x61
        | _ => 0x6F   -- '?' for characters outside this table

def space (c : Config) : UInt8 := c.chr 0x20
def quote (c : Config) : UInt8 := c.chr 0x22
def zeroChar (c : Config) : UInt8 := c.chr 0x30
def plusChar (c : Config) : UInt8 := c.chr 0x2B
def minusChar (c : Config) : UInt8 := c.chr 0x2D

/-- Encode an ASCII string literal in the platform character set. -/
def encodeAscii (c : Config) (s : String) : List UInt8 :=
  s.toList.map (fun ch => c.chr ch.toNat)

/-! ### Zoned-decimal bytes -/

/-- Byte of digit `d` in a non-sign position (`'0' + d`). -/
def digitByte (c : Config) (d : Nat) : UInt8 :=
  match c.charset with
  | .ebcdic => UInt8.ofNat (0xF0 + d)
  | .ascii => UInt8.ofNat (0x30 + d)

/-- Byte carrying digit `d` and an embedded sign (`neg`). -/
def signByte (c : Config) (neg : Bool) (d : Nat) : UInt8 :=
  match c.zonedSign with
  | .ebcdic => UInt8.ofNat ((if neg then 0xD0 else 0xC0) + d)
  | .asciiMF => UInt8.ofNat ((if neg then 0x70 else 0x30) + d)
  | .asciiOverpunch =>
    UInt8.ofNat <| if neg then (if d = 0 then 0x7D else 0x49 + d)
                  else (if d = 0 then 0x7B else 0x40 + d)

/-- Separate sign character (`SIGN ... SEPARATE`). -/
def sepSignByte (c : Config) (neg : Bool) : UInt8 :=
  if neg then c.minusChar else c.plusChar

/-- Decode a digit byte in a non-sign position. -/
def decDigit (c : Config) (b : UInt8) : Option Nat :=
  let z := match c.charset with | .ebcdic => 0xF0 | .ascii => 0x30
  if z ≤ b.toNat ∧ b.toNat ≤ z + 9 then some (b.toNat - z) else none

/-- Decode the sign byte of a signed zoned item: `(negative, digit)`. -/
def decSign (c : Config) (b : UInt8) : Option (Bool × Nat) :=
  let n := b.toNat
  match c.zonedSign with
  | .ebcdic =>
    let zone := n / 16
    let d := n % 16
    if d ≤ 9 then
      if zone = 0xC ∨ zone = 0xF ∨ (!c.numprocPfd && (zone = 0xA || zone = 0xE)) then
        some (false, d)
      else if zone = 0xD ∨ (!c.numprocPfd && zone = 0xB) then some (true, d)
      else none
    else none
  | .asciiMF =>
    if 0x30 ≤ n ∧ n ≤ 0x39 then some (false, n - 0x30)
    else if 0x70 ≤ n ∧ n ≤ 0x79 then some (true, n - 0x70)
    else none
  | .asciiOverpunch =>
    if n = 0x7B then some (false, 0)
    else if 0x41 ≤ n ∧ n ≤ 0x49 then some (false, n - 0x40)
    else if n = 0x7D then some (true, 0)
    else if 0x4A ≤ n ∧ n ≤ 0x52 then some (true, n - 0x49)
    else if 0x30 ≤ n ∧ n ≤ 0x39 then some (false, n - 0x30)
    else none

/-- Decode the last byte of an unsigned zoned item.  Under `NUMPROC(NOPFD)` on EBCDIC any
sign zone `A`-`F` is accepted (the compiler forces the sign to `F`). -/
def decUnsLast (c : Config) (b : UInt8) : Option Nat :=
  match c.decDigit b with
  | some d => some d
  | none =>
    if c.zonedSign = .ebcdic ∧ c.numprocPfd = false ∧ 0xA ≤ b.toNat / 16 ∧ b.toNat % 16 ≤ 9
    then some (b.toNat % 16) else none

/-- Decode a separate sign character. -/
def decSepSign (c : Config) (b : UInt8) : Option Bool :=
  if b = c.plusChar then some false else if b = c.minusChar then some true else none

/-! ### Packed-decimal sign nibbles -/

/-- Sign nibble written for a packed item. -/
def packedSignNibble (signed neg : Bool) : Nat :=
  if signed then (if neg then 0xD else 0xC) else 0xF

/-- Decode a packed sign nibble: `some negative`, or `none` if invalid. -/
def decPackedSign (c : Config) (signed : Bool) (s : Nat) : Option Bool :=
  if signed then
    if s = 0xC ∨ s = 0xF ∨ (!c.numprocPfd && (s = 0xA || s = 0xE)) then some false
    else if s = 0xD ∨ (!c.numprocPfd && s = 0xB) then some true
    else none
  else
    if s = 0xF ∨ (!c.numprocPfd && (0xA ≤ s && s ≤ 0xE)) then some false else none

/-! ### Binary sizes -/

/-- Storage size in bytes of a binary item with `digits` digit positions. -/
def binBytes (c : Config) (digits : Nat) : Nat :=
  if c.binary1Byte && digits ≤ 2 then 1
  else if digits ≤ 4 then 2 else if digits ≤ 9 then 4 else 8

end Config
end Cobol
