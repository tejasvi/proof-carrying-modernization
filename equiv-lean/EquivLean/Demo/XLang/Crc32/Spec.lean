/-!
# CRC-32: the specification both ports are proved against

CRC-32 as in zlib (IEEE 802.3, reflected, polynomial `0xEDB88320`), table-driven, on an inverted
register: `crc32 prev bytes` is zlib's `crc32(prev, bytes, len)`.  The table entry of a byte is
computed by the eight shift/xor steps of zlib's `make_crc_table` (`entry`), not listed.

Used by `Demo/XLang/Crc32/` (pako's `crc32`, TypeScript, against crc32fast's baseline `update`,
Rust): each side is proved equal to `crc32`, and the two are related through it.
-/

namespace EquivLean.Demo.Crc32

/-- One step of zlib's `make_crc_table`: `c & 1 ? 0xEDB88320 ^ (c >> 1) : c >> 1`. -/
def entryStep (c : BitVec 32) : BitVec 32 :=
  if c &&& 1 = 0 then c >>> 1 else 0xEDB88320 ^^^ (c >>> 1)

/-- The table entry of `n` (for `n < 256`): eight steps from `n`. -/
def entry (n : Nat) : BitVec 32 := Nat.repeat entryStep 8 (BitVec.ofNat 32 n)

/-- One byte of the table-driven update of the inverted register. -/
def step (c : BitVec 32) (b : BitVec 8) : BitVec 32 :=
  entry ((c ^^^ b.setWidth 32) &&& 0xFF).toNat ^^^ (c >>> 8)

/-- zlib's `crc32(prev, bytes)`: the register is inverted before and after the bytes. -/
def crc32 (prev : BitVec 32) (bytes : List (BitVec 8)) : BitVec 32 :=
  ~~~ (bytes.foldl step (~~~ prev))

/-- `crc32` of the concatenation (incremental use). -/
theorem crc32_append (prev : BitVec 32) (xs ys : List (BitVec 8)) :
    crc32 prev (xs ++ ys) = crc32 (crc32 prev xs) ys := by
  simp [crc32, List.foldl_append]

/-! Check values (zlib): `crc32(0, "hello")`, the table entries 1 and 255. -/
set_option maxRecDepth 100000 in
example : crc32 0 [104, 101, 108, 108, 111] = 0x3610a686 := by decide
set_option maxRecDepth 100000 in
example : entry 1 = 0x77073096 := by decide
set_option maxRecDepth 100000 in
example : entry 255 = 0x2d02ef8d := by decide

end EquivLean.Demo.Crc32
