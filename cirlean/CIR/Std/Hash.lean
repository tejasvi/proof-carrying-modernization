/-!
  libc++'s hashing support in its dylib: `std::__hash_memory(p, n)`, the hash of `n` bytes that
  `std::hash` of strings (and of scalars wider than `size_t`) and `__gnu_cxx::hash<const char *>`
  call, and `std::__next_prime(n)`, the bucket counts of the unordered containers. `__hash_memory` is
  `__murmur2_or_cityhash<size_t>` of `<__functional/hash.h>` for a 64-bit `size_t`, CityHash64 in
  libc++'s ABI version 1 (without `_LIBCPP_ABI_FIX_CITYHASH_IMPLEMENTATION`: for 4 to 8 bytes, the
  first word shifted left by 3 in 32 bits); `__next_prime` (libc++'s `src/hash.cpp`) gives 0 for 0
  and otherwise the smallest prime not below `n`.
-/

namespace CIR.Std

namespace City

def k0 : UInt64 := 0xc3a5c85c97cb3127
def k1 : UInt64 := 0xb492b66fbe98f273
def k2 : UInt64 := 0x9ae16a3b2f90404f
def k3 : UInt64 := 0xc949d7c7509e6557

/-- The little-endian word of the `n` bytes of `s` from `i` on (`__loadword`). -/
def load (s : Array UInt8) (i n : Nat) : UInt64 :=
  (List.range n).foldr (fun k acc => (acc <<< 8) ||| (s[i + k]!).toUInt64) 0

/-- `__rotate`: right by `r` bits, `0 ≤ r < 64`. -/
def rot (v : UInt64) (r : Nat) : UInt64 :=
  if r = 0 then v else (v >>> r.toUInt64) ||| (v <<< (64 - r).toUInt64)

def shiftMix (v : UInt64) : UInt64 := v ^^^ (v >>> 47)

def len16 (u v : UInt64) : UInt64 :=
  let mul : UInt64 := 0x9ddfea08eb382d69
  let a := (u ^^^ v) * mul
  let a := a ^^^ (a >>> 47)
  let b := (v ^^^ a) * mul
  let b := b ^^^ (b >>> 47)
  b * mul

def len0to16 (s : Array UInt8) (len : Nat) : UInt64 :=
  if 8 < len then
    let a := load s 0 8
    let b := load s (len - 8) 8
    len16 a (rot (b + len.toUInt64) len) ^^^ b
  else if 4 ≤ len then
    let a := (load s 0 4).toUInt32
    let b := (load s (len - 4) 4).toUInt32
    len16 (len.toUInt64 + (a <<< 3).toUInt64) b.toUInt64
  else if 0 < len then
    let a := s[0]!
    let b := s[len / 2]!
    let c := s[len - 1]!
    let y : UInt32 := a.toUInt32 + (b.toUInt32 <<< 8)
    let z : UInt32 := len.toUInt32 + (c.toUInt32 <<< 2)
    shiftMix (y.toUInt64 * k2 ^^^ z.toUInt64 * k3) * k2
  else k2

def len17to32 (s : Array UInt8) (len : Nat) : UInt64 :=
  let a := load s 0 8 * k1
  let b := load s 8 8
  let c := load s (len - 8) 8 * k2
  let d := load s (len - 16) 8 * k0
  len16 (rot (a - b) 43 + rot c 30 + d) (a + rot (b ^^^ k3) 20 - c + len.toUInt64)

def weak (w x y z a b : UInt64) : UInt64 × UInt64 :=
  let a := a + w
  let b := rot (b + a + z) 21
  let c := a
  let a := a + x + y
  let b := b + rot a 44
  (a + z, b + c)

def weakAt (s : Array UInt8) (i : Nat) (a b : UInt64) : UInt64 × UInt64 :=
  weak (load s i 8) (load s (i + 8) 8) (load s (i + 16) 8) (load s (i + 24) 8) a b

def len33to64 (s : Array UInt8) (len : Nat) : UInt64 :=
  let z := load s 24 8
  let a := load s 0 8 + (len.toUInt64 + load s (len - 16) 8) * k0
  let b := rot (a + z) 52
  let c := rot a 37
  let a := a + load s 8 8
  let c := c + rot a 7
  let a := a + load s 16 8
  let vf := a + z
  let vs := b + rot a 31 + c
  let a := load s 16 8 + load s (len - 32) 8
  let z := z + load s (len - 8) 8
  let b := rot (a + z) 52
  let c := rot a 37
  let a := a + load s (len - 24) 8
  let c := c + rot a 7
  let a := a + load s (len - 16) 8
  let wf := a + z
  let ws := b + rot a 31 + c
  let r := shiftMix ((vf + ws) * k2 + (wf + vs) * k0)
  shiftMix (r * k0 + vs) * k2

/-- The 64-byte chunks of the long case, from offset `i`, `n` chunks. -/
def chunks (s : Array UInt8) : Nat → Nat → UInt64 → UInt64 → UInt64 → UInt64 × UInt64 → UInt64 × UInt64 →
    UInt64 × UInt64 × UInt64 × (UInt64 × UInt64) × (UInt64 × UInt64)
  | 0, _, x, y, z, v, w => (x, y, z, v, w)
  | n + 1, i, x, y, z, v, w =>
    let x := rot (x + y + v.1 + load s (i + 8) 8) 37 * k1
    let y := rot (y + v.2 + load s (i + 48) 8) 42 * k1
    let x := x ^^^ w.2
    let y := y + v.1 + load s (i + 40) 8
    let z := rot (z + w.1) 33 * k1
    let v' := weakAt s i (v.2 * k1) (x + w.1)
    let w' := weakAt s (i + 32) (z + w.2) (y + load s (i + 16) 8)
    chunks s n (i + 64) z y x v' w'

/-- CityHash64 of `s` as libc++ computes it (`__murmur2_or_cityhash<size_t, 64>`). -/
def hash64 (s : Array UInt8) : UInt64 :=
  let len := s.size
  if len ≤ 16 then len0to16 s len
  else if len ≤ 32 then len17to32 s len
  else if len ≤ 64 then len33to64 s len
  else
    let x := load s (len - 40) 8
    let y := load s (len - 16) 8 + load s (len - 56) 8
    let z := len16 (load s (len - 48) 8 + len.toUInt64) (load s (len - 24) 8)
    let v := weakAt s (len - 64) len.toUInt64 z
    let w := weakAt s (len - 32) (y + k1) x
    let x := x * k1 + load s 0 8
    let (x, y, z, v, w) := chunks s ((len - 1) / 64) 0 x y z v w
    len16 (len16 v.1 w.1 + shiftMix y * k1 + z) (len16 v.2 w.2 + x)

end City

/-- Trial division up to the square root (`fuel` bounds the divisors tried). -/
def primeTD (n : Nat) : Bool :=
  let rec go (d : Nat) : Nat → Bool
    | 0 => true
    | fuel + 1 => if n < d * d then true else if n % d = 0 then false else go (d + 1) fuel
  2 ≤ n && go 2 n

/-- libc++'s `__next_prime(n)`: 0 for 0, else the smallest prime not below `n` (there is one below
`2n`, Bertrand's postulate, so the search ends within `n + 1` candidates). -/
def nextPrime (n : Nat) : Nat :=
  let rec go (k : Nat) : Nat → Nat
    | 0 => k
    | fuel + 1 => if primeTD k then k else go (k + 1) fuel
  if n = 0 then 0 else go n (n + 1)

end CIR.Std
