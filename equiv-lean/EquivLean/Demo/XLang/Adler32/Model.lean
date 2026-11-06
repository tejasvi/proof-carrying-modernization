/-!
# zlib adler32: a functional model of `adler32_z`, `adler32` and `adler32_combine64`

zlib v1.3.1 (`adler32.c` @ 51b7f2a, unmodified), default configuration (`MOD` is `% BASE`, no `NO_DIVIDE`), x86_64
LP64: `uLong` is a 64-bit `unsigned long`, `z_size_t` is `size_t`, `z_off_t` and `z_off64_t` are 64-bit signed.

* `adler32z adler buf`: `adler32_z(adler, buf, len)` with `buf` the bytes (their number is `len`), `none` for
  `Z_NULL`.  It follows the code's paths: `len == 1` (one byte, each sum reduced by a single subtraction of
  `BASE`), `Z_NULL` (returns 1; with `len == 1` the C reads `buf[0]` first, which is undefined), `len < 16` (the
  bytes, then a single subtraction for `adler` and `MOD28` for `sum2`), and the main path (`mainPath`: blocks of
  `NMAX` bytes, each followed by `MOD` of both sums, then the remaining bytes, if any, followed by `MOD`).  The
  single subtractions differ from `% BASE` when the initial sums are `BASE` or more.
* `adler32` (`uInt len`) is `adler32_z` on the same bytes.
* `combine adler1 adler2 len2`: `adler32_combine64` (and `adler32_combine`, the same on LP64); a negative `len2`
  returns `0xffffffff`.
* `sums a s bs`: the two sums after the bytes (`DO1` on each), unreduced; `pack a s` is `a | (sum2 << 16)`.

The bytes are numbers below 256; `adler`, `adler1`, `adler2` are `unsigned long` values (below `2^64`).
-/

namespace EquivLean.Demo.XLang.Adler32

/-- `BASE`: the largest prime below 65536. -/
def BASE : Nat := 65521

/-- `NMAX`: the largest `n` with `255 n (n + 1) / 2 + (n + 1) (BASE - 1) ≤ 2^32 - 1`. -/
def NMAX : Nat := 5552

/-- The two sums after the bytes, from `(a, s)`: `DO1` on each byte (`adler += b; sum2 += adler`), unreduced. -/
def sums (a s : Nat) : List Nat → Nat × Nat
  | [] => (a, s)
  | b :: bs => sums (a + b) (s + (a + b)) bs

/-- `adler32_z`'s main path (`len ≥ 16`) from the sums `(a, s)`: while at least `NMAX` bytes remain, a block of
`NMAX` bytes followed by `MOD` of both sums; then the remaining bytes, if any, followed by `MOD` of both sums (none
when nothing remains). -/
def mainPath (a s : Nat) (bs : List Nat) : Nat × Nat :=
  if _h : NMAX ≤ bs.length then
    mainPath ((sums a s (bs.take NMAX)).1 % BASE) ((sums a s (bs.take NMAX)).2 % BASE) (bs.drop NMAX)
  else if bs.length = 0 then (a, s)
  else ((sums a s bs).1 % BASE, (sums a s bs).2 % BASE)
termination_by bs.length
decreasing_by simp only [List.length_drop]; unfold NMAX at _h ⊢; omega

/-- `adler | (sum2 << 16)`. -/
def pack (a s : Nat) : Nat := a ||| (s <<< 16)

/-- **The model of `adler32_z(adler, buf, len)`**: `buf` the bytes (`len` their number), `none` for `Z_NULL` with
`len != 1`. -/
def adler32z (adler : Nat) : Option (List Nat) → Nat
  | none => 1
  | some bs =>
    if bs.length = 1 then
      let a := (adler &&& 0xffff) + bs.headD 0
      let a := if BASE ≤ a then a - BASE else a
      let s := ((adler >>> 16) &&& 0xffff) + a
      let s := if BASE ≤ s then s - BASE else s
      pack a s
    else if bs.length < 16 then
      let p := sums (adler &&& 0xffff) ((adler >>> 16) &&& 0xffff) bs
      pack (if BASE ≤ p.1 then p.1 - BASE else p.1) (p.2 % BASE)
    else
      let p := mainPath (adler &&& 0xffff) ((adler >>> 16) &&& 0xffff) bs
      pack p.1 p.2

/-- **The model of `adler32_combine64(adler1, adler2, len2)`** (and of `adler32_combine`). -/
def combine (adler1 adler2 : Nat) (len2 : Int) : Nat :=
  if len2 < 0 then 0xffffffff
  else
    let rem := (len2 % (BASE : Int)).toNat
    let sum1 := adler1 &&& 0xffff
    let sum2 := rem * sum1 % BASE
    let sum1 := sum1 + (adler2 &&& 0xffff) + BASE - 1
    let sum2 := sum2 + ((adler1 >>> 16) &&& 0xffff) + ((adler2 >>> 16) &&& 0xffff) + BASE - rem
    let sum1 := if BASE ≤ sum1 then sum1 - BASE else sum1
    let sum1 := if BASE ≤ sum1 then sum1 - BASE else sum1
    let sum2 := if BASE <<< 1 ≤ sum2 then sum2 - (BASE <<< 1) else sum2
    let sum2 := if BASE ≤ sum2 then sum2 - BASE else sum2
    pack sum1 sum2

/-! Check values (zlib): `adler32(1, "Wikipedia")` and the initial value. -/
example : adler32z 1 (some [87, 105, 107, 105, 112, 101, 100, 105, 97]) = 0x11E60398 := by decide
example : adler32z 0 none = 1 := rfl

end EquivLean.Demo.XLang.Adler32
