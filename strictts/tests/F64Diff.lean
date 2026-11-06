import StrictTS.Num.F64
import Std.Data.HashMap

/-!
Differential test of the `StrictTS.F64` model.

* `float`: bit-exact comparison with the host IEEE double (`Float`, `Float32`) on special values,
  random bit patterns and random "nice" values (NaN results compared after canonicalization).
* `js`: operations without a `Float` counterpart (and a cross-check of the others) compared with
  V8 through `tests/f64_node_ref.js` (node is started as a child process).

usage (from the project root): `lake exe f64diff [all|float|js] [seed] [count]`
Prints `OP <name> cases=<n> mismatches=<k>` per operation and the first 5 mismatches.
-/

open StrictTS

namespace F64Diff

/-! ## Deterministic PRNG (splitmix64) -/

def mix (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

abbrev Gen := StateT UInt64 IO

def next : Gen UInt64 := do
  let s := (← get) + 0x9E3779B97F4A7C15
  set s
  return mix s

def below (n : Nat) : Gen Nat := return (← next).toNat % n

def pick {α : Type} [Inhabited α] (xs : Array α) : Gen α := return xs[← below xs.size]!

/-! ## Bit patterns -/

def canon (b : UInt64) : UInt64 :=
  if (b >>> 52) &&& 0x7FF == 0x7FF && b &&& 0xFFFFFFFFFFFFF != 0 then 0x7FF8000000000000 else b

def canon32 (b : UInt32) : UInt32 :=
  if (b >>> 23) &&& 0xFF == 0xFF && b &&& 0x7FFFFF != 0 then 0x7FC00000 else b

def model (b : UInt64) : F64 := F64.ofBits (BitVec.ofNat 64 b.toNat)
def mbits (x : F64) : UInt64 := x.toBits.toNat.toUInt64
def hbits (x : Float) : UInt64 := canon x.toBits
def hex (b : UInt64) : String := F64.hexPad b.toNat 16

/-- Bit pattern of `2^k` (`-1074 ≤ k ≤ 1023`). -/
def pow2Bits (k : Int) : UInt64 :=
  if k ≥ -1022 then ((k + 1023).toNat <<< 52).toUInt64 else (1 <<< (k + 1074).toNat).toUInt64

def specials : Array UInt64 := Id.run do
  let mut a : Array UInt64 := #[
    0x0000000000000000, 0x8000000000000000, 0x7FF0000000000000, 0xFFF0000000000000,
    0x7FF8000000000000, 0xFFF8000000000000, 0x7FF0000000000001, 0x7FFFFFFFFFFFFFFF,
    0x0000000000000001, 0x8000000000000001, 0x0000000000000002, 0x0000000000000003,
    0x000FFFFFFFFFFFFF, 0x800FFFFFFFFFFFFF, 0x0008000000000000, 0x0010000000000000,
    0x8010000000000000, 0x0010000000000001, 0x001FFFFFFFFFFFFF, 0x7FEFFFFFFFFFFFFF,
    0xFFEFFFFFFFFFFFFF, 0x7FEFFFFFFFFFFFFE, 0x7FE0000000000000, 0x3CB0000000000000,
    0x47EFFFFFE0000000, 0x47EFFFFFF0000000, 0x47EFFFFFEFFFFFFF, 0x47F0000000000000,
    0x36A0000000000000, 0x3690000000000000, 0x3690000000000001, 0x380FFFFFFFFFFFFF,
    0x3810000000000000, 0x380FFFFFE0000000, 0x380FFFFFF0000000]
  let ks : List Int := [-1074, -1073, -1060, -1023, -1022, -1021, -600, -150, -149, -126, -60,
    -54, -53, -52, -2, -1, 0, 1, 2, 30, 31, 32, 33, 51, 52, 53, 54, 63, 64, 100, 128, 1000, 1022,
    1023]
  for k in ks do
    let p := pow2Bits k
    for s in [0, 0x8000000000000000] do
      a := a.push (p ||| s)
      a := a.push ((p + 1) ||| s)
      if p > 1 then a := a.push ((p - 1) ||| s)
  let ints : List Int := [2^31 - 1, 2^31, 2^31 + 1, 2^32 - 1, 2^32, 2^32 + 1, 2^53 - 1, 2^53,
    2^53 + 2, 2^52 - 1, 2^52, 2^52 + 1, 255, 256, 254, 127, 128, 65535, 65536, 32767, 32768, 3, 5, 7]
  for n in ints do
    for s in [1, -1] do
      a := a.push (Float.ofInt (s * n)).toBits
  for n in [0, 1, 2, 3, 254, 255, 256, 2^31, 2^52 - 1] do
    for s in [1.0, -1.0] do
      a := a.push (s * (Float.ofInt n + 0.5)).toBits
      a := a.push (s * (Float.ofInt n + 0.25)).toBits
      a := a.push (s * (Float.ofInt n + 0.75)).toBits
  return a

/-- Random bit pattern, biased toward subnormal, near-overflow and moderate exponents and toward
short significands. -/
def randBits : Gen UInt64 := do
  let r ← next
  match ← below 8 with
  | 0 => return (r &&& (0x800FFFFFFFFFFFFF : UInt64)) ||| ((← below 3).toUInt64 <<< 52)
  | 1 => return (r &&& (0x800FFFFFFFFFFFFF : UInt64)) ||| ((2040 + (← below 7)).toUInt64 <<< 52)
  | 2 => return (r &&& (0x800FFFFFFFFFFFFF : UInt64)) ||| ((983 + (← below 120)).toUInt64 <<< 52)
  | 3 =>
    let keep ← below 53
    let r := if (r >>> 52) &&& 0x7FF == 0x7FF then r &&& 0xBFFFFFFFFFFFFFFF else r
    return r &&& ~~~(((1 : UInt64) <<< (52 - keep).toUInt64) - 1)
  | _ => return r

/-- Random pair; two thirds of the time the exponents are within 60 of each other. -/
def randPair : Gen (UInt64 × UInt64) := do
  let a ← randBits
  if (← below 3) == 0 then return (a, ← randBits)
  let ea := ((a >>> 52) &&& 0x7FF).toNat
  let d ← below 121
  let eb := if ea + d < 60 then 0 else Nat.min 2046 (ea + d - 60)
  let r ← next
  return (a, (r &&& (0x800FFFFFFFFFFFFF : UInt64)) ||| (eb.toUInt64 <<< 52))

def sgnInt (n : Nat) (neg : Bool) : Int := if neg then -(n : Int) else n

/-- Random "nice" value: small integers, short decimals, halves, int32/safe-integer edges, large
integers, repeating fractions, products, scaled values, tiny integers. -/
def nice : Gen Float := do
  match ← below 10 with
  | 0 => return Float.ofInt ((← below 4001 : Nat) - 2000 : Int)
  | 1 =>
    let k : Int := (← below 200001 : Nat) - 100000
    return Float.ofInt k / Float.ofNat (10 ^ (← below 7))
  | 2 => return Float.ofInt ((← below 2001 : Nat) - 1000 : Int) + 0.5
  | 3 => return Float.ofInt ((← below 4001 : Nat) - 2000 : Int) / Float.ofNat (2 ^ (← below 4))
  | 4 =>
    let base ← pick #[(2^31 : Int), -2^31, 2^32, -2^32, 2^53, -2^53, 2^52, -2^52, 2^30, 0, 255, 128]
    let off : Int := (← below 9 : Nat) - 4
    let h : Float := if (← below 2) == 0 then 0.0 else 0.5
    return Float.ofInt (base + off) + h
  | 5 => return Float.ofInt (sgnInt ((← next).toNat % 2^60) ((← below 2) == 0))
  | 6 =>
    let d ← pick #[3, 7, 9, 11, 13, 10, 100]
    return Float.ofInt ((← below 2001 : Nat) - 1000 : Int) / Float.ofNat d
  | 7 =>
    let a := Float.ofInt ((← below 2001 : Nat) - 1000 : Int) / 10.0
    let b := Float.ofInt ((← below 2001 : Nat) - 1000 : Int) / 100.0
    return a * b
  | 8 =>
    let k := Float.ofInt ((← below 2001 : Nat) - 1000 : Int) / Float.ofNat (10 ^ (← below 4))
    return k.scaleB ((← below 2200 : Nat) - 1100 : Int)
  | _ => return Float.ofInt ((← below 100 : Nat) - 40 : Int)

def niceBits : Gen UInt64 := return (← nice).toBits

/-! ## Statistics -/

structure Stat where
  name : String
  cases : Nat := 0
  mism : Nat := 0
  first : Array String := #[]

def Stat.push (s : Stat) (ok : Bool) (msg : Unit → String) : Stat :=
  if ok then { s with cases := s.cases + 1 }
  else { s with cases := s.cases + 1, mism := s.mism + 1,
                first := if s.first.size < 5 then s.first.push (msg ()) else s.first }

def Stat.print (s : Stat) : IO Unit := do
  IO.println s!"OP {s.name} cases={s.cases} mismatches={s.mism}"
  for m in s.first do IO.println s!"    {m}"

/-! ## Host `Float` comparison -/

def binOps : Array (String × (F64 → F64 → F64) × (Float → Float → Float)) := #[
  ("add", (· + ·), (· + ·)), ("sub", (· - ·), (· - ·)),
  ("mul", (· * ·), (· * ·)), ("div", (· / ·), (· / ·))]

def unOps : Array (String × (F64 → F64) × (Float → Float)) := #[
  ("sqrt", F64.sqrt, Float.sqrt), ("floor", F64.floor, Float.floor),
  ("ceil", F64.ceil, Float.ceil),
  ("trunc", F64.trunc, fun x => if x < 0 then Float.ceil x else Float.floor x),
  ("abs", F64.abs, Float.abs), ("neg", (- ·), (- ·)),
  ("fround", F64.fround, fun x => x.toFloat32.toFloat)]

def cmpOps : Array (String × (F64 → F64 → Bool) × (Float → Float → Bool)) := #[
  ("lt", F64.lt, fun a b => a < b), ("le", F64.le, fun a b => a ≤ b),
  ("gt", F64.gt, fun a b => a > b), ("ge", F64.ge, fun a b => a ≥ b),
  ("eq", F64.eq, fun a b => a == b)]

def runFloat (seed : UInt64) (n : Nat) : IO Nat := do
  let ((singles, pairs), _) ← (do
    let mut singles := specials
    let mut pairs : Array (UInt64 × UInt64) := #[]
    for a in specials do
      for b in specials do
        pairs := pairs.push (a, b)
    for _ in [0:n] do
      singles := singles.push (← randBits)
      pairs := pairs.push (← randPair)
    for _ in [0:n] do
      singles := singles.push (← niceBits)
      pairs := pairs.push (← niceBits, ← niceBits)
    return (singles, pairs) : Gen _).run seed
  let ms := singles.map model
  let mp := pairs.map fun (a, b) => (model a, model b)
  let mut total := 0
  -- encoding round trip (exercises ofBits/toBits on every input)
  let mut sb : Stat := { name := "bits" }
  for a in singles, x in ms do
    sb := sb.push (mbits x == canon a) fun _ => s!"{hex a} -> {hex (mbits x)}"
  sb.print; total := total + sb.mism
  for (name, f, g) in binOps do
    let mut st : Stat := { name }
    for (a, b) in pairs, (x, y) in mp do
      let want := hbits (g (Float.ofBits a) (Float.ofBits b))
      let got := mbits (f x y)
      st := st.push (want == got) fun _ => s!"{hex a} {hex b}: want {hex want} got {hex got}"
    st.print; total := total + st.mism
  for (name, f, g) in unOps do
    let mut st : Stat := { name }
    for a in singles, x in ms do
      let want := hbits (g (Float.ofBits a))
      let got := mbits (f x)
      st := st.push (want == got) fun _ => s!"{hex a}: want {hex want} got {hex got}"
    st.print; total := total + st.mism
  for (name, f, g) in cmpOps do
    let mut st : Stat := { name }
    for (a, b) in pairs, (x, y) in mp do
      let want := g (Float.ofBits a) (Float.ofBits b)
      let got := f x y
      st := st.push (want == got) fun _ => s!"{hex a} {hex b}: want {want} got {got}"
    st.print; total := total + st.mism
  let mut sf : Stat := { name := "toF32Bits" }
  for a in singles, x in ms do
    let want := canon32 (Float.ofBits a).toFloat32.toBits
    let got := x.toF32Bits.toNat.toUInt32
    sf := sf.push (want == got) fun _ => s!"{hex a}: want {want.toNat} got {got.toNat}"
  sf.print; total := total + sf.mism
  return total

/-! ## V8 comparison -/

def b2s (b : Bool) : String := if b then "1" else "0"
def r64 (x : F64) : String := hex (mbits x)

def jsUnary : Array (String × (F64 → String)) := #[
  ("jsRound", fun a => r64 a.jsRound), ("floor", fun a => r64 a.floor),
  ("ceil", fun a => r64 a.ceil), ("trunc", fun a => r64 a.trunc),
  ("sqrt", fun a => r64 a.sqrt), ("sign", fun a => r64 a.sign),
  ("abs", fun a => r64 a.abs), ("neg", fun a => r64 (-a)),
  ("fround", fun a => r64 a.fround), ("toF32Bits", fun a => F64.hexPad a.toF32Bits.toNat 8),
  ("clz32", fun a => r64 a.clz32), ("bnot", fun a => r64 a.bnot),
  ("toInt32", fun a => toString a.toInt32.toInt), ("toUint32", fun a => toString a.toInt32.toNat),
  ("toInt8", fun a => toString (a.toBitsN 8).toInt),
  ("toUint8", fun a => toString (a.toBitsN 8).toNat),
  ("toInt16", fun a => toString (a.toBitsN 16).toInt),
  ("toUint16", fun a => toString (a.toBitsN 16).toNat),
  ("toUint8Clamp", fun a => toString a.toUint8Clamp.toNat),
  ("isInteger", fun a => b2s a.isInteger), ("isSafeInteger", fun a => b2s a.isSafeInteger),
  ("isFinite", fun a => b2s a.isFinite), ("isNaN", fun a => b2s a.isNaN),
  ("toBigInt", fun a => match a.toBigInt? with | some k => toString k | none => "none")]

def jsBinary : Array (String × (F64 → F64 → String)) := #[
  ("add", fun a b => r64 (a + b)), ("sub", fun a b => r64 (a - b)),
  ("mul", fun a b => r64 (a * b)), ("div", fun a b => r64 (a / b)),
  ("rem", fun a b => r64 (a % b)),
  ("min", fun a b => r64 (F64.min a b)), ("max", fun a b => r64 (F64.max a b)),
  ("imul", fun a b => r64 (F64.imul a b)),
  ("band", fun a b => r64 (F64.band a b)), ("bor", fun a b => r64 (F64.bor a b)),
  ("bxor", fun a b => r64 (F64.bxor a b)),
  ("shl", fun a b => r64 (F64.shl a b)), ("sar", fun a b => r64 (F64.sar a b)),
  ("shr", fun a b => r64 (F64.shr a b)),
  ("lt", fun a b => b2s (a.lt b)), ("le", fun a b => b2s (a.le b)),
  ("eq", fun a b => b2s (a.eq b)),
  ("sameValue", fun a b => b2s (F64.sameValue a b)),
  ("sameValueZero", fun a b => b2s (F64.sameValueZero a b))]

/-- Random (signed) integer of up to 1100 bits; a third are exact or near ties of 54-bit
significands. -/
def randBigInt : Gen Int := do
  let neg := (← below 2) == 0
  match ← below 3 with
  | 0 =>
    let m := 2^52 + (← next).toNat % 2^52
    let k ← below 1000
    let off : Int := (← below 3 : Nat) - 1
    return sgnInt ((((2 * m + 1) * 2^k : Nat) : Int) + off).toNat neg
  | _ =>
    let bits ← below 1100
    let mut v : Nat := 0
    for _ in [0:(bits / 64 + 1)] do
      v := (v <<< 64) + (← next).toNat
    return sgnInt (v % 2^(bits + 1)) neg

/-- Random decimal literal `(sign, digits, exponent)`; a third are exact midpoints between
consecutive doubles (or one unit away in the last digit). -/
def randDecimal : Gen (Bool × Nat × Int) := do
  let neg := (← below 2) == 0
  match ← below 3 with
  | 0 =>
    -- midpoint (2M+1) * 2^(Q-1) of a random finite double M * 2^Q with Q ≤ 0
    let x := model ((← randBits) &&& 0x7FEFFFFFFFFFFFFF)
    match x with
    | .fin f =>
      if f.exp > 0 then return (neg, f.man, 0) else
      let k := (1 - f.exp).toNat
      let off : Int := (← below 3 : Nat) - 1
      return (neg, ((((2 * f.man + 1) * 5 ^ k : Nat) : Int) + off).toNat, -(k : Int))
    | _ => return (neg, 1, 0)
  | _ =>
    let len := 1 + (← below 25)
    let mut d : Nat := 0
    for _ in [0:len] do
      d := 10 * d + (← below 10)
    let e : Int := (← below 700 : Nat) - 360
    return (neg, d, e)

def runJs (seed : UInt64) (n : Nat) : IO Nat := do
  let (cases, _) ← (do
    let mut cases : Array (String × String × String) := #[]  -- (op, input line, model result)
    for (name, f) in jsUnary do
      let mut xs := specials
      for _ in [0:n] do
        xs := xs.push (← randBits)
        xs := xs.push (← niceBits)
      for a in xs do
        cases := cases.push (name, s!"{name} {hex a}", f (model a))
    for (name, f) in jsBinary do
      let mut ps : Array (UInt64 × UInt64) := #[]
      for a in specials do
        for _ in [0:3] do
          ps := ps.push (a, ← pick specials)
      for _ in [0:n] do
        ps := ps.push (← randPair)
        ps := ps.push (← niceBits, ← niceBits)
      for (a, b) in ps do
        cases := cases.push (name, s!"{name} {hex a} {hex b}", f (model a) (model b))
    for _ in [0:2*n] do
      let v ← randBigInt
      cases := cases.push ("ofBigInt", s!"ofBigInt {v}", r64 (F64.ofBigInt v))
    for _ in [0:2*n] do
      let (neg, d, e) ← randDecimal
      let x := F64.ofFrac neg (d * 10 ^ e.toNat) (10 ^ (-e).toNat) 0
      cases := cases.push ("dec", s!"dec {b2s neg} {d} {e}", r64 x)
    return cases : Gen _).run seed
  let inPath := "scratch/f64/js_in.txt"
  let outPath := "scratch/f64/js_out.txt"
  IO.FS.writeFile inPath (String.intercalate "\n" (cases.toList.map (·.2.1)) ++ "\n")
  let out ← IO.Process.output
    { cmd := "node", args := #["tests/f64_node_ref.js", inPath, outPath] }
  if out.exitCode != 0 then
    throw (IO.userError s!"node failed ({out.exitCode}): {out.stderr}")
  let res := ((← IO.FS.readFile outPath).splitOn "\n").toArray
  if res.size < cases.size then
    throw (IO.userError s!"node returned {res.size} lines for {cases.size} cases")
  let mut stats : Array Stat := #[]
  let mut idx : Std.HashMap String Nat := {}
  for (op, line, want) in cases, got in res do
    let i ← match idx[op]? with
      | some i => pure i
      | none =>
        idx := idx.insert op stats.size
        stats := stats.push { name := "v8." ++ op }
        pure (stats.size - 1)
    stats := stats.modify i fun s =>
      s.push (got == want) fun _ => s!"{line}: node {got} model {want}"
  let mut total := 0
  for s in stats do
    s.print
    total := total + s.mism
  return total

end F64Diff

def main (args : List String) : IO UInt32 := do
  let mode := args.getD 0 "all"
  let seed := (args.getD 1 "1").toNat!.toUInt64
  let n := (args.getD 2 "250000").toNat!
  let mut total := 0
  if mode == "all" || mode == "float" then
    total := total + (← F64Diff.runFloat seed n)
  if mode == "all" || mode == "js" then
    total := total + (← F64Diff.runJs (seed + 1) (Nat.max 1 (n / 20)))
  IO.println s!"TOTAL mismatches={total}"
  return if total == 0 then 0 else 1
