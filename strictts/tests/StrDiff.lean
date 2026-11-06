/-
Differential test of the StrictTS string layer against Node/V8.

  node tests/str_node_ref.js DIR [SEED]     -- writes DIR/{fmt,parse,bigint,str}.txt
  lake exe strdiff DIR/fmt.txt ...          -- recomputes every case in Lean and compares

The case format is documented in `tests/str_node_ref.js`. Output: one line
`OP <name> cases=<n> mismatches=<k>` per operation, the first 5 mismatches of each, `INFO` lines
for observed spec-vs-V8 disagreements, and a final `TOTAL` line; exit code 1 on any mismatch.
-/
import Std.Data.HashMap
import StrictTS.Str.JSStr
import StrictTS.Num.Format
import StrictTS.Num.Parse

open StrictTS StrictTS.NumFormat StrictTS.NumParse

namespace StrDiff

/-! ## Decoding and encoding -/

def splitChar (sep : Char) (s : String) : List String :=
  let rec go : List Char → List Char → List String
    | [], cur => [String.ofList cur.reverse]
    | c :: cs, cur => if c = sep then String.ofList cur.reverse :: go cs [] else go cs (c :: cur)
  go s.toList []

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

def parseHex? (s : String) : Option Nat :=
  if s.isEmpty then none
  else s.toList.foldlM (fun acc c => (hexDigit? c).map (acc * 16 + ·)) 0

def hexStr (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def pad16 (s : String) : String := String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- The double with IEEE-754 bit pattern `b`. -/
def ofBits (b : Nat) : F64 :=
  let neg : Bool := b / 2 ^ 63 % 2 == 1
  let be : Nat := b / 2 ^ 52 % 2048
  let fr : Nat := b % 2 ^ 52
  if be == 2047 then (if fr == 0 then .inf neg else .nan)
  else if be == 0 then F64.mkFin neg fr (-1074)
  else F64.mkFin neg (fr + 2 ^ 52) ((be : Int) - 1075)

/-- Bit pattern (canonical quiet NaN `7ff8000000000000`). -/
def toBits : F64 → Nat
  | .nan => 0x7ff8000000000000
  | .inf neg => (if neg then 2 ^ 63 else 0) + 0x7ff0000000000000
  | .fin x =>
    let s := if x.neg then 2 ^ 63 else 0
    if x.man < 2 ^ 52 then s + x.man
    else s + (x.exp + 1075).toNat * 2 ^ 52 + (x.man - 2 ^ 52)

def encD (x : F64) : String := pad16 (hexStr (toBits x))

def decS? (s : String) : Option JSStr :=
  if s == "~" then some JSStr.empty
  else (splitChar '.' s).mapM (fun h => (parseHex? h).map Nat.toUInt16) |>.map JSStr.mk

def encS (j : JSStr) : String :=
  if j.units.isEmpty then "~" else ".".intercalate (j.units.map fun u => hexStr u.toNat)

def decL? (s : String) : Option (List JSStr) :=
  match s.toList with
  | 'L' :: rest => if rest.isEmpty then some [] else (splitChar ',' (String.ofList rest)).mapM decS?
  | _ => none

def encL (l : List JSStr) : String := "L" ++ ",".intercalate (l.map encS)

def decNats? (s : String) : Option (List Nat) :=
  if s == "~" then some [] else (splitChar ',' s).mapM String.toNat?

def encNats (l : List Nat) : String := if l.isEmpty then "~" else ",".intercalate (l.map toString)

def encOpt (o : Option JSStr) : String := o.elim "!" encS

def ascii (j : JSStr) : String := j.toLeanString

def bit (b : Bool) : String := if b then "1" else "0"

/-! ## Evaluation of one case -/

/-- Our result for a case (fields without the expected value), or an error message. -/
def eval (op : String) (a : Array String) : Except String String := do
  let arg (i : Nat) : Except String String := match a[i]? with
    | some s => pure s
    | none => throw s!"missing field {i}"
  let str (i : Nat) : Except String JSStr := do
    match decS? (← arg i) with
    | some j => pure j
    | none => throw s!"bad string field {i}"
  let dbl (i : Nat) : Except String F64 := do
    match parseHex? (← arg i) with
    | some b => pure (ofBits b)
    | none => throw s!"bad double field {i}"
  let nat (i : Nat) : Except String Nat := do
    match (← arg i).toNat? with
    | some n => pure n
    | none => throw s!"bad nat field {i}"
  let int (i : Nat) : Except String Int := do
    match (← arg i).toInt? with
    | some n => pure n
    | none => throw s!"bad int field {i}"
  -- optional numeric argument: "u" ↦ `d`
  let natU (i : Nat) (d : Nat) : Except String Nat := do
    if (← arg i) == "u" then pure d else nat i
  let intU (i : Nat) (d : Int) : Except String Int := do
    if (← arg i) == "u" then pure d else int i
  match op with
  -- number formatting
  | "ts" => return ascii (toJSString (← dbl 0))
  | "tr" => return (toStringRadix (← dbl 0) (← nat 1)).elim "!" ascii
  | "tf" => return (toFixed (← dbl 0) (← nat 1)).elim "!" ascii
  | "tp" => return (toPrecision (← dbl 0) (← nat 1)).elim "!" ascii
  | "te" =>
    let f ← if (← arg 1) == "u" then pure none else some <$> nat 1
    return (toExponential (← dbl 0) f).elim "!" ascii
  | "bt" => return (bigintToStringRadix (← int 0) (← nat 1)).elim "!" ascii
  -- parsing
  | "sn" => return encD (stringToNumber (← str 0))
  | "pf" => return encD (parseFloat (← str 0))
  | "pi" => return encD (parseInt (← str 0) (← intU 1 0))
  | "bi" => return (stringToBigInt (← str 0)).elim "!" toString
  -- strings
  | "cca" => return ((← str 0).charCodeAt? (← nat 1)).elim "!" (toString ·.toNat)
  | "cpa" => return ((← str 0).codePointAt? (← nat 1)).elim "!" toString
  | "cha" => return encS ((← str 0).charAt (← nat 1))
  | "at" => return encOpt ((← str 0).at? (← int 1))
  | "sl" => let s ← str 0; return encS (s.slice (← int 1) (← intU 2 s.length))
  | "ss" => let s ← str 0; return encS (s.substring (← int 1) (← intU 2 s.length))
  | "io" => return toString ((← str 0).indexOf (← str 1) (← natU 2 0))
  | "inc" => return bit ((← str 0).includes (← str 1) (← natU 2 0))
  | "sw" => return bit ((← str 0).startsWith (← str 1) (← natU 2 0))
  | "lio" => let s ← str 0; return toString (s.lastIndexOf (← str 1) (← natU 2 s.length))
  | "ew" => let s ← str 0; return bit (s.endsWith (← str 1) (← natU 2 s.length))
  | "tm" => return encS (← str 0).trim
  | "tms" => return encS (← str 0).trimStart
  | "tme" => return encS (← str 0).trimEnd
  | "ps" => return encS ((← str 0).padStart (← nat 1) (← str 2))
  | "pe" => return encS ((← str 0).padEnd (← nat 1) (← str 2))
  | "rp" => return encS ((← str 0).repeat (← nat 1))
  | "sp" =>
    let lim ← if (← arg 2) == "u" then pure none else some <$> nat 2
    return encL ((← str 0).split (← str 1) lim)
  | "rf" => return encS ((← str 0).replaceFirst (← str 1) (← str 2))
  | "ra" => return encS ((← str 0).replaceAll (← str 1) (← str 2))
  | "cc" =>
    match decL? (← arg 1) with
    | some l => return encS ((← str 0).concat l)
    | none => throw "bad list"
  | "up" => return encS (← str 0).toUpperASCII
  | "lo" => return encS (← str 0).toLowerASCII
  | "asc" => return bit (← str 0).isASCII
  | "fcc" =>
    match decNats? (← arg 0) with
    | some l => return encS (JSStr.fromCharCodes l)
    | none => throw "bad nats"
  | "fcp" =>
    match decNats? (← arg 0) with
    | some l => return encOpt (JSStr.fromCodePoint? l)
    | none => throw "bad nats"
  | "cps" => return encNats (← str 0).codePoints
  | "cmp" =>
    let s ← str 0
    let t ← str 1
    return bit (s.lt t) ++ bit (s.le t) ++ bit (s.gt t) ++ bit (s.ge t)
  | "join" =>
    match decL? (← arg 0) with
    | some l => return encS (JSStr.join (← str 1) l)
    | none => throw "bad list"
  | _ => throw s!"unknown op {op}"

/-! ## Internal consistency checks run alongside the differential cases -/

/-- Extra checks keyed by derived op names: `(name, expected, ours)`. -/
def extras (op : String) (a : Array String) (expected : String) : List (String × String × String) :=
  match op, a[0]? |>.bind parseHex? |>.map ofBits with
  | "ts", some d =>
    -- `Number(String(x))` is `x` (bit for bit; all NaNs alike; `String(-0)` is `"0"`)
    let back := if toBits d = 2 ^ 63 then F64.zero false else d
    let rt := ("ts.roundtrip-through-stringToNumber", encD back, encD (stringToNumber (toJSString d)))
    match d with
    | .fin x =>
      -- the integer fast path agrees with the general shortest-digit search
      match intValue? x.man x.exp with
      | some v =>
        if x.man ≠ 0 ∧ v < 2 ^ 53 then
          let g := JSStr.toLeanString ⟨(if x.neg then [45] else []) ++ magGeneral x.man x.exp⟩
          [rt, ("ts.general-on-int", expected, g)]
        else [rt]
      | none => [rt]
    | _ => [rt]
  | "bt", _ =>
    -- `BigInt(String(v)) === v`, and with a 0x/0o/0b prefix for non-negative values
    match a[0]?.bind String.toInt?, a[1]?.bind String.toNat? with
    | some v, some r =>
      let pre : Option String := if r = 10 then some "" else if v < 0 then none
        else if r = 16 then some "0x" else if r = 8 then some "0o" else if r = 2 then some "0b" else none
      match pre, bigintToStringRadix v r with
      | some p, some str =>
        [("bt.roundtrip-through-stringToBigInt", toString v,
          (stringToBigInt (JSStr.ofString p ++ str)).elim "!" toString)]
      | _, _ => []
    | _, _ => []
  | "tr", some (.fin x) =>
    match intValue? x.man x.exp, (a[1]?.bind String.toNat?) with
    | some v, some r =>
      if x.man ≠ 0 ∧ v < 2 ^ 53 ∧ 2 ≤ r ∧ r ≤ 36 ∧ r ≠ 10 then
        let g := JSStr.toLeanString ⟨(if x.neg then [45] else []) ++ v8RadixInt r (x.man, x.exp)⟩
        [("tr.v8-path-on-small-int", expected, g)]
      else []
    | _, _ => []
  | _, _ => []

/-- Spec-vs-V8 observations: V8's radix output for large integers vs the exact integer digits. -/
def info (op : String) (a : Array String) (expected : String) : Option String :=
  match op, a[0]? |>.bind parseHex? |>.map ofBits, a[1]?.bind String.toNat? with
  | "tr", some (.fin x), some r =>
    match intValue? x.man x.exp with
    | some v =>
      if x.man ≠ 0 ∧ 2 ^ 53 ≤ v ∧ 2 ≤ r ∧ r ≤ 36 ∧ r ≠ 10 then
        let exact := JSStr.toLeanString ⟨(if x.neg then [45] else []) ++ natDigits r v⟩
        some (if exact == expected then "tr.v8-equals-exact-digits(int>=2^53)" else
          "tr.v8-differs-from-exact-digits(int>=2^53)")
      else none
    | none => none
  | _, _, _ => none

/-! ## Driver -/

structure Stat where
  cases : Nat := 0
  bad : Nat := 0
  examples : Array String := #[]

def bump (m : Std.HashMap String Stat) (name : String) (ok : Bool) (msg : Unit → String) :
    Std.HashMap String Stat :=
  let st := m.getD name {}
  let st := { st with cases := st.cases + 1, bad := st.bad + (if ok then 0 else 1) }
  let st := if !ok && st.examples.size < 5 then { st with examples := st.examples.push (msg ()) } else st
  m.insert name st

def trunc (s : String) (n : Nat := 400) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ "..."

def runFile (path : String) (m : Std.HashMap String Stat) (infos : Std.HashMap String Nat) :
    IO (Std.HashMap String Stat × Std.HashMap String Nat) := do
  let lines ← IO.FS.lines path
  let mut m := m
  let mut infos := infos
  for line in lines do
    if line.isEmpty then continue
    let fs := (splitChar ' ' line).toArray
    if fs.size < 2 then
      m := bump m "parse-error" false (fun _ => trunc line)
      continue
    let op := fs[0]!
    let expected := fs[fs.size - 1]!
    let args := fs.extract 1 (fs.size - 1)
    match eval op args with
    | .ok ours => m := bump m op (ours == expected) (fun _ => s!"{trunc line} | ours={trunc ours}")
    | .error e => m := bump m op false (fun _ => s!"{trunc line} | error: {e}")
    for (name, exp, ours) in extras op args expected do
      m := bump m name (ours == exp) (fun _ => s!"{trunc line} | ours={trunc ours}")
    if let some key := info op args expected then
      infos := infos.insert key (infos.getD key 0 + 1)
  return (m, infos)

end StrDiff

open StrDiff in
def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: strdiff CASEFILE..."
    return 2
  let mut m : Std.HashMap String Stat := {}
  let mut infos : Std.HashMap String Nat := {}
  for p in args do
    (m, infos) ← runFile p m infos
  let names := (m.toList.map (·.1)).toArray.qsort (· < ·)
  let mut total := 0
  let mut totalBad := 0
  for n in names do
    let st := m.getD n {}
    total := total + st.cases
    totalBad := totalBad + st.bad
    IO.println s!"OP {n} cases={st.cases} mismatches={st.bad}"
    for ex in st.examples do
      IO.println s!"  MISMATCH {n}: {ex}"
  for (k, v) in infos.toList.toArray.qsort (fun a b => a.1 < b.1) do
    IO.println s!"INFO {k} cases={v}"
  IO.println s!"TOTAL cases={total} mismatches={totalBad}"
  return (if totalBad = 0 then 0 else 1)
