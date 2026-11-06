import EquivLean.Modernize.Cbstm03a.Java.Iface0

/-!
# CBSTM03A → Java: the contracts of the numeric and text helpers

In the conventions of `CbA.Iface0`: string results are new objects (`σ.next ≤ x`), the heap only grows
(`Grows σ σ'`), class-initialization states and statics are unchanged; methods that allocate nothing have
`σ' = σ`; methods that call other methods of `Cbstm03a` require the class initialized
(`σ.initOf "Cbstm03a" = .done`, also part of `CP037At`). Results are described by pure functions of the arguments (`Int`/`Nat`, and the texts `zpadStr`,
`fixStr` of the CBSTM03B proofs). Numbers are exact without bounds where the code is (`pow10`: `10 ^ n` modulo
`2 ^ 64`; `decodeZoned`: its value modulo `2 ^ 64`); the only excluded long is `Long.MIN_VALUE`, whose
negation overflows (`zu`, `zs`, `trunc11`, `fmtCurrBal`, `fmtZ`).

* `pow10(n)`: `10 ^ n` (`1` for `n ≤ 0`), as a `long`;
* `zu(v, n)`: the last `n ≥ 0` digits of `|v|` (`zpadStr`);
* `zs(v, n)`: the last `n ≥ 1` digits of `|v|`, the last one overpunched with the sign (`zsStr`);
* `trunc11(v)`: `v` with its magnitude cut to the last 11 digits, sign kept (`trunc11Z`);
* `fmtCurrBal(v)`: `9(9).99` of `|v|`'s last 11 digits and a sign character, `-` or space (`currStr`);
* `fmtZ(v)`: the same with the integer part's leading zeros as spaces (`fmtZStr`);
* `decodeZoned(s)`: the value of a zoned-decimal text (`zonedVal`, the loop's digits and sign `zAcc`);
* `ebc(c)`: the EBCDIC code of `c` by the `CP037` table (first index), `256 + c` when there is none (`ebcIdx`);
  the table is the static `CP037` (`CP037At σ`: the class is initialized and the static holds an `int` array
  with the entries `cp037Table`);
* `ebcCompare(a, b)`: `-1`, `0`, `1` by the EBCDIC order of the texts, the shorter padded with spaces (`ebcCmp`);
* `app(dst, cap, src, delim)`: appends to the builder `dst` the part of `src` before `delim` (all of `src` for
  `delim == null` or not found), cut so that the builder holds at most `cap` characters (`appStr`); only `dst`
  changes among the old objects (`Keeps (· = dst)`);
* `para(p, f)`, `star(p, f)`: the 100-character display lines built by `app` (`paraStr`, `starStr`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr digitChar argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

/-! ## References and signatures -/

abbrev pow10Ref : MethodRef := Gen.Cbstm03a.«pow10(int)».ref
abbrev zuRef : MethodRef := Gen.Cbstm03a.«zu(long,int)».ref
abbrev zsRef : MethodRef := Gen.Cbstm03a.«zs(long,int)».ref
abbrev trunc11Ref : MethodRef := Gen.Cbstm03a.«trunc11(long)».ref
abbrev fmtCurrBalRef : MethodRef := Gen.Cbstm03a.«fmtCurrBal(long)».ref
abbrev fmtZRef : MethodRef := Gen.Cbstm03a.«fmtZ(long)».ref
abbrev decodeZonedRef : MethodRef := Gen.Cbstm03a.«decodeZoned(java.lang.String)».ref
abbrev ebcRef : MethodRef := Gen.Cbstm03a.«ebc(char)».ref
abbrev ebcCompareRef : MethodRef := Gen.Cbstm03a.«ebcCompare(java.lang.String,java.lang.String)».ref
abbrev appRef : MethodRef :=
  Gen.Cbstm03a.«app(java.lang.StringBuilder,int,java.lang.String,java.lang.String)».ref
abbrev paraRef : MethodRef := Gen.Cbstm03a.«para(java.lang.String,java.lang.String)».ref
abbrev starRef : MethodRef := Gen.Cbstm03a.«star(java.lang.String,java.lang.String)».ref

def pow10Sig : MethodSig := ⟨"Cbstm03a", .prim .long, "pow10", [.prim .int]⟩
def zuSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "zu", [.prim .long, .prim .int]⟩
def zsSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "zs", [.prim .long, .prim .int]⟩
def trunc11Sig : MethodSig := ⟨"Cbstm03a", .prim .long, "trunc11", [.prim .long]⟩
def fmtCurrBalSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "fmtCurrBal", [.prim .long]⟩
def fmtZSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "fmtZ", [.prim .long]⟩
def decodeZonedSig : MethodSig := ⟨"Cbstm03a", .prim .long, "decodeZoned", [.cls "java.lang.String"]⟩
def ebcSig : MethodSig := ⟨"Cbstm03a", .prim .int, "ebc", [.prim .char]⟩
def ebcCompareSig : MethodSig :=
  ⟨"Cbstm03a", .prim .int, "ebcCompare", [.cls "java.lang.String", .cls "java.lang.String"]⟩
def appSig : MethodSig :=
  ⟨"Cbstm03a", .void, "app", [.cls "java.lang.StringBuilder", .prim .int, .cls "java.lang.String",
    .cls "java.lang.String"]⟩
def paraSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "para", [.cls "java.lang.String", .cls "java.lang.String"]⟩
def starSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "star", [.cls "java.lang.String", .cls "java.lang.String"]⟩

/-! ## Texts and numbers -/

/-- A string argument that is not `null` (of `int` length, as every Java string). -/
def StrNN (σ : State) (v : Value) : Prop :=
  ∃ x s, v = .ref x ∧ σ.heap x = some (.str s) ∧ s.length < 2147483648

/-- The overpunched last character of a zoned number: digit `d`, negative or not (`{`, `A`–`I`; `}`, `J`–`R`). -/
def ovpChar (neg : Bool) (d : Nat) : JChar :=
  BitVec.ofNat 16 (if neg then (if d = 0 then 125 else 73 + d) else (if d = 0 then 123 else 64 + d))

/-- `zs(v, n)`: the last `n ≥ 1` digits of `|v|`, the last one overpunched with the sign of `v`. -/
def zsStr (v : Int) (n : Nat) : JStr :=
  zpadStr (v.natAbs / 10) (n - 1) ++ [ovpChar (decide (v < 0)) (v.natAbs % 10)]

/-- `trunc11(v)`: the sign of `v` and the last 11 digits of `|v|`. -/
def trunc11Z (v : Int) : Int :=
  if v < 0 then -((v.natAbs % 100000000000 : Nat) : Int) else ((v.natAbs % 100000000000 : Nat) : Int)

/-- The sign character of the formatted amounts: `-` for a negative value, otherwise a space. -/
def signStr (v : Int) : JStr := JStr.ofString (if v < 0 then "-" else " ")

/-- `fmtCurrBal(v)`: the last 11 digits of `|v|` as `9(9).99`, then the sign character. -/
def currStr (v : Int) : JStr :=
  zpadStr (v.natAbs / 100) 9 ++ JStr.ofString "." ++ zpadStr v.natAbs 2 ++ signStr v

/-- The number of leading `'0'` characters of a text. -/
def lead0 : JStr → Nat
  | [] => 0
  | c :: s => if c = digitChar 0 then lead0 s + 1 else 0

/-- `fmtZ(v)`: `currStr v` with the leading zeros of the integer part as spaces. -/
def fmtZStr (v : Int) : JStr :=
  List.replicate (lead0 (zpadStr (v.natAbs / 100) 9)) space ++
    (zpadStr (v.natAbs / 100) 9).drop (lead0 (zpadStr (v.natAbs / 100) 9)) ++
    JStr.ofString "." ++ zpadStr v.natAbs 2 ++ signStr v

/-- `(c & 0x0F) % 10`: the digit `decodeZoned` takes from a character that is not a digit. -/
def lowDigit (c : JChar) : Nat := c.toNat % 16 % 10

/-- `decodeZoned`'s digit and sign for a last character `c` that is not a digit (`neg`: the sign so far). -/
def zLast (c : JChar) (neg : Bool) : Nat × Bool :=
  if c.toNat = 123 then (0, neg)
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 73 then (c.toNat - 64, neg)
  else if c.toNat = 125 then (0, true)
  else if 74 ≤ c.toNat ∧ c.toNat ≤ 82 then (c.toNat - 73, true)
  else if 112 ≤ c.toNat ∧ c.toNat ≤ 121 then (c.toNat - 112, true)
  else (lowDigit c, neg)

/-- `decodeZoned`'s magnitude and sign after the first `i` characters of `s` (its loop, exactly). -/
def zAcc (s : JStr) : Nat → Nat × Bool
  | 0 => (0, false)
  | i + 1 =>
    if 48 ≤ (s.getD i 0).toNat ∧ (s.getD i 0).toNat ≤ 57 then
      ((zAcc s i).1 * 10 + ((s.getD i 0).toNat - 48), (zAcc s i).2)
    else if i + 1 = s.length then
      ((zAcc s i).1 * 10 + (zLast (s.getD i 0) (zAcc s i).2).1, (zLast (s.getD i 0) (zAcc s i).2).2)
    else ((zAcc s i).1 * 10 + lowDigit (s.getD i 0), (zAcc s i).2)

/-- `decodeZoned(s)`: the signed value of the zoned text `s`. -/
def zonedVal (s : JStr) : Int :=
  if (zAcc s s.length).2 then -((zAcc s s.length).1 : Int) else ((zAcc s s.length).1 : Int)

/-- The static `CP037` of `Cbstm03a`: EBCDIC code → Unicode. -/
def cp037Table : List Nat := [
  0x00, 0x01, 0x02, 0x03, 0x9C, 0x09, 0x86, 0x7F, 0x97, 0x8D, 0x8E, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
  0x10, 0x11, 0x12, 0x13, 0x9D, 0x85, 0x08, 0x87, 0x18, 0x19, 0x92, 0x8F, 0x1C, 0x1D, 0x1E, 0x1F,
  0x80, 0x81, 0x82, 0x83, 0x84, 0x0A, 0x17, 0x1B, 0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x05, 0x06, 0x07,
  0x90, 0x91, 0x16, 0x93, 0x94, 0x95, 0x96, 0x04, 0x98, 0x99, 0x9A, 0x9B, 0x14, 0x15, 0x9E, 0x1A,
  0x20, 0xA0, 0xE2, 0xE4, 0xE0, 0xE1, 0xE3, 0xE5, 0xE7, 0xF1, 0xA2, 0x2E, 0x3C, 0x28, 0x2B, 0x7C,
  0x26, 0xE9, 0xEA, 0xEB, 0xE8, 0xED, 0xEE, 0xEF, 0xEC, 0xDF, 0x21, 0x24, 0x2A, 0x29, 0x3B, 0xAC,
  0x2D, 0x2F, 0xC2, 0xC4, 0xC0, 0xC1, 0xC3, 0xC5, 0xC7, 0xD1, 0xA6, 0x2C, 0x25, 0x5F, 0x3E, 0x3F,
  0xF8, 0xC9, 0xCA, 0xCB, 0xC8, 0xCD, 0xCE, 0xCF, 0xCC, 0x60, 0x3A, 0x23, 0x40, 0x27, 0x3D, 0x22,
  0xD8, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0xAB, 0xBB, 0xF0, 0xFD, 0xFE, 0xB1,
  0xB0, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0xAA, 0xBA, 0xE6, 0xB8, 0xC6, 0xA4,
  0xB5, 0x7E, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7A, 0xA1, 0xBF, 0xD0, 0xDD, 0xDE, 0xAE,
  0x5E, 0xA3, 0xA5, 0xB7, 0xA9, 0xA7, 0xB6, 0xBC, 0xBD, 0xBE, 0x5B, 0x5D, 0xAF, 0xA8, 0xB4, 0xD7,
  0x7B, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0xAD, 0xF4, 0xF6, 0xF2, 0xF3, 0xF5,
  0x7D, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0xB9, 0xFB, 0xFC, 0xF9, 0xFA, 0xFF,
  0x5C, 0xF7, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A, 0xB2, 0xD4, 0xD6, 0xD2, 0xD3, 0xD5,
  0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0xB3, 0xDB, 0xDC, 0xD9, 0xDA, 0x9F]

/-- The static `CP037` as `<clinit>` builds it: an `int` array. -/
def cp037Arr : List Value := cp037Table.map fun n => .int (BitVec.ofNat 32 n)

/-- `Cbstm03a` is initialized and its static `CP037` holds the code page table. -/
def CP037At (σ : State) : Prop :=
  σ.initOf "Cbstm03a" = .done ∧
    ∃ a, σ.static ("Cbstm03a", "CP037") = some (.ref a) ∧ σ.heap a = some (.array (.prim .int) cp037Arr)

/-- `ebc`'s loop from index `i` over the rest `ts` of the table. -/
def ebcGo (c : Nat) : List Nat → Nat → Nat
  | [], _ => 256 + c
  | t :: ts, i => if t = c then i else ebcGo c ts (i + 1)

/-- `ebc(c)`: the first index of `c` in `cp037Table`, `256 + c` when there is none. -/
def ebcIdx (c : Nat) : Nat := ebcGo c cp037Table 0

/-- `ebcCompare`'s loop over the space-padded texts: the first position whose characters differ in their
EBCDIC codes decides. -/
def ebcScan : JStr → JStr → Int
  | ca :: xs, cb :: ys =>
    if ca ≠ cb ∧ ebcIdx ca.toNat ≠ ebcIdx cb.toNat then
      (if ebcIdx ca.toNat < ebcIdx cb.toNat then -1 else 1)
    else ebcScan xs ys
  | _, _ => 0

/-- `ebcCompare(a, b)`: `0` for equal texts, otherwise the scan of both padded to the longer length. -/
def ebcCmp (a b : JStr) : Int :=
  if a = b then 0 else ebcScan (fixStr a (max a.length b.length)) (fixStr b (max a.length b.length))

/-- `app`'s text before the cut: the part of `s` before the first `d` (all of `s` without `d` or a match). -/
def cutAt (s : JStr) : Option JStr → JStr
  | none => s
  | some d => if 0 ≤ JStr.indexOf s d then s.take (JStr.indexOf s d).toNat else s

/-- `app(dst, cap, src, delim)` on a builder holding `b`: `b` with `cutAt src delim` appended, cut at `cap`. -/
def appStr (b : JStr) (cap : Int) (src : JStr) (d : Option JStr) : JStr :=
  if cap - b.length ≤ 0 then b else b ++ (cutAt src d).take (cap - b.length).toNat

/-- `para(p, f)`: the prefix to its `*`, the field to its double space, a double space and `</p>`, cut and
padded to 100 characters. -/
def paraStr (p f : JStr) : JStr :=
  fixStr (appStr (appStr (appStr (appStr [] 100 p (some (JStr.ofString "*"))) 100 f
    (some (JStr.ofString "  "))) 100 (JStr.ofString "  ") none) 100 (JStr.ofString "</p>")
    (some (JStr.ofString "*"))) 100

/-- `star(p, f)`: the prefix and the field each to its `*`, then `</p>`, cut and padded to 100 characters. -/
def starStr (p f : JStr) : JStr :=
  fixStr (appStr (appStr (appStr [] 100 p (some (JStr.ofString "*"))) 100 f (some (JStr.ofString "*"))) 100
    (JStr.ofString "</p>") (some (JStr.ofString "*"))) 100

/-! ## Contracts

A method that calls another method of `Cbstm03a` (`staticinvoke`) or reads its statics needs the class
initialized (`σ.initOf "Cbstm03a" = .done`): otherwise the call runs `<clinit>`, which writes the statics.
`spacesSpecI`, `fixSpecI`: `Iface0`'s `spacesSpec`, `fixSpec` with this precondition added (CBSTM03A's
`spaces` calls `repeat`, `fix` calls `spaces`). -/

/-- `spaces(n)`, `n ≤ 2^30`: `n` spaces (none for `n ≤ 0`); `Cbstm03a` initialized. -/
def spacesSpecI : Spec := Spec.of
  (fun args σ => ∃ n : I32, args = [.int n] ∧ n.toInt ≤ 1073741824 ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     ∃ x, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str (List.replicate n.toInt.toNat space)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `fix(s, n)`: `s` (`""` for `null`) cut or space-padded to `0 ≤ n ≤ 2^30` characters; `Cbstm03a` initialized. -/
def fixSpecI : Spec := Spec.of
  (fun args σ => ∃ sv n, args = [sv, .int n] ∧ StrOk σ sv ∧ 0 ≤ n.toInt ∧ n.toInt ≤ 1073741824 ∧
     σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ sv n, args = [sv, .int n] →
     ∃ x, r = some (.ref x) ∧ (σ.next ≤ x ∨ sv = .ref x) ∧
       σ'.heap x = some (.str (fixStr (argText σ sv) n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `pow10(n)`: `10 ^ n` modulo `2 ^ 64` (`1` for `n ≤ 0`). -/
def pow10Spec : Spec := Spec.of
  (fun args _ => ∃ n : I32, args = [.int n])
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     r = some (.long (BitVec.ofNat 64 (10 ^ n.toInt.toNat))) ∧ σ' = σ)

/-- `zu(v, n)`: the last `n ≥ 0` digits of `|v|`. -/
def zuSpec : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧ -9223372036854775808 < v.toInt ∧
     0 ≤ n.toInt ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str (zpadStr v.toInt.natAbs n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `zs(v, n)`: the last `n ≥ 1` digits of `|v|`, the last one overpunched with the sign. -/
def zsSpec : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧ -9223372036854775808 < v.toInt ∧
     1 ≤ n.toInt ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str (zsStr v.toInt n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `trunc11(v)`: the sign of `v` with the last 11 digits of `|v|`. -/
def trunc11Spec : Spec := Spec.of
  (fun args _ => ∃ v : I64, args = [.long v] ∧ -9223372036854775808 < v.toInt)
  (fun args σ r σ' => ∀ v : I64, args = [.long v] →
     r = some (.long (BitVec.ofInt 64 (trunc11Z v.toInt))) ∧ σ' = σ)

/-- `fmtCurrBal(v)`: `currStr v`. -/
def fmtCurrBalSpec : Spec := Spec.of
  (fun args σ => ∃ v : I64, args = [.long v] ∧ -9223372036854775808 < v.toInt ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ v : I64, args = [.long v] →
     ∃ x, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str (currStr v.toInt)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `fmtZ(v)`: `fmtZStr v`. -/
def fmtZSpec : Spec := Spec.of
  (fun args σ => ∃ v : I64, args = [.long v] ∧ -9223372036854775808 < v.toInt ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ v : I64, args = [.long v] →
     ∃ x, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str (fmtZStr v.toInt)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `decodeZoned(s)`: the value of the zoned text `s` (not `null`) modulo `2 ^ 64`. -/
def decodeZonedSpec : Spec := Spec.of
  (fun args σ => ∃ sv, args = [sv] ∧ StrNN σ sv)
  (fun args σ r σ' => ∀ sv, args = [sv] →
     r = some (.long (BitVec.ofInt 64 (zonedVal (argText σ sv)))) ∧ σ' = σ)

/-- `ebc(c)`: the EBCDIC code of the character `c` (`256 + c` outside the code page). -/
def ebcSpec : Spec := Spec.of
  (fun args σ => ∃ c : I32, args = [.int c] ∧ CP037At σ)
  (fun args σ r σ' => ∀ c : I32, args = [.int c] →
     r = some (.int (BitVec.ofNat 32 (ebcIdx c.toNat))) ∧ σ' = σ)

/-- `ebcCompare(a, b)`: the EBCDIC order of two texts (not `null`), `-1`, `0` or `1`. -/
def ebcCompareSpec : Spec := Spec.of
  (fun args σ => ∃ av bv, args = [av, bv] ∧ StrNN σ av ∧ StrNN σ bv ∧ CP037At σ)
  (fun args σ r σ' => ∀ av bv, args = [av, bv] →
     r = some (.int (BitVec.ofInt 32 (ebcCmp (argText σ av) (argText σ bv)))) ∧ σ' = σ)

/-- `app(dst, cap, src, delim)`: the builder `dst` (of `int` length) gets `appStr`; `src` is not `null`,
`delim` may be; `cap ≥ 0`. Old objects other than `dst` are unchanged. -/
def appSpec : Spec := Spec.of
  (fun args σ => ∃ (d : Addr) (cap : I32) (sv dv : Value) (b : JStr), args = [.ref d, .int cap, sv, dv] ∧
     σ.heap d = some (.builder "java.lang.StringBuilder" b) ∧ b.length < 2147483648 ∧ 0 ≤ cap.toInt ∧
     StrNN σ sv ∧ StrOk σ dv)
  (fun args σ r σ' => ∀ (d : Addr) (cap : I32) (sv dv : Value) (b : JStr), args = [.ref d, .int cap, sv, dv] →
     σ.heap d = some (.builder "java.lang.StringBuilder" b) →
     r = none ∧
       σ'.heap d = some (.builder "java.lang.StringBuilder" (appStr b cap.toInt (argText σ sv) (strOf σ dv))) ∧
       Keeps (fun y => y = d) σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `para(p, f)`: `paraStr` of the two texts (not `null`). -/
def paraSpec : Spec := Spec.of
  (fun args σ => ∃ pv fv, args = [pv, fv] ∧ StrNN σ pv ∧ StrNN σ fv ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ pv fv, args = [pv, fv] →
     ∃ x, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str (paraStr (argText σ pv) (argText σ fv))) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `star(p, f)`: `starStr` of the two texts (not `null`). -/
def starSpec : Spec := Spec.of
  (fun args σ => ∃ pv fv, args = [pv, fv] ∧ StrNN σ pv ∧ StrNN σ fv ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ pv fv, args = [pv, fv] →
     ∃ x, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str (starStr (argText σ pv) (argText σ fv))) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-! ## Callee tables -/

def spacesCallees : Contracts := [(repeatSig, repeatSpec)]
def fixCallees : Contracts := [(spacesSig, spacesSpecI)]
def zuCallees : Contracts := [(pow10Sig, pow10Spec), (zeroPadSig, zeroPadSpec)]
def fmtCallees : Contracts := [(zeroPadSig, zeroPadSpec), (spacesSig, spacesSpecI)]
def ebcCompareCallees : Contracts := [(ebcSig, ebcSpec)]
def paraCallees : Contracts := [(appSig, appSpec), (fixSig, fixSpecI)]

end EquivLean.Modernize.Cbstm03a.Java
