/-
  Jimple/Native.lean

  Library models. Library classes are not executed from their JDK bytecode; their
  methods are given by Lean functions over the native representations of
  `Jimple/Value.lean`. A model may
  * return a value, throw a (library) exception, or go `wrong` (no model / undefined),
  * ask for a nondeterministic choice (`Res.choose`) where the JDK leaves behaviour
    unspecified,
  * call back into application code (`Res.call`), e.g. `toString()` of an
    application object passed to `StringBuilder.append(Object)`.
  Calls with no model return `none`; the semantics turns that into `wrong`, so proofs
  never silently assume behaviour for an unmodelled library method.
-/
import Jimple.Monad
import Jimple.Unicode
import Jimple.ClassInit

namespace Jimple
namespace Native

/-! ### Result and argument helpers -/

def ok (v : Value) (σ : State) : NRes := .ret (.ok v σ)
def okVoid (σ : State) : NRes := .ret (.ok .null σ)
def okObj (o : Obj) (σ : State) : NRes := .ret (retObj o σ)
def okStr (s : JStr) (σ : State) : NRes := okObj (.str s) σ
def okInt (i : Int) (σ : State) : NRes := ok (.int (BitVec.ofInt 32 i)) σ
def okBool (b : Bool) (σ : State) : NRes := ok (Value.ofBool b) σ
def bad (msg : String) : NRes := .ret (.wrong msg)
def thr (cls : ClassName) (msg : Option String) (σ : State) : NRes :=
  .ret (throwNew cls (msg.map JStr.ofString) σ)
def thrNPE (σ : State) : NRes := .ret (npe σ)

def AE := "java.lang.ArithmeticException"
def IOOBE := "java.lang.IndexOutOfBoundsException"
def UOE := "java.lang.UnsupportedOperationException"
def NSEE := "java.util.NoSuchElementException"
def NFE := "java.lang.NumberFormatException"
def IAE := "java.lang.IllegalArgumentException"

def argI (v : Value) (k : I32 → NRes) : NRes :=
  match v with | .int x => k x | _ => bad "expected int"
def argL (v : Value) (k : I64 → NRes) : NRes :=
  match v with | .long x => k x | _ => bad "expected long"
def argObj (σ : State) (v : Value) (k : Addr → Obj → NRes) : NRes :=
  match v with
  | .null => thrNPE σ
  | .ref a => match σ.heap a with
    | some o => k a o
    | none => bad "dangling reference"
  | _ => bad "expected reference"
def argDec (σ : State) (v : Value) (k : BigDec → NRes) : NRes :=
  argObj σ v fun _ o => match o with | .dec d => k d | _ => bad "expected BigDecimal"
def argBigInt (σ : State) (v : Value) (k : Int → NRes) : NRes :=
  argObj σ v fun _ o => match o with | .bigInt i => k i | _ => bad "expected BigInteger"
def argStr (σ : State) (v : Value) (k : JStr → NRes) : NRes :=
  argObj σ v fun _ o => match o with | .str s => k s | _ => bad "expected String"
/-- `CharSequence` argument: a `String` or a `StringBuilder` -/
def argChars (σ : State) (v : Value) (k : JStr → NRes) : NRes :=
  argObj σ v fun _ o => match o with
    | .str s => k s | .builder _ s => k s | _ => bad "expected CharSequence"
def argRM (σ : State) (v : Value) (k : RoundingMode → NRes) : NRes :=
  argObj σ v fun _ o => match o with | .rmode r => k r | _ => bad "expected RoundingMode"
def argMC (σ : State) (v : Value) (k : MathCtx → NRes) : NRes :=
  argObj σ v fun _ o => match o with | .mctx m => k m | _ => bad "expected MathContext"
/-- legacy `int` rounding-mode constants (`BigDecimal.ROUND_*`) -/
def argRMInt (σ : State) (v : Value) (k : RoundingMode → NRes) : NRes :=
  argI v fun i => match RoundingMode.ofOrdinal? i.toNat with
    | some r => if i.toInt < 0 then thr IAE (some "Invalid rounding mode") σ else k r
    | none => thr IAE (some "Invalid rounding mode") σ

def jstr (s : String) : JStr := JStr.ofString s

/-! ### Formatting of primitives (`String.valueOf`) -/

def boolStr (b : Bool) : JStr := jstr (if b then "true" else "false")

/-- `String.valueOf` of a primitive of static type `t`; `none` for `float`/`double`
    (`Float.toString`/`Double.toString` are not modelled). -/
def primStr (t : JType) (v : Value) : Option JStr :=
  match t, v with
  | .prim .boolean, .int x => some (boolStr (x ≠ 0))
  | .prim .char, .int x => some [x.setWidth 16]
  | .prim .byte, .int x | .prim .short, .int x | .prim .int, .int x => some (JStr.ofInt x.toInt)
  | .prim .long, .long x => some (JStr.ofInt x.toInt)
  | _, _ => none

/-- Canonical bit pattern used by `Double.equals`/`Float.equals` (`doubleToLongBits`). -/
def canonBits : Value → Value
  | .double x => if JFloat.isNaN64 x then .double JFloat.nan64 else .double x
  | .float x => if JFloat.isNaN32 x then .float JFloat.nan32 else .float x
  | v => v

def toStringSub : SubSig := ⟨"toString", [], .cls "java.lang.String"⟩
def equalsSub : SubSig := ⟨"equals", [.cls "java.lang.Object"], .prim .boolean⟩
def hashCodeSub : SubSig := ⟨"hashCode", [], .prim .int⟩

def overrides (P : Program) (c : ClassName) (sub : SubSig) : Bool :=
  match P.selectVirtual c sub with
  | .jimple _ => true
  | _ => false

/-- `a.equals(b)` for receivers whose `equals` is library code; `none` when it would
    run application code or is not modelled. -/
def nEquals (P : Program) (σ : State) (a b : Value) : Option Bool :=
  match a with
  | .null => some (b == .null)
  | .ref x =>
    match σ.heap x with
    | some (.str s) => some (strOf σ b == some s)
    | some (.boxed c v) =>
      some (match objAt σ b with
        | some (_, .boxed d w) => c == d && canonBits v == canonBits w
        | _ => false)
    | some (.dec d) => some (decOf σ b == some d)
    | some (.bigInt i) => some (bigIntOf σ b == some i)
    | some (.rmode r) => some (match objAt σ b with | some (_, .rmode r') => r == r' | _ => false)
    | some (.plain c _) =>
      -- the plain-object models of library lists and sets compare elements
      if overrides P c equalsSub || c == "java.util.Arrays$ArrayList" || c == "java.util.ArrayList$SubList" ||
         c == "java.util.Collections$EmptySet" then none
      else some (b == .ref x)
    | some (.list ..) | some (.map ..) | some (.set ..) | some (.entry ..) | some (.view ..)
    | some (.mctx _) =>
      if b == .ref x then some true else none
    | some _ => some (b == .ref x)
    | none => none
  | _ => none

/-- Natural ordering (`Comparable.compareTo`) for library value objects. -/
def nCompare (σ : State) (a b : Value) : Option Int :=
  match objAt σ a, objAt σ b with
  | some (_, .str s), some (_, .str t) => some (JStr.compareTo s t).toInt
  | some (_, .dec d), some (_, .dec e) => some (d.compareTo e)
  | some (_, .bigInt i), some (_, .bigInt j) => some (if i < j then -1 else if i = j then 0 else 1)
  | some (_, .boxed c (.int x)), some (_, .boxed d (.int y)) =>
    if c == d then
      if c == "java.lang.Character" then some ((x.toNat : Int) - y.toNat)
      else if c == "java.lang.Boolean" then some ((x.toNat : Int) - y.toNat)
      else some (if x.toInt < y.toInt then -1 else if x = y then 0 else 1)
    else none
  | some (_, .boxed c (.long x)), some (_, .boxed d (.long y)) =>
    if c == d then some (if x.toInt < y.toInt then -1 else if x = y then 0 else 1) else none
  | _, _ => none

/-- Insertion into a key-sorted association list (TreeMap/TreeSet) -/
def insertSorted (σ : State) (k : Value) (v : Value) :
    List (Value × Value) → Option (List (Value × Value))
  | [] => some [(k, v)]
  | (k', v') :: rest =>
    match nCompare σ k k' with
    | none => none
    | some c =>
      if c < 0 then some ((k, v) :: (k', v') :: rest)
      else if c = 0 then some ((k', v) :: rest)
      else ((k', v') :: ·) <$> insertSorted σ k v rest

/-- Key lookup with library `equals` (hash/linked maps) or `compareTo` (tree maps). -/
def keyEq (P : Program) (σ : State) (tree : Bool) (k k' : Value) : Option Bool :=
  if tree then (· == 0) <$> nCompare σ k k' else nEquals P σ k k'

def findKey (P : Program) (σ : State) (tree : Bool) (k : Value) :
    List (Value × Value) → Option (Option (Nat × Value))
  | [] => some none
  | (k', v) :: rest =>
    match keyEq P σ tree k k' with
    | none => none
    | some true => some (some (0, v))
    | some false => (Option.map (fun (i, w) => (i + 1, w))) <$> findKey P σ tree k rest

def findElem (P : Program) (σ : State) (x : Value) : List Value → Option (Option Nat)
  | [] => some none
  | y :: rest =>
    match nEquals P σ x y with
    | none => none
    | some true => some (some 0)
    | some false => (Option.map (· + 1)) <$> findElem P σ x rest

/-- Library `toString` of library objects; `none` if application code would run. -/
def nObjStr (σ : State) (o : Obj) : Option JStr :=
  match o with
  | .str s => some s
  | .builder _ s => some s
  | .dec d => some (jstr d.toJavaString)
  | .bigInt i => some (JStr.ofInt i)
  | .rmode r => some (jstr r.name)
  | .mctx m => some (jstr s!"precision={m.prec} roundingMode={m.rm.name}")
  | .boxed "java.lang.Integer" v | .boxed "java.lang.Short" v | .boxed "java.lang.Byte" v =>
    primStr (.prim .int) v
  | .boxed "java.lang.Long" v => primStr (.prim .long) v
  | .boxed "java.lang.Character" v => primStr (.prim .char) v
  | .boxed "java.lang.Boolean" v => primStr (.prim .boolean) v
  | .plain c fs =>
    -- library exceptions with an unmodified `toString`
    if isLibClass c then
      match Fields.get fs ("java.lang.Throwable", "detailMessage") with
      | some .null => some (jstr c)
      | some m => (fun s =>
          -- `AssertionFailedError.toString` omits an empty message
          if c == "org.opentest4j.AssertionFailedError" && s.isEmpty then jstr c
          -- `ArrayComparisonFailure.toString` is `getMessage()`
          else if c == "org.junit.internal.ArrayComparisonFailure" then s
          else jstr c ++ jstr ": " ++ s) <$> strOf σ m
      | none => none
    else none
  | _ => none

def toStringSig : MethodSig := ⟨"java.lang.Object", .cls "java.lang.String", "toString", []⟩
def equalsSig : MethodSig := ⟨"java.lang.Object", .prim .boolean, "equals", [.cls "java.lang.Object"]⟩

/-- `StringJoiner.toString()` from the fields of a `java.util.StringJoiner` object: the empty value
    if nothing was added and one is set, otherwise prefix, the parts joined by the delimiter, and
    suffix. -/
def joinerStr? (σ : State) (fs : List (FieldKey × Value)) : Option JStr :=
  let c := "java.util.StringJoiner"
  let get (f : String) : Value := (Fields.get fs (c, f)).getD .null
  let str (f : String) : JStr := (strOf σ (get f)).getD []
  if get "parts" == .null && get "emptyValue" != .null then strOf σ (get "emptyValue")
  else
    let parts : List Value := match objAt σ (get "parts") with | some (_, .array _ xs) => xs | _ => []
    some (str "prefix" ++ ((parts.filterMap (strOf σ ·)).intersperse (str "delimiter")).flatten ++ str "suffix")

/-- `Object.toString()`, `Throwable.toString()`, `Enum.toString()` as library code (reached
    when the runtime class does not override `toString`); `StringJoiner.toString()`; no model for
    the `ArrayList.subList` views and `Collections.emptySet()`. -/
def libToString (P : Program) (c : ClassName) (fs : List (FieldKey × Value)) (σ : State) : NRes :=
  if c == "java.util.StringJoiner" then
    match joinerStr? σ fs with
    | some s => okStr s σ
    | none => bad "malformed StringJoiner"
  else if c == "java.util.ArrayList$SubList" || c == "java.util.Collections$EmptySet" then
    bad s!"toString of {c} is not modelled"
  else if P.isSubclass c "java.lang.Throwable" == some true then
    if overrides P c ⟨"getLocalizedMessage", [], .cls "java.lang.String"⟩ ∨
       overrides P c ⟨"getMessage", [], .cls "java.lang.String"⟩ then
      bad "Throwable.toString with an overridden getMessage is not modelled"
    else match Fields.get fs ("java.lang.Throwable", "detailMessage") with
      | some .null | none => okStr (jstr c) σ
      | some m => match strOf σ m with
        | some s =>
          if c == "org.opentest4j.AssertionFailedError" && s.isEmpty then okStr (jstr c) σ
          else if c == "org.junit.internal.ArrayComparisonFailure" then okStr s σ
          else okStr (jstr c ++ jstr ": " ++ s) σ
        | none => bad "detailMessage"
  else if P.isSubclass c "java.lang.Enum" == some true then
    match Fields.get fs ("java.lang.Enum", "name") with
    | some nm => ok nm σ
    | none => bad "enum name"
  else if overrides P c hashCodeSub then bad "Object.toString with an overridden hashCode is not modelled"
  else .choose fun h => okStr (jstr c ++ jstr "@" ++ jstr (String.ofList (Nat.toDigits 16 (h % 2 ^ 32)))) σ

/-- Iteration order of a set or map's keys: insertion (linked), sorted (tree, kept
    sorted on insertion) or unspecified (hash: every permutation is possible). -/
def orderKeys (hash : Bool) (keys : List Value) (k : List Value → NRes) : NRes :=
  if hash then .choose fun n => k (permuteBy n keys) else k keys

/-- Render the values of a list with an element renderer, separated by `", "`. -/
def joinWith (f : Value → State → (JStr → State → NRes) → NRes) :
    List Value → State → (JStr → State → NRes) → NRes
  | [], σ, k => k [] σ
  | [x], σ, k => f x σ k
  | x :: xs, σ, k => f x σ fun s σ' => joinWith f xs σ' fun t σ'' => k (s ++ jstr ", " ++ t) σ''

/-- Render map entries `k=v`, separated by `", "`. -/
def entriesWith (f : Value → State → (JStr → State → NRes) → NRes) :
    List (Value × Value) → State → (JStr → State → NRes) → NRes
  | [], σ, k => k [] σ
  | (a, b) :: rest, σ, k =>
    f a σ fun sa σ1 => f b σ1 fun sb σ2 =>
      match rest with
      | [] => k (sa ++ jstr "=" ++ sb) σ2
      | _ => entriesWith f rest σ2 fun t σ3 => k (sa ++ jstr "=" ++ sb ++ jstr ", " ++ t) σ3

/-- `String.valueOf(Object)`: may call back into application `toString()`; collections are
    rendered as `AbstractCollection.toString`/`AbstractMap.toString` do (nesting bounded). -/
def valueOfObjN (P : Program) : Nat → Value → State → (JStr → State → NRes) → NRes
  | 0, _, _, _ => bad "toString nesting too deep"
  | n + 1, v, σ, k =>
    match v with
    | .null => k (jstr "null") σ
    | .ref a =>
      match σ.heap a with
      | none => bad "dangling reference"
      | some o =>
        match nObjStr σ o with
        | some s => k s σ
        | none =>
          match o with
          | .plain c fs =>
            if c == "java.util.Arrays$ArrayList" then
              match (Fields.get fs (c, "a")).bind (objAt σ ·) with
              | some (_, .array _ xs) => joinWith (valueOfObjN P n) xs σ fun s σ' => k (jstr "[" ++ s ++ jstr "]") σ'
              | _ => bad "malformed Arrays.asList"
            else if c == "java.util.ArrayList$SubList" then
              match Fields.get fs (c, "root"), Fields.get fs (c, "offset"), Fields.get fs (c, "size"),
                    Fields.get fs (c, "modCount") with
              | some root, some (.int off), some (.int sz), some (.int mc) =>
                match objAt σ root with
                | some (_, .list _ xs m) =>
                  if m != mc.toNat then .ret (throwNew "java.util.ConcurrentModificationException" none σ)
                  else joinWith (valueOfObjN P n) ((xs.drop off.toNat).take sz.toNat) σ fun s σ' =>
                    k (jstr "[" ++ s ++ jstr "]") σ'
                | _ => bad "subList of a non-list"
              | _, _, _, _ => bad "malformed subList"
            else if c == "java.util.Collections$EmptySet" then k (jstr "[]") σ
            else if P.isProgClass c then
              .call toStringSig (.virtual c) [v] σ fun out =>
                match out with
                | .normal (some r) σ' =>
                  if r == .null then k (jstr "null") σ'
                  else match strOf σ' r with
                    | some s => k s σ'
                    | none => bad "toString returned a non-string"
                | .normal none _ => bad "toString returned no value"
                | .exc e σ' => .ret (.thr e σ')
                | .wrong msg => bad msg
            else
              (libToString P c fs σ).bind fun r =>
                match r with
                | .ok sv σ' => match strOf σ' sv with
                  | some s => k s σ'
                  | none => bad "toString returned a non-string"
                | .thr e σ' => .ret (.thr e σ')
                | .wrong m => .ret (.wrong m)
          | .list _ xs _ => joinWith (valueOfObjN P n) xs σ fun s σ' => k (jstr "[" ++ s ++ jstr "]") σ'
          | .set sk xs _ =>
            orderKeys (sk == .hash) xs fun ys =>
              joinWith (valueOfObjN P n) ys σ fun s σ' => k (jstr "[" ++ s ++ jstr "]") σ'
          | .map mk kvs _ =>
            orderKeys (mk == .hash) (kvs.map (·.1)) fun ks =>
              entriesWith (valueOfObjN P n) (ks.filterMap fun key => kvs.find? (·.1 == key)) σ
                fun s σ' => k (jstr "{" ++ s ++ jstr "}") σ'
          | .view src part =>
            match σ.heap src with
            | some (.map mk kvs _) =>
              orderKeys (mk == .hash) (kvs.map (·.1)) fun ks =>
                let kvs' := ks.filterMap fun key => kvs.find? (·.1 == key)
                let close := fun (s : JStr) (σ' : State) => k (jstr "[" ++ s ++ jstr "]") σ'
                match part with
                | .keys => joinWith (valueOfObjN P n) ks σ close
                | .values => joinWith (valueOfObjN P n) (kvs'.map (·.2)) σ close
                | .entries => entriesWith (valueOfObjN P n) kvs' σ close
            | _ => bad "map view of a non-map"
          | _ => bad "toString not modelled for this library object"
    | _ => bad "expected reference"

def valueOfObj (P : Program) (v : Value) (σ : State) (k : JStr → State → NRes) : NRes :=
  valueOfObjN P 8 v σ k

/-- Append the `String.valueOf` rendering of an argument of static type `t`. -/
def valueOfArg (P : Program) (t : JType) (v : Value) (σ : State) (k : JStr → State → NRes) :
    NRes :=
  if t.isRef then valueOfObj P v σ k
  else match primStr t v with
    | some s => k s σ
    | none => bad "floating-point to string conversion is not modelled"

/-! ### Helpers of the models added with the differential-testing corpus -/

/-- Digit `d < 36` of a number in a radix up to 36 (`0-9`, then `a-z`). -/
def digitChar36 (d : Nat) : JChar := BitVec.ofNat 16 (if d < 10 then 48 + d else 87 + d)

/-- `v` in upper-case hexadecimal (`String.format("%X", …)` of a non-negative value). -/
def hexUpper (v : Nat) : String := String.ofList ((Nat.toDigits 16 v).map Char.toUpper)

/-- Digits of `v` in base `b ≥ 2`, most significant first (`0` for zero). -/
def natDigits (b v : Nat) : JStr :=
  go v [] (v + 1)
where
  go (v : Nat) (acc : JStr) : Nat → JStr
    | 0 => acc
    | fuel + 1 =>
      let acc' := digitChar36 (v % b) :: acc
      if v < b ∨ b < 2 then acc' else go (v / b) acc' fuel

/-- Signed digits in radix `b` (`Integer.toString(int, radix)`, `BigInteger.toString(radix)`). -/
def intDigits (b : Nat) (i : Int) : JStr :=
  (if i < 0 then jstr "-" else []) ++ natDigits b i.natAbs

/-- Value of an ASCII digit or letter in radix `b` (`Character.digit` on ASCII). -/
def digitVal? (c : JChar) (b : Nat) : Option Nat :=
  let n := c.toNat
  let d := if 48 ≤ n ∧ n ≤ 57 then n - 48 else if 97 ≤ n ∧ n ≤ 122 then n - 87
    else if 65 ≤ n ∧ n ≤ 90 then n - 55 else 36
  if d < b then some d else none

/-- An optionally signed digit string in radix `b`. -/
def parseRadix? (s : JStr) (b : Nat) : Option Int :=
  let (neg, ds) := match s with
    | c :: r => if c.toNat = 45 then (true, r) else if c.toNat = 43 then (false, r) else (false, s)
    | [] => (false, [])
  if ds.isEmpty then none
  else (ds.foldlM (fun acc c => (digitVal? c b).map (acc * b + ·)) 0).map
    fun n => if neg then -(n : Int) else n

/-- Length of the minimal two's-complement representation without the sign bit
    (`BigInteger.bitLength`). -/
def bitLen (i : Int) : Nat :=
  let n := if i < 0 then (-i - 1).toNat else i.toNat
  if n = 0 then 0 else Nat.log2 n + 1

/-- `b ^ e % m` by repeated squaring (`BigInteger.modPow`, `m > 0`). -/
def powModNat (b e m : Nat) : Nat :=
  if h : e = 0 then 1 % m
  else
    let r := powModNat (b * b % m) (e / 2) m
    if e % 2 = 1 then r * (b % m) % m else r
termination_by e
decreasing_by omega

/-! ### java.util.Formatter: `String.format`, `String.formatted`, `PrintStream.printf`/`format`

What fixed-width business text uses, in the default locale (en_US): `%s %S` (width, `-`,
precision), `%d` on `Integer`/`Long`/`Short`/`Byte`/`BigInteger` (flags `-` `0` `+` space `,` `(`),
`%x %X %o` on `Integer`/`Long`, `%c` on `Character`, `%b %B`, `%f` on `BigDecimal` (rounded
`HALF_UP`, the same flags as `%d`), `%n`, `%%`, explicit (`2$`) and relative (`<`) argument
indices. A missing argument throws MissingFormatArgumentException, an unknown conversion
UnknownFormatConversionException, an argument of the wrong class IllegalFormatConversionException.
Floating-point arguments, `%e %g %a %h %t`, the `#` flag and the other flag combinations go
`wrong`. -/

/-- A piece of a format string: text, or a format specifier. -/
inductive FmtPiece where
  | lit (s : JStr)
  | spec (idx : Option Nat) (rel : Bool) (flags : List Nat) (width prec : Option Nat) (conv : Nat)
      (raw : JStr)

def isDigitJ (c : JChar) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

/-- The leading decimal digits of `s` and the rest. -/
def spanDigits (s : JStr) : List JChar × JStr := (s.takeWhile isDigitJ, s.dropWhile isDigitJ)

def digitsVal (ds : List JChar) : Nat := ds.foldl (fun n c => n * 10 + (c.toNat - 48)) 0

/-- Parse a format string (as `Formatter.parse`: `%[n$][flags][width][.prec]conv`); `none` for
    an unknown conversion, with the offending character. -/
def parseFmt : Nat → JStr → JStr → Except (Option JChar) (List FmtPiece)
  | 0, _, _ => .error none
  | fuel + 1, s, acc =>
    match s with
    | [] => .ok (if acc.isEmpty then [] else [.lit acc.reverse])
    | c :: rest =>
      if c.toNat != 37 then parseFmt fuel rest (c :: acc)
      else
        let pre : List FmtPiece := if acc.isEmpty then [] else [.lit acc.reverse]
        -- explicit index `n$`
        let (d0, r0) := spanDigits rest
        let (idx, r1) := match r0 with
          | c' :: r' => if c'.toNat == 36 && !d0.isEmpty then (some (digitsVal d0), r') else (none, rest)
          | [] => (none, rest)
        let flagChars : List Nat := [45, 35, 43, 32, 48, 44, 40, 60]
        let fl := r1.takeWhile (fun c => flagChars.contains c.toNat)
        let r2 := r1.dropWhile (fun c => flagChars.contains c.toNat)
        let (wd, r3) := spanDigits r2
        let (prec, r4) := match r3 with
          | c' :: r' => if c'.toNat == 46 then
              let (pd, r'') := spanDigits r'
              if pd.isEmpty then (none, r3) else (some (digitsVal pd), r'')
            else (none, r3)
          | [] => (none, r3)
        match r4 with
        | cv :: r5 =>
          let n := cv.toNat
          let isConv := (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || n == 37
          if !isConv then .error (some cv)
          else
            let consumed := (c :: rest).length - r5.length
            let raw := (c :: rest).take consumed
            let sp := FmtPiece.spec idx (fl.any (·.toNat == 60)) ((fl.map (·.toNat)).filter (· != 60))
              (if wd.isEmpty then none else some (digitsVal wd)) prec n raw
            (parseFmt fuel r5 []).map (pre ++ sp :: ·)
        | [] => .error (some c)

/-- Pad `s` to `w` with spaces, on the right if `left`. -/
def justifyJ (left : Bool) (w : Option Nat) (s : JStr) : JStr :=
  match w with
  | some w => if s.length ≥ w then s
    else if left then s ++ List.replicate (w - s.length) (BitVec.ofNat 16 32)
    else List.replicate (w - s.length) (BitVec.ofNat 16 32) ++ s
  | none => s

/-- `1234567` → `1,234,567`. -/
def groupDigits (ds : JStr) : JStr :=
  let r := ds.reverse
  let rec go : Nat → JStr → JStr → JStr
    | 0, _, acc => acc
    | fuel + 1, xs, acc =>
      match xs with
      | [] => acc
      | _ =>
        let chunk := xs.take 3
        let rest := xs.drop 3
        let acc' := chunk.reverse ++ acc
        if rest.isEmpty then acc' else go fuel rest (BitVec.ofNat 16 44 :: acc')
  go (r.length + 1) r []

/-- A signed number as `%d`/`%f` render it: digits `mag` (with the integer part grouped if `,`),
    sign by the flags, zero-padded (`0`) or justified to the width. `none` for unsupported flag
    combinations. -/
def fmtNumber (neg : Bool) (intPart frac : JStr) (flags : List Nat) (w : Option Nat) :
    Option JStr :=
  let has (c : Nat) := flags.contains c
  if has 35 || (has 48 && (has 45 || w.isNone)) || (has 48 && has 44) || (has 48 && has 40) ||
      (has 43 && has 32) then none
  else
    let ip := if has 44 then groupDigits intPart else intPart
    let mag := ip ++ frac
    if neg && has 40 then some (justifyJ (has 45) w (jstr "(" ++ mag ++ jstr ")"))
    else
      let sign := if neg then jstr "-" else if has 43 then jstr "+" else if has 32 then jstr " " else []
      if has 48 then
        let w := w.getD 0
        let pad := w - (sign.length + mag.length)
        some (sign ++ List.replicate pad (BitVec.ofNat 16 48) ++ mag)
      else some (justifyJ (has 45) w (sign ++ mag))

/-- ASCII upper case (`%S`, `%B`, `%X`); `none` beyond ASCII. -/
def upperAsciiJ (s : JStr) : Option JStr :=
  if s.all (·.toNat < 128) then
    some (s.map fun c => if 97 ≤ c.toNat && c.toNat ≤ 122 then c - 32 else c)
  else none

/-- Class name of an argument, for IllegalFormatConversionException. -/
def fmtArgClass (σ : State) (v : Value) : String :=
  match objAt σ v with
  | some (_, o) => match o.ty with
    | .cls c => c
    | _ => "java.lang.Object"
  | none => "null"

/-- Format `pieces` with the arguments `args`, from argument `next` (ordinary specifiers) with
    `prev` the last argument used (`<`). -/
def formatPieces (P : Program) : Nat → List FmtPiece → List Value → Nat → Option Value → JStr →
    State → (JStr → State → NRes) → NRes
  | 0, _, _, _, _, _, _, _ => bad "format nesting too deep"
  | _ + 1, [], _, _, _, acc, σ, k => k acc σ
  | fuel + 1, .lit t :: rest, args, next, prev, acc, σ, k =>
    formatPieces P fuel rest args next prev (acc ++ t) σ k
  | fuel + 1, .spec idx rel flags w prec conv raw :: rest, args, next, prev, acc, σ, k =>
    let cont (s : JStr) (next' : Nat) (prev' : Option Value) (σ' : State) : NRes :=
      formatPieces P fuel rest args next' prev' (acc ++ s) σ' k
    let has (c : Nat) := flags.contains c
    if conv == 110 then -- %n
      if flags.isEmpty && w.isNone && prec.isNone then cont (jstr "\n") next prev σ
      else bad "format: %n with flags, width or precision"
    else if conv == 37 then -- %%
      if flags.isEmpty && prec.isNone then cont (justifyJ false w (jstr "%")) next prev σ
      else bad "format: %% with flags or precision"
    else
      -- the argument
      let arg? : Option (Value × Nat) :=
        if rel then prev.map (·, next)
        else match idx with
          | some i => if i ≥ 1 then args[i - 1]?.map (·, next) else none
          | none => args[next]?.map (·, next + 1)
      match arg? with
      | none => thr "java.util.MissingFormatArgumentException"
          (some s!"Format specifier '{String.ofList (raw.map fun c => Char.ofNat c.toNat)}'") σ
      | some (v, next') =>
        let mismatch := thr "java.util.IllegalFormatConversionException"
          (some s!"{Char.ofNat conv} != {fmtArgClass σ v}") σ
        let onlyMinus := flags.all (· == 45) && (!has 45 || w.isSome)
        -- %s %S
        if conv == 115 || conv == 83 then
          if !onlyMinus then bad "format: flags of %s" else
          valueOfObj P v σ fun str σ' =>
            let str := match prec with | some p => str.take p | none => str
            match (if conv == 83 then upperAsciiJ str else some str) with
            | some str => cont (justifyJ (has 45) w str) next' (some v) σ'
            | none => bad "format: %S beyond ASCII"
        -- %b %B
        else if conv == 98 || conv == 66 then
          if !onlyMinus then bad "format: flags of %b" else
          let b := match objAt σ v with
            | none => false
            | some (_, .boxed "java.lang.Boolean" (.int x)) => x ≠ 0
            | some _ => true
          let str := boolStr b
          let str := match prec with | some p => str.take p | none => str
          let str := if conv == 66 then (upperAsciiJ str).getD str else str
          cont (justifyJ (has 45) w str) next' (some v) σ
        -- %c
        else if conv == 99 then
          if !onlyMinus || prec.isSome then bad "format: flags of %c" else
          match objAt σ v with
          | none => cont (justifyJ (has 45) w (jstr "null")) next' (some v) σ
          | some (_, .boxed "java.lang.Character" (.int x)) =>
            cont (justifyJ (has 45) w [x.setWidth 16]) next' (some v) σ
          | some _ => bad "format: %c of a non-Character"
        -- %d
        else if conv == 100 then
          if prec.isSome then bad "format: precision with %d" else
          let num? : Option Int := match objAt σ v with
            | some (_, .boxed "java.lang.Integer" (.int x)) | some (_, .boxed "java.lang.Short" (.int x))
            | some (_, .boxed "java.lang.Byte" (.int x)) => some x.toInt
            | some (_, .boxed "java.lang.Long" (.long x)) => some x.toInt
            | some (_, .bigInt i) => some i
            | _ => none
          match objAt σ v, num? with
          | none, _ => cont (justifyJ (has 45) w (jstr "null")) next' (some v) σ
          | some _, none => mismatch
          | some _, some i =>
            match fmtNumber (i < 0) (natDigits 10 i.natAbs) [] flags w with
            | some str => cont str next' (some v) σ
            | none => bad "format: flags of %d"
        -- %x %X %o
        else if conv == 120 || conv == 88 || conv == 111 then
          if prec.isSome || has 35 || has 43 || has 32 || has 44 || has 40 then
            bad "format: flags of %x/%o"
          else
            let base := if conv == 111 then 8 else 16
            let num? : Option Nat := match objAt σ v with
              | some (_, .boxed "java.lang.Integer" (.int x)) => some x.toNat
              | some (_, .boxed "java.lang.Long" (.long x)) => some x.toNat
              | _ => none
            match objAt σ v, num? with
            | none, _ => cont (justifyJ (has 45) w (jstr "null")) next' (some v) σ
            | some _, none => bad "format: %x/%o of this class"
            | some _, some n =>
              let ds := natDigits base n
              let ds := if conv == 88 then (upperAsciiJ ds).getD ds else ds
              match fmtNumber false ds [] flags w with
              | some str => cont str next' (some v) σ
              | none => bad "format: flags of %x/%o"
        -- %f on BigDecimal
        else if conv == 102 then
          match objAt σ v with
          | none => cont (justifyJ (has 45) w (jstr "null")) next' (some v) σ
          | some (_, .dec d) =>
            let p := prec.getD 6
            match BigDec.setScale d (p : Int) .HALF_UP with
            | some r =>
              let neg := r.unscaled < 0
              let ds := natDigits 10 r.unscaled.natAbs
              let ds := if ds.length ≤ p then List.replicate (p + 1 - ds.length) (BitVec.ofNat 16 48) ++ ds else ds
              let ip := ds.take (ds.length - p)
              let fp := ds.drop (ds.length - p)
              let frac := if p = 0 then [] else jstr "." ++ fp
              match fmtNumber neg ip frac flags w with
              | some str => cont str next' (some v) σ
              | none => bad "format: flags of %f"
            | none => bad "format: rounding"
          | some (_, .boxed "java.lang.Double" _) | some (_, .boxed "java.lang.Float" _) =>
            bad "floating-point to string conversion is not modelled"
          | some _ => mismatch
        else if (65 ≤ conv && conv ≤ 90) || (97 ≤ conv && conv ≤ 122) then
          -- conversions the JDK knows but the model does not
          if [101, 69, 103, 71, 97, 65, 104, 72, 116, 84].contains conv then
            bad s!"format: conversion %{Char.ofNat conv} is not modelled"
          else thr "java.util.UnknownFormatConversionException"
            (some s!"Conversion = '{Char.ofNat conv}'") σ
        else bad "format: conversion"

/-- `Formatter.format` of `fmt` with the argument array `argv` (`null`: no arguments). -/
def formatK (P : Program) (fmt : JStr) (argv : Value) (σ : State) (k : JStr → State → NRes) :
    NRes :=
  let args : Option (List Value) := match objAt σ argv with
    | none => some []
    | some (_, .array _ xs) => some xs
    | some _ => none
  match args with
  | none => bad "format: arguments are not an array"
  | some args =>
    match parseFmt (fmt.length + 1) fmt [] with
    | .error (some c) => thr "java.util.UnknownFormatConversionException"
        (some s!"Conversion = '{Char.ofNat c.toNat}'") σ
    | .error none => bad "format: parse"
    | .ok pieces => formatPieces P (pieces.length + 1) pieces args 0 none [] σ k

/-- Sort key of a primitive array element (numeric order; `char`s are zero-extended). -/
def primKey : Value → Int
  | .int x => x.toInt
  | .long x => x.toInt
  | _ => 0

/-- Kind of a value under natural ordering: values of one kind are mutually comparable by
    `nCompare` (strings, one boxed integral class, `BigDecimal`, `BigInteger`). -/
def natKind (σ : State) (v : Value) : Option String :=
  match objAt σ v with
  | some (_, .str _) => some "java.lang.String"
  | some (_, .dec _) => some "java.math.BigDecimal"
  | some (_, .bigInt _) => some "java.math.BigInteger"
  | some (_, .boxed c (.int _)) => some c
  | some (_, .boxed c (.long _)) => some c
  | _ => none

/-- Outcome of an operation by natural ordering over library values. -/
inductive NatOrd (α : Type) where
  | ok (a : α)
  /-- the exception Java throws: `null` elements (NPE), elements not mutually comparable (CCE) -/
  | exc (cls : ClassName)
  /-- an application `compareTo` (or a floating-point box) would decide: not modelled -/
  | unsupported

/-- Check that the elements `xs` (at least two) can be ordered naturally by the model. -/
def natCheck (σ : State) (xs : List Value) : NatOrd Unit :=
  if xs.any (· == .null) then .exc "java.lang.NullPointerException"
  else match xs.mapM (natKind σ) with
    | none => .unsupported
    | some ks => if ks.all (· == ks.headD "") then .ok () else .exc "java.lang.ClassCastException"

/-- Stable sort by natural ordering (`Collections.sort`, `Arrays.sort(Object[])`). -/
def natSort (σ : State) (xs : List Value) : NatOrd (List Value) :=
  if xs.length ≤ 1 then .ok xs
  else match natCheck σ xs with
    | .ok () => .ok (xs.mergeSort fun a b => decide ((nCompare σ a b).getD 0 ≤ 0))
    | .exc c => .exc c
    | .unsupported => .unsupported

/-- The first maximal (`wantMax`) or minimal element in iteration order
    (`Collections.max`/`min`); `none` for no elements. -/
def natExtreme (σ : State) (xs : List Value) (wantMax : Bool) : NatOrd (Option Value) :=
  match xs with
  | [] => .ok none
  | [x] => .ok (some x)
  | x :: rest =>
    match natCheck σ xs with
    | .ok () => .ok (some (rest.foldl (fun c y =>
        let r := (nCompare σ y c).getD 0
        if (wantMax && decide (r > 0)) || (!wantMax && decide (r < 0)) then y else c) x))
    | .exc c => .exc c
    | .unsupported => .unsupported

/-- Library objects that are `Comparable` in the JDK (strings, boxes, big numbers, rounding
    modes, string builders): casting one to `Comparable` succeeds and comparing it with itself
    has no effect. -/
def isLibComparableObj (σ : State) (v : Value) : Bool :=
  match objAt σ v with
  | some (_, .str _) | some (_, .boxed _ _) | some (_, .dec _) | some (_, .bigInt _)
  | some (_, .rmode _) | some (_, .builder _ _) => true
  | _ => false

/-- Can `v` be cast to `java.lang.Comparable`, as `TreeMap` casts a key before comparing it?
    Library value objects can, application objects if their class implements `Comparable`;
    other library objects cannot. -/
def isComparableObj (P : Program) (σ : State) (v : Value) : Bool :=
  isLibComparableObj σ v ||
    match objAt σ v with
    | some (_, .plain c _) => P.isSubclass c "java.lang.Comparable" == some true
    | _ => false

/-- Add `v` to the elements of a set of kind `k`; `none` when application code would decide
    equality or ordering (including the self-comparison of the first element of a tree set,
    see `selfCompareK`). The flag tells whether the set changed. -/
def setAdd? (P : Program) (σ : State) (k : SetKind) (xs : List Value) (v : Value) :
    Option (List Value × Bool) :=
  let kvs := xs.map (·, Value.null)
  if k == .tree ∧ xs.isEmpty ∧ !isLibComparableObj σ v then none else
  match findKey P σ (k == .tree) v kvs with
  | none => none
  | some (some _) => some (xs, false)
  | some none =>
    if k == .tree then (insertSorted σ v .null kvs).map fun kvs' => (kvs'.map (·.1), true)
    else some (xs ++ [v], true)

/-- Add all of `vs` in order (`addAll`, copy constructors); `none` as for `setAdd?`. -/
def setAddAll? (P : Program) (σ : State) (k : SetKind) (xs vs : List Value) :
    Option (List Value × Bool) :=
  vs.foldlM (fun (acc : List Value × Bool) v =>
    (setAdd? P σ k acc.1 v).map fun (ys, ch) => (ys, acc.2 || ch)) (xs, false)

/-- Elements of a `char[]` as a string. -/
def charsOf (xs : List Value) : JStr := xs.map fun | .int x => x.setWidth 16 | _ => 0

/-- The code of an ASCII `char`, `none` beyond ASCII (Unicode tables are not modelled). -/
def asciiChar? (c : I32) : Option Nat := if c.toNat < 128 then some c.toNat else none

/-- After reversing UTF-16 code units, put every valid surrogate pair back in high-low order
    (`StringUTF16.reverseAllValidSurrogatePairs`, used by `AbstractStringBuilder.reverse`). -/
def restoreSurrogatePairs : JStr → JStr
  | c2 :: tl@(c1 :: rest) =>
    if 0xDC00 ≤ c2.toNat ∧ c2.toNat ≤ 0xDFFF ∧ 0xD800 ≤ c1.toNat ∧ c1.toNat ≤ 0xDBFF then
      c1 :: c2 :: restoreSurrogatePairs rest
    else c2 :: restoreSurrogatePairs tl
  | s => s

/-! ### Callbacks into application `equals` / `compareTo` from library code -/

/-- The method reference used for `compareTo` callbacks (`Comparable.compareTo(Object)`). -/
def compareToSig : MethodSig :=
  ⟨"java.lang.Comparable", .prim .int, "compareTo", [.cls "java.lang.Object"]⟩

/-- `x.equals(y)` as library code performs it: decided by the model for library receivers
    (`nEquals`), otherwise by calling the application's `equals` (receivers of application
    classes only). With `idFirst`, identical references are equal without a call
    (`Objects.equals`, hash-map key lookup); without it, `equals` runs even on the same
    object (`ArrayList.indexOf`). -/
def equalsK (P : Program) (idFirst : Bool) (σ : State) (x y : Value)
    (k : Bool → State → NRes) : NRes :=
  if idFirst && x == y then k true σ
  else match nEquals P σ x y with
    | some b => k b σ
    | none =>
      match objAt σ x with
      | some (_, .plain c _) =>
        if P.isProgClass c then
          .call equalsSig (.virtual c) [x, y] σ fun out => match out with
            | .normal (some (.int r)) σ' => k (r ≠ 0) σ'
            | .normal _ _ => bad "equals returned no boolean"
            | .exc e σ' => .ret (.thr e σ')
            | .wrong msg => bad msg
        else bad "equals of this library object is not modelled"
      | _ => bad "equals of this library object kind is not modelled"

/-- `x.compareTo(y)` as natural ordering performs it (tree maps and sets, sorting): decided by
    the model for library value objects (`nCompare`), otherwise by calling the application's
    `compareTo`. `null` receivers throw `NullPointerException`; receivers that are not
    `Comparable`, and library values compared with other kinds, `ClassCastException`. -/
def compareK (P : Program) (σ : State) (x y : Value) (k : Int → State → NRes) : NRes :=
  match nCompare σ x y with
  | some r => k r σ
  | none =>
    if x == .null then thrNPE σ
    else match objAt σ x with
      | some (_, .plain c _) =>
        if P.isProgClass c ∧ P.isSubclass c "java.lang.Comparable" = some true then
          .call compareToSig (.virtual c) [x, y] σ fun out => match out with
            | .normal (some (.int r)) σ' => k r.toInt σ'
            | .normal _ _ => bad "compareTo returned no int"
            | .exc e σ' => .ret (.thr e σ')
            | .wrong msg => bad msg
        else thr "java.lang.ClassCastException" none σ
      | some (_, .boxed c (.double _)) | some (_, .boxed c (.float _)) =>
        if y == .null then thrNPE σ
        else match objAt σ y with
          | some (_, .boxed d _) =>
            if c == d then bad "compareTo of floating-point boxes is not modelled"
            else thr "java.lang.ClassCastException" none σ
          | _ => thr "java.lang.ClassCastException" none σ
      | some (_, .builder _ _) => bad "compareTo of StringBuilder/StringBuffer is not modelled"
      | some _ => if y == .null then thrNPE σ else thr "java.lang.ClassCastException" none σ
      | none => bad "compareTo on a non-object"

/-- The type check of the first insertion into an empty tree map or set
    (`TreeMap.addEntryToEmptyMap` calls `compare(key, key)`): nothing for library value
    objects, otherwise `compareK` on (key, key): NullPointerException for `null`,
    ClassCastException if the key is not `Comparable`, a call of the application's
    `compareTo` otherwise (its effects and exceptions are kept). -/
def selfCompareK (P : Program) (σ : State) (key : Value) (k : State → NRes) : NRes :=
  if isLibComparableObj σ key then k σ else compareK P σ key key fun _ σ' => k σ'

/-- Index of the first `y` of the list with `x.equals(y)` (`indexOf`, `contains`,
    `remove(Object)`, `containsValue`), calling application `equals` as needed. -/
def findElemK (P : Program) (idFirst : Bool) (x : Value) :
    List Value → Nat → State → (Option Nat → State → NRes) → NRes
  | [], _, σ, k => k none σ
  | y :: ys, i, σ, k => equalsK P idFirst σ x y fun b σ' =>
      if b then k (some i) σ' else findElemK P idFirst x ys (i + 1) σ' k

/-- Do all pairs satisfy `Objects.equals(x, y)` (`List.equals`, `Arrays.equals`)? Stops at the
    first difference. -/
def allEqualK (P : Program) : List (Value × Value) → State → (Bool → State → NRes) → NRes
  | [], σ, k => k true σ
  | (x, y) :: rest, σ, k => equalsK P true σ x y fun b σ' =>
      if b then allEqualK P rest σ' k else k false σ'

/-- Key lookup with callbacks: hash and linked maps test `key.equals(k')` (identical keys match
    without a call), tree maps compare `key.compareTo(k')` along the sorted keys and stop at
    the first larger key. Result: the index and value of the matching entry. -/
def findKeyK (P : Program) (tree : Bool) (key : Value) :
    List (Value × Value) → Nat → State → (Option (Nat × Value) → State → NRes) → NRes
  | [], _, σ, k => k none σ
  | (k', v) :: rest, i, σ, k =>
    if tree then compareK P σ key k' fun r σ' =>
      if r = 0 then k (some (i, v)) σ' else if r < 0 then k none σ'
      else findKeyK P tree key rest (i + 1) σ' k
    else equalsK P true σ key k' fun b σ' =>
      if b then k (some (i, v)) σ' else findKeyK P tree key rest (i + 1) σ' k

/-- Insertion into a key-sorted entry list with `key.compareTo(k')` callbacks: the new list
    and the previous value of an equal key (whose key object is kept). -/
def insertSortedK (P : Program) (key v : Value) :
    List (Value × Value) → State → (List (Value × Value) → Option Value → State → NRes) → NRes
  | [], σ, k => k [(key, v)] none σ
  | (k', v') :: rest, σ, k => compareK P σ key k' fun r σ' =>
      if r < 0 then k ((key, v) :: (k', v') :: rest) none σ'
      else if r = 0 then k ((k', v) :: rest) (some v') σ'
      else insertSortedK P key v rest σ' fun kvs old σ'' => k ((k', v') :: kvs) old σ''

/-- `Map.put` with callbacks on the map at `a` (kind `mk`, entries `kvs`, modification count
    `m`): returns the previous value; replacing a value keeps the key object. -/
def mapPutK (P : Program) (a : Addr) (mk : MapKind) (key v : Value)
    (kvs : List (Value × Value)) (m : Nat) (σ : State) : NRes :=
  let put (kvs' : List (Value × Value)) (m' : Nat) (σ : State) : State := σ.setObj a (.map mk kvs' m')
  if mk == .tree ∧ kvs.isEmpty then selfCompareK P σ key fun σ' => ok .null (put [(key, v)] (m + 1) σ')
  else if mk == .tree then insertSortedK P key v kvs σ fun kvs' old σ' => match old with
    | some o => ok o (put kvs' m σ')
    | none => ok .null (put kvs' (m + 1) σ')
  else findKeyK P false key kvs 0 σ fun r σ' => match r with
    | some (i, o) => ok o (put (kvs.set i (kvs[i]?.map (·.1) |>.getD key, v)) m σ')
    | none => ok .null (put (kvs ++ [(key, v)]) (m + 1) σ')

/-- `Map.putIfAbsent` with callbacks (as `mapPutK`). -/
def mapPutIfAbsentK (P : Program) (a : Addr) (mk : MapKind) (key v : Value)
    (kvs : List (Value × Value)) (m : Nat) (σ : State) : NRes :=
  let put (kvs' : List (Value × Value)) (m' : Nat) (σ : State) : State := σ.setObj a (.map mk kvs' m')
  if mk == .tree ∧ kvs.isEmpty then selfCompareK P σ key fun σ' => ok .null (put [(key, v)] (m + 1) σ') else
  findKeyK P (mk == .tree) key kvs 0 σ fun r σ' => match r with
    | some (i, o) =>
      if o == .null then ok .null (put (kvs.set i (kvs[i]?.map (·.1) |>.getD key, v)) m σ')
      else ok o σ'
    | none =>
      if mk == .tree then insertSortedK P key v kvs σ' fun kvs' _ σ'' => ok .null (put kvs' (m + 1) σ'')
      else ok .null (put (kvs ++ [(key, v)]) (m + 1) σ')

/-- `Set.add` with callbacks (tree sets by `compareTo`, others by `equals`): the new elements
    and whether the set changed. -/
def setAddK (P : Program) (sk : SetKind) (xs : List Value) (v : Value) (σ : State)
    (k : List Value × Bool → State → NRes) : NRes :=
  let kvs := xs.map (·, Value.null)
  if sk == .tree ∧ xs.isEmpty then selfCompareK P σ v fun σ' => k ([v], true) σ'
  else if sk == .tree then insertSortedK P v .null kvs σ fun kvs' old σ' =>
    k (if old.isSome then (xs, false) else (kvs'.map (·.1), true)) σ'
  else findKeyK P false v kvs 0 σ fun r σ' =>
    k (if r.isSome then (xs, false) else (xs ++ [v], true)) σ'

/-- Add all of `vs` in order with callbacks (`addAll`, copy constructors). -/
def setAddAllK (P : Program) (sk : SetKind) :
    List Value → List Value × Bool → State → (List Value × Bool → State → NRes) → NRes
  | [], acc, σ, k => k acc σ
  | v :: vs, acc, σ, k => setAddK P sk acc.1 v σ fun r σ' => setAddAllK P sk vs (r.1, acc.2 || r.2) σ' k

/-- `key.compareTo(k')` for every key, in order. -/
def compareAllK (P : Program) (key : Value) :
    List Value → State → (List (Value × Int) → State → NRes) → NRes
  | [], σ, k => k [] σ
  | k' :: rest, σ, k => compareK P σ key k' fun r σ' =>
      compareAllK P key rest σ' fun cs σ'' => k ((k', r) :: cs) σ''

/-- `TreeMap` navigation (`ceilingKey`, `higherKey`, `floorKey`, `lowerKey`): the first (or,
    with `last`, the final) key `k'` of the sorted keys with `sel (key.compareTo(k'))`. -/
def navKey (P : Program) (σ : State) (keys : List Value) (key : Value) (sel : Int → Bool)
    (last : Bool) : NRes :=
  let pick := fun (cs : List (Value × Int)) (σ : State) =>
    let hits := (cs.filter (sel ·.2)).map (·.1)
    ok ((if last then hits.getLast? else hits.head?).getD .null) σ
  if key == .null then thrNPE σ
  else match keys.mapM (fun k' => (nCompare σ key k').map (k', ·)) with
    | some cs => pick cs σ
    | none => compareAllK P key keys σ pick

/-- Stable merge with `compareTo` callbacks (the left element first on ties). -/
def mergeK (P : Program) : List Value → List Value → State → (List Value → State → NRes) → NRes
  | [], ys, σ, k => k ys σ
  | xs, [], σ, k => k xs σ
  | x :: xs, y :: ys, σ, k => compareK P σ x y fun r σ' =>
      if r ≤ 0 then mergeK P xs (y :: ys) σ' fun zs σ'' => k (x :: zs) σ''
      else mergeK P (x :: xs) ys σ' fun zs σ'' => k (y :: zs) σ''
termination_by xs ys _ _ => xs.length + ys.length

/-- Stable merge sort with `compareTo` callbacks (`Collections.sort` and `Arrays.sort` of
    application `Comparable` objects). The result is the JDK's for a consistent ordering;
    the number and order of the `compareTo` calls differ from TimSort's. -/
def msortK (P : Program) (xs : List Value) (σ : State) (k : List Value → State → NRes) : NRes :=
  if h : xs.length < 2 then k xs σ
  else
    msortK P (xs.take (xs.length / 2)) σ fun l σ1 =>
      msortK P (xs.drop (xs.length / 2)) σ1 fun r σ2 => mergeK P l r σ2 k
termination_by xs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]
  all_goals omega

/-- `Collections.max`/`min` with callbacks: `y.compareTo(candidate)` for each later `y`; the
    first maximal (minimal) element wins. -/
def extremeK (P : Program) (wantMax : Bool) :
    Value → List Value → State → (Value → State → NRes) → NRes
  | c, [], σ, k => k c σ
  | c, y :: ys, σ, k => compareK P σ y c fun r σ' =>
      extremeK P wantMax
        (if (wantMax && decide (r > 0)) || (!wantMax && decide (r < 0)) then y else c) ys σ' k

/-- `String.valueOf(char[])` and `PrintStream.print/println(char[])` print the characters of
    the array; other argument types are rendered by `valueOfArg`. (String concatenation of a
    `char[]` is `String.valueOf(Object)` and does not come here.) -/
def valueOfCharsArg (P : Program) (t : JType) (v : Value) (σ : State) (k : JStr → State → NRes) :
    NRes :=
  match t with
  | .array (.prim .char) => argObj σ v fun _ o => match o with
    | .array _ cs => k (charsOf cs) σ
    | _ => bad "expected char[]"
  | _ => valueOfArg P t v σ k

/-! ### java.lang.String -/

def charAtIdx (s : JStr) (i : I32) (σ : State) (k : JChar → NRes) : NRes :=
  if 0 ≤ i.toInt ∧ i.toInt < s.length then
    match s[i.toNat]? with
    | some c => k c
    | none => bad "index"
  else thr "java.lang.StringIndexOutOfBoundsException"
    (some s!"Index {i.toInt} out of bounds for length {s.length}") σ

def isHighSurr (c : JChar) : Bool := 0xD800 ≤ c.toNat && c.toNat ≤ 0xDBFF
def isLowSurr (c : JChar) : Bool := 0xDC00 ≤ c.toNat && c.toNat ≤ 0xDFFF

/-- `Character.toCodePoint` of a surrogate pair. -/
def surrPair (h l : JChar) : Int := (h.toNat - 0xD800) * 1024 + (l.toNat - 0xDC00) + 0x10000

/-- The code point at index `i` of `s`, whose unit is `c` (`Character.codePointAt`). -/
def codePointAtJ (s : JStr) (i : Nat) (c : JChar) : Int :=
  if isHighSurr c then
    match s[i + 1]? with
    | some d => if isLowSurr d then surrPair c d else c.toNat
    | none => c.toNat
  else c.toNat

/-- The code point before index `i` of `s` (`Character.codePointBefore`; `charAt(i - 1)` checks
    the index). -/
def codePointBeforeK (s : JStr) (i : I32) (σ : State) (k : Int → NRes) : NRes :=
  charAtIdx s (i - 1) σ fun c2 =>
    if isLowSurr c2 && i.toInt - 1 > 0 then
      match s[(i.toInt - 2).toNat]? with
      | some c1 => if isHighSurr c1 then k (surrPair c1 c2) else k c2.toNat
      | none => k c2.toNat
    else k c2.toNat

/-- `seq.charAt(i)` as `Character.codePointAt`/`codePointBefore` call it, with the JDK 17 messages:
    "String index out of range: i" for a `String` of Latin-1 characters (`latin`), "index i, length n"
    for other strings and for builders. -/
def seqCharAt (latin : Bool) (s : JStr) (i : I32) (σ : State) (k : JChar → NRes) : NRes :=
  if 0 ≤ i.toInt ∧ i.toInt < s.length then
    match s[i.toNat]? with
    | some c => k c
    | none => bad "index"
  else thr "java.lang.StringIndexOutOfBoundsException"
    (some (if latin then s!"String index out of range: {i.toInt}" else s!"index {i.toInt}, length {s.length}")) σ

/-- `Character.codePointBefore(seq, i)`: `seq.charAt(i - 1)`, and `seq.charAt(i - 2)` after a low
    surrogate. -/
def codePointBeforeSeq (latin : Bool) (s : JStr) (i : I32) (σ : State) (k : Int → NRes) : NRes :=
  seqCharAt latin s (i - 1) σ fun c2 =>
    if isLowSurr c2 && i.toInt - 1 > 0 then
      match s[(i.toInt - 2).toNat]? with
      | some c1 => if isHighSurr c1 then k (surrPair c1 c2) else k c2.toNat
      | none => k c2.toNat
    else k c2.toNat

/-- A `CharSequence` argument of `Character`'s methods: a `String` (whether its characters are all
    Latin-1, which selects the JDK's index message) or a builder. -/
def argSeq (σ : State) (v : Value) (k : Bool → JStr → NRes) : NRes :=
  argObj σ v fun _ o => match o with
    | .str s => k (s.all (·.toNat < 256)) s | .builder _ s => k false s | _ => bad "expected CharSequence"

/-- The number of code points of UTF-16 units: a high surrogate followed by a low surrogate
    counts once (such pairs cannot overlap). -/
def cpCount (s : JStr) : Nat :=
  s.length - ((s.zip s.tail).filter fun (c, d) => isHighSurr c && isLowSurr d).length

/-- `Character.getType` of an ASCII code point. -/
def asciiType (c : Nat) : Int :=
  if c < 32 || c == 127 then 15
  else if c == 32 then 12
  else if 48 ≤ c && c ≤ 57 then 9
  else if 65 ≤ c && c ≤ 90 then 1
  else if 97 ≤ c && c ≤ 122 then 2
  else match c with
    | 36 => 26
    | 40 | 91 | 123 => 21
    | 41 | 93 | 125 => 22
    | 43 | 60 | 61 | 62 | 124 | 126 => 25
    | 45 => 20
    | 94 | 96 => 27
    | 95 => 23
    | _ => 24

/-- The `Character` predicates on `int` code points, for ASCII code points. -/
def asciiPred (name : String) (c : Nat) : Option Bool :=
  let upper := 65 ≤ c && c ≤ 90
  let lower := 97 ≤ c && c ≤ 122
  let digit := 48 ≤ c && c ≤ 57
  let ignorable := c ≤ 8 || (14 ≤ c && c ≤ 27) || c == 127
  match name with
  | "isUpperCase" => some upper
  | "isLowerCase" => some lower
  | "isTitleCase" | "isIdeographic" => some false
  | "isLetter" | "isAlphabetic" | "isUnicodeIdentifierStart" => some (upper || lower)
  | "isDigit" => some digit
  | "isLetterOrDigit" => some (upper || lower || digit)
  | "isWhitespace" => some ((9 ≤ c && c ≤ 13) || (28 ≤ c && c ≤ 32))
  | "isSpaceChar" => some (c == 32)
  | "isDefined" => some true
  | "isMirrored" => some (c == 40 || c == 41 || c == 60 || c == 62 || c == 91 || c == 93 || c == 123 || c == 125)
  | "isJavaIdentifierStart" => some (upper || lower || c == 36 || c == 95)
  | "isJavaIdentifierPart" => some (upper || lower || digit || c == 36 || c == 95 || ignorable)
  | "isUnicodeIdentifierPart" => some (upper || lower || digit || c == 95 || ignorable)
  | "isIdentifierIgnorable" => some ignorable
  | _ => none

/-- `asciiPred` beyond ASCII, from the Unicode tables (`Jimple/Unicode.lean`); `none` for the
    predicates the tables do not cover. -/
def uniPred (name : String) (c : Nat) : Option Bool :=
  match name with
  | "isUpperCase" => some (Unicode.isUpper c)
  | "isLowerCase" => some (Unicode.isLower c)
  | "isTitleCase" => some (Unicode.isTitle c)
  | "isIdeographic" => some (Unicode.isIdeographic c)
  | "isLetter" => some (Unicode.isLetter c)
  | "isAlphabetic" => some (Unicode.isAlphabetic c)
  | "isDigit" => some (Unicode.isDigit c)
  | "isLetterOrDigit" => some (Unicode.isLetter c || Unicode.isDigit c)
  | "isWhitespace" => some (Unicode.isWhitespace c)
  | "isSpaceChar" => some (Unicode.isSpaceChar c)
  | "isDefined" => some (Unicode.charType c != 0)
  | _ => none

/-- `lastIndexOf(t, fromIdx)`: the largest index `i ≤ fromIdx` where `t` occurs in `s`, or `-1`. -/
def lastIndexFrom (s t : JStr) (fromIdx : Int) : Int :=
  let top := min fromIdx (s.length - t.length)
  if top < 0 then -1
  else
    let hits := (List.range (top.toNat + 1)).filter fun i => JStr.isPrefixOf t (s.drop i)
    match hits.getLast? with
    | some i => i
    | none => -1

/-- A UTF-16 surrogate unit. -/
def isSurrJ (c : JChar) : Bool := 0xD800 ≤ c.toNat && c.toNat ≤ 0xDFFF

/-- Two units equal ignoring case, as `String.regionMatches(true, …)` compares them: equal, or
    with equal upper cases, or with equal lower cases of those (the Georgian exception). -/
def charEqIC (c1 c2 : JChar) : Bool :=
  c1 == c2 ||
    (let u1 := Unicode.toUpper c1.toNat % 65536
     let u2 := Unicode.toUpper c2.toNat % 65536
     u1 == u2 || Unicode.toLower u1 % 65536 == Unicode.toLower u2 % 65536)

/-- Case-insensitive equality of two strings of equal length (`equalsIgnoreCase`); `none` if a
    surrogate occurs (supplementary characters are not modelled here). -/
def strEqIC (a b : JStr) : Option Bool :=
  if JStr.isAscii a && JStr.isAscii b then some (JStr.asciiLower a == JStr.asciiLower b)
  else if a.any isSurrJ || b.any isSurrJ then none
  else some (a.length == b.length && (a.zip b).all fun (x, y) => charEqIC x y)

/-- `String.compareToIgnoreCase` (`CASE_INSENSITIVE_ORDER`): the first difference of the
    upper-then-lower-cased units, else the length difference; `none` with surrogates. -/
def strCompareIC (a b : JStr) : Option Int :=
  if a.any isSurrJ || b.any isSurrJ then none
  else
    let fold (c : JChar) : Nat := Unicode.toLower (Unicode.toUpper c.toNat % 65536) % 65536
    let diff := (a.zip b).findSome? fun (x, y) =>
      if x == y then none
      else
        let ux := Unicode.toUpper x.toNat % 65536
        let uy := Unicode.toUpper y.toNat % 65536
        if ux == uy then none
        else
          let lx := Unicode.toLower ux % 65536
          let ly := Unicode.toLower uy % 65536
          if lx == ly then none else some ((lx : Int) - ly)
    let _ := fold
    some (diff.getD ((a.length : Int) - b.length))

/-- UTF-16 encoding of a code point. -/
def encodeCp (cp : Nat) : JStr :=
  if cp < 0x10000 then [BitVec.ofNat 16 cp]
  else [BitVec.ofNat 16 (0xD800 + (cp - 0x10000) / 1024), BitVec.ofNat 16 (0xDC00 + (cp - 0x10000) % 1024)]

/-- Map each code point of `s` (`kind` 0 upper, 1 lower case) as `String.toUpperCase()` /
    `toLowerCase()` do in the default (English) locale, with the special mappings of
    multi-character results. -/
def strCaseMapJ (kind : Nat) : Nat → JStr → JStr
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, c :: rest =>
    match rest with
    | d :: rest' =>
      if 0xD800 ≤ c.toNat && c.toNat ≤ 0xDBFF && 0xDC00 ≤ d.toNat && d.toNat ≤ 0xDFFF then
        let cp := (c.toNat - 0xD800) * 1024 + (d.toNat - 0xDC00) + 0x10000
        encodeCp (if kind == 0 then Unicode.toUpper cp else Unicode.toLower cp) ++ strCaseMapJ kind f rest'
      else one c ++ strCaseMapJ kind f rest
    | [] => one c
where
  one (c : JChar) : JStr :=
    if isSurrJ c then [c]
    else match Unicode.specialMap kind c.toNat with
      | some us => us.map (BitVec.ofNat 16 ·)
      | none => encodeCp (if kind == 0 then Unicode.toUpper c.toNat else Unicode.toLower c.toNat)

/-- `String.regionMatches`: `none` when case is ignored and a compared unit is a surrogate. -/
def regionMatchesJ (ic : Bool) (s : JStr) (to : Int) (t : JStr) (oo n : Int) : Option Bool :=
  if oo < 0 ∨ to < 0 ∨ to > s.length - n ∨ oo > t.length - n then some false
  else
    let a := (s.drop to.toNat).take n.toNat
    let b := (t.drop oo.toNat).take n.toNat
    if !ic then some (a == b)
    else strEqIC a b

/-! ### Calls into application classes (library classes loaded from Jimple) -/

/-- Call the static method `sig` of an application class, initializing the class first as
    `invokestatic` does, and continue with its result; `none` if `sig` is not an application
    method with a body (for example when the classes are not part of the program). -/
def callStaticK (P : Program) (sig : MethodSig) (args : List Value) (σ : State)
    (k : Option Value → State → NRes) : Option NRes :=
  match P.selectStatic sig with
  | .jimple m =>
    if m.decl.body.isNone then none
    else some <| initThen P m.cls σ fun σ => .call sig (.method m) args σ fun out => match out with
      | .normal r σ' => k r σ'
      | .exc e σ' => .ret (.thr e σ')
      | .wrong msg => bad msg
  | _ => none

/-- Call the instance method `sig` on an object of an application class (selected by its runtime
    class) and continue with its result. -/
def callVirtK (P : Program) (sig : MethodSig) (recv : Value) (args : List Value) (σ : State)
    (k : Option Value → State → NRes) : NRes :=
  match objAt σ recv with
  | some (_, .plain c _) =>
    if P.isProgClass c then
      .call sig (.virtual c) (recv :: args) σ fun out => match out with
        | .normal r σ' => k r σ'
        | .exc e σ' => .ret (.thr e σ')
        | .wrong msg => bad msg
    else bad s!"{sig.name} on a library object is not modelled"
  | _ => if recv == .null then thrNPE σ else bad s!"{sig.name} on this object kind is not modelled"

def patternCls : ClassName := "java.util.regex.Pattern"
def matcherCls : ClassName := "java.util.regex.Matcher"
def patCompileSig : MethodSig := ⟨patternCls, .cls patternCls, "compile", [.cls "java.lang.String"]⟩
def patMatchesSig : MethodSig :=
  ⟨patternCls, .prim .boolean, "matches", [.cls "java.lang.String", .cls "java.lang.CharSequence"]⟩
def patMatcherSig : MethodSig := ⟨patternCls, .cls matcherCls, "matcher", [.cls "java.lang.CharSequence"]⟩
def patSplitSig : MethodSig :=
  ⟨patternCls, .array (.cls "java.lang.String"), "split", [.cls "java.lang.CharSequence", .prim .int]⟩
def matcherReplaceSig (name : String) : MethodSig := ⟨matcherCls, .cls "java.lang.String", name, [.cls "java.lang.String"]⟩

/-- `String.replaceAll`/`replaceFirst`: `Pattern.compile(regex).matcher(this).replaceAll(rep)`. -/
def regexReplaceK (P : Program) (name : String) (self r rp : Value) (σ : State) : Option NRes :=
  callStaticK P patCompileSig [r] σ fun pat σ1 =>
    callVirtK P patMatcherSig (pat.getD .null) [self] σ1 fun m σ2 =>
      callVirtK P (matcherReplaceSig name) (m.getD .null) [rp] σ2 fun res σ3 => ok (res.getD .null) σ3

/-- The separator of `String.split`'s fast path: a one-character regex that is not one of
    `.$|()[{^?*+\`, or a backslash followed by a character that is not an ASCII letter or digit;
    in both cases not a surrogate. -/
def splitFastChar? (r : JStr) : Option JChar :=
  let surr (c : JChar) : Bool := 0xD800 ≤ c.toNat && c.toNat ≤ 0xDFFF
  match r with
  | [c] => if (jstr ".$|()[{^?*+\\").contains c || surr c then none else some c
  | [b, c] =>
    let alnum := (48 ≤ c.toNat && c.toNat ≤ 57) || (65 ≤ c.toNat && c.toNat ≤ 90) || (97 ≤ c.toNat && c.toNat ≤ 122)
    if b.toNat == 92 && !alnum && !surr c then some c else none
  | _ => none

/-- The segments `(begin, end)` the fast path's loop produces from the separator positions. -/
def fastSplitSegs (n : Nat) (limited : Bool) (limit : Int) :
    List Nat → Nat → List (Nat × Nat) → List (Nat × Nat) × Nat
  | [], off, acc => (acc, off)
  | next :: rest, off, acc =>
    if !limited || (acc.length : Int) < limit - 1 then fastSplitSegs n limited limit rest (next + 1) (acc ++ [(off, next)])
    else (acc ++ [(off, n)], n)

/-- `String.split` on a single literal separator `ch` (the JDK's fast path): new strings for the
    segments (`this` for the whole string, as `substring` returns it), trailing empty segments
    removed when `limit` is 0. -/
def fastSplitArr (self : Value) (s : JStr) (ch : JChar) (limit : Int) (σ : State) : NRes :=
  let idxs := (List.range s.length).filter fun i => s[i]? == some ch
  if idxs.isEmpty then okObj (.array (.cls "java.lang.String") [self]) σ
  else
    let limited := limit > 0
    let (segs, off) := fastSplitSegs s.length limited limit idxs 0 []
    let segs := if !limited || (segs.length : Int) < limit then segs ++ [(off, s.length)] else segs
    let segs := if limit == 0 then (segs.reverse.dropWhile fun (b, e) => b == e).reverse else segs
    let (vs, σ) := segs.foldl (fun (acc : List Value × State) (b, e) =>
      if b == 0 && e == s.length then (acc.1 ++ [self], acc.2)
      else let (v, σ') := allocStr ((s.take e).drop b) acc.2; (acc.1 ++ [v], σ')) ([], σ)
    okObj (.array (.cls "java.lang.String") vs) σ

/-- `String.split(regex, limit)`: the fast path natively, otherwise
    `Pattern.compile(regex).split(this, limit)` (when the regex classes are in the program). -/
def splitK (P : Program) (self : Value) (s : JStr) (r : Value) (limit : Int) (σ : State) : Option NRes :=
  if r == .null then some (thrNPE σ)
  else match strOf σ r with
    | none => some (bad "expected String")
    | some rs =>
      match splitFastChar? rs with
      | some ch => some (fastSplitArr self s ch limit σ)
      | none => callStaticK P patCompileSig [r] σ fun pat σ1 =>
          callVirtK P patSplitSig (pat.getD .null) [self, .int (BitVec.ofInt 32 limit)] σ1 fun res σ2 =>
            ok (res.getD .null) σ2

def stringInst (P : Program) (sig : MethodSig) (self : Value) (s : JStr) (args : List Value)
    (σ : State) : Option NRes :=
  match sig.name, sig.params, args with
  | "length", [], [] => some (okInt s.length σ)
  | "formatted", [_], [av] => some (formatK P s av σ fun r σ' => okStr r σ')
  | "isEmpty", [], [] => some (okBool s.isEmpty σ)
  | "charAt", [_], [i] => some <| argI i fun i => charAtIdx s i σ fun c => ok (.int (c.zeroExtend 32)) σ
  | "equals", [_], [o] => some (okBool (strOf σ o == some s) σ)
  | "equalsIgnoreCase", [_], [o] =>
    some <| match strOf σ o with
      | none => okBool false σ
      | some t =>
        if JStr.isAscii s ∧ JStr.isAscii t then okBool (JStr.asciiUpper s == JStr.asciiUpper t) σ
        else if s.length != t.length then okBool false σ
        else match strEqIC s t with
          | some b => okBool b σ
          | none => bad "equalsIgnoreCase with surrogates is not modelled"
  | "hashCode", [], [] => some (ok (.int (JStr.hashCode s)) σ)
  | "compareTo", [_], [o] => some <| argStr σ o fun t => ok (.int (JStr.compareTo s t)) σ
  | "compareToIgnoreCase", [_], [o] => some <| argStr σ o fun t => match strCompareIC s t with
      | some r => okInt r σ
      | none => bad "compareToIgnoreCase with surrogates is not modelled"
  | "concat", [_], [o] => some <| argStr σ o fun t => okStr (s ++ t) σ
  | "substring", [_], [b] => some <| argI b fun b =>
      if 0 ≤ b.toInt ∧ b.toInt ≤ s.length then okStr (s.drop b.toNat) σ
      else thr "java.lang.StringIndexOutOfBoundsException"
        (some s!"begin {b.toInt}, end {s.length}, length {s.length}") σ
  | "substring", [_, _], [b, e] => some <| argI b fun b => argI e fun e =>
      if 0 ≤ b.toInt ∧ b.toInt ≤ e.toInt ∧ e.toInt ≤ s.length then
        okStr ((s.take e.toNat).drop b.toNat) σ
      else thr "java.lang.StringIndexOutOfBoundsException"
        (some s!"begin {b.toInt}, end {e.toInt}, length {s.length}") σ
  | "indexOf", [.cls _], [o] => some <| argStr σ o fun t => okInt (JStr.indexOf s t) σ
  | "indexOf", [.prim .int], [c] => some <| argI c fun c =>
      if c.toNat < 0x10000 then okInt (JStr.indexOf s [c.setWidth 16]) σ
      else bad "indexOf of a supplementary code point is not modelled"
  | "contains", [_], [o] => some <| argChars σ o fun t => okBool (JStr.indexOf s t ≥ 0) σ
  | "startsWith", [_], [o] => some <| argStr σ o fun t => okBool (JStr.isPrefixOf t s) σ
  | "endsWith", [_], [o] => some <| argStr σ o fun t =>
      okBool (JStr.isPrefixOf t.reverse s.reverse) σ
  | "trim", [], [] => some (okStr (JStr.trim s) σ)
  | "toUpperCase", [], [] =>
    some <| if JStr.isAscii s then okStr (JStr.asciiUpper s) σ
      else okStr (strCaseMapJ 0 (s.length + 1) s) σ
  | "toLowerCase", [], [] =>
    some <| if JStr.isAscii s then okStr (JStr.asciiLower s) σ
      -- the final-sigma rule (Σ → ς at the end of a word) depends on the context: not modelled
      else if s.any (·.toNat == 0x03A3) then bad "toLowerCase of a capital sigma is not modelled"
      else okStr (strCaseMapJ 1 (s.length + 1) s) σ
  | "toString", [], [] => some (ok self σ)
  | "intern", [], [] => some (ok self σ)
  | "replace", [.prim .char, .prim .char], [a, b] => some <| argI a fun a => argI b fun b =>
      okStr (s.map fun c => if c = a.setWidth 16 then b.setWidth 16 else c) σ
  | "repeat", [_], [n] => some <| argI n fun n =>
      if n.toInt < 0 then thr IAE (some s!"count is negative: {n.toInt}") σ
      else okStr ((List.replicate n.toNat s).flatten) σ
  | "toCharArray", [], [] => some (okObj (.array (.prim .char) (s.map fun c => .int (c.zeroExtend 32))) σ)
  | "codePointAt", [_], [i] => some <| argI i fun i => charAtIdx s i σ fun c => okInt (codePointAtJ s i.toNat c) σ
  | "codePointBefore", [_], [i] => some <| argI i fun i => codePointBeforeK s i σ fun cp => okInt cp σ
  | "codePointCount", [_, _], [b, e] => some <| argI b fun b => argI e fun e =>
      if b.toInt < 0 ∨ b.toInt > e.toInt ∨ e.toInt > s.length then
        thr IOOBE (some s!"Range [{b.toInt}, {e.toInt}) out of bounds for length {s.length}") σ
      else okInt (cpCount ((s.take e.toNat).drop b.toNat)) σ
  | "subSequence", [_, _], [b, e] => some <| argI b fun b => argI e fun e =>
      if 0 ≤ b.toInt ∧ b.toInt ≤ e.toInt ∧ e.toInt ≤ s.length then okStr ((s.take e.toNat).drop b.toNat) σ
      else thr "java.lang.StringIndexOutOfBoundsException"
        (some s!"begin {b.toInt}, end {e.toInt}, length {s.length}") σ
  | "indexOf", [.cls _, .prim .int], [o, f] => some <| argStr σ o fun t => argI f fun f =>
      let f' := (max f.toInt 0).toNat
      if f' ≥ s.length then okInt (if t.isEmpty then s.length else -1) σ
      else
        let r := JStr.indexOf (s.drop f') t
        okInt (if r < 0 then -1 else r + f') σ
  | "indexOf", [.prim .int, .prim .int], [c, f] => some <| argI c fun c => argI f fun f =>
      if c.toNat ≥ 0x10000 then bad "indexOf of a supplementary code point is not modelled"
      else
        let f' := (max f.toInt 0).toNat
        let r := JStr.indexOf (s.drop f') [c.setWidth 16]
        okInt (if f' ≥ s.length ∨ r < 0 then -1 else r + f') σ
  | "lastIndexOf", [.prim .int], [c] => some <| argI c fun c =>
      if c.toNat ≥ 0x10000 then bad "lastIndexOf of a supplementary code point is not modelled"
      else
        let r := JStr.indexOf s.reverse [c.setWidth 16]
        okInt (if r < 0 then -1 else s.length - 1 - r) σ
  | "lastIndexOf", [.prim .int, .prim .int], [c, f] => some <| argI c fun c => argI f fun f =>
      if c.toNat ≥ 0x10000 then bad "lastIndexOf of a supplementary code point is not modelled"
      else okInt (lastIndexFrom s [c.setWidth 16] f.toInt) σ
  | "lastIndexOf", [.cls _], [o] => some <| argStr σ o fun t => okInt (lastIndexFrom s t s.length) σ
  | "lastIndexOf", [.cls _, .prim .int], [o, f] => some <| argStr σ o fun t => argI f fun f =>
      okInt (lastIndexFrom s t f.toInt) σ
  | "matches", [_], [r] => callStaticK P patMatchesSig [r, self] σ fun res σ' => ok (res.getD .null) σ'
  | "replaceAll", [_, _], [r, rp] => regexReplaceK P "replaceAll" self r rp σ
  | "replaceFirst", [_, _], [r, rp] => regexReplaceK P "replaceFirst" self r rp σ
  | "split", [_], [r] => splitK P self s r 0 σ
  | "split", [_, .prim .int], [r, .int l] => splitK P self s r l.toInt σ
  | "regionMatches", [.prim .int, .cls _, .prim .int, .prim .int], [to, o, oo, n] => some <|
      argI to fun to => argStr σ o fun t => argI oo fun oo => argI n fun n =>
        match regionMatchesJ false s to.toInt t oo.toInt n.toInt with
        | some b => okBool b σ
        | none => bad "regionMatches"
  | "regionMatches", [.prim .boolean, .prim .int, .cls _, .prim .int, .prim .int], [ic, to, o, oo, n] => some <|
      argI ic fun ic => argI to fun to => argStr σ o fun t => argI oo fun oo => argI n fun n =>
        match regionMatchesJ (ic ≠ 0) s to.toInt t oo.toInt n.toInt with
        | some b => okBool b σ
        | none => bad "regionMatches ignoring case on non-ASCII text is not modelled"
  | _, _, _ => none

/-! ### StringBuilder / StringBuffer -/

def builderInst (P : Program) (sig : MethodSig) (a : Addr) (c : ClassName) (s : JStr)
    (args : List Value) (σ : State) : Option NRes :=
  let self := Value.ref a
  let upd (t : JStr) (σ : State) : State := σ.setObj a (.builder c t)
  match sig.name, sig.params, args with
  | "append", [t], [v] => some <|
      match t with
      | .array (.prim .char) => argObj σ v fun _ o => match o with
        | .array _ cs => ok self (upd (s ++ cs.map fun | .int x => x.setWidth 16 | _ => 0) σ)
        | _ => bad "expected char[]"
      | _ => valueOfArg P t v σ fun t σ' => ok self (upd (s ++ t) σ')
  | "toString", [], [] => some (okStr s σ)
  | "length", [], [] => some (okInt s.length σ)
  | "charAt", [_], [i] => some <| argI i fun i => charAtIdx s i σ fun ch => ok (.int (ch.zeroExtend 32)) σ
  | "reverse", [], [] =>
    some <| if s.all (fun ch => ch.toNat < 0xD800 ∨ ch.toNat ≥ 0xE000) then ok self (upd s.reverse σ)
      else ok self (upd (restoreSurrogatePairs s.reverse) σ)
  | "setLength", [_], [n] => some <| argI n fun n =>
      if n.toInt < 0 then thr IOOBE none σ
      else ok .null (upd (s.take n.toNat ++ List.replicate (n.toNat - s.length) 0) σ)
  | "insert", [.prim .int, t], [i, v] => some <| argI i fun i =>
      if 0 ≤ i.toInt ∧ i.toInt ≤ s.length then
        valueOfArg P t v σ fun t σ' => ok self (upd (s.take i.toNat ++ t ++ s.drop i.toNat) σ')
      else thr "java.lang.StringIndexOutOfBoundsException" (some s!"offset {i.toInt}, length {s.length}") σ
  | "deleteCharAt", [_], [i] => some <| argI i fun i =>
      charAtIdx s i σ fun _ => ok self (upd (s.eraseIdx i.toNat) σ)
  | "setCharAt", [_, _], [i, ch] => some <| argI i fun i => argI ch fun ch =>
      charAtIdx s i σ fun _ => ok .null (upd (s.set i.toNat (ch.setWidth 16)) σ)
  | "indexOf", [_], [o] => some <| argStr σ o fun t => okInt (JStr.indexOf s t) σ
  | "isEmpty", [], [] => some (okBool s.isEmpty σ)
  | "delete", [_, _], [b, e] => some <| argI b fun b => argI e fun e =>
      let e' := min e.toInt s.length
      if b.toInt < 0 ∨ b.toInt > e' then
        thr "java.lang.StringIndexOutOfBoundsException" (some s!"start {b.toInt}, end {e'}, length {s.length}") σ
      else ok self (upd (s.take b.toNat ++ s.drop e'.toNat) σ)
  | "replace", [_, _, _], [b, e, x] => some <| argI b fun b => argI e fun e => argStr σ x fun t =>
      let e' := min e.toInt s.length
      if b.toInt < 0 ∨ b.toInt > e' then
        thr "java.lang.StringIndexOutOfBoundsException" (some s!"start {b.toInt}, end {e'}, length {s.length}") σ
      else ok self (upd (s.take b.toNat ++ t ++ s.drop e'.toNat) σ)
  | "substring", [_], [b] => some <| argI b fun b =>
      if 0 ≤ b.toInt ∧ b.toInt ≤ s.length then okStr (s.drop b.toNat) σ
      else thr "java.lang.StringIndexOutOfBoundsException"
        (some s!"start {b.toInt}, end {s.length}, length {s.length}") σ
  | "substring", [_, _], [b, e] | "subSequence", [_, _], [b, e] => some <| argI b fun b => argI e fun e =>
      if 0 ≤ b.toInt ∧ b.toInt ≤ e.toInt ∧ e.toInt ≤ s.length then okStr ((s.take e.toNat).drop b.toNat) σ
      else thr "java.lang.StringIndexOutOfBoundsException"
        (some s!"start {b.toInt}, end {e.toInt}, length {s.length}") σ
  | "lastIndexOf", [_], [o] => some <| argStr σ o fun t =>
      let i := JStr.indexOf s.reverse t.reverse
      okInt (if i < 0 then -1 else s.length - t.length - i) σ
  | "appendCodePoint", [_], [cp] => some <| argI cp fun cp =>
      if 0 ≤ cp.toInt ∧ cp.toInt < 0x10000 then ok self (upd (s ++ [cp.setWidth 16]) σ)
      else if 0 ≤ cp.toInt ∧ cp.toInt ≤ 0x10FFFF then
        let v := cp.toNat - 0x10000
        ok self (upd (s ++ [BitVec.ofNat 16 (0xD800 + v / 1024), BitVec.ofNat 16 (0xDC00 + v % 1024)]) σ)
      else bad "appendCodePoint of an invalid code point is not modelled"
  | "append", [.cls _, .prim .int, .prim .int], [x, b, e] => some <| argI b fun b => argI e fun e =>
      let go (t : JStr) : NRes :=
        if b.toInt < 0 ∨ b.toInt > e.toInt ∨ e.toInt > t.length then
          thr IOOBE (some s!"start {b.toInt}, end {e.toInt}, length {t.length}") σ
        else ok self (upd (s ++ (t.take e.toNat).drop b.toNat) σ)
      if x == .null then go (jstr "null") else argChars σ x go
  | _, _, _ => none

/-! ### Boxed primitives -/

def boxedInst (sig : MethodSig) (self : Value) (c : ClassName) (v : Value) (args : List Value)
    (σ : State) : Option NRes :=
  match sig.name, args with
  | "intValue", [] => match v with
    | .int x => some (ok (.int x) σ)
    | .long x => some (ok (.int (JLong.toInt x)) σ)
    | .double x => some (ok (.int (JFloat.d2i x)) σ)
    | .float x => some (ok (.int (JFloat.f2i x)) σ)
    | _ => none
  | "longValue", [] => match v with
    | .int x => some (ok (.long (JInt.toLong x)) σ)
    | .long x => some (ok (.long x) σ)
    | .double x => some (ok (.long (JFloat.d2l x)) σ)
    | .float x => some (ok (.long (JFloat.f2l x)) σ)
    | _ => none
  | "shortValue", [] => match v with | .int x => some (ok (.int (JInt.toShort x)) σ) | _ => none
  | "byteValue", [] => match v with | .int x => some (ok (.int (JInt.toByte x)) σ) | _ => none
  | "doubleValue", [] => match v with
    | .int x => some (ok (.double (JFloat.i2d x)) σ)
    | .long x => some (ok (.double (JFloat.l2d x)) σ)
    | .double x => some (ok (.double x) σ)
    | .float x => some (ok (.double (JFloat.f2d x)) σ)
    | _ => none
  | "booleanValue", [] => some (ok v σ)
  | "charValue", [] => some (ok v σ)
  | "equals", [o] => some <| okBool (match objAt σ o with
      | some (_, .boxed d w) => c == d && canonBits v == canonBits w
      | _ => false) σ
  | "hashCode", [] => match c, v with
    | "java.lang.Boolean", .int x => some (okInt (if x ≠ 0 then 1231 else 1237) σ)
    | _, .int x => some (ok (.int x) σ)
    | _, .long x => some (ok (.int (JLong.toInt (x ^^^ (x >>> 32)))) σ)
    | _, _ => none
  | "compareTo", [o] => some <| match nCompare σ self o with
    | some r => okInt r σ
    | none => match o with
      | .null => thrNPE σ
      | _ => bad "compareTo"
  | "floatValue", [] => match v with
    | .int x => some (ok (.float (JFloat.i2f x)) σ)
    | .long x => some (ok (.float (JFloat.l2f x)) σ)
    | .float x => some (ok (.float x) σ)
    | .double x => some (ok (.float (JFloat.d2f x)) σ)
    | _ => none
  | "toString", [] => match nObjStr σ (.boxed c v) with
    | some s => some (okStr s σ)
    | none => none
  | _, _ => none

def parseIntStr (s : JStr) (lo hi : Int) : Option Int :=
  let cs := JStr.toLean s
  let (neg, ds) := match cs.toList with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  if ds.isEmpty ∨ ¬ ds.all Char.isDigit then none
  else
    let n : Int := BigDec.digitsVal ds
    let v := if neg then -n else n
    if lo ≤ v ∧ v ≤ hi then some v else none

/-! ### java.math.BigDecimal -/

def rnd (r : Option BigDec) (σ : State) : NRes :=
  match r with
  | some d => okObj (.dec d) σ
  | none => thr AE (some "Rounding necessary") σ

def divZero (d : BigDec) (σ : State) : NRes :=
  thr AE (some (if d.unscaled = 0 then "Division undefined" else "Division by zero")) σ

def decInst (sig : MethodSig) (self : Value) (d : BigDec) (args : List Value) (σ : State) :
    Option NRes :=
  match sig.name, sig.params, args with
  | "add", [_], [x] => some <| argDec σ x fun e => okObj (.dec (d.add e)) σ
  | "subtract", [_], [x] => some <| argDec σ x fun e => okObj (.dec (d.sub e)) σ
  | "multiply", [_], [x] => some <| argDec σ x fun e => okObj (.dec (d.mul e)) σ
  | "add", [_, _], [x, mc] => some <| argDec σ x fun e => argMC σ mc fun mc =>
      if d.unscaled = 0 ∨ e.unscaled = 0 then bad "add(MathContext) with a zero operand is not modelled"
      else rnd ((d.add e).roundPrec mc) σ
  | "subtract", [_, _], [x, mc] => some <| argDec σ x fun e => argMC σ mc fun mc =>
      if d.unscaled = 0 ∨ e.unscaled = 0 then bad "subtract(MathContext) with a zero operand is not modelled"
      else rnd ((d.sub e).roundPrec mc) σ
  | "multiply", [_, _], [x, mc] => some <| argDec σ x fun e => argMC σ mc fun mc =>
      rnd ((d.mul e).roundPrec mc) σ
  | "divide", [_], [x] => some <| argDec σ x fun e =>
      if e.unscaled = 0 then divZero d σ
      else match d.divExact e with
        | some q => okObj (.dec q) σ
        | none => thr AE (some "Non-terminating decimal expansion; no exact representable decimal result.") σ
  | "divide", [_, .prim .int, .cls "java.math.RoundingMode"], [x, s, rm] =>
    some <| argDec σ x fun e => argI s fun s => argRM σ rm fun rm =>
      if e.unscaled = 0 then divZero d σ else rnd (d.divScale e s.toInt rm) σ
  | "divide", [_, .prim .int, .prim .int], [x, s, rm] =>
    some <| argDec σ x fun e => argI s fun s => argRMInt σ rm fun rm =>
      if e.unscaled = 0 then divZero d σ else rnd (d.divScale e s.toInt rm) σ
  | "divide", [_, .cls "java.math.RoundingMode"], [x, rm] =>
    some <| argDec σ x fun e => argRM σ rm fun rm =>
      if e.unscaled = 0 then divZero d σ else rnd (d.divScale e d.scale rm) σ
  | "divide", [_, .prim .int], [x, rm] =>
    some <| argDec σ x fun e => argRMInt σ rm fun rm =>
      if e.unscaled = 0 then divZero d σ else rnd (d.divScale e d.scale rm) σ
  | "divide", [_, .cls "java.math.MathContext"], [x, mc] =>
    some <| argDec σ x fun e => argMC σ mc fun mc =>
      if e.unscaled = 0 then divZero d σ
      else match d.divMC e mc with
        | some q => okObj (.dec q) σ
        | none => thr AE (some (if mc.prec = 0 then
            "Non-terminating decimal expansion; no exact representable decimal result."
            else "Rounding necessary")) σ
  | "divideToIntegralValue", [_], [x] => some <| argDec σ x fun e =>
      if e.unscaled = 0 then divZero d σ
      else match d.divToIntegral e with | some q => okObj (.dec q) σ | none => divZero d σ
  | "remainder", [_], [x] => some <| argDec σ x fun e =>
      if e.unscaled = 0 then divZero d σ
      else match d.remainder e with | some q => okObj (.dec q) σ | none => divZero d σ
  | "setScale", [_, .cls _], [s, rm] => some <| argI s fun s => argRM σ rm fun rm =>
      rnd (d.setScale s.toInt rm) σ
  | "setScale", [_, .prim .int], [s, rm] => some <| argI s fun s => argRMInt σ rm fun rm =>
      rnd (d.setScale s.toInt rm) σ
  | "setScale", [_], [s] => some <| argI s fun s => rnd (d.setScale s.toInt .UNNECESSARY) σ
  | "round", [_], [mc] => some <| argMC σ mc fun mc => rnd (d.roundPrec mc) σ
  | "negate", [], [] => some (okObj (.dec d.negate) σ)
  | "abs", [], [] => some (if d.unscaled < 0 then okObj (.dec d.negate) σ else ok self σ)
  | "plus", [], [] => some (ok self σ)
  | "signum", [], [] => some (okInt d.signum σ)
  | "scale", [], [] => some (okInt d.scale σ)
  | "precision", [], [] => some (okInt d.precision σ)
  | "unscaledValue", [], [] => some (okObj (.bigInt d.unscaled) σ)
  | "compareTo", [_], [x] => some <| argDec σ x fun e => okInt (d.compareTo e) σ
  | "equals", [_], [x] => some (okBool (decOf σ x == some d) σ)
  | "hashCode", [], [] => some (ok (.int d.hashCode) σ)
  | "max", [_], [x] => some <| argDec σ x fun e => ok (if d.compareTo e ≥ 0 then self else x) σ
  | "min", [_], [x] => some <| argDec σ x fun e => ok (if d.compareTo e ≤ 0 then self else x) σ
  | "stripTrailingZeros", [], [] => some (okObj (.dec d.stripTrailingZeros) σ)
  | "toString", [], [] => some (okStr (jstr d.toJavaString) σ)
  | "toPlainString", [], [] => some (okStr (jstr d.toPlainString) σ)
  | "intValue", [], [] => some (ok (.int (BitVec.ofInt 32 d.toBigInt)) σ)
  | "longValue", [], [] => some (ok (.long (BitVec.ofInt 64 d.toBigInt)) σ)
  | "intValueExact", [], [] => some <| match d.toIntExact 32 with
    | some i => okInt i σ
    | none => thr AE (some (if (d.toBigInt : Rat) ≠ d.toRat then "Rounding necessary" else "Overflow")) σ
  | "longValueExact", [], [] => some <| match d.toIntExact 64 with
    | some i => ok (.long (BitVec.ofInt 64 i)) σ
    | none => thr AE (some (if (d.toBigInt : Rat) ≠ d.toRat then "Rounding necessary" else "Overflow")) σ
  | "doubleValue", [], [] =>
    some (ok (.double (JFloat.enc64 (if d.unscaled = 0 then .zero false else .num d.toRat))) σ)
  | "floatValue", [], [] =>
    some (ok (.float (JFloat.enc32 (if d.unscaled = 0 then .zero false else .num d.toRat))) σ)
  | "toBigInteger", [], [] => some (okObj (.bigInt d.toBigInt) σ)
  | "pow", [_], [n] => some <| argI n fun n => match d.pow n.toInt with
    | some r => okObj (.dec r) σ
    | none => thr AE (some "Invalid operation") σ
  | "movePointLeft", [_], [n] => some <| argI n fun n => okObj (.dec (d.movePointLeft n.toInt)) σ
  | "movePointRight", [_], [n] => some <| argI n fun n => okObj (.dec (d.movePointRight n.toInt)) σ
  | "scaleByPowerOfTen", [_], [n] => some <| argI n fun n =>
      okObj (.dec (d.scaleByPowerOfTen n.toInt)) σ
  | "divideAndRemainder", [_], [x] => some <| argDec σ x fun e =>
      if e.unscaled = 0 then divZero d σ
      else match d.divToIntegral e, d.remainder e with
        | some q, some r =>
          let (qa, σ1) := σ.alloc (.dec q)
          let (ra, σ2) := σ1.alloc (.dec r)
          okObj (.array (.cls "java.math.BigDecimal") [.ref qa, .ref ra]) σ2
        | _, _ => divZero d σ
  | _, _, _ => none

def bigIntInst (sig : MethodSig) (self : Value) (i : Int) (args : List Value) (σ : State) :
    Option NRes :=
  match sig.name, args with
  | "add", [x] => some <| argBigInt σ x fun j => okObj (.bigInt (i + j)) σ
  | "subtract", [x] => some <| argBigInt σ x fun j => okObj (.bigInt (i - j)) σ
  | "multiply", [x] => some <| argBigInt σ x fun j => okObj (.bigInt (i * j)) σ
  | "divide", [x] => some <| argBigInt σ x fun j =>
      if j = 0 then thr AE (some "BigInteger divide by zero") σ else okObj (.bigInt (i.tdiv j)) σ
  | "remainder", [x] => some <| argBigInt σ x fun j =>
      if j = 0 then thr AE (some "BigInteger divide by zero") σ else okObj (.bigInt (i.tmod j)) σ
  | "mod", [x] => some <| argBigInt σ x fun j =>
      if j ≤ 0 then thr AE (some "BigInteger: modulus not positive") σ
      else okObj (.bigInt (i.emod j)) σ
  | "negate", [] => some (okObj (.bigInt (-i)) σ)
  | "abs", [] => some (okObj (.bigInt i.natAbs) σ)
  | "signum", [] => some (okInt (if i > 0 then 1 else if i < 0 then -1 else 0) σ)
  | "compareTo", [x] => some <| argBigInt σ x fun j => okInt (if i < j then -1 else if i = j then 0 else 1) σ
  | "equals", [x] => some (okBool (bigIntOf σ x == some i) σ)
  | "hashCode", [] => some (ok (.int (BigDec.bigIntHash i)) σ)
  | "pow", [n] => some <| argI n fun n =>
      if n.toInt < 0 then thr AE (some "Negative exponent") σ else okObj (.bigInt (i ^ n.toNat)) σ
  | "gcd", [x] => some <| argBigInt σ x fun j => okObj (.bigInt (Int.gcd i j)) σ
  | "max", [x] => some <| argBigInt σ x fun j => ok (if i ≥ j then self else x) σ
  | "min", [x] => some <| argBigInt σ x fun j => ok (if i ≤ j then self else x) σ
  | "toString", [] => some (okStr (JStr.ofInt i) σ)
  | "intValue", [] => some (ok (.int (BitVec.ofInt 32 i)) σ)
  | "longValue", [] => some (ok (.long (BitVec.ofInt 64 i)) σ)
  | "shiftLeft", [n] => some <| argI n fun n =>
      if n.toInt.natAbs > 1048576 then bad "BigInteger shift by more than 2^20 bits is not modelled"
      else okObj (.bigInt (if n.toInt ≥ 0 then i * 2 ^ n.toNat else Int.fdiv i (2 ^ n.toInt.natAbs))) σ
  | "shiftRight", [n] => some <| argI n fun n =>
      if n.toInt.natAbs > 1048576 then bad "BigInteger shift by more than 2^20 bits is not modelled"
      else okObj (.bigInt (if n.toInt ≥ 0 then Int.fdiv i (2 ^ n.toNat) else i * 2 ^ n.toInt.natAbs)) σ
  | "testBit", [n] => some <| argI n fun n =>
      if n.toInt < 0 then thr AE (some "Negative bit address") σ
      else okBool (Int.fdiv i (2 ^ n.toNat) % 2 = 1) σ
  | "bitLength", [] => some (okInt (bitLen i) σ)
  | "toString", [r] => some <| argI r fun r =>
      okStr (intDigits (if 2 ≤ r.toInt ∧ r.toInt ≤ 36 then r.toNat else 10) i) σ
  | "modPow", [e, m] => some <| argBigInt σ e fun e => argBigInt σ m fun m =>
      if m ≤ 0 then thr AE (some "BigInteger: modulus not positive") σ
      else if e < 0 then bad "BigInteger.modPow with a negative exponent is not modelled"
      else okObj (.bigInt (powModNat (i.emod m).toNat e.toNat m.toNat)) σ
  | _, _ => none

/-! ### Collections -/

def listMutable (k : ListKind) (σ : State) (go : NRes) : NRes :=
  if k = .immutable then thr UOE none σ else go

def idxCheck (i : I32) (n : Nat) (σ : State) (go : Nat → NRes) : NRes :=
  if 0 ≤ i.toInt ∧ i.toInt < n then go i.toNat
  else thr IOOBE (some s!"Index {i.toInt} out of bounds for length {n}") σ

/-- Elements of a collection-like object (for `addAll`, copy constructors). -/
def elemsOf (σ : State) (o : Obj) : Option (List Value) :=
  match o with
  | .list _ xs _ => some xs
  | .set _ xs _ => some xs
  | .view src .keys => match σ.heap src with | some (.map _ kvs _) => some (kvs.map (·.1)) | _ => none
  | .view src .values => match σ.heap src with | some (.map _ kvs _) => some (kvs.map (·.2)) | _ => none
  | .plain "java.util.Arrays$ArrayList" fs =>
    match (Fields.get fs ("java.util.Arrays$ArrayList", "a")).bind (objAt σ ·) with
    | some (_, .array _ xs) => some xs
    | _ => none
  | .plain "java.util.ArrayList$SubList" fs =>
    -- a sublist of a list changed structurally since has no elements here (the JDK throws)
    let c := "java.util.ArrayList$SubList"
    match Fields.get fs (c, "root"), Fields.get fs (c, "offset"), Fields.get fs (c, "size"), Fields.get fs (c, "modCount") with
    | some root, some (.int off), some (.int sz), some (.int mc) =>
      match objAt σ root with
      | some (_, .list _ xs m) => if m == mc.toNat then some ((xs.drop off.toNat).take sz.toNat) else none
      | _ => none
    | _, _, _, _ => none
  | _ => none

/-- `toArray(T[] a)` of a list with elements `xs` (`ArrayList`, its sublists): a new array of
    `a`'s type if `a` is too short, otherwise `xs` copied into `a`, followed by `null` if room is
    left. -/
def toArrayInto (P : Program) (xs : List Value) (arr : Value) (σ : State) : NRes :=
  argObj σ arr fun aa o => match o with
    | .array et ys =>
      let storable := xs.all fun v => v == .null || (match objAt σ v with
        | some (_, ob) => P.subtype ob.ty et == some true
        | none => false)
      if !storable then bad "toArray into an array of an incompatible type is not modelled"
      else if ys.length < xs.length then okObj (.array et xs) σ
      else
        let ys' := xs ++ (if ys.length > xs.length then .null :: ys.drop (xs.length + 1) else [])
        ok arr (σ.setObj aa (.array et ys'))
    | _ => bad "expected an array"

/-- `ArrayList.subList` views are plain objects of this class: the list (`root`), the range
    (`offset`, `size`) and the list's modification count when the view was made. -/
def subListCls : ClassName := "java.util.ArrayList$SubList"

def subListFields (root : Value) (off size mods : Nat) : List (FieldKey × Value) :=
  [((subListCls, "root"), root), ((subListCls, "offset"), .int (BitVec.ofNat 32 off)),
   ((subListCls, "size"), .int (BitVec.ofNat 32 size)), ((subListCls, "modCount"), .int (BitVec.ofNat 32 mods))]

/-- `ArrayList.subListRangeCheck`, then `k`. -/
def subListRange (f t : I32) (n : Nat) (σ : State) (k : NRes) : NRes :=
  if f.toInt < 0 then thr IOOBE (some s!"fromIndex = {f.toInt}") σ
  else if t.toInt > n then thr IOOBE (some s!"toIndex = {t.toInt}") σ
  else if f.toInt > t.toInt then thr IAE (some s!"fromIndex({f.toInt}) > toIndex({t.toInt})") σ
  else k

def listInst (P : Program) (sig : MethodSig) (a : Addr) (k : ListKind) (xs : List Value)
    (m : Nat) (args : List Value) (σ : State) : Option NRes :=
  let self := Value.ref a
  let put (ys : List Value) (m' : Nat) (σ : State) : State := σ.setObj a (.list k ys m')
  match sig.name, sig.params, args with
  | "size", [], [] => some (okInt xs.length σ)
  | "isEmpty", [], [] => some (okBool xs.isEmpty σ)
  | "get", [_], [i] => some <| argI i fun i => idxCheck i xs.length σ fun n =>
      match xs[n]? with | some v => ok v σ | none => bad "index"
  | "add", [_], [v] => some <| listMutable k σ <| okBool true (put (xs ++ [v]) (m + 1) σ)
  | "add", [.prim .int, _], [i, v] => some <| listMutable k σ <| argI i fun i =>
      if 0 ≤ i.toInt ∧ i.toInt ≤ xs.length then okVoid (put (xs.insertIdx i.toNat v) (m + 1) σ)
      else thr IOOBE (some s!"Index: {i.toInt}, Size: {xs.length}") σ
  | "set", [_, _], [i, v] => some <| listMutable k σ <| argI i fun i =>
      idxCheck i xs.length σ fun n =>
        match xs[n]? with | some old => ok old (put (xs.set n v) m σ) | none => bad "index"
  | "remove", [.prim .int], [i] => some <| listMutable k σ <| argI i fun i =>
      idxCheck i xs.length σ fun n =>
        match xs[n]? with | some old => ok old (put (xs.eraseIdx n) (m + 1) σ) | none => bad "index"
  | "remove", [.cls _], [v] => some <| listMutable k σ <| match findElem P σ v xs with
    | some (some n) => okBool true (put (xs.eraseIdx n) (m + 1) σ)
    | some none => okBool false σ
    | none => findElemK P false v xs 0 σ fun r σ' => match r with
      | some n => okBool true (put (xs.eraseIdx n) (m + 1) σ')
      | none => okBool false σ'
  | "contains", [_], [v] => some <| match findElem P σ v xs with
    | some r => okBool r.isSome σ
    | none => findElemK P false v xs 0 σ fun r σ' => okBool r.isSome σ'
  | "indexOf", [_], [v] => some <| match findElem P σ v xs with
    | some (some n) => okInt n σ
    | some none => okInt (-1) σ
    | none => findElemK P false v xs 0 σ fun r σ' => okInt ((r.map Int.ofNat).getD (-1)) σ'
  | "clear", [], [] => some <| listMutable k σ <| okVoid (put [] (m + 1) σ)
  | "addAll", [_], [c] => some <| listMutable k σ <| argObj σ c fun _ o => match elemsOf σ o with
    | some ys => okBool (!ys.isEmpty) (put (xs ++ ys) (m + 1) σ)
    | none => bad "addAll from this collection kind is not modelled"
  | "iterator", [], [] => some (okObj (.iter a .list [] 0 m) σ)
  | "toString", [], [] => some <|
      match xs.mapM (fun v => if v == .null then some (jstr "null") else (objAt σ v).bind (nObjStr σ ·.2)) with
      | some ss => okStr (jstr "[" ++ (ss.intersperse (jstr ", ")).flatten ++ jstr "]") σ
      | none => bad "toString of these list elements is not modelled"
  | "addFirst", [_], [v] => some <| listMutable k σ <| okVoid (put (v :: xs) (m + 1) σ)
  | "addLast", [_], [v] => some <| listMutable k σ <| okVoid (put (xs ++ [v]) (m + 1) σ)
  | "getFirst", [], [] => some <| match xs with
    | v :: _ => ok v σ | [] => thr NSEE none σ
  | "getLast", [], [] => some <| match xs.getLast? with
    | some v => ok v σ | none => thr NSEE none σ
  | "removeFirst", [], [] => some <| listMutable k σ <| match xs with
    | v :: rest => ok v (put rest (m + 1) σ) | [] => thr NSEE none σ
  | "equals", [_], [o] => some <|
      if o == self then okBool true σ
      else match objAt σ o with
        | some (_, .list _ ys _) =>
          if ys.length ≠ xs.length then okBool false σ
          else match (xs.zip ys).mapM (fun (x, y) => nEquals P σ x y) with
            | some bs => okBool (bs.all id) σ
            | none => allEqualK P (xs.zip ys) σ fun b σ' => okBool b σ'
        | some (_, .plain c fs') =>
          if c == "java.util.ArrayList$SubList" then bad "equals with an ArrayList.subList view is not modelled"
          else if c == "java.util.Arrays$ArrayList" then
            match (Fields.get fs' (c, "a")).bind (objAt σ ·) with
            | some (_, .array _ ys) => allEqualK P (xs.zip ys) σ fun b σ' => okBool (b && xs.length == ys.length) σ'
            | _ => bad "malformed Arrays.asList"
          else okBool false σ
        | some _ => okBool false σ
        | none => okBool false σ
  | "toArray", [], [] => some (okObj (.array (.cls "java.lang.Object") xs) σ)
  | "toArray", [.array _], [arr] => some (toArrayInto P xs arr σ)
  | "subList", [_, _], [f, t] => some <| argI f fun f => argI t fun t =>
      subListRange f t xs.length σ <|
        if k != .arrayList then bad "subList of this list kind is not modelled"
        else okObj (.plain subListCls (subListFields self f.toNat (t.toNat - f.toNat) m)) σ
  | _, _, _ => none

def mapInst (P : Program) (sig : MethodSig) (a : Addr) (k : MapKind) (kvs : List (Value × Value))
    (m : Nat) (args : List Value) (σ : State) : Option NRes :=
  let tree := k == .tree
  let put (kvs' : List (Value × Value)) (m' : Nat) (σ : State) : State := σ.setObj a (.map k kvs' m')
  let nokey : NRes := bad "key equality on application objects is not modelled"
  match sig.name, sig.params, args with
  | "size", [], [] => some (okInt kvs.length σ)
  | "isEmpty", [], [] => some (okBool kvs.isEmpty σ)
  | "get", [_], [key] => some <|
      if tree ∧ key == .null then thrNPE σ
      else if tree ∧ !isComparableObj P σ key then thr "java.lang.ClassCastException" none σ
      else match findKey P σ tree key kvs with
        | some (some (_, v)) => ok v σ
        | some none => ok .null σ
        | none => findKeyK P tree key kvs 0 σ fun r σ' => ok ((r.map (·.2)).getD .null) σ'
  | "getOrDefault", [_, _], [key, dflt] => some <|
      if tree ∧ key == .null then thrNPE σ
      else if tree ∧ !isComparableObj P σ key then thr "java.lang.ClassCastException" none σ
      else match findKey P σ tree key kvs with
        | some (some (_, v)) => ok v σ
        | some none => ok dflt σ
        | none => findKeyK P tree key kvs 0 σ fun r σ' => ok ((r.map (·.2)).getD dflt) σ'
  | "containsKey", [_], [key] => some <|
      if tree ∧ key == .null then thrNPE σ
      else if tree ∧ !isComparableObj P σ key then thr "java.lang.ClassCastException" none σ
      else match findKey P σ tree key kvs with
        | some r => okBool r.isSome σ
        | none => findKeyK P tree key kvs 0 σ fun r σ' => okBool r.isSome σ'
  | "put", [_, _], [key, v] => some <|
      if tree ∧ key == .null then thrNPE σ
      else if tree ∧ kvs.isEmpty then selfCompareK P σ key fun σ' => ok .null (put [(key, v)] (m + 1) σ')
      else match findKey P σ tree key kvs with
        | some (some (i, old)) => ok old (put (kvs.set i (kvs[i]?.map (·.1) |>.getD key, v)) m σ)
        | some none =>
          if tree then match insertSorted σ key v kvs with
            | some kvs' => ok .null (put kvs' (m + 1) σ)
            | none => nokey
          else ok .null (put (kvs ++ [(key, v)]) (m + 1) σ)
        | none => mapPutK P a k key v kvs m σ
  | "putIfAbsent", [_, _], [key, v] => some <|
      if tree ∧ key == .null then thrNPE σ
      else if tree ∧ kvs.isEmpty then selfCompareK P σ key fun σ' => ok .null (put [(key, v)] (m + 1) σ')
      else match findKey P σ tree key kvs with
        | some (some (i, old)) =>
          if old == .null then ok .null (put (kvs.set i (key, v)) m σ) else ok old σ
        | some none =>
          if tree then match insertSorted σ key v kvs with
            | some kvs' => ok .null (put kvs' (m + 1) σ)
            | none => nokey
          else ok .null (put (kvs ++ [(key, v)]) (m + 1) σ)
        | none => mapPutIfAbsentK P a k key v kvs m σ
  | "remove", [_], [key] => some <|
      if tree ∧ key == .null then thrNPE σ
      else if tree ∧ !isComparableObj P σ key then thr "java.lang.ClassCastException" none σ
      else match findKey P σ tree key kvs with
        | some (some (i, old)) => ok old (put (kvs.eraseIdx i) (m + 1) σ)
        | some none => ok .null σ
        | none => findKeyK P tree key kvs 0 σ fun r σ' => match r with
          | some (i, old) => ok old (put (kvs.eraseIdx i) (m + 1) σ')
          | none => ok .null σ'
  | "clear", [], [] => some (okVoid (put [] (m + 1) σ))
  | "keySet", [], [] => some (okObj (.view a .keys) σ)
  | "values", [], [] => some (okObj (.view a .values) σ)
  | "entrySet", [], [] => some (okObj (.view a .entries) σ)
  | "firstKey", [], [] => if !tree then none else some <| match kvs.head? with
    | some kv => ok kv.1 σ
    | none => thr NSEE none σ
  | "lastKey", [], [] => if !tree then none else some <| match kvs.getLast? with
    | some kv => ok kv.1 σ
    | none => thr NSEE none σ
  | "ceilingKey", [_], [key] => if !tree then none else some (navKey P σ (kvs.map (·.1)) key (· ≤ 0) false)
  | "higherKey", [_], [key] => if !tree then none else some (navKey P σ (kvs.map (·.1)) key (· < 0) false)
  | "floorKey", [_], [key] => if !tree then none else some (navKey P σ (kvs.map (·.1)) key (· ≥ 0) true)
  | "lowerKey", [_], [key] => if !tree then none else some (navKey P σ (kvs.map (·.1)) key (· > 0) true)
  | "containsValue", [_], [v] => some <| match kvs.mapM (fun kv => nEquals P σ v kv.2) with
    | some bs => okBool (bs.any id) σ
    | none => findElemK P (!tree) v (kvs.map (·.2)) 0 σ fun r σ' => okBool r.isSome σ'
  | _, _, _ => none

def setInst (P : Program) (sig : MethodSig) (a : Addr) (k : SetKind) (xs : List Value)
    (m : Nat) (args : List Value) (σ : State) : Option NRes :=
  let put (ys : List Value) (m' : Nat) (σ : State) : State := σ.setObj a (.set k ys m')
  let tree := k == .tree
  let noeq : NRes := bad "element equality on application objects is not modelled"
  let kvs := xs.map (·, Value.null)
  match sig.name, sig.params, args with
  | "size", [], [] => some (okInt xs.length σ)
  | "isEmpty", [], [] => some (okBool xs.isEmpty σ)
  | "contains", [_], [v] => some <|
    if tree ∧ v == .null then thrNPE σ
    else if tree ∧ !isComparableObj P σ v then thr "java.lang.ClassCastException" none σ
    else match findKey P σ tree v kvs with
    | some r => okBool r.isSome σ
    | none => findKeyK P tree v kvs 0 σ fun r σ' => okBool r.isSome σ'
  | "add", [_], [v] => some <|
      if tree ∧ v == .null then thrNPE σ
      else if tree ∧ xs.isEmpty then selfCompareK P σ v fun σ' => okBool true (put [v] (m + 1) σ')
      else match findKey P σ tree v kvs with
        | some (some _) => okBool false σ
        | some none =>
          if tree then match insertSorted σ v .null kvs with
            | some kvs' => okBool true (put (kvs'.map (·.1)) (m + 1) σ)
            | none => noeq
          else okBool true (put (xs ++ [v]) (m + 1) σ)
        | none => setAddK P k xs v σ fun r σ' => okBool r.2 (if r.2 then put r.1 (m + 1) σ' else σ')
  | "remove", [_], [v] => some <|
    if tree ∧ v == .null then thrNPE σ
    else if tree ∧ !isComparableObj P σ v then thr "java.lang.ClassCastException" none σ
    else match findKey P σ tree v kvs with
    | some (some (i, _)) => okBool true (put (xs.eraseIdx i) (m + 1) σ)
    | some none => okBool false σ
    | none => findKeyK P tree v kvs 0 σ fun r σ' => match r with
      | some (i, _) => okBool true (put (xs.eraseIdx i) (m + 1) σ')
      | none => okBool false σ'
  | "clear", [], [] => some (okVoid (put [] (m + 1) σ))
  | "iterator", [], [] => some <| orderKeys (k == .hash) xs fun ord => okObj (.iter a .set ord 0 m) σ
  | "first", [], [] => if !tree then none else some <| match xs.head? with
    | some v => ok v σ
    | none => thr NSEE none σ
  | "last", [], [] => if !tree then none else some <| match xs.getLast? with
    | some v => ok v σ
    | none => thr NSEE none σ
  | "addAll", [_], [c] => some <| argObj σ c fun _ co => match elemsOf σ co with
    | some vs =>
      if tree ∧ vs.any (· == .null) then thrNPE σ
      else match setAddAll? P σ k xs vs with
        | some (ys, ch) => okBool ch (if ch then put ys (m + 1) σ else σ)
        | none => setAddAllK P k vs (xs, false) σ fun r σ' => okBool r.2 (if r.2 then put r.1 (m + 1) σ' else σ')
    | none => bad "addAll from this collection kind is not modelled"
  | _, _, _ => none

def viewInst (sig : MethodSig) (src : Addr) (part : ViewKind) (σ : State) (args : List Value) :
    Option NRes :=
  match σ.heap src with
  | some (.map mk kvs m) =>
    match sig.name, args with
    | "size", [] => some (okInt kvs.length σ)
    | "isEmpty", [] => some (okBool kvs.isEmpty σ)
    | "iterator", [] => some <|
        orderKeys (mk == .hash) (kvs.map (·.1)) fun ord =>
          okObj (.iter src (match part with | .keys => .keys | .values => .values | .entries => .entries)
            ord 0 m) σ
    | _, _ => none
  | _ => none

def modsOf : Obj → Option Nat
  | .list _ _ m | .map _ _ m | .set _ _ m => some m
  | _ => none

def iterInst (P : Program) (sig : MethodSig) (a : Addr) (src : Addr) (part : IterSrc)
    (ord : List Value) (pos : Nat) (m : Nat) (args : List Value) (σ : State) : Option NRes :=
  match σ.heap src with
  | none => some (bad "dangling iterator source")
  | some so =>
    if modsOf so ≠ some m then some (bad "iterator used after a structural modification")
    else
      let len := match so with | .list _ xs _ => xs.length | _ => ord.length
      match sig.name, args with
      | "hasNext", [] => some (okBool (pos < len) σ)
      | "next", [] => some <|
          if pos < len then
            let σ' := σ.setObj a (.iter src part ord (pos + 1) m)
            match part, so with
            | .list, .list _ xs _ => match xs[pos]? with | some v => ok v σ' | none => bad "index"
            | .set, _ | .keys, _ => match ord[pos]? with | some v => ok v σ' | none => bad "index"
            | .values, .map mk kvs _ =>
              match ord[pos]? with
              | some key => match findKey P σ (mk == .tree) key kvs with
                | some (some (_, v)) => ok v σ'
                | _ => match kvs.find? (·.1 == key) with
                  | some kv => ok kv.2 σ'
                  | none => bad "iterator key vanished"
              | none => bad "index"
            | .entries, _ => match ord[pos]? with
              | some key => okObj (.entry src key m) σ'
              | none => bad "index"
            | _, _ => bad "iterator source kind"
          else thr NSEE none σ
      | "remove", [] => some <|
          -- removes the element returned by the last `next`. List iterators read the list
          -- by position, so the position moves back and `ord` (unused for lists) records
          -- it to detect a second `remove`; set and map iterators keep their key snapshot
          -- and a second `remove` finds the key already gone.
          let ise := thr "java.lang.IllegalStateException" none σ
          let m' := m + 1
          match part, so with
          | .list, .list k xs _ =>
            if k = .immutable then thr UOE none σ
            else if pos = 0 ∨ ord == [.int (BitVec.ofNat 32 pos)] then ise
            else
              let σ1 := σ.setObj src (.list k (xs.eraseIdx (pos - 1)) m')
              okVoid (σ1.setObj a (.iter src part [.int (BitVec.ofNat 32 (pos - 1))] (pos - 1) m'))
          | .set, .set k xs _ =>
            match (if pos = 0 then none else ord[pos - 1]?) with
            | some key =>
              if !xs.contains key then ise
              else okVoid ((σ.setObj src (.set k (xs.erase key) m')).setObj a (.iter src part ord pos m'))
            | none => ise
          | .keys, .map k kvs _ | .values, .map k kvs _ | .entries, .map k kvs _ =>
            match (if pos = 0 then none else ord[pos - 1]?) with
            | some key =>
              if !kvs.any (·.1 == key) then ise
              else okVoid ((σ.setObj src (.map k (kvs.filter (·.1 != key)) m')).setObj a (.iter src part ord pos m'))
            | none => ise
          | _, _ => bad "iterator source kind"
      | _, _ => none

def entryInst (P : Program) (sig : MethodSig) (src : Addr) (key : Value) (m : Nat)
    (args : List Value) (σ : State) : Option NRes :=
  match sig.name, args with
  | "getKey", [] => some (ok key σ)
  | "getValue", [] => some <| match σ.heap src with
    | some (.map mk kvs m') =>
      if m' ≠ m then bad "map entry used after a structural modification"
      else match findKey P σ (mk == .tree) key kvs with
        | some (some (_, v)) => ok v σ
        | _ => match kvs.find? (·.1 == key) with
          | some kv => ok kv.2 σ
          | none => bad "entry key vanished"
    | _ => bad "entry source"
  | _, _ => none

/-! ### Plain objects whose method resolves to a library class -/

def throwableField (fs : List (FieldKey × Value)) (f : String) : Value :=
  (Fields.get fs ("java.lang.Throwable", f)).getD .null

/-- `ArrayList.subList` views, read only: `size`, `isEmpty`, `get`, `toArray` and `subList` read
    through to the list, with ConcurrentModificationException after a structural change of the
    list (in the JDK's order of checks); writes and the other methods have no model. -/
def subListInst (P : Program) (sig : MethodSig) (fs : List (FieldKey × Value)) (args : List Value)
    (σ : State) : NRes :=
  match Fields.get fs (subListCls, "root"), Fields.get fs (subListCls, "offset"),
        Fields.get fs (subListCls, "size"), Fields.get fs (subListCls, "modCount") with
  | some root, some (.int off), some (.int sz), some (.int mc) =>
    match objAt σ root with
    | some (_, .list _ xs m) =>
      let elems := (xs.drop off.toNat).take sz.toNat
      let comod (k : NRes) : NRes :=
        if m != mc.toNat then thr "java.util.ConcurrentModificationException" none σ else k
      match sig.name, sig.params, args with
      | "size", [], [] => comod (okInt sz.toInt σ)
      | "isEmpty", [], [] => comod (okBool (sz.toInt == 0) σ)
      | "get", [_], [i] => argI i fun i => idxCheck i sz.toNat σ fun n => comod <|
          match elems[n]? with
          | some v => ok v σ
          | none => bad "index"
      | "toArray", [], [] => comod (okObj (.array (.cls "java.lang.Object") elems) σ)
      | "toArray", [.array _], [arr] => comod (toArrayInto P elems arr σ)
      | "subList", [_, _], [f, t] => argI f fun f => argI t fun t =>
          subListRange f t sz.toNat σ <|
            okObj (.plain subListCls (subListFields root (off.toNat + f.toNat) (t.toNat - f.toNat) mc.toNat)) σ
      | "toString", [], [] => comod (joinWith (valueOfObjN P 8) elems σ fun t σ' => okStr (jstr "[" ++ t ++ jstr "]") σ')
      | _, _, _ => bad s!"ArrayList.subList: {sig.name} is not modelled"
    | _ => bad "subList of a non-list"
  | _, _, _, _ => bad "malformed subList"

/-- `Stream.of(values)` streams are plain objects of this class: the source array, read at the
    terminal operation, and whether the stream has been used. -/
def streamCls : ClassName := "java.util.stream.ReferencePipeline$Head"

def predTestSig : MethodSig := ⟨"java.util.function.Predicate", .prim .boolean, "test", [.cls "java.lang.Object"]⟩

/-- `noneMatch`/`anyMatch`/`allMatch`: the predicate called on the elements in order until the
    result is decided. -/
def matchK (P : Program) (kind : String) (pr : Value) : List Value → State → NRes
  | [], σ => okBool (kind != "anyMatch") σ
  | x :: xs, σ =>
    match objAt σ pr with
    | some (_, .plain c _) =>
      if !P.isProgClass c then bad "a library predicate is not modelled"
      else .call predTestSig (.virtual c) [pr, x] σ fun out => match out with
        | .normal (some (.int r)) σ' =>
          let hit := r ≠ 0
          if kind == "noneMatch" && hit then okBool false σ'
          else if kind == "anyMatch" && hit then okBool true σ'
          else if kind == "allMatch" && !hit then okBool false σ'
          else matchK P kind pr xs σ'
        | .normal _ _ => bad "test returned no boolean"
        | .exc e σ' => .ret (.thr e σ')
        | .wrong msg => bad msg
    | _ => bad "predicate of this kind is not modelled"

/-- The elements of a stream: its source array sliced by the `skip`/`limit` operations so far
    (`start`, and `count` with `-1` for no limit). -/
def streamElems (σ : State) (fs : List (FieldKey × Value)) : Option (List Value) :=
  match Fields.get fs (streamCls, "source") with
  | some src =>
    match objAt σ src with
    | some (_, .array _ xs) =>
      let start : Nat := match Fields.get fs (streamCls, "start") with | some (.long n) => n.toNat | _ => 0
      let count : Int := match Fields.get fs (streamCls, "count") with | some (.long n) => n.toInt | _ => -1
      let ys := xs.drop start
      some (if count < 0 then ys else ys.take count.toNat)
    | _ => none
  | none => none

def collectorSig (name : String) (ret : ClassName) : MethodSig := ⟨"java.util.stream.Collector", .cls ret, name, []⟩
def supplierGet0 : MethodSig := ⟨"java.util.function.Supplier", .cls "java.lang.Object", "get", []⟩
def biConsumerAccept : MethodSig :=
  ⟨"java.util.function.BiConsumer", .void, "accept", [.cls "java.lang.Object", .cls "java.lang.Object"]⟩
def functionApply : MethodSig := ⟨"java.util.function.Function", .cls "java.lang.Object", "apply", [.cls "java.lang.Object"]⟩

def emptySetCls : ClassName := "java.util.Collections$EmptySet"

/-- A collector's characteristics, when known to be empty (`Collections.emptySet()`, an empty
    set); `none` otherwise. -/
def emptyCharacteristics? (σ : State) (v : Value) : Option Bool :=
  match objAt σ v with
  | some (_, .plain c _) => if c == emptySetCls then some true else none
  | some (_, .set _ [] _) => some true
  | _ => none

/-- The accumulator called on the container and each element in order. -/
def accumulateK (P : Program) (acc st : Value) : List Value → State → (State → NRes) → NRes
  | [], σ, k => k σ
  | x :: xs, σ, k => callVirtK P biConsumerAccept acc [st, x] σ fun _ σ' => accumulateK P acc st xs σ' k

/-- Streams made by `Stream.of`/`Stream.empty`: `skip` and `limit` (new stages over the same source;
    the old stage becomes linked, except for `skip(0)`, which returns the stream itself),
    `noneMatch`, `anyMatch`, `allMatch` (the predicate is checked for `null` first) and
    `collect(Collector)`: `supplier()`, `accumulator()`, `combiner()`, then the single-use check,
    `characteristics()`, `get()` of the supplier, the accumulator on each element, `characteristics()`
    again and, unless it contains `IDENTITY_FINISH`, `finisher().apply(container)` (characteristics
    must be empty sets). A second terminal operation throws IllegalStateException; other operations
    have no model. -/
def streamInst (P : Program) (sig : MethodSig) (a : Addr) (fs : List (FieldKey × Value)) (args : List Value)
    (σ : State) : NRes :=
  let linked (fs : List (FieldKey × Value)) : Bool := match Fields.get fs (streamCls, "linked") with
    | some (.int u) => u ≠ 0
    | _ => false
  let ise (σ : State) : NRes :=
    thr "java.lang.IllegalStateException" (some "stream has already been operated upon or closed") σ
  let markLinked (fs : List (FieldKey × Value)) (σ : State) : State :=
    σ.setObj a (.plain streamCls (Fields.set fs (streamCls, "linked") (.int 1)))
  let start : Int := match Fields.get fs (streamCls, "start") with | some (.long n) => n.toInt | _ => 0
  let count : Int := match Fields.get fs (streamCls, "count") with | some (.long n) => n.toInt | _ => -1
  -- a new stage over the same source with the slice (start', count')
  let stage (start' count' : Int) : NRes :=
    if linked fs then ise σ
    else
      let src := (Fields.get fs (streamCls, "source")).getD .null
      okObj (.plain streamCls [((streamCls, "source"), src), ((streamCls, "linked"), .int 0),
        ((streamCls, "start"), .long (BitVec.ofInt 64 start')), ((streamCls, "count"), .long (BitVec.ofInt 64 count'))])
        (markLinked fs σ)
  match sig.name, args with
  | "skip", [.long n] =>
    if n.toInt < 0 then thr IAE (some s!"{n.toInt}") σ
    else if n.toInt == 0 then ok (.ref a) σ
    else stage (start + n.toInt) (if count < 0 then -1 else max 0 (count - n.toInt))
  | "limit", [.long m] =>
    if m.toInt < 0 then thr IAE (some s!"{m.toInt}") σ
    else stage start (if count < 0 then m.toInt else min count m.toInt)
  | "noneMatch", [pr] | "anyMatch", [pr] | "allMatch", [pr] =>
    if pr == .null then thrNPE σ
    else if linked fs then ise σ
    else match streamElems σ fs with
      | some xs => matchK P sig.name pr xs (markLinked fs σ)
      | none => bad "stream source"
  | "collect", [c] =>
    if c == .null then thrNPE σ
    else
      callVirtK P (collectorSig "supplier" "java.util.function.Supplier") c [] σ fun sup σ1 =>
      callVirtK P (collectorSig "accumulator" "java.util.function.BiConsumer") c [] σ1 fun acc σ2 =>
      callVirtK P (collectorSig "combiner" "java.util.function.BinaryOperator") c [] σ2 fun _ σ3 =>
        match σ3.heap a with
        | some (.plain _ fs3) =>
          if linked fs3 then ise σ3
          else
            let σ4 := markLinked fs3 σ3
            callVirtK P (collectorSig "characteristics" "java.util.Set") c [] σ4 fun ch1 σ5 =>
              if ch1.getD .null == .null then thrNPE σ5
              else match emptyCharacteristics? σ5 (ch1.getD .null), streamElems σ5 fs3 with
              | some _, some xs =>
                callVirtK P supplierGet0 (sup.getD .null) [] σ5 fun st σ6 =>
                accumulateK P (acc.getD .null) (st.getD .null) xs σ6 fun σ7 =>
                callVirtK P (collectorSig "characteristics" "java.util.Set") c [] σ7 fun ch2 σ8 =>
                  if ch2.getD .null == .null then thrNPE σ8
                  else match emptyCharacteristics? σ8 (ch2.getD .null) with
                  | some _ =>
                    callVirtK P (collectorSig "finisher" "java.util.function.Function") c [] σ8 fun fin σ9 =>
                    callVirtK P functionApply (fin.getD .null) [st.getD .null] σ9 fun r σ10 => ok (r.getD .null) σ10
                  | none => bad "collector characteristics other than an empty set are not modelled"
              | none, _ => bad "collector characteristics other than an empty set are not modelled"
              | _, none => bad "stream source"
        | _ => bad "malformed stream"
  | _, _ => bad s!"Stream.{sig.name} is not modelled"

def joinerCls : ClassName := "java.util.StringJoiner"

/-- `java.util.StringJoiner` objects (prefix, delimiter, suffix, the added parts, the empty value):
    `add` (`String.valueOf` of the element), `toString`, `length`, `setEmptyValue`; other methods
    have no model. -/
def joinerInst (P : Program) (sig : MethodSig) (a : Addr) (fs : List (FieldKey × Value)) (args : List Value)
    (σ : State) : NRes :=
  let get (f : String) : Value := (Fields.get fs (joinerCls, f)).getD .null
  let str (f : String) : JStr := (strOf σ (get f)).getD []
  let parts : List Value := match objAt σ (get "parts") with | some (_, .array _ xs) => xs | _ => []
  let joined : JStr := str "prefix" ++ ((parts.filterMap (strOf σ ·)).intersperse (str "delimiter")).flatten ++ str "suffix"
  let useEmpty : Bool := get "parts" == .null && get "emptyValue" != .null
  match sig.name, args with
  | "add", [x] => valueOfObj P x σ fun t σ' =>
      let (tv, σ1) := allocStr t σ'
      let (arr, σ2) := σ1.alloc (.array (.cls "java.lang.String") (parts ++ [tv]))
      ok (.ref a) (σ2.setObj a (.plain joinerCls (Fields.set fs (joinerCls, "parts") (.ref arr))))
  | "toString", [] => if useEmpty then ok (get "emptyValue") σ else okStr ((joinerStr? σ fs).getD joined) σ
  | "length", [] => okInt ((joinerStr? σ fs).getD joined).length σ
  | "setEmptyValue", [x] =>
    if x == .null then thr "java.lang.NullPointerException" (some "The empty value must not be null") σ
    else argChars σ x fun t =>
      let (tv, σ1) := allocStr t σ
      ok (.ref a) (σ1.setObj a (.plain joinerCls (Fields.set fs (joinerCls, "emptyValue") tv)))
  | _, _ => bad s!"StringJoiner.{sig.name} is not modelled"

/-- `Collections.emptySet()` (one shared object). -/
def emptySetInst (sig : MethodSig) (args : List Value) (σ : State) : NRes :=
  match sig.name, args with
  | "size", [] => okInt 0 σ
  | "isEmpty", [] => okBool true σ
  | "contains", [_] => okBool false σ
  | "remove", [_] => okBool false σ
  | "clear", [] => okVoid σ
  | "hashCode", [] => okInt 0 σ
  | "add", [_] => thr UOE none σ
  | _, _ => bad s!"Collections.emptySet().{sig.name} is not modelled"

def asListCls : ClassName := "java.util.Arrays$ArrayList"
def arrItrCls : ClassName := "java.util.Arrays$ArrayItr"
def consumerAccept : MethodSig := ⟨"java.util.function.Consumer", .void, "accept", [.cls "java.lang.Object"]⟩

/-- `AbstractList.equals` over two element lists: `o1 == null ? o2 == null : o1.equals(o2)` along the
    common prefix, then equal lengths. -/
def abstractListEqK (P : Program) : List Value → List Value → State → NRes
  | x :: xs, y :: ys, σ => equalsK P false σ x y fun b σ' => if b then abstractListEqK P xs ys σ' else okBool false σ'
  | [], [], σ => okBool true σ
  | _, _, σ => okBool false σ

/-- `forEach(action)`: the consumer called on each element in order. -/
def forEachK (P : Program) (f : Value) : List Value → State → NRes
  | [], σ => okVoid σ
  | x :: xs, σ => callVirtK P consumerAccept f [x] σ fun _ σ' => forEachK P f xs σ'

/-- `Arrays.asList` lists: plain objects over the array (field `a`), read and written through
    (`get`, `set`, `size`, `indexOf`, `contains`, `toArray`, `iterator`, `forEach`, `equals`,
    `toString`); `add`, `remove(int)`, and `remove(Object)`/`clear`/`addAll` when they would change
    the list, throw UnsupportedOperationException as `AbstractList`/`AbstractCollection` do. -/
def asListInst (P : Program) (sig : MethodSig) (a : Addr) (fs : List (FieldKey × Value)) (args : List Value)
    (σ : State) : NRes :=
  let aioobe (i : I32) (n : Nat) : NRes :=
    thr "java.lang.ArrayIndexOutOfBoundsException" (some s!"Index {i.toInt} out of bounds for length {n}") σ
  match Fields.get fs (asListCls, "a") with
  | some arr =>
    match objAt σ arr with
    | some (aa, .array et xs) =>
      match sig.name, sig.params, args with
      | "size", [], [] => okInt xs.length σ
      | "isEmpty", [], [] => okBool xs.isEmpty σ
      | "get", [_], [i] => argI i fun i =>
          match (if 0 ≤ i.toInt then xs[i.toNat]? else none) with
          | some v => ok v σ
          | none => aioobe i xs.length
      | "set", [_, _], [i, v] => argI i fun i =>
          match (if 0 ≤ i.toInt then xs[i.toNat]? else none) with
          | some old =>
            let storable := !et.isRef || v == .null ||
              (match objAt σ v with | some (_, ob) => P.subtype ob.ty et == some true | none => false)
            if storable then ok old (σ.setObj aa (.array et (xs.set i.toNat (et.narrow v))))
            else thr "java.lang.ArrayStoreException" none σ
          | none => aioobe i xs.length
      | "indexOf", [_], [o] => findElemK P false o xs 0 σ fun r σ' => okInt ((r.map Int.ofNat).getD (-1)) σ'
      | "contains", [_], [o] => findElemK P false o xs 0 σ fun r σ' => okBool r.isSome σ'
      | "toArray", [], [] => okObj (.array (.cls "java.lang.Object") xs) σ
      | "toArray", [.array _], [dst] => toArrayInto P xs dst σ
      | "iterator", [], [] => okObj (.plain arrItrCls [((arrItrCls, "a"), arr), ((arrItrCls, "cursor"), .int 0)]) σ
      | "forEach", [_], [f] => if f == .null then thrNPE σ else forEachK P f xs σ
      | "equals", [_], [o] =>
        if o == .ref a then okBool true σ
        else match objAt σ o with
          | some (_, .list _ ys _) => abstractListEqK P xs ys σ
          | some (_, .plain c fs') =>
            if c == asListCls then
              match (Fields.get fs' (c, "a")).bind (objAt σ ·) with
              | some (_, .array _ ys) => abstractListEqK P xs ys σ
              | _ => bad "malformed Arrays.asList"
            else if P.isSubclass c "java.util.List" == some true then bad "equals with this list is not modelled"
            else okBool false σ
          | _ => okBool false σ
      | "toString", [], [] => valueOfObj P (.ref a) σ fun t σ' => okStr t σ'
      | "add", [_], [_] => thr UOE none σ
      | "add", [.prim .int, _], [_, _] => thr UOE none σ
      | "remove", [.prim .int], [_] => thr UOE none σ
      | "remove", [_], [o] => findElemK P false o xs 0 σ fun r σ' =>
          if r.isSome then thr UOE (some "remove") σ' else okBool false σ'
      | "clear", [], [] => if xs.isEmpty then okVoid σ else thr UOE none σ
      | "addAll", [_], [c] => argObj σ c fun _ co => match elemsOf σ co with
          | some [] => okBool false σ
          | some _ => thr UOE none σ
          | none => bad "addAll from this collection kind is not modelled"
      | _, _, _ => bad s!"Arrays.asList: {sig.name} is not modelled"
    | _ => bad "malformed Arrays.asList"
  | none => bad "malformed Arrays.asList"

/-- Iterators of `Arrays.asList` lists: the array read live at the cursor; `remove` is the default
    `Iterator.remove` (UnsupportedOperationException "remove"). -/
def arrItrInst (sig : MethodSig) (a : Addr) (fs : List (FieldKey × Value)) (args : List Value) (σ : State) : NRes :=
  match Fields.get fs (arrItrCls, "a"), Fields.get fs (arrItrCls, "cursor") with
  | some arr, some (.int cur) =>
    match objAt σ arr with
    | some (_, .array _ xs) =>
      match sig.name, args with
      | "hasNext", [] => okBool (cur.toNat < xs.length) σ
      | "next", [] =>
        match xs[cur.toNat]? with
        | some v => ok v (σ.setObj a (.plain arrItrCls (Fields.set fs (arrItrCls, "cursor") (.int (cur + 1)))))
        | none => thr NSEE none σ
      | "remove", [] => thr UOE (some "remove") σ
      | _, _ => bad s!"Arrays.asList iterator: {sig.name} is not modelled"
    | _ => bad "malformed iterator"
  | _, _ => bad "malformed iterator"

def plainInst (P : Program) (sig : MethodSig) (lc : ClassName) (a : Addr) (c : ClassName)
    (fs : List (FieldKey × Value)) (args : List Value) (σ : State) : Option NRes :=
  if c == subListCls && sig.name != "getClass" then some (subListInst P sig fs args σ) else
  if c == streamCls && sig.name != "getClass" then some (streamInst P sig a fs args σ) else
  if c == joinerCls && sig.name != "getClass" then some (joinerInst P sig a fs args σ) else
  if c == emptySetCls && sig.name != "getClass" then some (emptySetInst sig args σ) else
  if c == asListCls && sig.name != "getClass" then some (asListInst P sig a fs args σ) else
  if c == arrItrCls && sig.name != "getClass" then some (arrItrInst sig a fs args σ) else
  let self := Value.ref a
  let isThrowable := P.isSubclass c "java.lang.Throwable" == some true
  let isEnum := P.isSubclass c "java.lang.Enum" == some true
  match sig.name, sig.params, args with
  | "equals", [_], [o] => some (okBool (o == self) σ)
  | "hashCode", [], [] => some (.choose fun h => ok (.int (BitVec.ofNat 32 h)) σ)
  | "toString", [], [] => some (libToString P c fs σ)
  | "getClass", [], [] => some (okObj (.clazz c) σ)
  | "getMessage", [], [] => if isThrowable then some (ok (throwableField fs "detailMessage") σ) else none
  | "getLocalizedMessage", [], [] =>
    if isThrowable then some (ok (throwableField fs "detailMessage") σ) else none
  | "getCause", [], [] =>
    if isThrowable then
      let cv := throwableField fs "cause"
      some (ok (if cv == self then .null else cv) σ)
    else none
  | "initCause", [_], [cause] =>
    if isThrowable then some <|
      if throwableField fs "cause" ≠ self then thr "java.lang.IllegalStateException" (some "Can't overwrite cause") σ
      else if cause == self then thr IAE (some "Self-causation not permitted") σ
      else ok self (σ.setObj a (.plain c (Fields.set fs ("java.lang.Throwable", "cause") cause)))
    else none
  | "printStackTrace", [], [] => if isThrowable then some (okVoid σ) else none
  | "fillInStackTrace", [], [] => if isThrowable then some (ok self σ) else none
  | "addSuppressed", [_], [o] =>
    if isThrowable then some <|
      if o == .null then thrNPE σ
      else if o == self then thr IAE (some "Self-suppression not permitted") σ
      else okVoid σ
    else none
  | "name", [], [] => if isEnum then some (ok ((Fields.get fs ("java.lang.Enum", "name")).getD .null) σ) else none
  | "ordinal", [], [] => if isEnum then some (ok ((Fields.get fs ("java.lang.Enum", "ordinal")).getD (.int 0)) σ) else none
  | "compareTo", [_], [o] =>
    if isEnum then some <| argObj σ o fun _ ob => match ob with
      | .plain c' fs' =>
        if c' ≠ c then bad "Enum.compareTo across enum classes"
        else match Fields.get fs ("java.lang.Enum", "ordinal"), Fields.get fs' ("java.lang.Enum", "ordinal") with
          | some (.int x), some (.int y) => ok (.int (x - y)) σ
          | _, _ => bad "enum ordinal"
      | _ => bad "Enum.compareTo"
    else none
  | _, _, _ =>
    let _ := lc
    none

/-! ### Dispatch: instance methods on library objects -/

/-- Binary class name of a runtime type, as `Class.getName()` prints it. -/
def classNameOf : JType → String
  | .cls c => c
  | .array t => "[" ++ descOf t
  | .prim _ => "?"
  | _ => "?"
where
  descOf : JType → String
    | .prim .boolean => "Z" | .prim .byte => "B" | .prim .char => "C" | .prim .short => "S"
    | .prim .int => "I" | .prim .long => "J" | .prim .float => "F" | .prim .double => "D"
    | .cls c => "L" ++ c ++ ";"
    | .array t => "[" ++ descOf t
    | _ => "?"

/-- The element type name and dimension count of an array class name (`[[I`, `[Lp.C;`). -/
def arrayParts (n : String) : Option (String × Nat) :=
  let cs := n.toList
  let dims := (cs.takeWhile (· == '[')).length
  if dims == 0 then none else
  match cs.drop dims with
  | ['Z'] => some ("boolean", dims) | ['B'] => some ("byte", dims) | ['C'] => some ("char", dims)
  | ['S'] => some ("short", dims) | ['I'] => some ("int", dims) | ['J'] => some ("long", dims)
  | ['F'] => some ("float", dims) | ['D'] => some ("double", dims)
  | 'L' :: rest => if rest.getLast? == some ';' then some (String.ofList rest.dropLast, dims) else none
  | _ => none

def primTypeNames : List String := ["boolean", "byte", "char", "short", "int", "long", "float", "double"]

/-- `getSimpleName()` of a class that is not an array: the part after the package and, for
    nested and local classes, the part after the last `$` without the digits of local and
    anonymous class names. (The JDK reads it from the `InnerClasses` attribute, which Jimple does
    not keep: a nested class whose own name contains `$` comes out shorter.) -/
def simpleNameNonArray (n : String) : String :=
  let afterDot := (n.splitOn ".").getLast?.getD n
  match afterDot.splitOn "$" with
  | [_] => afterDot
  | parts => String.ofList (((parts.getLast?.getD "").toList).dropWhile Char.isDigit)

/-- `Class.getSimpleName()` from a binary class name (arrays: element name and `[]`s). -/
def simpleNameOf (n : String) : String :=
  match arrayParts n with
  | some (e, dims) =>
    (if primTypeNames.contains e then e else simpleNameNonArray e) ++ String.join (List.replicate dims "[]")
  | none => simpleNameNonArray n

/-- `getCanonicalName()` of a class that is not an array: `none` for local and anonymous
    classes (a digit after a `$`), otherwise the binary name with `.` for `$` (same caveat as
    `simpleNameNonArray`). -/
def canonicalNonArray? (n : String) : Option String :=
  if ((n.splitOn "$").drop 1).any (fun seg => (seg.toList.head?.map Char.isDigit).getD true) then none
  else some (n.map fun c => if c == '$' then '.' else c)

/-- `Class.getCanonicalName()` from a binary class name (arrays: element name and `[]`s). -/
def canonicalName? (n : String) : Option String :=
  match arrayParts n with
  | some (e, dims) =>
    (if primTypeNames.contains e then some e else canonicalNonArray? e).map
      (· ++ String.join (List.replicate dims "[]"))
  | none => canonicalNonArray? n

/-- The canonical name, or the binary name if there is none (as JUnit prints classes). -/
def canonicalOrName (n : String) : String := (canonicalName? n).getD n

def instCall (P : Program) (sig : MethodSig) (a : Addr) (o : Obj) (args : List Value)
    (σ : State) : Option NRes :=
  let self := Value.ref a
  if sig.name == "getClass" ∧ args.isEmpty then some (okObj (.clazz (classNameOf o.ty)) σ) else
  match o with
  | .str s => stringInst P sig self s args σ
  | .builder c s => builderInst P sig a c s args σ
  | .boxed c v => boxedInst sig self c v args σ
  | .dec d => decInst sig self d args σ
  | .bigInt i => bigIntInst sig self i args σ
  | .list k xs m => listInst P sig a k xs m args σ
  | .map k kvs m => mapInst P sig a k kvs m args σ
  | .set k xs m => setInst P sig a k xs m args σ
  | .view src part => viewInst sig src part σ args
  | .iter src part ord pos m => iterInst P sig a src part ord pos m args σ
  | .entry src key m => entryInst P sig src key m args σ
  | .rmode r => match sig.name, args with
    | "ordinal", [] => some (okInt r.ordinal σ)
    | "name", [] | "toString", [] => some (okStr (jstr r.name) σ)
    | "equals", [x] => some (okBool (match objAt σ x with | some (_, .rmode r') => r == r' | _ => false) σ)
    | _, _ => none
  | .mctx mc => match sig.name, args with
    | "getPrecision", [] => some (okInt mc.prec σ)
    | "getRoundingMode", [] => some (okObj (.rmode mc.rm) σ)
    | _, _ => none
  | .stream fd => match sig.name, sig.params, args with
    | "println", [], [] => some (okVoid (if fd = 1 then { σ with out := σ.out ++ jstr "\n" } else σ))
    | "println", [t], [v] => some <| valueOfCharsArg P t v σ fun s σ' =>
        okVoid (if fd = 1 then { σ' with out := σ'.out ++ s ++ jstr "\n" } else σ')
    | "print", [t], [v] => some <| valueOfCharsArg P t v σ fun s σ' =>
        okVoid (if fd = 1 then { σ' with out := σ'.out ++ s } else σ')
    | "flush", [], [] => some (okVoid σ)
    | "printf", [_, _], [f, av] | "format", [_, _], [f, av] => some <|
        if f == .null then thrNPE σ else argStr σ f fun fmt => formatK P fmt av σ fun s σ' =>
          ok self (if fd = 1 then { σ' with out := σ'.out ++ s } else σ')
    | _, _, _ => none
  | .array t xs => match sig.name, args with
    | "clone", [] => some (okObj (.array t xs) σ)
    | "equals", [x] => some (okBool (x == self) σ)
    | _, _ => none
  | .plain _ _ => none
  | .clazz n => match sig.name, args with
    | "getName", [] => some (okStr (jstr n) σ)
    | "desiredAssertionStatus", [] => some (okBool false σ)
    | "getSimpleName", [] => some (okStr (jstr (simpleNameOf n)) σ)
    | "getCanonicalName", [] => some (match canonicalName? n with
      | some c => okStr (jstr c) σ
      | none => ok .null σ)
    | "equals", [x] => some (okBool (match objAt σ x with | some (_, .clazz m) => m == n | _ => false) σ)
    | _, _ => none

/-! ### Constructors of library classes (`specialinvoke r.<L: void <init>(..)>`) -/

def ctorCall (P : Program) (sig : MethodSig) (a : Addr) (o : Obj) (args : List Value)
    (σ : State) : Option NRes :=
  let init (o' : Obj) : NRes := okVoid (σ.setObj a o')
  let blank : Bool := match o with
    | .plain c [] => c == sig.cls
    | _ => false
  match sig.cls, sig.params, args with
  | "java.lang.Object", [], [] => some (okVoid σ)
  | "java.lang.Record", [], [] => some (okVoid σ)
  | "java.math.BigDecimal", [.cls "java.lang.String"], [s] =>
    if !blank then none else some <| argStr σ s fun s =>
      if !JStr.isAscii s then bad "non-ASCII numeric text is not modelled" else match BigDec.parse? (JStr.toLean s) with
      | some d => init (.dec d)
      | none => thr NFE none σ
  | "java.math.BigDecimal", [.prim .int], [.int x] => if !blank then none else some (init (.dec ⟨x.toInt, 0⟩))
  | "java.math.BigDecimal", [.prim .long], [.long x] => if !blank then none else some (init (.dec ⟨x.toInt, 0⟩))
  | "java.math.BigDecimal", [.prim .double], [.double x] =>
    if !blank then none else some <| match BigDec.ofDoubleExact x with
      | some d => init (.dec d)
      | none => thr NFE (some "Infinite or NaN") σ
  | "java.math.BigDecimal", [.cls "java.math.BigInteger"], [i] =>
    if !blank then none else some <| argBigInt σ i fun i => init (.dec ⟨i, 0⟩)
  | "java.math.BigDecimal", [.cls "java.math.BigInteger", .prim .int], [i, .int s] =>
    if !blank then none else some <| argBigInt σ i fun i => init (.dec ⟨i, s.toInt⟩)
  | "java.math.BigInteger", [.cls "java.lang.String"], [s] =>
    if !blank then none else some <| argStr σ s fun s =>
      if !JStr.isAscii s then bad "non-ASCII numeric text is not modelled" else
      match parseIntStr s (-(2 ^ 4096 : Nat)) (2 ^ 4096 : Nat) with
      | some i => init (.bigInt i)
      | none => thr NFE none σ
  | "java.math.BigInteger", [.cls "java.lang.String", .prim .int], [s, .int r] =>
    if !blank then none else some <| argStr σ s fun s =>
      if r.toInt < 2 ∨ r.toInt > 36 then thr NFE (some "Radix out of range") σ
      else if !JStr.isAscii s then bad "non-ASCII numeric text is not modelled"
      else match parseRadix? s r.toNat with
        | some i => init (.bigInt i)
        | none => thr NFE none σ
  | "java.math.MathContext", [.prim .int], [.int p] =>
    if !blank then none else some <|
      if p.toInt < 0 then thr IAE (some "Digits < 0") σ else init (.mctx ⟨p.toNat, .HALF_UP⟩)
  | "java.math.MathContext", [.prim .int, _], [.int p, rm] =>
    if !blank then none else some <| argRM σ rm fun rm =>
      if p.toInt < 0 then thr IAE (some "Digits < 0") σ else init (.mctx ⟨p.toNat, rm⟩)
  | "java.lang.String", [], [] => if !blank then none else some (init (.str []))
  | "java.lang.String", [.cls "java.lang.String"], [s] =>
    if !blank then none else some <| argStr σ s fun s => init (.str s)
  | "java.lang.String", [.array (.prim .char)], [arr] =>
    if !blank then none else some <| argObj σ arr fun _ o => match o with
      | .array _ cs => init (.str (charsOf cs))
      | _ => bad "expected char[]"
  | "java.lang.String", [.array (.prim .char), .prim .int, .prim .int], [arr, .int off, .int cnt] =>
    if !blank then none else some <| argObj σ arr fun _ o => match o with
      | .array _ cs =>
        if off.toInt < 0 ∨ cnt.toInt < 0 ∨ off.toInt > cs.length - cnt.toInt then
          thr "java.lang.StringIndexOutOfBoundsException"
            (some s!"offset {off.toInt}, count {cnt.toInt}, length {cs.length}") σ
        else init (.str (charsOf ((cs.drop off.toNat).take cnt.toNat)))
      | _ => bad "expected char[]"
  | "java.lang.String", [.array (.prim .int), .prim .int, .prim .int], [arr, .int off, .int cnt] =>
    if !blank then none else some <| argObj σ arr fun _ o => match o with
      | .array _ cps =>
        if off.toInt < 0 ∨ cnt.toInt < 0 ∨ off.toInt > cps.length - cnt.toInt then
          thr "java.lang.StringIndexOutOfBoundsException"
            (some s!"offset {off.toInt}, count {cnt.toInt}, length {cps.length}") σ
        else
          let sel := (cps.drop off.toNat).take cnt.toNat
          match sel.find? (fun v => match v with | .int c => c.toInt < 0 ∨ c.toInt > 0x10FFFF | _ => true) with
          | some (.int c) => thr IAE (some s!"{c.toInt}") σ
          | some _ => bad "expected int[]"
          | none => init (.str (sel.map (fun v => match v with
              | .int c =>
                if c.toInt < 0x10000 then [c.setWidth 16]
                else
                  let w := c.toNat - 0x10000
                  [BitVec.ofNat 16 (0xD800 + w / 1024), BitVec.ofNat 16 (0xDC00 + w % 1024)]
              | _ => [])).flatten)
      | _ => bad "expected int[]"
  | "java.lang.StringBuilder", ps, args' | "java.lang.StringBuffer", ps, args' =>
    if !blank then none else match ps, args' with
      | [], [] => some (init (.builder sig.cls []))
      | [.prim .int], [.int n] => some <|
          if n.toInt < 0 then thr "java.lang.NegativeArraySizeException" none σ else init (.builder sig.cls [])
      | [.cls _], [s] => some <| argChars σ s fun s => init (.builder sig.cls s)
      | _, _ => none
  | "java.util.ArrayList", ps, args' | "java.util.LinkedList", ps, args' =>
    let k := if sig.cls == "java.util.ArrayList" then ListKind.arrayList else .linkedList
    if !blank then none else match ps, args' with
      | [], [] => some (init (.list k [] 0))
      | [.prim .int], [.int n] => some <|
          if n.toInt < 0 then thr IAE (some s!"Illegal Capacity: {n.toInt}") σ else init (.list k [] 0)
      | [.cls _], [c] => some <| argObj σ c fun _ co => match elemsOf σ co with
          | some xs => init (.list k xs 0)
          | none => bad "copy constructor from this collection kind is not modelled"
      | _, _ => none
  | "java.util.HashMap", ps, _ | "java.util.LinkedHashMap", ps, _ | "java.util.TreeMap", ps, _ =>
    let k := if sig.cls == "java.util.HashMap" then MapKind.hash
      else if sig.cls == "java.util.LinkedHashMap" then .linked else .tree
    if !blank then none else match ps with
      | [] => some (init (.map k [] 0))
      | [.prim .int] => some (init (.map k [] 0))
      | _ => none
  | "java.util.HashSet", ps, args' | "java.util.LinkedHashSet", ps, args' | "java.util.TreeSet", ps, args' =>
    let k := if sig.cls == "java.util.HashSet" then SetKind.hash
      else if sig.cls == "java.util.LinkedHashSet" then .linked else .tree
    if !blank then none else match ps, args' with
      | [], [] => some (init (.set k [] 0))
      | [.prim .int], [_] => some (init (.set k [] 0))
      | [.cls "java.util.Collection"], [c] => some <| argObj σ c fun _ co => match elemsOf σ co with
          | some vs =>
            if k == .tree ∧ vs.any (· == .null) then thrNPE σ
            else match setAddAll? P σ k [] vs with
              | some (ys, _) => init (.set k ys 0)
              | none => setAddAllK P k vs ([], false) σ fun r σ' => okVoid (σ'.setObj a (.set k r.1 0))
          | none => bad "copy constructor from this collection kind is not modelled"
      | [.cls "java.util.SortedSet"], [c] =>
        -- `TreeSet(SortedSet)` copies the (naturally ordered) elements without comparing them
        if k != .tree then none else some <| argObj σ c fun _ co => match co with
          | .set .tree xs _ => init (.set .tree xs 0)
          | .view src .keys => match σ.heap src with
            | some (.map .tree kvs _) => init (.set .tree (kvs.map (·.1)) 0)
            | _ => bad "TreeSet(SortedSet) from this collection kind is not modelled"
          | _ => bad "TreeSet(SortedSet) from this collection kind is not modelled"
      | _, _ => none
  | "java.lang.AssertionError", [.cls "java.lang.Object"], [m] => match o with
    | .plain c fs => some <| valueOfObj P m σ fun s σ' =>
        let (mv, σ'') := allocStr s σ'
        let cause := match objAt σ'' m with
          | some (_, .plain mc _) => if P.isSubclass mc "java.lang.Throwable" == some true then m else .ref a
          | _ => .ref a
        okVoid (σ''.setObj a (.plain c (Fields.set (Fields.set fs ("java.lang.Throwable", "detailMessage") mv)
                                         ("java.lang.Throwable", "cause") cause)))
    | _ => none
  | "java.util.StringJoiner", ps, args' =>
    if !blank then none else
    let initJ (pt dt st : JStr) : NRes :=
      let (pv, σ1) := allocStr pt σ
      let (dv, σ2) := allocStr dt σ1
      let (sv, σ3) := allocStr st σ2
      okVoid (σ3.setObj a (.plain joinerCls [((joinerCls, "prefix"), pv), ((joinerCls, "delimiter"), dv),
        ((joinerCls, "suffix"), sv), ((joinerCls, "parts"), .null), ((joinerCls, "emptyValue"), .null)]))
    let npe (what : String) : NRes := thr "java.lang.NullPointerException" (some s!"The {what} must not be null") σ
    match ps, args' with
    | [.cls _], [d] => some <| if d == .null then npe "delimiter" else argChars σ d fun dt => initJ [] dt []
    | [.cls _, .cls _, .cls _], [d, p, sf] => some <|
      if p == .null then npe "prefix" else if d == .null then npe "delimiter" else if sf == .null then npe "suffix"
      else argChars σ p fun pt => argChars σ d fun dt => argChars σ sf fun st => initJ pt dt st
    | _, _ => none
  | "java.lang.Enum", [_, _], [nm, ord] => match o with
    | .plain c fs => some (init (.plain c (Fields.set (Fields.set fs ("java.lang.Enum", "name") nm)
                                              ("java.lang.Enum", "ordinal") ord)))
    | _ => none
  | lc, ps, args' =>
    -- constructors of library exception classes (also reached via `super(...)`)
    if P.isSubclass lc "java.lang.Throwable" == some true ∧ isLibClass lc then
      match o with
      | .plain c fs =>
        let setF (msg cause : Value) : NRes :=
          init (.plain c (Fields.set (Fields.set fs ("java.lang.Throwable", "detailMessage") msg)
                            ("java.lang.Throwable", "cause") cause))
        match ps, args' with
        | [], [] => some (setF .null (.ref a))
        | [.cls "java.lang.String"], [m] => some (setF m (.ref a))
        | [.cls "java.lang.String", .cls _], [m, cause] => some (setF m cause)
        | [.cls "java.lang.String", .cls _, .prim .boolean, .prim .boolean], [m, cause, _, _] =>
          some (setF m cause)
        | [.cls _], [cause] => some <|
            if cause == .null then setF .null .null
            else valueOfObj P cause σ fun s σ' =>
              let (mv, σ'') := allocStr s σ'
              okVoid (σ''.setObj a (.plain c (Fields.set (Fields.set fs ("java.lang.Throwable", "detailMessage") mv)
                                     ("java.lang.Throwable", "cause") cause)))
        | _, _ => none
      | _ => none
    else none

/-! ### JUnit assertions -/

/-- Throw a new library exception of class `cls` with message `msg` (`none`: `null`) and cause
    `cause` (`none`: not initialized, so `getCause()` is `null` and `initCause` still works). -/
def thrWith (cls : ClassName) (msg : Option JStr) (cause : Option Value) (σ : State) : NRes :=
  let (mv, σ) := match msg with
    | none => (Value.null, σ)
    | some s => allocStr s σ
  let (e, σ) := σ.alloc (.plain cls [(("java.lang.Throwable", "detailMessage"), mv),
                                     (("java.lang.Throwable", "cause"), .null)])
  let σ := σ.setObj e (.plain cls [(("java.lang.Throwable", "detailMessage"), mv),
                                   (("java.lang.Throwable", "cause"), cause.getD (.ref e))])
  .ret (.thr e σ)

/-- `String.trim().isEmpty()`: only characters up to U+0020. -/
def isBlankJ (s : JStr) : Bool := s.all (·.toNat ≤ 32)

def AFE := "org.opentest4j.AssertionFailedError"

/-- Throw an `org.opentest4j.AssertionFailedError`, whose constructor replaces a `null` or blank
    message by `""`. -/
def afeThrow (msg : Option JStr) (cause : Option Value) (σ : State) : NRes :=
  thrWith AFE (some (match msg with
    | some s => if isBlankJ s then [] else s
    | none => [])) cause σ

def supplierGetSig : MethodSig := ⟨"java.util.function.Supplier", .cls "java.lang.Object", "get", []⟩
def executeSig : MethodSig := ⟨"org.junit.jupiter.api.function.Executable", .void, "execute", []⟩
def runnableRunSig : MethodSig := ⟨"org.junit.function.ThrowingRunnable", .void, "run", []⟩

/-- A call of `sig` (no arguments) on an application object, continued with its result;
    exceptions propagate. -/
def callAppK (P : Program) (sig : MethodSig) (x : Value) (σ : State)
    (k : Option Value → State → NRes) : NRes :=
  match objAt σ x with
  | some (_, .plain c _) =>
    if P.isProgClass c then
      .call sig (.virtual c) [x] σ fun out => match out with
        | .normal r σ' => k r σ'
        | .exc e σ' => .ret (.thr e σ')
        | .wrong msg => bad msg
    else bad s!"{sig.name} of a library object is not modelled"
  | _ => if x == .null then thrNPE σ else bad s!"{sig.name} of this object kind is not modelled"

/-- The binary class name of the object `v` refers to (`getClass().getName()`). -/
def classNameOfVal (σ : State) (v : Value) : Option String :=
  (objAt σ v).map fun (_, o) => classNameOf o.ty

/-- A hexadecimal identity hash code (any value). -/
def anyHashK (k : JStr → NRes) : NRes :=
  .choose fun h => k (jstr (String.ofList (Nat.toDigits 16 (h % 2 ^ 32))))

/-- `x.equals(y)` for the assertion models: `equalsK`, with lists compared by their `equals`
    model. -/
def jEqualsK (P : Program) (idFirst : Bool) (σ : State) (x y : Value) (k : Bool → State → NRes) :
    NRes :=
  match objAt σ x with
  | some (a, o@(.list ..)) =>
    if idFirst && x == y then k true σ
    else match instCall P equalsSig a o [y] σ with
      | some r => r.bind fun ev => match ev with
        | .ok (.int b) σ' => k (b ≠ 0) σ'
        | .ok _ _ => bad "equals returned no boolean"
        | .thr e σ' => .ret (.thr e σ')
        | .wrong m => bad m
      | none => bad "equals of this list is not modelled"
  | some (a, .plain c fs) =>
    if c == asListCls then
      if idFirst && x == y then k true σ
      else (asListInst P equalsSig a fs [y] σ).bind fun ev => match ev with
        | .ok (.int b) σ' => k (b ≠ 0) σ'
        | .ok _ _ => bad "equals returned no boolean"
        | .thr e σ' => .ret (.thr e σ')
        | .wrong m => bad m
    else equalsK P idFirst σ x y k
  | _ => equalsK P idFirst σ x y k

/-- `Arrays.toString` of a primitive array (`none` for floating-point elements). -/
def primArrStr? (t : JType) (xs : List Value) : Option JStr :=
  (xs.mapM (primStr t)).map fun ss => jstr "[" ++ (ss.intersperse (jstr ", ")).flatten ++ jstr "]"

/-- `Arrays.toString` (primitive arrays) and `Arrays.deepToString` (reference arrays: nested
    arrays recursively, `[...]` for an array inside itself, other elements by `toString()`). -/
def deepStrK (P : Program) : Nat → List Addr → Addr → State → (JStr → State → NRes) → NRes
  | 0, _, _, _, _ => bad "array nesting too deep"
  | n + 1, seen, a, σ, k =>
    match σ.heap a with
    | some (.array t xs) =>
      if t.isRef then
        let elem (v : Value) (σ : State) (k' : JStr → State → NRes) : NRes :=
          match v with
          | .ref b =>
            match σ.heap b with
            | some (.array _ _) =>
              if b == a || seen.contains b then k' (jstr "[...]") σ else deepStrK P n (a :: seen) b σ k'
            | _ => valueOfObj P v σ k'
          | _ => valueOfObj P v σ k'
        joinWith elem xs σ fun s σ' => k (jstr "[" ++ s ++ jstr "]") σ'
      else match primArrStr? t xs with
        | some s => k s σ
        | none => bad "floating-point to string conversion is not modelled"
    | _ => bad "expected an array"

/-- `StringUtils.nullSafeToString` (JUnit 5): `"null"` for `null`, otherwise `toString()`
    (`"null"` if that returns `null`); an exception thrown by `toString()` is swallowed and the
    default `Class@hash` rendering used instead (`OutOfMemoryError` propagates). Arrays are
    rendered by `Arrays.toString`/`Arrays.deepToString`. -/
def nullSafeStrK (P : Program) (v : Value) (σ : State) (k : JStr → State → NRes) : NRes :=
  let render : NRes := match objAt σ v with
    | some (a, .array ..) => deepStrK P 64 [] a σ fun s σ' => okStr s σ'
    | _ => valueOfObj P v σ fun s σ' => okStr s σ'
  render.bind fun r => match r with
    | .ok sv σ' => match strOf σ' sv with
      | some s => k s σ'
      | none => bad "toString returned a non-string"
    | .thr e σ' =>
      let ec := match σ'.heap e with | some (.plain c _) => c | _ => ""
      if P.isSubclass ec "java.lang.OutOfMemoryError" == some true then .ret (.thr e σ')
      else match classNameOfVal σ' v with
        | some c => anyHashK fun h => k (jstr c ++ jstr "@" ++ h) σ'
        | none => bad "toString of a non-object"
    | .wrong m => bad m

/-- `AssertionFailureBuilder.toString`: classes by canonical name, other values by
    `nullSafeToString`. -/
def j5StrK (P : Program) (v : Value) (σ : State) (k : JStr → State → NRes) : NRes :=
  match objAt σ v with
  | some (_, .clazz n) => k (jstr (canonicalOrName n)) σ
  | _ => nullSafeStrK P v σ k

/-- `AssertionFailureBuilder.formatClassAndValue` (with any identity hash code). -/
def j5ClassAndValueK (σ : State) (v : Value) (s : JStr) (k : JStr → NRes) : NRes :=
  match objAt σ v with
  | none => k (jstr "<null>")
  | some (_, .clazz n) => anyHashK fun h => k (jstr "<" ++ jstr (canonicalOrName n) ++ jstr "@" ++ h ++ jstr ">")
  | some (_, o) => anyHashK fun h => k (jstr (classNameOf o.ty) ++ jstr "@" ++ h ++ jstr "<" ++ s ++ jstr ">")

/-- `AssertionFailureBuilder.formatValues`: `expected: <e> but was: <a>`; if both render alike,
    with class names and identity hash codes. -/
def j5ValuesK (P : Program) (e a : Value) (σ : State) (k : JStr → State → NRes) : NRes :=
  j5StrK P e σ fun es σ1 => j5StrK P a σ1 fun as σ2 =>
    if es == as then
      j5ClassAndValueK σ2 e es fun ce => j5ClassAndValueK σ2 a as fun ca =>
        k (jstr "expected: " ++ ce ++ jstr " but was: " ++ ca) σ2
    else k (jstr "expected: <" ++ es ++ jstr "> but was: <" ++ as ++ jstr ">") σ2

/-- The message argument of a JUnit 5 assertion (`AssertionFailureBuilder.nullSafeGet`): absent,
    a `String` (or `null`), or a `Supplier` whose `get()` result is rendered by
    `nullSafeToString`. -/
def j5MsgK (P : Program) (t : Option JType) (m : Value) (σ : State)
    (k : Option JStr → State → NRes) : NRes :=
  match t with
  | none => k none σ
  | some (.cls "java.util.function.Supplier") =>
    if m == .null then k none σ
    else callAppK P supplierGetSig m σ fun r σ' => nullSafeStrK P (r.getD .null) σ' fun s σ'' => k (some s) σ''
  | some _ =>
    if m == .null then k none σ
    else match strOf σ m with
      | some s => k (some s) σ
      | none => bad "expected String"

/-- `AssertionFailureBuilder.buildPrefix`: a non-blank message and `" ==> "`. -/
def j5Prefix (m : Option JStr) : JStr :=
  match m with
  | some s => if isBlankJ s then [] else s ++ jstr " ==> "
  | none => []

def boxClassOf : PrimType → ClassName
  | .boolean => "java.lang.Boolean" | .byte => "java.lang.Byte" | .char => "java.lang.Character"
  | .short => "java.lang.Short" | .int => "java.lang.Integer" | .long => "java.lang.Long"
  | .float => "java.lang.Float" | .double => "java.lang.Double"

/-- Autoboxing of a value of static type `t`. -/
def boxIfPrim (t : JType) (v : Value) (σ : State) : Value × State :=
  match t with
  | .prim p => let (a, σ') := σ.alloc (.boxed (boxClassOf p) v); (.ref a, σ')
  | _ => (v, σ)

/-- `assertThrows`: run the executable (`execute()`, or `run()` for JUnit 4) and return what it
    throws if that is an instance of the expected class; `mismatch e σ` and `none σ` build the
    failures. A `null` executable throws `NullPointerException` inside the `try`. -/
def throwsK (P : Program) (callSig : MethodSig) (c x : Value) (σ : State)
    (mismatch : String → String → Addr → State → NRes) (nothing : String → State → NRes) : NRes :=
  match objAt σ c with
  | some (_, .clazz en) =>
    let caught (e : Addr) (σ' : State) : NRes :=
      match σ'.heap e with
      | some (.plain ec _) =>
        match P.isSubclass ec en with
        | some true => ok (.ref e) σ'
        | some false =>
          if P.isSubclass ec "java.lang.OutOfMemoryError" == some true then .ret (.thr e σ')
          else mismatch en ec e σ'
        | none => bad "exception of an unknown class"
      | _ => bad "thrown value is not an exception object"
    if x == .null then
      let (e, σ') := mkExc "java.lang.NullPointerException" none σ
      caught e σ'
    else match objAt σ x with
      | some (_, .plain xc _) =>
        if P.isProgClass xc then
          .call callSig (.virtual xc) [x] σ fun out => match out with
            | .normal _ σ' => nothing en σ'
            | .exc e σ' => caught e σ'
            | .wrong msg => bad msg
        else bad "assertThrows with a library executable is not modelled"
      | _ => bad "assertThrows with this executable kind is not modelled"
  | _ => bad "assertThrows: the expected type is not a class object"

/-- `AssertionUtils.formatIndexes`: ` at index [i][j]`, or nothing. -/
def fmtIndexes (idx : List Nat) : JStr :=
  if idx.isEmpty then [] else jstr " at index " ++ (idx.map fun i => jstr s!"[{i}]").flatten

/-- The kind of an array value: `some none` for arrays of references, `some (some p)` for arrays
    of primitives `p`, `none` for other values. -/
def arrKind (σ : State) (v : Value) : Option (Option PrimType) :=
  match objAt σ v with
  | some (_, .array (.prim p) _) => some (some p)
  | some (_, .array _ _) => some none
  | _ => none

mutual
/-- `AssertArrayEquals.assertArrayEquals` (JUnit 5.10) on arrays `e`, `a` of one kind (or `null`)
    at the index path `idx`: `k` if they are equal, otherwise `fail reason`. -/
def j5ArrEqK (P : Program) (fail : JStr → State → NRes) :
    Nat → List Nat → Value → Value → State → (State → NRes) → NRes
  | 0, _, _, _, _, _ => bad "array comparison too deep"
  | n + 1, idx, e, a, σ, k =>
    if e == a then k σ
    else if e == .null then fail (jstr "expected array was <null>" ++ fmtIndexes idx) σ
    else if a == .null then fail (jstr "actual array was <null>" ++ fmtIndexes idx) σ
    else match objAt σ e, objAt σ a with
      | some (_, .array te xs), some (_, .array _ ys) =>
        if xs.length != ys.length then
          fail (jstr "array lengths differ" ++ fmtIndexes idx ++ jstr ", expected: <" ++
            JStr.ofInt xs.length ++ jstr "> but was: <" ++ JStr.ofInt ys.length ++ jstr ">") σ
        else if te.isRef then j5ElemsK P fail n idx 0 (xs.zip ys) σ k
        else match ((List.range xs.length).zip (xs.zip ys)).find? (fun (_, x, y) => canonBits x != canonBits y) with
          | none => k σ
          | some (i, x, y) => match primStr te x, primStr te y with
            | some xs', some ys' => fail (jstr "array contents differ" ++ fmtIndexes (idx ++ [i]) ++
                jstr ", expected: <" ++ xs' ++ jstr "> but was: <" ++ ys' ++ jstr ">") σ
            | _, _ => bad "floating-point to string conversion is not modelled"
      | _, _ => bad "expected arrays"

/-- The elements of two reference arrays of equal length (`assertArrayElementsEqual`): nested
    arrays of one kind recursively, other pairs by `Objects.equals`. -/
def j5ElemsK (P : Program) (fail : JStr → State → NRes) :
    Nat → List Nat → Nat → List (Value × Value) → State → (State → NRes) → NRes
  | 0, _, _, _, _, _ => bad "array comparison too deep"
  | _ + 1, _, _, [], σ, k => k σ
  | n + 1, idx, i, (x, y) :: rest, σ, k =>
    let next (σ' : State) : NRes := j5ElemsK P fail n idx (i + 1) rest σ' k
    let idx' := idx ++ [i]
    let differ (σ : State) : NRes :=
      jEqualsK P true σ x y fun b σ' =>
        if b then next σ'
        else if x == .null && (arrKind σ' y).isSome then
          fail (jstr "expected array was <null>" ++ fmtIndexes idx') σ'
        else if (arrKind σ' x).isSome && y == .null then
          fail (jstr "actual array was <null>" ++ fmtIndexes idx') σ'
        else j5ValuesK P x y σ' fun vs σ'' =>
          fail (jstr "array contents differ" ++ fmtIndexes idx' ++ jstr ", " ++ vs) σ''
    if x == y then next σ
    else match arrKind σ x, arrKind σ y with
      | some kx, some ky => if kx == ky then j5ArrEqK P fail n idx' x y σ next else differ σ
      | _, _ => differ σ
end

/-- `org.junit.jupiter.api.Assertions.fail` (JUnit 5.10). -/
def jupiterFail (P : Program) (ps : List JType) (args : List Value) (σ : State) : Option NRes :=
  match ps, args with
  | [], [] => some (afeThrow none none σ)
  | [.cls "java.lang.String"], [m] => some (afeThrow (strOf σ m) none σ)
  | [.cls "java.lang.String", .cls "java.lang.Throwable"], [m, c] => some (afeThrow (strOf σ m) (some c) σ)
  | [.cls "java.lang.Throwable"], [c] => some (afeThrow none (some c) σ)
  | [.cls "java.util.function.Supplier"], [sup] => some <|
    if sup == .null then afeThrow none none σ
    else callAppK P supplierGetSig sup σ fun r σ' => match r with
      | some .null | none => afeThrow none none σ'
      | some v => match strOf σ' v with
        | some s => afeThrow (some s) none σ'
        | none => thr "java.lang.ClassCastException" none σ'
  | _, _ => none

/-- `org.junit.jupiter.api.Assertions` (JUnit 5.10): `assertTrue`/`assertFalse`, `assertNull`/
    `assertNotNull`, `assertSame`/`assertNotSame`, `assertEquals` (primitives; boxed and `Object`
    values by `equals`, with application `equals` called back), `assertThrows` (calling back
    `execute()`) and `fail`, each with an optional trailing `String` or `Supplier<String>`
    message. Failures throw `org.opentest4j.AssertionFailedError` with JUnit's messages
    (`msg ==> expected: <e> but was: <a>`); floating-point values in messages are not modelled. -/
def jupiterAssert (P : Program) (name : String) (ps : List JType) (args : List Value) (σ : State) :
    Option NRes :=
  if name == "fail" then jupiterFail P ps args σ else
  let (core, msgT, msgV) : List JType × Option JType × Value :=
    match ps.reverse, args.reverse with
    | .cls "java.lang.String" :: ps', m :: _ => (ps'.reverse, some (.cls "java.lang.String"), m)
    | .cls "java.util.function.Supplier" :: ps', m :: _ =>
      (ps'.reverse, some (.cls "java.util.function.Supplier"), m)
    | _, _ => (ps, none, .null)
  let cargs := if msgT.isSome then args.dropLast else args
  -- the message is computed after the values, as `AssertionFailureBuilder.build` does
  let failWith (reason : JStr) (σ : State) : NRes :=
    j5MsgK P msgT msgV σ fun m σ' => afeThrow (some (j5Prefix m ++ reason)) (some .null) σ'
  match name, core, cargs with
  | "assertTrue", [.prim .boolean], [.int b] =>
    some (if b ≠ 0 then okVoid σ else failWith (jstr "expected: <true> but was: <false>") σ)
  | "assertFalse", [.prim .boolean], [.int b] =>
    some (if b = 0 then okVoid σ else failWith (jstr "expected: <false> but was: <true>") σ)
  | "assertNull", [.cls "java.lang.Object"], [a] =>
    some (if a == .null then okVoid σ else j5ValuesK P .null a σ failWith)
  | "assertNotNull", [.cls "java.lang.Object"], [a] =>
    some (if a != .null then okVoid σ else failWith (jstr "expected: not <null>") σ)
  | "assertSame", [.cls "java.lang.Object", .cls "java.lang.Object"], [e, a] =>
    some (if e == a then okVoid σ else j5ValuesK P e a σ failWith)
  | "assertNotSame", [.cls "java.lang.Object", .cls "java.lang.Object"], [u, a] =>
    some (if u != a then okVoid σ else valueOfObj P a σ fun s σ' =>
      failWith (jstr "expected: not same but was: <" ++ s ++ jstr ">") σ')
  | "assertEquals", [.prim p, .prim q], [e, a] =>
    if p != q then none else some <|
      if canonBits e == canonBits a then okVoid σ
      else match primStr (.prim p) e, primStr (.prim q) a with
        | some es, some as => failWith (jstr "expected: <" ++ es ++ jstr "> but was: <" ++ as ++ jstr ">") σ
        | _, _ => bad "floating-point to string conversion is not modelled"
  | "assertEquals", [t1, t2], [e, a] =>
    -- boxed and `Object` overloads: `AssertionUtils.objectsAreEqual` on the boxed values
    let (e', σ1) := boxIfPrim t1 e σ
    let (a', σ2) := boxIfPrim t2 a σ1
    some <| jEqualsK P false σ2 e' a' fun b σ3 => if b then okVoid σ3 else j5ValuesK P e' a' σ3 failWith
  | "assertNotEquals", [.prim p, .prim q], [u, a] =>
    if p != q then none else some <|
      if canonBits u != canonBits a then okVoid σ
      else match primStr (.prim q) a with
        | some as => failWith (jstr "expected: not equal but was: <" ++ as ++ jstr ">") σ
        | none => bad "floating-point to string conversion is not modelled"
  | "assertNotEquals", [t1, t2], [u, a] =>
    let (u', σ1) := boxIfPrim t1 u σ
    let (a', σ2) := boxIfPrim t2 a σ1
    some <| jEqualsK P false σ2 u' a' fun b σ3 =>
      if !b then okVoid σ3
      else valueOfObj P a' σ3 fun s σ4 => failWith (jstr "expected: not equal but was: <" ++ s ++ jstr ">") σ4
  | "assertArrayEquals", [.array t1, .array t2], [e, a] =>
    if t1 != t2 then none else some (j5ArrEqK P failWith 1000000 [] e a σ okVoid)
  | "assertThrows", [.cls "java.lang.Class", .cls "org.junit.jupiter.api.function.Executable"], [c, x] =>
    some <| throwsK P executeSig c x σ
      (fun en ec e σ' => j5MsgK P msgT msgV σ' fun m σ'' =>
        afeThrow (some (j5Prefix m ++ jstr "Unexpected exception type thrown, expected: <" ++
          jstr (canonicalOrName en) ++ jstr "> but was: <" ++ jstr (canonicalOrName ec) ++ jstr ">"))
          (some (.ref e)) σ'')
      (fun en σ' => j5MsgK P msgT msgV σ' fun m σ'' =>
        afeThrow (some (j5Prefix m ++ jstr "Expected " ++ jstr (canonicalOrName en) ++
          jstr " to be thrown, but nothing was thrown.")) (some .null) σ'')
  | _, _, _ => none

/-- `ComparisonFailure.getMessage()` (JUnit 4.13): the strings with their common prefix and
    suffix (beyond 20 characters elided by `...`) around the differing parts in brackets,
    formatted by `Assert.format`. -/
def compact4 (msg : JStr) (e a : JStr) : JStr :=
  let rec commonPre : JStr → JStr → Nat
    | x :: xs, y :: ys => if x == y then commonPre xs ys + 1 else 0
    | _, _ => 0
  let pre := commonPre e a
  let suf := min (commonPre e.reverse a.reverse) (min (e.length - pre) (a.length - pre))
  let cpre := if pre ≤ 20 then e.take pre else jstr "..." ++ (e.take pre).drop (pre - 20)
  let sharedSuf := e.drop (e.length - suf)
  let csuf := if suf ≤ 20 then sharedSuf else sharedSuf.take 20 ++ jstr "..."
  let diff (s : JStr) : JStr := jstr "[" ++ (s.drop pre).take (s.length - pre - suf) ++ jstr "]"
  let es := cpre ++ diff e ++ csuf
  let as := cpre ++ diff a ++ csuf
  let pfx := if msg.isEmpty then [] else msg ++ jstr " "
  if es == as then
    pfx ++ jstr "expected: java.lang.String<" ++ es ++ jstr "> but was: java.lang.String<" ++ as ++ jstr ">"
  else pfx ++ jstr "expected:<" ++ es ++ jstr "> but was:<" ++ as ++ jstr ">"

/-- `Assert.format` (JUnit 4.13) of two values: `expected:<e> but was:<a>` (renderings by
    `String.valueOf`); if both render alike, with their class names. -/
def format4K (P : Program) (msg : Option JStr) (e a : Value) (σ : State) (k : JStr → State → NRes) :
    NRes :=
  let pfx := match msg with | some s => if s.isEmpty then [] else s ++ jstr " " | none => []
  let cls (v : Value) (σ : State) : JStr := jstr ((classNameOfVal σ v).getD "null")
  valueOfObj P e σ fun es σ1 => valueOfObj P a σ1 fun as σ2 =>
    if es == as then
      k (pfx ++ jstr "expected: " ++ cls e σ2 ++ jstr "<" ++ es ++ jstr "> but was: " ++ cls a σ2 ++
        jstr "<" ++ as ++ jstr ">") σ2
    else k (pfx ++ jstr "expected:<" ++ es ++ jstr "> but was:<" ++ as ++ jstr ">") σ2

mutual
/-- `Arrays.deepEquals0(e1, e2)` for `e1 ≠ null`, elements' `equals` called back. -/
def deepEq0K (P : Program) : Nat → Value → Value → State → (Bool → State → NRes) → NRes
  | 0, _, _, _, _ => bad "array comparison too deep"
  | n + 1, e1, e2, σ, k =>
    match objAt σ e1, objAt σ e2 with
    | some (_, .array t1 xs), some (_, .array t2 ys) =>
      if t1.isRef && t2.isRef then
        if xs.length != ys.length then k false σ else deepEqElemsK P n (xs.zip ys) σ k
      else if t1 == t2 then
        k (xs.length == ys.length && (xs.zip ys).all fun (x, y) => canonBits x == canonBits y) σ
      else jEqualsK P false σ e1 e2 k
    | _, _ => jEqualsK P false σ e1 e2 k

/-- The element loop of `Arrays.deepEquals(Object[], Object[])`. -/
def deepEqElemsK (P : Program) : Nat → List (Value × Value) → State → (Bool → State → NRes) → NRes
  | 0, _, _, _ => bad "array comparison too deep"
  | _ + 1, [], σ, k => k true σ
  | n + 1, (x, y) :: rest, σ, k =>
    if x == y then deepEqElemsK P n rest σ k
    else if x == .null then k false σ
    else deepEq0K P n x y σ fun b σ' => if b then deepEqElemsK P n rest σ' k else k false σ'
end

/-- Outcome of JUnit 4's `ComparisonCriteria.arrayEquals`: equal; `Assert.fail(msg)`; or an
    `ArrayComparisonFailure` with its header, index path and the class and message of its cause. -/
inductive Arr4 where
  | equal
  | fail (msg : JStr)
  | acf (header : JStr) (idx : List Nat) (causeCls : ClassName) (causeMsg : JStr)

/-- JUnit's anonymous class of the "end of array" sentinel and of nested-array placeholders. -/
def junitAnonCls : ClassName := "org.junit.internal.ComparisonCriteria$1"

def primTypeName : PrimType → String
  | .boolean => "boolean" | .byte => "byte" | .char => "char" | .short => "short"
  | .int => "int" | .long => "long" | .float => "float" | .double => "double"

/-- `ComparisonCriteria.componentTypeName` of an array whose elements have type `t`. -/
def componentName : JType → String
  | .array t => componentName t ++ "[]"
  | .prim p => primTypeName p
  | .cls c => c
  | _ => "?"

/-- The end of JUnit 4's `arrayEquals` when the lengths differ and the common prefix is equal:
    `assertEquals` of `getToStringableArrayElement` of both arrays at index `i`, an element or the
    "end of array" sentinel (nested arrays as `T[n]`). An application `equals` called with the
    sentinel gets a plain `java.lang.Object` (JUnit's is an object of an anonymous class). -/
def arr4TailK (P : Program) (header : JStr) (te : JType) (xs ys : List Value) (i : Nat) (σ : State)
    (k : Arr4 → State → NRes) : NRes :=
  -- rendering and class name of one side
  let side (zs : List Value) (σ : State) (k' : JStr → JStr → State → NRes) : NRes :=
    match zs[i]? with
    | none => k' (jstr "end of array") (jstr junitAnonCls) σ
    | some v =>
      match te with
      | .prim p => match primStr te v with
        | some s => k' s (jstr (boxClassOf p)) σ
        | none => bad "floating-point to string conversion is not modelled"
      | _ => match objAt σ v with
        | some (_, .array et zs') =>
          k' (jstr (componentName et) ++ jstr "[" ++ JStr.ofInt zs'.length ++ jstr "]") (jstr junitAnonCls) σ
        | _ => valueOfObj P v σ fun s σ' => k' s (jstr ((classNameOfVal σ' v).getD "null")) σ'
  let report (σ : State) : NRes :=
    side xs σ fun es ec σ1 => side ys σ1 fun as ac σ2 =>
      k (.acf header [i] "java.lang.AssertionError"
        (if es == as then jstr "expected: " ++ ec ++ jstr "<" ++ es ++ jstr "> but was: " ++ ac ++
           jstr "<" ++ as ++ jstr ">"
         else jstr "expected:<" ++ es ++ jstr "> but was:<" ++ as ++ jstr ">")) σ2
  -- only an element of the longer expected array, compared with the sentinel, can call back
  match xs[i]?, ys[i]? with
  | some v, none =>
    if te.isRef && v != .null && (arrKind σ v).isNone then
      let (s, σ1) := σ.alloc (.plain "java.lang.Object" [])
      jEqualsK P false σ1 v (.ref s) fun b σ2 => if b then k .equal σ2 else report σ2
    else report σ
  | _, _ => report σ

mutual
/-- `ComparisonCriteria.arrayEquals(message, e, a, outer)` with `ExactComparisonCriteria`
    (JUnit 4.13): a `deepEquals` check, then the first difference. -/
def arr4K (P : Program) (msg : Option JStr) :
    Nat → Bool → Value → Value → State → (Arr4 → State → NRes) → NRes
  | 0, _, _, _, _, _ => bad "array comparison too deep"
  | n + 1, outer, e, a, σ, k =>
    let deep (k' : Bool → State → NRes) : NRes :=
      if e == a then k' true σ else if e == .null then k' false σ else deepEq0K P n e a σ k'
    deep fun same σ1 =>
      if same then k .equal σ1 else
      let header0 : JStr := match msg with | some s => s ++ jstr ": " | none => []
      let exMsg : JStr := if outer then header0 else []
      if e == .null then k (.fail (exMsg ++ jstr "expected array was null")) σ1
      else if a == .null then k (.fail (exMsg ++ jstr "actual array was null")) σ1
      else match objAt σ1 e, objAt σ1 a with
        | some (_, .array te xs), some (_, .array _ ys) =>
          let header := header0 ++ (if xs.length != ys.length then
            jstr "array lengths differed, expected.length=" ++ JStr.ofInt xs.length ++
            jstr " actual.length=" ++ JStr.ofInt ys.length ++ jstr "; " else [])
          let pre := min xs.length ys.length
          arr4ElemsK P msg n header te 0 ((xs.take pre).zip (ys.take pre)) σ1 fun r σ2 =>
            match r with
            | some f => k f σ2
            | none => if xs.length == ys.length then k .equal σ2 else arr4TailK P header te xs ys pre σ2 k
        | _, _ => bad "expected arrays"

/-- The loop of `arrayEquals` over the common prefix: nested arrays recursively (an inner
    failure gets the index prepended), other elements by `Assert.assertEquals`. -/
def arr4ElemsK (P : Program) (msg : Option JStr) :
    Nat → JStr → JType → Nat → List (Value × Value) → State → (Option Arr4 → State → NRes) → NRes
  | 0, _, _, _, _, _, _ => bad "array comparison too deep"
  | _ + 1, _, _, _, [], σ, k => k none σ
  | n + 1, header, te, i, (x, y) :: rest, σ, k =>
    let next (σ' : State) : NRes := arr4ElemsK P msg n header te (i + 1) rest σ' k
    if !te.isRef then
      -- primitive elements are compared as boxes by `assertEquals(Object, Object)`
      if canonBits x == canonBits y then next σ
      else match primStr te x, primStr te y with
        | some xs', some ys' => k (some (.acf header [i] "java.lang.AssertionError"
            (jstr "expected:<" ++ xs' ++ jstr "> but was:<" ++ ys' ++ jstr ">"))) σ
        | _, _ => bad "floating-point to string conversion is not modelled"
    else if (arrKind σ x).isSome && (arrKind σ y).isSome then
      arr4K P msg n false x y σ fun r σ' => match r with
        | .equal => next σ'
        | .acf h idx c m => k (some (.acf h (i :: idx) c m)) σ'
        | .fail m => k (some (.acf header [i] "java.lang.AssertionError" m)) σ'
    else
      jEqualsK P false σ x y fun b σ' =>
        if b then next σ'
        else match strOf σ' x, strOf σ' y with
          | some xs', some ys' =>
            k (some (.acf header [i] "org.junit.ComparisonFailure" (compact4 [] xs' ys'))) σ'
          | _, _ => format4K P none x y σ' fun s σ'' => k (some (.acf header [i] "java.lang.AssertionError" s)) σ''
end

/-- Throw JUnit 4's `ArrayComparisonFailure`: message `header` + "arrays first differed at element
    [i][j]; " + the cause's message; the cause is a new `causeCls` with message `causeMsg`. -/
def throwAcf (header : JStr) (idx : List Nat) (causeCls : ClassName) (causeMsg : JStr) (σ : State) : NRes :=
  let (cm, σ) := allocStr causeMsg σ
  let fs (cause : Value) : List (FieldKey × Value) :=
    [(("java.lang.Throwable", "detailMessage"), cm), (("java.lang.Throwable", "cause"), cause)]
  let (c, σ) := σ.alloc (.plain causeCls (fs .null))
  let σ := σ.setObj c (.plain causeCls (fs (.ref c)))
  thrWith "org.junit.internal.ArrayComparisonFailure"
    (some (header ++ jstr "arrays first differed at element " ++ (idx.map fun i => jstr s!"[{i}]").flatten ++
      jstr "; " ++ causeMsg)) (some (.ref c)) σ

/-- `org.junit.Assert` (JUnit 4.13): `assertTrue`/`assertFalse`, `assertNull`/`assertNotNull`,
    `assertSame`/`assertNotSame`, `assertEquals` (`long`; `Object` by `equals`, with application
    `equals` called back; two `String`s fail with `org.junit.ComparisonFailure`), `assertThrows`
    and `fail`, each with an optional leading `String` message. Failures throw
    `java.lang.AssertionError` with JUnit's messages. -/
def junit4Assert (P : Program) (name : String) (ps : List JType) (args : List Value) (σ : State) :
    Option NRes :=
  let (hasMsg, core, cargs) : Bool × List JType × List Value :=
    match ps, args with
    | .cls "java.lang.String" :: ps', _ :: args' => (true, ps', args')
    | _, _ => (false, ps, args)
  let msg : Option JStr := if hasMsg then (args.head?.bind (strOf σ ·)) else none
  -- `Assert.fail`: `new AssertionError()` for a `null` message, else `new AssertionError(message)`
  let fail4 (m : Option JStr) (σ : State) : NRes := thrWith "java.lang.AssertionError" m none σ
  -- the prefix of `failNotNull`, `failSame` and `failNotSame` (any non-null message) and of
  -- `Assert.format` (a non-empty message)
  let pre1 : JStr := match msg with | some s => s ++ jstr " " | none => []
  let pre2 : JStr := match msg with | some s => if s.isEmpty then [] else s ++ jstr " " | none => []
  -- the text of `failEquals` (assertNotEquals) before the rendering of `actual`
  let fe4 : JStr := (match msg with | some s => s ++ jstr ". " | none => jstr "Values should be different. ") ++
    jstr "Actual: "
  let arrays4 (e a : Value) : NRes :=
    arr4K P msg 1000000 true e a σ fun r σ' => match r with
      | .equal => okVoid σ'
      | .fail m => fail4 (some m) σ'
      | .acf h idx c m => throwAcf h idx c m σ'
  let O := JType.cls "java.lang.Object"
  match name, core, cargs with
  | "fail", [], [] => some (fail4 msg σ)
  | "assertTrue", [.prim .boolean], [.int b] => some (if b ≠ 0 then okVoid σ else fail4 msg σ)
  | "assertFalse", [.prim .boolean], [.int b] => some (if b = 0 then okVoid σ else fail4 msg σ)
  | "assertNotNull", [t], [o] => if t != O then none else some (if o != .null then okVoid σ else fail4 msg σ)
  | "assertNull", [t], [o] =>
    if t != O then none else some <|
      if o == .null then okVoid σ
      else valueOfObj P o σ fun s σ' => fail4 (some (pre1 ++ jstr "expected null, but was:<" ++ s ++ jstr ">")) σ'
  | "assertSame", [t1, t2], [e, a] =>
    if t1 != O || t2 != O then none else some <|
      if e == a then okVoid σ
      else valueOfObj P e σ fun es σ1 => valueOfObj P a σ1 fun as σ2 =>
        fail4 (some (pre1 ++ jstr "expected same:<" ++ es ++ jstr "> was not:<" ++ as ++ jstr ">")) σ2
  | "assertNotSame", [t1, t2], [u, a] =>
    if t1 != O || t2 != O then none else some <|
      if u != a then okVoid σ else fail4 (some (pre1 ++ jstr "expected not same")) σ
  | "assertEquals", [.prim .long, .prim .long], [.long e, .long a] => some <|
    -- `failNotEquals(message, Long.valueOf(expected), Long.valueOf(actual))`
    if e == a then okVoid σ
    else fail4 (some (pre2 ++ jstr "expected:<" ++ JStr.ofInt e.toInt ++ jstr "> but was:<" ++
      JStr.ofInt a.toInt ++ jstr ">")) σ
  | "assertEquals", [.prim .double, .prim .double], [_, _] =>
    -- deprecated: always fails, ignoring the message
    some (fail4 (some (jstr "Use assertEquals(expected, actual, delta) to compare floating-point numbers")) σ)
  | "assertNotEquals", [.prim .long, .prim .long], [.long u, .long a] => some <|
    if u != a then okVoid σ else fail4 (some (fe4 ++ JStr.ofInt a.toInt)) σ
  | "assertNotEquals", [t1, t2], [u, a] =>
    if t1 != O || t2 != O then none else some <|
      jEqualsK P false σ u a fun b σ1 =>
        if !b then okVoid σ1 else valueOfObj P a σ1 fun s σ2 => fail4 (some (fe4 ++ s)) σ2
  | "assertArrayEquals", [.array t1, .array t2], [e, a] =>
    if t1 != t2 || t1 == .prim .float || t1 == .prim .double then none else some (arrays4 e a)
  | "assertEquals", [.array t1, .array t2], [e, a] =>
    -- deprecated `assertEquals(Object[], Object[])`: `assertArrayEquals`
    if t1 != O || t2 != O then none else some (arrays4 e a)
  | "assertEquals", [t1, t2], [e, a] =>
    if t1 != O || t2 != O then none else some <|
      -- `equalsRegardingNull`: `expected == null ? actual == null : expected.equals(actual)`
      jEqualsK P false σ e a fun b σ1 =>
        if b then okVoid σ1
        else match strOf σ1 e, strOf σ1 a with
          | some es, some as =>
            thrWith "org.junit.ComparisonFailure" (some (compact4 (msg.getD []) es as)) none σ1
          | _, _ => format4K P msg e a σ1 fun s σ2 => fail4 (some s) σ2
  | "assertThrows", [.cls "java.lang.Class", .cls "org.junit.function.ThrowingRunnable"], [c, r] =>
    let pre3 : JStr := match msg with | some s => if s.isEmpty then [] else s ++ jstr ": " | none => []
    some <| throwsK P runnableRunSig c r σ
      (fun en ec e σ' =>
        if canonicalOrName en == canonicalOrName ec then
          bad "assertThrows with two classes of the same name is not modelled"
        else thrWith "java.lang.AssertionError"
          (some (pre3 ++ jstr "unexpected exception type thrown; expected:<" ++ jstr (canonicalOrName en) ++
            jstr "> but was:<" ++ jstr (canonicalOrName ec) ++ jstr ">")) (some (.ref e)) σ')
      (fun en σ' => thrWith "java.lang.AssertionError"
        (some (pre3 ++ jstr "expected " ++ jstr (canonicalOrName en) ++ jstr " to be thrown, but nothing was thrown"))
        none σ')
  | _, _, _ => none

/-- The Unicode blocks known to the model: the constant's name, the other names `forName` accepts
    (in upper case), and the code point range. -/
def unicodeBlocks : List (String × List String × Nat × Nat) :=
  [("BASIC_LATIN", ["BASIC LATIN", "BASICLATIN"], 0x0000, 0x007F),
   ("LATIN_1_SUPPLEMENT", ["LATIN-1 SUPPLEMENT", "LATIN-1SUPPLEMENT"], 0x0080, 0x00FF),
   ("LATIN_EXTENDED_A", ["LATIN EXTENDED-A", "LATINEXTENDED-A"], 0x0100, 0x017F),
   ("LATIN_EXTENDED_B", ["LATIN EXTENDED-B", "LATINEXTENDED-B"], 0x0180, 0x024F),
   ("IPA_EXTENSIONS", ["IPA EXTENSIONS", "IPAEXTENSIONS"], 0x0250, 0x02AF),
   ("SPACING_MODIFIER_LETTERS", ["SPACING MODIFIER LETTERS", "SPACINGMODIFIERLETTERS"], 0x02B0, 0x02FF),
   ("COMBINING_DIACRITICAL_MARKS", ["COMBINING DIACRITICAL MARKS", "COMBININGDIACRITICALMARKS"], 0x0300, 0x036F),
   ("GREEK", ["GREEK AND COPTIC", "GREEKANDCOPTIC"], 0x0370, 0x03FF)]

def ublockCls : ClassName := "java.lang.Character$UnicodeBlock"

/-- The `Character.UnicodeBlock` constant named `n`: one object per block, kept in static storage
    so that blocks compare by identity as in the JDK. -/
def ublockObj (n : String) (σ : State) : Value × State :=
  match σ.static (ublockCls, n) with
  | some v => (v, σ)
  | none =>
    let (nm, σ) := allocStr (jstr n) σ
    let (a, σ) := σ.alloc (.plain ublockCls [(("java.lang.Character$Subset", "name"), nm)])
    (.ref a, σ.setStatic (ublockCls, n) (.ref a))

/-- `String.valueOf` of each element (application `toString` called back), joined by `delim`. -/
def joinWith2K (P : Program) (delim : JStr) : List Value → State → (JStr → State → NRes) → NRes
  | [], σ, k => k [] σ
  | [x], σ, k => valueOfObj P x σ k
  | x :: xs, σ, k => valueOfObj P x σ fun s σ' => joinWith2K P delim xs σ' fun t σ'' => k (s ++ delim ++ t) σ''

/-! ### Static methods of library classes -/

def boxOf (cls : ClassName) (v : Value) (σ : State) : NRes := okObj (.boxed cls v) σ

def staticCall (P : Program) (sig : MethodSig) (args : List Value) (σ : State) : Option NRes :=
  match sig.cls, sig.name, sig.params, args with
  | "java.lang.Integer", "valueOf", [.prim .int], [v] => some (boxOf "java.lang.Integer" v σ)
  | "java.lang.Long", "valueOf", [.prim .long], [v] => some (boxOf "java.lang.Long" v σ)
  | "java.lang.Short", "valueOf", [.prim .short], [v] => some (boxOf "java.lang.Short" v σ)
  | "java.lang.Byte", "valueOf", [.prim .byte], [v] => some (boxOf "java.lang.Byte" v σ)
  | "java.lang.Character", "valueOf", [.prim .char], [v] => some (boxOf "java.lang.Character" v σ)
  | "java.lang.Boolean", "valueOf", [.prim .boolean], [v] => some (boxOf "java.lang.Boolean" v σ)
  | "java.lang.Double", "valueOf", [.prim .double], [v] => some (boxOf "java.lang.Double" v σ)
  | "java.lang.Float", "valueOf", [.prim .float], [v] => some (boxOf "java.lang.Float" v σ)
  | "java.lang.Integer", "parseInt", [.cls _], [s] => some <| if s == .null then thr NFE (some "Cannot parse null string") σ else argStr σ s fun s =>
      if !JStr.isAscii s then bad "non-ASCII numeric text is not modelled" else
      match parseIntStr s (-2147483648) 2147483647 with
      | some i => okInt i σ
      | none => thr NFE (some s!"For input string: \"{JStr.toLean s}\"") σ
  | "java.lang.Integer", "valueOf", [.cls _], [s] => some <| if s == .null then thr NFE (some "Cannot parse null string") σ else argStr σ s fun s =>
      if !JStr.isAscii s then bad "non-ASCII numeric text is not modelled" else
      match parseIntStr s (-2147483648) 2147483647 with
      | some i => boxOf "java.lang.Integer" (.int (BitVec.ofInt 32 i)) σ
      | none => thr NFE (some s!"For input string: \"{JStr.toLean s}\"") σ
  | "java.lang.Long", "parseLong", [.cls _], [s] => some <| if s == .null then thr NFE (some "Cannot parse null string") σ else argStr σ s fun s =>
      if !JStr.isAscii s then bad "non-ASCII numeric text is not modelled" else
      match parseIntStr s (-9223372036854775808) 9223372036854775807 with
      | some i => ok (.long (BitVec.ofInt 64 i)) σ
      | none => thr NFE (some s!"For input string: \"{JStr.toLean s}\"") σ
  | "java.lang.Integer", "toString", [.prim .int], [.int x] => some (okStr (JStr.ofInt x.toInt) σ)
  | "java.lang.Long", "toString", [.prim .long], [.long x] => some (okStr (JStr.ofInt x.toInt) σ)
  | "java.lang.Integer", "compare", [_, _], [.int x, .int y] =>
    some (okInt (if x.toInt < y.toInt then -1 else if x = y then 0 else 1) σ)
  | "java.lang.Long", "compare", [_, _], [.long x, .long y] =>
    some (okInt (if x.toInt < y.toInt then -1 else if x = y then 0 else 1) σ)
  | "java.lang.Integer", "max", [_, _], [.int x, .int y] => some (ok (.int (if x.toInt ≥ y.toInt then x else y)) σ)
  | "java.lang.Integer", "min", [_, _], [.int x, .int y] => some (ok (.int (if x.toInt ≤ y.toInt then x else y)) σ)
  | "java.lang.Integer", "sum", [_, _], [.int x, .int y] => some (ok (.int (x + y)) σ)
  | "java.lang.Integer", "signum", [_], [.int x] => some (okInt (if x.toInt > 0 then 1 else if x.toInt < 0 then -1 else 0) σ)
  | "java.lang.Boolean", "parseBoolean", [_], [s] => some <|
      match strOf σ s with
      | some t => okBool (JStr.asciiLower t == jstr "true") σ
      | none => okBool false σ
  | "java.lang.Character", "isDigit", [.prim .char], [.int c] =>
    some <| if c.toNat < 128 then okBool (48 ≤ c.toNat ∧ c.toNat ≤ 57) σ
      else okBool (Unicode.isDigit c.toNat) σ
  | "java.lang.Character", "isLetter", [.prim .char], [.int c] =>
    some <| if c.toNat < 128 then okBool ((65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 122)) σ
      else okBool (Unicode.isLetter c.toNat) σ
  | "java.lang.Double", "isNaN", [_], [.double x] => some (okBool (JFloat.isNaN64 x) σ)
  | "java.lang.Float", "isNaN", [_], [.float x] => some (okBool (JFloat.isNaN32 x) σ)
  | "java.lang.Double", "compare", [_, _], [.double x, .double y] =>
    -- Double.compare: total order with -0.0 < 0.0 and NaN greatest
    some <| let bx := (canonBits (.double x)); let by_ := (canonBits (.double y))
      let r := JFloat.dcmpg x y
      okInt (if JFloat.isNaN64 x then (if JFloat.isNaN64 y then 0 else 1)
             else if JFloat.isNaN64 y then -1
             else if r ≠ 0 then r.toInt else if bx == by_ then 0
             else if x.msb then -1 else 1) σ
  | "java.lang.Double", "doubleToLongBits", [_], [v] => some (match canonBits v with
      | .double b => ok (.long b) σ | _ => bad "double")
  | "java.lang.Double", "doubleToRawLongBits", [_], [.double b] => some (ok (.long b) σ)
  | "java.lang.Double", "longBitsToDouble", [_], [.long b] => some (ok (.double b) σ)
  | "java.lang.Math", "max", [.prim .int, _], [.int x, .int y] => some (ok (.int (if x.toInt ≥ y.toInt then x else y)) σ)
  | "java.lang.Math", "min", [.prim .int, _], [.int x, .int y] => some (ok (.int (if x.toInt ≤ y.toInt then x else y)) σ)
  | "java.lang.Math", "max", [.prim .long, _], [.long x, .long y] => some (ok (.long (if x.toInt ≥ y.toInt then x else y)) σ)
  | "java.lang.Math", "min", [.prim .long, _], [.long x, .long y] => some (ok (.long (if x.toInt ≤ y.toInt then x else y)) σ)
  | "java.lang.Math", "abs", [.prim .int], [.int x] => some (ok (.int (if x.toInt < 0 then -x else x)) σ)
  | "java.lang.Math", "abs", [.prim .long], [.long x] => some (ok (.long (if x.toInt < 0 then -x else x)) σ)
  | "java.lang.Math", "abs", [.prim .double], [.double x] =>
    some (ok (.double (x &&& BitVec.ofNat 64 (2 ^ 63 - 1))) σ)
  | "java.lang.Math", "addExact", [.prim .int, _], [.int x, .int y] => some <|
      let r := x.toInt + y.toInt
      if -2147483648 ≤ r ∧ r ≤ 2147483647 then ok (.int (x + y)) σ else thr AE (some "integer overflow") σ
  | "java.lang.Math", "subtractExact", [.prim .int, _], [.int x, .int y] => some <|
      let r := x.toInt - y.toInt
      if -2147483648 ≤ r ∧ r ≤ 2147483647 then ok (.int (x - y)) σ else thr AE (some "integer overflow") σ
  | "java.lang.Math", "multiplyExact", [.prim .int, _], [.int x, .int y] => some <|
      let r := x.toInt * y.toInt
      if -2147483648 ≤ r ∧ r ≤ 2147483647 then ok (.int (x * y)) σ else thr AE (some "integer overflow") σ
  | "java.lang.Math", "addExact", [.prim .long, _], [.long x, .long y] => some <|
      let r := x.toInt + y.toInt
      if -9223372036854775808 ≤ r ∧ r ≤ 9223372036854775807 then ok (.long (x + y)) σ else thr AE (some "long overflow") σ
  | "java.lang.Math", "subtractExact", [.prim .long, _], [.long x, .long y] => some <|
      let r := x.toInt - y.toInt
      if -9223372036854775808 ≤ r ∧ r ≤ 9223372036854775807 then ok (.long (x - y)) σ else thr AE (some "long overflow") σ
  | "java.lang.Math", "multiplyExact", [.prim .long, _], [.long x, .long y] => some <|
      let r := x.toInt * y.toInt
      if -9223372036854775808 ≤ r ∧ r ≤ 9223372036854775807 then ok (.long (x * y)) σ else thr AE (some "long overflow") σ
  | "java.lang.Math", "toIntExact", [_], [.long x] => some <|
      if -2147483648 ≤ x.toInt ∧ x.toInt ≤ 2147483647 then ok (.int (JLong.toInt x)) σ
      else thr AE (some "integer overflow") σ
  | "java.lang.Math", "floorDiv", [.prim .int, _], [.int x, .int y] => some <|
      if y = 0 then thr AE (some "/ by zero") σ else okInt (Int.fdiv x.toInt y.toInt) σ
  | "java.lang.Math", "floorMod", [.prim .int, _], [.int x, .int y] => some <|
      if y = 0 then thr AE (some "/ by zero") σ else okInt (Int.fmod x.toInt y.toInt) σ
  | "java.lang.String", "valueOf", [t], [v] => some <| valueOfCharsArg P t v σ fun s σ' => okStr s σ'
  | "java.lang.String", "format", [.cls "java.lang.String", _], [f, av] => some <|
      if f == .null then thrNPE σ else argStr σ f fun fmt => formatK P fmt av σ fun s σ' => okStr s σ'
  | "java.util.Objects", "equals", [_, _], [x, y] => some <|
      if x == y then okBool true σ
      else if x == .null then okBool false σ
      else match nEquals P σ x y with
        | some b => okBool b σ
        | none => match objAt σ x with
          | some (_, .plain c _) =>
            if !P.isProgClass c then okBool (x == y) σ else
            .call equalsSig (.virtual c) [x, y] σ fun out => match out with
              | .normal (some r) σ' => ok r σ'
              | .normal none _ => bad "equals returned no value"
              | .exc e σ' => .ret (.thr e σ')
              | .wrong msg => bad msg
          | _ => bad "equals"
  | "java.util.Objects", "requireNonNull", [_], [x] => some (if x == .null then thrNPE σ else ok x σ)
  | "java.util.Objects", "requireNonNull", [_, .cls "java.lang.String"], [x, msg] => some <|
      if x == .null then .ret (match strOf σ msg with
        | some s => throwNew "java.lang.NullPointerException" (some s) σ
        | none => npe σ)
      else ok x σ
  | "java.util.Objects", "isNull", [_], [x] => some (okBool (x == .null) σ)
  | "java.util.Objects", "nonNull", [_], [x] => some (okBool (x != .null) σ)
  | "java.util.Objects", "toString", [_], [x] => some <| valueOfObj P x σ fun s σ' => okStr s σ'
  | "java.math.BigDecimal", "valueOf", [.prim .long], [.long x] => some (okObj (.dec ⟨x.toInt, 0⟩) σ)
  | "java.math.BigDecimal", "valueOf", [.prim .long, .prim .int], [.long x, .int s] =>
    some (okObj (.dec ⟨x.toInt, s.toInt⟩) σ)
  | "java.math.BigInteger", "valueOf", [.prim .long], [.long x] => some (okObj (.bigInt x.toInt) σ)
  | "java.math.RoundingMode", "valueOf", [.prim .int], [.int i] => some <|
      match RoundingMode.ofOrdinal? i.toNat with
      | some r => if i.toInt < 0 then thr IAE (some "argument out of range") σ else okObj (.rmode r) σ
      | none => thr IAE (some "argument out of range") σ
  | "java.math.RoundingMode", "valueOf", [.cls _], [s] => some <| argStr σ s fun s =>
      match RoundingMode.ofName? (JStr.toLean s) with
      | some r => okObj (.rmode r) σ
      | none => thr IAE (some s!"No enum constant java.math.RoundingMode.{JStr.toLean s}") σ
  | "java.lang.System", "currentTimeMillis", [], [] => some (.choose fun n => ok (.long (BitVec.ofNat 64 n)) σ)
  | "java.lang.System", "nanoTime", [], [] => some (.choose fun n => ok (.long (BitVec.ofNat 64 n)) σ)
  | "java.lang.System", "identityHashCode", [_], [x] => some <|
      if x == .null then okInt 0 σ else .choose fun n => ok (.int (BitVec.ofNat 32 n)) σ
  | "java.lang.System", "lineSeparator", [], [] => some (okStr (jstr "\n") σ)
  | "java.lang.System", "arraycopy", [_, _, _, _, _], [src, .int sp, dst, .int dp, .int len] => some <|
      argObj σ src fun _ so => argObj σ dst fun da dobj =>
        match so, dobj with
        | .array st sxs, .array dt dxs =>
          let ok_types := match st, dt with
            | .prim p, .prim q => p == q
            | .prim _, _ | _, .prim _ => false
            | _, _ => true
          if !ok_types then thr "java.lang.ArrayStoreException" none σ
          else if sp.toInt < 0 ∨ dp.toInt < 0 ∨ len.toInt < 0 ∨ sp.toInt + len.toInt > sxs.length
              ∨ dp.toInt + len.toInt > dxs.length then
            thr "java.lang.ArrayIndexOutOfBoundsException" (some "arraycopy: last source index out of bounds") σ
          else
            let piece := (sxs.drop sp.toNat).take len.toNat
            if dt.isRef && !(piece.all fun v => v == .null ||
                (match objAt σ v with | some (_, ob) => P.subtype ob.ty dt == some true | none => false)) then
              bad "arraycopy with element store checks is not modelled"
            else okVoid (σ.setObj da (.array dt (dxs.take dp.toNat ++ piece ++ dxs.drop (dp.toNat + len.toNat))))
        | _, _ => thr "java.lang.ArrayStoreException" none σ
  | "java.util.List", "of", ps, xs =>
    if ps.all (· == .object) then
      some (if xs.any (· == .null) then thrNPE σ else okObj (.list .immutable xs 0) σ)
    else none
  | "java.util.Collections", "emptyList", [], [] => some (okObj (.list .immutable [] 0) σ)
  | "java.lang.Enum", "valueOf", [_, _], [cv, nv] => some <| argObj σ cv fun _ co => match co with
      | .clazz c =>
        if P.isSubclass c "java.lang.Enum" != some true then bad s!"Enum.valueOf on the non-enum class {c}"
        else if nv == .null then thr "java.lang.NullPointerException" (some "Name is null") σ
        else if σ.initOf c != .done then bad "Enum.valueOf on an enum class that is not initialized is not modelled"
        else argStr σ nv fun name =>
          -- the constants are the static fields of the enum's own type whose `name` matches
          let fields := ((P.lookup c).map (·.fields)).getD []
          let found := fields.findSome? fun f =>
            if f.isStatic ∧ f.ty = .cls c then
              (σ.static (c, f.name)).bind fun v => match objAt σ v with
                | some (_, .plain _ fs) =>
                  if (Fields.get fs ("java.lang.Enum", "name")).bind (strOf σ) == some name then some v else none
                | _ => none
            else none
          match found with
          | some v => ok v σ
          | none => thr IAE (some s!"No enum constant {c.replace "$" "."}.{JStr.toLean name}") σ
      | _ => bad "Enum.valueOf: expected a class object"
  | "java.lang.Character", "isUpperCase", [.prim .char], [.int c] => some <| match asciiChar? c with
      | some n => okBool (65 ≤ n ∧ n ≤ 90) σ
      | none => okBool (Unicode.isUpper c.toNat) σ
  | "java.lang.Character", "isLowerCase", [.prim .char], [.int c] => some <| match asciiChar? c with
      | some n => okBool (97 ≤ n ∧ n ≤ 122) σ
      | none => okBool (Unicode.isLower c.toNat) σ
  | "java.lang.Character", "isWhitespace", [.prim .char], [.int c] => some <| match asciiChar? c with
      | some n => okBool ((9 ≤ n ∧ n ≤ 13) ∨ (28 ≤ n ∧ n ≤ 32)) σ
      | none => okBool (Unicode.isWhitespace c.toNat) σ
  | "java.lang.Character", "isLetterOrDigit", [.prim .char], [.int c] => some <| match asciiChar? c with
      | some n => okBool ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 90) ∨ (97 ≤ n ∧ n ≤ 122)) σ
      | none => okBool (Unicode.isLetter c.toNat || Unicode.isDigit c.toNat) σ
  | "java.lang.Character", "toUpperCase", [.prim .char], [.int c] => some <| match asciiChar? c with
      | some n => ok (.int (BitVec.ofNat 32 (if 97 ≤ n ∧ n ≤ 122 then n - 32 else n))) σ
      | none => ok (.int (BitVec.ofNat 32 (Unicode.toUpper c.toNat % 65536))) σ
  | "java.lang.Character", "toLowerCase", [.prim .char], [.int c] => some <| match asciiChar? c with
      | some n => ok (.int (BitVec.ofNat 32 (if 65 ≤ n ∧ n ≤ 90 then n + 32 else n))) σ
      | none => ok (.int (BitVec.ofNat 32 (Unicode.toLower c.toNat % 65536))) σ
  | "java.lang.Character", "toString", [.prim .char], [.int c] => some (okStr [c.setWidth 16] σ)
  | "java.lang.Character", "forDigit", [_, _], [.int d, .int r] => some <|
      ok (.int (if 2 ≤ r.toInt ∧ r.toInt ≤ 36 ∧ 0 ≤ d.toInt ∧ d.toInt < r.toInt
        then (digitChar36 d.toNat).zeroExtend 32 else 0)) σ
  | "java.lang.Character", "digit", [.prim .char, _], [.int c, .int r] => some <| match asciiChar? c with
      | some _ => okInt (if 2 ≤ r.toInt ∧ r.toInt ≤ 36
          then ((digitVal? (c.setWidth 16) r.toNat).map Int.ofNat).getD (-1) else -1) σ
      | none => okInt (if 2 ≤ r.toInt ∧ r.toInt ≤ 36 then Unicode.digit c.toNat r.toNat else -1) σ
  | "java.lang.Character", "getNumericValue", [.prim .int], [.int cp] => some <|
      okInt (if 0 ≤ cp.toInt ∧ cp.toInt ≤ 0x10FFFF then Unicode.numericValue cp.toNat else -1) σ
  | "java.lang.Character", "digit", [.prim .int, .prim .int], [.int cp, .int r] => some <|
      okInt (if 0 ≤ cp.toInt ∧ cp.toInt ≤ 0x10FFFF ∧ 2 ≤ r.toInt ∧ r.toInt ≤ 36
        then Unicode.digit cp.toNat r.toNat else -1) σ
  | "java.lang.Character", "getNumericValue", [.prim .char], [.int c] => some <| match asciiChar? c with
      | some _ => okInt (((digitVal? (c.setWidth 16) 36).map Int.ofNat).getD (-1)) σ
      | none => okInt (Unicode.numericValue c.toNat) σ
  | "java.lang.Long", "signum", [_], [.long x] =>
    some (okInt (if x.toInt > 0 then 1 else if x.toInt < 0 then -1 else 0) σ)
  | "java.lang.Integer", "toBinaryString", [_], [.int x] => some (okStr (natDigits 2 x.toNat) σ)
  | "java.lang.Integer", "toHexString", [_], [.int x] => some (okStr (natDigits 16 x.toNat) σ)
  | "java.lang.Integer", "toOctalString", [_], [.int x] => some (okStr (natDigits 8 x.toNat) σ)
  | "java.lang.Long", "toBinaryString", [_], [.long x] => some (okStr (natDigits 2 x.toNat) σ)
  | "java.lang.Long", "toHexString", [_], [.long x] => some (okStr (natDigits 16 x.toNat) σ)
  | "java.lang.Long", "toOctalString", [_], [.long x] => some (okStr (natDigits 8 x.toNat) σ)
  | "java.lang.Integer", "toString", [.prim .int, .prim .int], [.int x, .int r] =>
    some (okStr (intDigits (if 2 ≤ r.toInt ∧ r.toInt ≤ 36 then r.toNat else 10) x.toInt) σ)
  | "java.lang.Integer", "parseInt", [.cls _, .prim .int], [s, .int r] => some <| if s == .null then thr NFE (some "Cannot parse null string") σ else argStr σ s fun s =>
      let msg := s!"For input string: \"{JStr.toLean s}\"" ++ (if r.toInt = 10 then "" else s!" under radix {r.toInt}")
      if r.toInt < 2 ∨ r.toInt > 36 then bad "Integer.parseInt with a radix out of range is not modelled"
      else if !JStr.isAscii s then bad "non-ASCII numeric text is not modelled"
      else match parseRadix? s r.toNat with
        | some i => if -2147483648 ≤ i ∧ i ≤ 2147483647 then okInt i σ else thr NFE (some msg) σ
        | none => thr NFE (some msg) σ
  | "java.util.Arrays", "toString", [.array t], [a] => some <|
      if a == .null then okStr (jstr "null") σ
      else argObj σ a fun _ o => match o with
        | .array _ xs =>
          if t.isRef then joinWith (valueOfObjN P 8) xs σ fun s σ' => okStr (jstr "[" ++ s ++ jstr "]") σ'
          else match xs.mapM (primStr t) with
            | some ss => okStr (jstr "[" ++ (ss.intersperse (jstr ", ")).flatten ++ jstr "]") σ
            | none => bad "floating-point to string conversion is not modelled"
        | _ => bad "expected an array"
  | "java.util.Arrays", "sort", [.array t], [a] => some <| argObj σ a fun ad o => match o with
      | .array et xs =>
        match t with
        | .prim .float | .prim .double => bad "sorting floating-point arrays is not modelled"
        | .prim _ => okVoid (σ.setObj ad (.array et (xs.mergeSort fun x y => decide (primKey x ≤ primKey y))))
        | _ => match natSort σ xs with
          | .ok ys => okVoid (σ.setObj ad (.array et ys))
          | .exc c => thr c none σ
          | .unsupported => msortK P xs σ fun ys σ' => okVoid (σ'.setObj ad (.array et ys))
      | _ => bad "expected an array"
  | "java.util.Arrays", "fill", [.array _, _], [a, v] => some <| argObj σ a fun ad o => match o with
      | .array et xs =>
        let storeOk : Bool := !et.isRef || v == .null ||
          (match objAt σ v with | some (_, ob) => P.subtype ob.ty et == some true | none => false)
        if storeOk then okVoid (σ.setObj ad (.array et (xs.map fun _ => et.narrow v)))
        else thr "java.lang.ArrayStoreException" none σ
      | _ => bad "expected an array"
  | "java.util.Arrays", "equals", [.array _, .array _], [a, b] => some <|
      if a == .null ∨ b == .null then okBool (a == b) σ
      else argObj σ a fun _ oa => argObj σ b fun _ ob => match oa, ob with
        | .array ta xs, .array _ ys =>
          if xs.length ≠ ys.length then okBool false σ
          else if ta.isRef then match (xs.zip ys).mapM (fun (x, y) => nEquals P σ x y) with
            | some bs => okBool (bs.all id) σ
            | none => allEqualK P (xs.zip ys) σ fun b σ' => okBool b σ'
          else okBool ((xs.zip ys).all fun (x, y) => canonBits x == canonBits y) σ
        | _, _ => bad "expected arrays"
  | "java.util.Arrays", "copyOf", [.array _, .prim .int], [a, .int n] => some <| argObj σ a fun _ o => match o with
      | .array et xs =>
        if n.toInt < 0 then thr "java.lang.NegativeArraySizeException" (some s!"{n.toInt}") σ
        else okObj (.array et (xs.take n.toNat ++ List.replicate (n.toNat - xs.length) et.default)) σ
      | _ => bad "expected an array"
  | "java.util.Arrays", "copyOfRange", [.array _, .prim .int, .prim .int], [a, .int f, .int t] => some <|
      argObj σ a fun _ o => match o with
      | .array et xs =>
        if f.toInt > t.toInt then thr IAE (some s!"{f.toInt} > {t.toInt}") σ
        else if f.toInt < 0 ∨ f.toInt > xs.length then thr "java.lang.ArrayIndexOutOfBoundsException" none σ
        else
          let part := (xs.drop f.toNat).take (t.toNat - f.toNat)
          okObj (.array et (part ++ List.replicate (t.toNat - f.toNat - part.length) et.default)) σ
      | _ => bad "expected an array"
  | "java.util.Collections", "sort", [_], [l] => some <| argObj σ l fun la lo => match lo with
      | .list k xs m =>
        if k = .immutable then thr UOE none σ
        else match natSort σ xs with
          -- `ArrayList.sort` counts as a structural modification; `List.sort` on a
          -- `LinkedList` writes the elements back with `ListIterator.set`, which does not
          | .ok ys => okVoid (σ.setObj la (.list k ys (if k = .arrayList then m + 1 else m)))
          | .exc c => thr c none σ
          | .unsupported => msortK P xs σ fun ys σ' =>
            okVoid (σ'.setObj la (.list k ys (if k = .arrayList then m + 1 else m)))
      | _ => bad "Collections.sort of this collection kind is not modelled"
  | "java.util.Collections", "max", [_], [c] => some <| argObj σ c fun _ co => match elemsOf σ co with
      | some xs => match natExtreme σ xs true with
        | .ok (some v) => ok v σ
        | .ok none => thr NSEE none σ
        | .exc cls => thr cls none σ
        | .unsupported => match xs with
          | x :: rest => extremeK P true x rest σ fun v σ' => ok v σ'
          | [] => thr NSEE none σ
      | none => bad "Collections.max of this collection kind is not modelled"
  | "java.util.Collections", "min", [_], [c] => some <| argObj σ c fun _ co => match elemsOf σ co with
      | some xs => match natExtreme σ xs false with
        | .ok (some v) => ok v σ
        | .ok none => thr NSEE none σ
        | .exc cls => thr cls none σ
        | .unsupported => match xs with
          | x :: rest => extremeK P false x rest σ fun v σ' => ok v σ'
          | [] => thr NSEE none σ
      | none => bad "Collections.min of this collection kind is not modelled"
  | "java.lang.Integer", "rotateLeft", [_, _], [.int x, .int d] => some (ok (.int (JInt.shl x d ||| JInt.ushr x (-d))) σ)
  | "java.lang.Integer", "rotateRight", [_, _], [.int x, .int d] => some (ok (.int (JInt.ushr x d ||| JInt.shl x (-d))) σ)
  | "java.lang.Long", "rotateLeft", [_, _], [.long x, .int d] => some (ok (.long (JLong.shl x d ||| JLong.ushr x (-d))) σ)
  | "java.lang.Long", "rotateRight", [_, _], [.long x, .int d] => some (ok (.long (JLong.ushr x d ||| JLong.shl x (-d))) σ)
  | "java.lang.Integer", "bitCount", [_], [.int x] =>
    some (okInt ((List.range 32).countP (x.getLsbD ·)) σ)
  | "java.lang.Long", "bitCount", [_], [.long x] =>
    some (okInt ((List.range 64).countP (x.getLsbD ·)) σ)
  | "java.lang.Integer", "numberOfLeadingZeros", [_], [.int x] =>
    some (okInt (32 - (if x.toNat = 0 then 0 else Nat.log2 x.toNat + 1)) σ)
  | "java.lang.Long", "numberOfLeadingZeros", [_], [.long x] =>
    some (okInt (64 - (if x.toNat = 0 then 0 else Nat.log2 x.toNat + 1)) σ)
  | "java.lang.Integer", "numberOfTrailingZeros", [_], [.int x] =>
    some (okInt (((List.range 32).find? (x.getLsbD ·)).getD 32) σ)
  | "java.lang.Long", "numberOfTrailingZeros", [_], [.long x] =>
    some (okInt (((List.range 64).find? (x.getLsbD ·)).getD 64) σ)
  | "java.lang.Integer", "highestOneBit", [_], [.int x] =>
    some (ok (.int (if x.toNat = 0 then 0 else BitVec.ofNat 32 (2 ^ Nat.log2 x.toNat))) σ)
  | "java.lang.Long", "highestOneBit", [_], [.long x] =>
    some (ok (.long (if x.toNat = 0 then 0 else BitVec.ofNat 64 (2 ^ Nat.log2 x.toNat))) σ)
  | "java.lang.Integer", "lowestOneBit", [_], [.int x] => some (ok (.int (x &&& -x)) σ)
  | "java.lang.Long", "lowestOneBit", [_], [.long x] => some (ok (.long (x &&& -x)) σ)
  | "java.util.Collections", "reverse", [_], [l] => some <| argObj σ l fun la lo => match lo with
      | .list k xs m =>
        if xs.length < 2 then okVoid σ
        else if k = .immutable then thr UOE none σ
        else okVoid (σ.setObj la (.list k xs.reverse m))
      | _ => bad "Collections.reverse of this collection kind is not modelled"
  | "java.lang.String", "join", [.cls _, .array _], [d, arr] => some <|
    if d == .null ∨ arr == .null then thrNPE σ
    else argChars σ d fun delim => argObj σ arr fun _ o => match o with
      | .array _ xs => joinWith2K P delim xs σ fun s σ' => okStr s σ'
      | _ => bad "expected an array"
  | "java.lang.String", "join", [.cls _, .cls _], [d, it] => some <|
    if d == .null ∨ it == .null then thrNPE σ
    else argChars σ d fun delim => argObj σ it fun _ o => match o with
      | .list _ xs _ => joinWith2K P delim xs σ fun s σ' => okStr s σ'
      | _ => bad "String.join of this Iterable is not modelled"
  | "java.util.Objects", "toString", [_, _], [x, d] => some <|
    if x == .null then ok d σ else valueOfObj P x σ fun s σ' => okStr s σ'
  | "java.lang.Character", "getType", [.prim .char], [.int c] => some <|
    if c.toNat < 128 then okInt (asciiType c.toNat) σ else okInt (Unicode.charType c.toNat) σ
  | "java.lang.reflect.Array", "newInstance", [.cls _, .prim .int], [c, .int n] => some <|
    argObj σ c fun _ o => match o with
      | .clazz cn =>
        let et : JType := match arrayParts cn with
          | some (e, dims) =>
            let base : JType := match e with
              | "boolean" => .prim .boolean | "byte" => .prim .byte | "char" => .prim .char
              | "short" => .prim .short | "int" => .prim .int | "long" => .prim .long
              | "float" => .prim .float | "double" => .prim .double | _ => .cls e
            (List.range dims).foldl (fun t _ => .array t) base
          | none => .cls cn
        if n.toInt < 0 then thr "java.lang.NegativeArraySizeException" (some s!"{n.toInt}") σ
        else okObj (.array et (List.replicate n.toNat et.default)) σ
      | _ => bad "expected a Class"
  | "java.lang.reflect.Array", "getLength", [_], [x] => some <|
    argObj σ x fun _ o => match o with
      | .array _ xs => okInt xs.length σ
      | _ => thr IAE (some "Argument is not an array") σ
  | "java.util.Arrays", "asList", [.array _], [arr] => some <|
    if arr == .null then thrNPE σ else okObj (.plain asListCls [((asListCls, "a"), arr)]) σ
  | "java.util.stream.Stream", "empty", [], [] => some <|
    let (src, σ') := σ.alloc (.array (.cls "java.lang.Object") [])
    okObj (.plain streamCls [((streamCls, "source"), .ref src), ((streamCls, "linked"), .int 0)]) σ'
  | "java.util.Collections", "emptySet", [], [] => some <|
    match σ.static ("java.util.Collections", "EMPTY_SET") with
    | some v => ok v σ
    | none =>
      let (e, σ') := σ.alloc (.plain emptySetCls [])
      ok (.ref e) (σ'.setStatic ("java.util.Collections", "EMPTY_SET") (.ref e))
  | "java.util.stream.Stream", "of", [.array _], [arr] => some <|
    if arr == .null then thrNPE σ
    else okObj (.plain streamCls [((streamCls, "source"), arr), ((streamCls, "linked"), .int 0)]) σ
  | "java.util.stream.Stream", "of", [.cls _], [x] => some <|
    let (src, σ') := σ.alloc (.array (.cls "java.lang.Object") [x])
    okObj (.plain streamCls [((streamCls, "source"), .ref src), ((streamCls, "linked"), .int 0)]) σ'
  | "java.lang.Character$UnicodeBlock", "forName", [_], [nm] => some <|
    if nm == .null then thrNPE σ
    else argStr σ nm fun t =>
      if !JStr.isAscii t then bad "UnicodeBlock.forName with non-ASCII text is not modelled"
      else
        let u := JStr.toLean (JStr.asciiUpper t)
        match unicodeBlocks.find? (fun (n, al, _, _) => n == u || al.contains u) with
        | some (n, _, _, _) => let (v, σ') := ublockObj n σ; ok v σ'
        | none => bad s!"Unicode block {u} is not modelled"
  | "java.lang.Character$UnicodeBlock", "of", [.prim _], [.int cp] => some <|
    if cp.toInt < 0 ∨ cp.toInt > 0x10FFFF then bad "UnicodeBlock.of an invalid code point is not modelled"
    else match unicodeBlocks.find? (fun (_, _, lo, hi) => lo ≤ cp.toNat ∧ cp.toNat ≤ hi) with
      | some (n, _, _, _) => let (v, σ') := ublockObj n σ; ok v σ'
      | none => bad "UnicodeBlock.of beyond the first Unicode blocks is not modelled"
  | "java.lang.Character", "charCount", [.prim .int], [.int cp] => some (okInt (if cp.toInt ≥ 0x10000 then 2 else 1) σ)
  | "java.lang.Character", "isHighSurrogate", [.prim .char], [.int c] => some (okBool (isHighSurr (c.setWidth 16)) σ)
  | "java.lang.Character", "isLowSurrogate", [.prim .char], [.int c] => some (okBool (isLowSurr (c.setWidth 16)) σ)
  | "java.lang.Character", "isSurrogate", [.prim .char], [.int c] =>
    some (okBool (0xD800 ≤ c.toNat ∧ c.toNat ≤ 0xDFFF) σ)
  | "java.lang.Character", "isSurrogatePair", [_, _], [.int h, .int l] =>
    some (okBool (isHighSurr (h.setWidth 16) && isLowSurr (l.setWidth 16)) σ)
  | "java.lang.Character", "toCodePoint", [_, _], [.int h, .int l] =>
    some (okInt ((h.toNat : Int) * 1024 + l.toNat - 56613888) σ)
  | "java.lang.Character", "isSupplementaryCodePoint", [_], [.int cp] =>
    some (okBool (0x10000 ≤ cp.toInt ∧ cp.toInt < 0x110000) σ)
  | "java.lang.Character", "isBmpCodePoint", [_], [.int cp] => some (okBool (0 ≤ cp.toInt ∧ cp.toInt < 0x10000) σ)
  | "java.lang.Character", "isValidCodePoint", [_], [.int cp] => some (okBool (0 ≤ cp.toInt ∧ cp.toInt ≤ 0x10FFFF) σ)
  | "java.lang.Character", "isISOControl", [.prim .char], [.int cp] | "java.lang.Character", "isISOControl", [.prim .int], [.int cp] =>
    some (okBool (0 ≤ cp.toInt ∧ (cp.toInt ≤ 0x1F ∨ (0x7F ≤ cp.toInt ∧ cp.toInt ≤ 0x9F))) σ)
  | "java.lang.Character", "codePointAt", [.cls _, .prim .int], [seq, .int i] => some <|
    argSeq σ seq fun latin s => seqCharAt latin s i σ fun c => okInt (codePointAtJ s i.toNat c) σ
  | "java.lang.Character", "codePointBefore", [.cls _, .prim .int], [seq, .int i] => some <|
    argSeq σ seq fun latin s => codePointBeforeSeq latin s i σ fun cp => okInt cp σ
  | "java.lang.Character", "getType", [.prim .int], [.int cp] => some <|
    if 0 ≤ cp.toInt ∧ cp.toInt < 128 then okInt (asciiType cp.toNat) σ
    else if 0 ≤ cp.toInt ∧ cp.toInt ≤ 0x10FFFF then okInt (Unicode.charType cp.toNat) σ else okInt 0 σ
  | "java.lang.Character", "toUpperCase", [.prim .int], [.int cp] => some <|
    if 0 ≤ cp.toInt ∧ cp.toInt < 128 then okInt (if 97 ≤ cp.toInt ∧ cp.toInt ≤ 122 then cp.toInt - 32 else cp.toInt) σ
    else if 0 ≤ cp.toInt ∧ cp.toInt ≤ 0x10FFFF then okInt (Unicode.toUpper cp.toNat) σ else okInt cp.toInt σ
  | "java.lang.Character", "toTitleCase", [.prim .char], [.int cp] | "java.lang.Character", "toTitleCase", [.prim .int], [.int cp] =>
    some <|
    if 0 ≤ cp.toInt ∧ cp.toInt < 128 then okInt (if 97 ≤ cp.toInt ∧ cp.toInt ≤ 122 then cp.toInt - 32 else cp.toInt) σ
    else if 0 ≤ cp.toInt ∧ cp.toInt ≤ 0x10FFFF then okInt (Unicode.toTitle cp.toNat) σ
    else okInt cp.toInt σ
  | "java.lang.Character", "toLowerCase", [.prim .int], [.int cp] => some <|
    if 0 ≤ cp.toInt ∧ cp.toInt < 128 then okInt (if 65 ≤ cp.toInt ∧ cp.toInt ≤ 90 then cp.toInt + 32 else cp.toInt) σ
    else if 0 ≤ cp.toInt ∧ cp.toInt ≤ 0x10FFFF then okInt (Unicode.toLower cp.toNat) σ else okInt cp.toInt σ
  | "java.lang.Character", "compare", [.prim .char, .prim .char], [.int x, .int y] =>
    some (okInt ((x.toNat : Int) - y.toNat) σ)
  | "java.lang.Character", "toChars", [.prim .int], [.int cp] => some <|
    if 0 ≤ cp.toInt ∧ cp.toInt ≤ 0x10FFFF then
      okObj (.array (.prim .char) ((encodeCp cp.toNat).map fun c => .int (c.zeroExtend 32))) σ
    else thr IAE (some s!"Not a valid Unicode code point: 0x{hexUpper cp.toNat}") σ
  | "java.lang.Character", "codePointAt", [.array (.prim .char), .prim .int], [arr, .int i] => some <|
    argObj σ arr fun _ o => match o with
      | .array _ xs =>
        if 0 ≤ i.toInt ∧ i.toInt < xs.length then
          match (charsOf xs)[i.toNat]? with
          | some c => okInt (codePointAtJ (charsOf xs) i.toNat c) σ
          | none => bad "index"
        else thr "java.lang.ArrayIndexOutOfBoundsException"
          (some s!"Index {i.toInt} out of bounds for length {xs.length}") σ
      | _ => bad "expected char[]"
  | "java.lang.Character", "codePointCount", [.cls _, .prim .int, .prim .int], [seq, .int b, .int e] => some <|
    argChars σ seq fun s =>
      if b.toInt < 0 ∨ e.toInt > s.length ∨ b.toInt > e.toInt then thr IOOBE none σ
      else okInt (cpCount ((s.take e.toNat).drop b.toNat)) σ
  | "java.lang.Character", "codePointCount", [.array (.prim .char), .prim .int, .prim .int], [arr, .int off, .int cnt] =>
    some <|
    argObj σ arr fun _ o => match o with
      | .array _ xs =>
        if cnt.toInt > xs.length - off.toInt ∨ off.toInt < 0 ∨ cnt.toInt < 0 then thr IOOBE none σ
        else okInt (cpCount (((charsOf xs).drop off.toNat).take cnt.toNat)) σ
      | _ => bad "expected char[]"
  | "java.lang.Character", n, [.prim .int], [.int cp] =>
    if 0 ≤ cp.toInt ∧ cp.toInt < 128 then (asciiPred n cp.toNat).map fun b => okBool b σ
    else if 0 ≤ cp.toInt ∧ cp.toInt ≤ 0x10FFFF then
      match uniPred n cp.toNat with
      | some b => some (okBool b σ)
      | none => (asciiPred n 0).map fun _ => bad s!"Character.{n} beyond ASCII is not modelled"
    else (asciiPred n 0).map fun _ => okBool false σ
  -- `Character.isX(char c)` is `isX((int) c)`
  | "java.lang.Character", n, [.prim .char], [.int c] =>
    if c.toNat < 128 then (asciiPred n c.toNat).map fun b => okBool b σ
    else match uniPred n c.toNat with
      | some b => some (okBool b σ)
      | none => (asciiPred n 0).map fun _ => bad s!"Character.{n} beyond ASCII is not modelled"
  | "java.util.Objects", "checkFromToIndex", [_, _, _], [.int f, .int t, .int n] => some <|
    if f.toInt < 0 ∨ f.toInt > t.toInt ∨ t.toInt > n.toInt then
      thr IOOBE (some s!"Range [{f.toInt}, {t.toInt}) out of bounds for length {n.toInt}") σ
    else okInt f.toInt σ
  | "jdk.internal.util.ArraysSupport", "newLength", [_, _, _], [.int o, .int mi, .int pr] => some <|
    -- `prefLength` may overflow; then the minimum growth decides (`hugeLength`)
    let soft : Int := 2147483647 - 8
    let pref := (BitVec.ofInt 32 (o.toInt + max mi.toInt pr.toInt)).toInt
    if 0 < pref ∧ pref ≤ soft then okInt pref σ
    else
      let minLen := (BitVec.ofInt 32 (o.toInt + mi.toInt)).toInt
      if minLen < 0 then thr "java.lang.OutOfMemoryError"
        (some s!"Required array length {o.toInt} + {mi.toInt} is too large") σ
      else okInt (if minLen ≤ soft then soft else minLen) σ
  | "org.junit.jupiter.api.Assertions", n, ps, vs => jupiterAssert P n ps vs σ
  | "org.junit.Assert", n, ps, vs => junit4Assert P n ps vs σ
  | _, _, _, _ => none

/-! ### Static fields of library classes -/

def libStatic (f : FieldSig) (σ : State) : Option EvOut :=
  match f.cls, f.name with
  | "java.lang.System", "out" =>
    match σ.static ("java.lang.System", "out") with
    | some v => some (.ok v σ)
    | none => let (a, σ') := σ.alloc (.stream 1)
      some (.ok (.ref a) (σ'.setStatic ("java.lang.System", "out") (.ref a)))
  | "java.lang.System", "err" =>
    match σ.static ("java.lang.System", "err") with
    | some v => some (.ok v σ)
    | none => let (a, σ') := σ.alloc (.stream 2)
      some (.ok (.ref a) (σ'.setStatic ("java.lang.System", "err") (.ref a)))
  | "java.math.BigDecimal", "ZERO" => some (retObj (.dec ⟨0, 0⟩) σ)
  | "java.math.BigDecimal", "ONE" => some (retObj (.dec ⟨1, 0⟩) σ)
  | "java.math.BigDecimal", "TWO" => some (retObj (.dec ⟨2, 0⟩) σ)
  | "java.math.BigDecimal", "TEN" => some (retObj (.dec ⟨10, 0⟩) σ)
  | "java.math.BigInteger", "ZERO" => some (retObj (.bigInt 0) σ)
  | "java.math.BigInteger", "ONE" => some (retObj (.bigInt 1) σ)
  | "java.math.BigInteger", "TWO" => some (retObj (.bigInt 2) σ)
  | "java.math.BigInteger", "TEN" => some (retObj (.bigInt 10) σ)
  | "java.math.RoundingMode", n => (RoundingMode.ofName? n).map fun r => retObj (.rmode r) σ
  | "java.math.MathContext", "DECIMAL32" => some (retObj (.mctx .DECIMAL32) σ)
  | "java.math.MathContext", "DECIMAL64" => some (retObj (.mctx .DECIMAL64) σ)
  | "java.math.MathContext", "DECIMAL128" => some (retObj (.mctx .DECIMAL128) σ)
  | "java.math.MathContext", "UNLIMITED" => some (retObj (.mctx .UNLIMITED) σ)
  | "java.lang.Boolean", "TRUE" => some (retObj (.boxed "java.lang.Boolean" (.int 1)) σ)
  | "java.lang.Boolean", "FALSE" => some (retObj (.boxed "java.lang.Boolean" (.int 0)) σ)
  | "java.lang.Integer", "MAX_VALUE" => some (.ok (.int JInt.MAX) σ)
  | "java.lang.Integer", "MIN_VALUE" => some (.ok (.int JInt.MIN) σ)
  | "java.lang.Long", "MAX_VALUE" => some (.ok (.long JLong.MAX) σ)
  | "java.lang.Long", "MIN_VALUE" => some (.ok (.long JLong.MIN) σ)
  | _, _ => none

/-! ### `invokedynamic` with library bootstrap methods: records -/

def hashCodeSig : MethodSig := ⟨"java.lang.Object", .prim .int, "hashCode", []⟩

/-- The instance field read by a `REF_GET_FIELD` method handle constant (rendered by the
    parser as `REF_GET_FIELD <C: T f>`), resolved: its key and declared type. -/
def getterField? (P : Program) (h : String) : Option (FieldKey × JType) :=
  let pre := "REF_GET_FIELD <".toList
  let cs := h.toList
  if cs.take pre.length != pre then none else
  match (cs.drop pre.length).reverse with
  | '>' :: rb =>
    let (c, rest) := rb.reverse.span (· != ':')
    let n := String.ofList (rest.reverse.takeWhile (· != ' ')).reverse
    match P.resolveFieldN P.fuel (String.ofList c) n with
    | some (dc, fd) => if fd.isStatic then none else some ((dc, n), fd.ty)
    | none => none
  | _ => none

/-- The record components named by the bootstrap's getter handles, in order. -/
def recordComps (P : Program) (σ : State) : List Value → Option (List (FieldKey × JType))
  | [] => some []
  | h :: hs =>
    match objAt σ h with
    | some (_, .clazz d) =>
      match getterField? P d, recordComps P σ hs with
      | some f, some fs => some (f :: fs)
      | _, _ => none
    | _ => none

/-- `names.split(";")` for the bootstrap's component-name string. -/
def splitSemis : JStr → List JStr
  | [] => [[]]
  | c :: cs =>
    if c == 59 then [] :: splitSemis cs
    else match splitSemis cs with
      | w :: ws => (c :: w) :: ws
      | [] => [[c]]

/-- `Integer.hashCode(int)`, `Long.hashCode(long)`, `Boolean.hashCode(boolean)`, ... of a
    primitive of type `t` (`Float`/`Double`: of the canonical bits, as `floatToIntBits`). -/
def primHash (t : JType) (v : Value) : Option I32 :=
  match t, v with
  | .prim .boolean, .int x => some (if x ≠ 0 then 1231 else 1237)
  | .prim .long, .long x => some (JLong.toInt (x ^^^ (x >>> 32)))
  | .prim .float, .float x => some (if JFloat.isNaN32 x then JFloat.nan32 else x)
  | .prim .double, .double x =>
    let b := if JFloat.isNaN64 x then JFloat.nan64 else x
    some (JLong.toInt (b ^^^ (b >>> 32)))
  | .prim _, .int x => some x
  | _, _ => none

/-- The primitive type of a box class. -/
def boxedPrim : ClassName → Option JType
  | "java.lang.Integer" => some (.prim .int)
  | "java.lang.Long" => some (.prim .long)
  | "java.lang.Short" => some (.prim .short)
  | "java.lang.Byte" => some (.prim .byte)
  | "java.lang.Character" => some (.prim .char)
  | "java.lang.Boolean" => some (.prim .boolean)
  | "java.lang.Float" => some (.prim .float)
  | "java.lang.Double" => some (.prim .double)
  | _ => none

/-- `Objects.hashCode(v)`: `0` for `null`, the model's `hashCode` for library value objects, a
    call of `hashCode()` for application objects, and any value for identity hash codes. -/
def hashK (P : Program) (v : Value) (σ : State) (k : I32 → State → NRes) : NRes :=
  match v with
  | .null => k 0 σ
  | .ref a =>
    match σ.heap a with
    | some (.str s) => k (JStr.hashCode s) σ
    | some (.dec d) => k d.hashCode σ
    | some (.bigInt i) => k (BigDec.bigIntHash i) σ
    | some (.boxed c w) =>
      match (boxedPrim c).bind (primHash · w) with
      | some h => k h σ
      | none => bad "hashCode of this box is not modelled"
    | some (.plain c _) =>
      if P.isProgClass c then
        .call hashCodeSig (.virtual c) [v] σ fun out => match out with
          | .normal (some (.int r)) σ' => k r σ'
          | .normal _ _ => bad "hashCode returned no int"
          | .exc e σ' => .ret (.thr e σ')
          | .wrong msg => bad msg
      else .choose fun h => k (BitVec.ofNat 32 h) σ
    | some (.array ..) | some (.builder ..) | some (.clazz _) | some (.rmode _) | some (.stream _) =>
      .choose fun h => k (BitVec.ofNat 32 h) σ
    | some _ => bad "hashCode of this library object kind is not modelled"
    | none => bad "dangling reference"
  | _ => bad "expected reference"

/-- The `name=value` parts of a record's `toString`, separated by `", "`; components rendered by
    `String.valueOf`, from the first to the last. -/
def recordStrK (P : Program) (fs : List (FieldKey × Value)) :
    List (JStr × FieldKey × JType) → State → (JStr → State → NRes) → NRes
  | [], σ, k => k [] σ
  | (nm, key, ty) :: rest, σ, k =>
    match Fields.get fs key with
    | none => bad "record object has no such field"
    | some v => valueOfArg P ty v σ fun s σ' =>
      match rest with
      | [] => k (nm ++ jstr "=" ++ s) σ'
      | _ => recordStrK P fs rest σ' fun t σ'' => k (nm ++ jstr "=" ++ s ++ jstr ", " ++ t) σ''

/-- A record's `hashCode`: `h = 31 * h + hash(c)` over the components from the first to the
    last. -/
def recordHashK (P : Program) (fs : List (FieldKey × Value)) :
    List (FieldKey × JType) → I32 → State → (I32 → State → NRes) → NRes
  | [], h, σ, k => k h σ
  | (key, ty) :: rest, h, σ, k =>
    match Fields.get fs key with
    | none => bad "record object has no such field"
    | some v =>
      if ty.isRef then hashK P v σ fun x σ' => recordHashK P fs rest (h * 31 + x) σ' k
      else match primHash ty v with
        | some x => recordHashK P fs rest (h * 31 + x) σ k
        | none => bad "record component of unknown type"

/-- Componentwise equality of two records (in the order given; stops at the first difference):
    `Objects.equals` for references, `==` for primitives (`Float.compare`/`Double.compare` for
    floating-point, i.e. equal canonical bits). -/
def recordEqK (P : Program) (fs gs : List (FieldKey × Value)) :
    List (FieldKey × JType) → State → (Bool → State → NRes) → NRes
  | [], σ, k => k true σ
  | (key, ty) :: rest, σ, k =>
    match Fields.get fs key, Fields.get gs key with
    | some v, some w =>
      if ty.isRef then
        equalsK P true σ v w fun b σ' => if b then recordEqK P fs gs rest σ' k else k false σ'
      else if canonBits v == canonBits w then recordEqK P fs gs rest σ k else k false σ
    | _, _ => bad "record object has no such field"

/-- The call sites `javac` emits for a record's `toString`, `hashCode` and `equals`
    (`ObjectMethods.bootstrap` with the record class, the component names `"a;b;c"` and one
    `REF_GET_FIELD` handle per component), as the JDK's method handles compute them:
    * `toString`: `Name[a=1, b=x]` (simple class name; components by `String.valueOf`);
    * `hashCode`: `h = 31 * h + hash(c)` from `h = 0`;
    * `equals`: true for the same object; otherwise false unless the argument is an instance of
      the record class, then componentwise, from the last component to the first (the order of
      the JDK's `guardWithTest` chain). -/
def recordMethod (P : Program) (name : String) (args bsmArgs : List Value) (σ : State) : NRes :=
  match bsmArgs with
  | rc :: nm :: hs =>
    match objAt σ rc, strOf σ nm, recordComps P σ hs with
    | some (_, .clazz recCls), some names, some comps =>
      let names := if names.isEmpty then [] else splitSemis names
      if names.length != comps.length then bad "record component names and getters do not match"
      else match name, args with
        | "toString", [self] =>
          match objAt σ self with
          | some (_, .plain _ fs) =>
            recordStrK P fs (names.zip comps) σ fun s σ' =>
              okStr (jstr (simpleNameOf recCls) ++ jstr "[" ++ s ++ jstr "]") σ'
          | _ => bad "record toString on a non-record"
        | "hashCode", [self] =>
          match objAt σ self with
          | some (_, .plain _ fs) => recordHashK P fs comps 0 σ fun h σ' => ok (.int h) σ'
          | _ => bad "record hashCode on a non-record"
        | "equals", [self, other] =>
          if self == other then okBool true σ
          else match objAt σ self, objAt σ other with
            | some (_, .plain _ fs), some (_, .plain c gs) =>
              if P.isSubclass c recCls == some true then
                recordEqK P fs gs comps.reverse σ fun b σ' => okBool b σ'
              else okBool false σ
            | some (_, .plain _ _), _ => okBool false σ
            | _, _ => bad "record equals on a non-record"
        | _, _ => bad s!"ObjectMethods.bootstrap for {name} is not modelled"
    | _, _, _ => bad "ObjectMethods.bootstrap arguments"
  | _ => bad "ObjectMethods.bootstrap arguments"

/-- `invokedynamic` with a bootstrap method the semantics does not handle itself (it handles
    string concatenation): records' `ObjectMethods.bootstrap`; `none` for the others. -/
def dynCall (P : Program) (name : String) (_params : List JType) (args : List Value)
    (bsm : MethodSig) (bsmArgs : List Value) (σ : State) : Option NRes :=
  if bsm.cls == "java.lang.runtime.ObjectMethods" ∧ bsm.name == "bootstrap" then
    some (recordMethod P name args bsmArgs σ)
  else none

end Native
end Jimple
