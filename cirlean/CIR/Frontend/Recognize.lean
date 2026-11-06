import CIR.Module

/-!
  Recognition of C++ standard library functions that have a native model.

  The frontend calls `recognize` once per `cir.func`; a `some m` result is
  stored in `FuncDecl.model`. This file is the trusted name-to-model table.

  Recognition works on the demangled name (libc++ `std::__1::…` and
  libstdc++ `std::…`, `std::__cxx11::…`, `__gnu_cxx::…`), and is always
  confirmed against the CIR signature (argument count, pointer/value
  arguments, element types) before a model is returned. When `c++filt`
  could not demangle a symbol (libc++ constrained template constructors), a
  structural fallback uses the constructor/destructor marker, the record of
  `this` and the parameter types. Only element types the models handle
  soundly are accepted: integers, floating point, pointers (and `bool`,
  except for the bit-packed `std::vector<bool>`). When in doubt the result
  is `none`: the body is then executed, or the call is undefined, which is
  always sound.
-/

namespace CIR.Frontend

/-- What the frontend knows about a function when asking for a model. -/
structure FuncInfo where
  /-- Mangled symbol. -/
  sym       : String
  /-- `c++filt` output (empty when demangling failed or is unavailable). -/
  demangled : String
  params    : List Ty
  ret       : Ty
  special   : SpecialMember
  /-- Record declarations of the module, to inspect class names. -/
  records   : List RecordDecl

/-! ### Text utilities over character lists -/

def trimS (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

def dropS (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

def dropRightS (s : String) (n : Nat) : String :=
  String.ofList (s.toList.take (s.length - n))

def dropRightWhileS (s : String) (p : Char → Bool) : String :=
  String.ofList (s.toList.reverse.dropWhile p).reverse

def frontS (s : String) : Char := s.toList.headD ' '

/-- Remove every `[abi:…]` tag. -/
def stripAbiTags (s : String) : String :=
  let rec go : List Char → Bool → List Char
    | [], _ => []
    | c :: rest, true => if c == ']' then go rest false else go rest true
    | '[' :: 'a' :: 'b' :: 'i' :: ':' :: rest, false => go rest true
    | c :: rest, false => c :: go rest false
  String.ofList (go s.toList false)

/-- Split at top-level occurrences of `sep` (outside `<…>`, `(…)`, `[…]`). -/
def splitTop (s : String) (sep : Char) : List String :=
  let rec go : List Char → Nat → List Char → List String → List String
    | [], _, cur, acc => (acc ++ [String.ofList cur.reverse])
    | c :: cs, d, cur, acc =>
      if c == sep && d == 0 then go cs d [] (acc ++ [String.ofList cur.reverse])
      else
        let d' := if c == '<' || c == '(' || c == '[' then d + 1
          else if (c == '>' || c == ')' || c == ']') && d > 0 then d - 1 else d
        go cs d' (c :: cur) acc
  (go s.toList 0 [] []).map trimS

/-- Split a qualified name at top-level `::`. -/
def splitScope (s : String) : List String :=
  let rec go : List Char → Nat → List Char → List String → List String
    | [], _, cur, acc => acc ++ [String.ofList cur.reverse]
    | ':' :: ':' :: cs, 0, cur, acc => go cs 0 [] (acc ++ [String.ofList cur.reverse])
    | c :: cs, d, cur, acc =>
      let d' := if c == '<' || c == '(' then d + 1
        else if (c == '>' || c == ')') && d > 0 then d - 1 else d
      go cs d' (c :: cur) acc
  go s.toList 0 [] []

/-- The name without its top-level template argument list. -/
def stripTemplate (s : String) : String :=
  trimS (String.ofList (s.toList.takeWhile (· != '<')))

/-- Top-level template arguments of `X<a, b<c>>`. -/
def templateArgs (s : String) : List String :=
  match s.toList.dropWhile (· != '<') with
  | '<' :: rest =>
    -- drop the final `>` that closes the list
    let inner := rest.reverse.dropWhile (· == ' ') |>.drop 1 |>.reverse
    splitTop (String.ofList inner) ','
  | _ => []

/-- `std::__1::x` and `std::__cxx11::x` become `std::x`. -/
def normalizeNs (s : String) : String :=
  let parts := (splitScope s).filter fun p => p != "__1" && p != "__cxx11"
  "::".intercalate parts

/-- A parsed demangled function name. -/
structure DName where
  /-- Qualifier: enclosing class (with template arguments) or namespace. -/
  qual   : String
  /-- Function name without template arguments (`push_back`, `operator==`,
  `vector` for a constructor, `~vector` for a destructor). -/
  fname  : String
  /-- Parameter types as written. -/
  params : List String
  /-- Trailing qualifiers (` const`, ` &`, ` const &`, …). -/
  quals  : String
  deriving Repr, Inhabited

/-- Index of the `(` matching the `)` at index `close`. -/
def matchingOpen (cs : Array Char) (close : Nat) : Option Nat := Id.run do
  let mut d : Nat := 0
  let mut i := close + 1
  while i > 0 do
    i := i - 1
    let c := cs[i]!
    if c == ')' then d := d + 1
    else if c == '(' then
      d := d - 1
      if d == 0 then return some i
  return none

/-- Start of the last top-level space-separated token of `cs[0:stop]`
(respecting `<…>` and `(…)`). -/
def lastTokenStart (cs : Array Char) (stop : Nat) : Nat := Id.run do
  let mut d : Nat := 0
  let mut i := stop
  while i > 0 do
    let c := cs[i - 1]!
    if c == '>' || c == ')' then d := d + 1
    else if (c == '<' || c == '(') && d > 0 then d := d - 1
    else if c == ' ' && d == 0 then return i
    i := i - 1
  return 0

/-- The operator symbol at the start of `r` (the text after `operator`),
followed either by nothing or by a template argument list. -/
def operatorSymbol (r : String) : String :=
  let syms := ["<=>", "<<=", ">>=", "<<", ">>", "<=", ">=", "==", "!=", "->*", "->", "++", "--",
    "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "&&", "||", "()", "[]", "<", ">", "+", "-",
    "*", "/", "%", "&", "|", "^", "~", "!", "=", ","]
  -- keep the symbol whose remainder is empty or a template argument list
  let ok (sym : String) : Bool :=
    r.startsWith sym &&
      (let rest := trimS (dropS r sym.length)
       rest.isEmpty || (rest.startsWith "<" && rest.endsWith ">"))
  match syms.find? ok with
  | some s => s
  | none => trimS r  -- `operator bool`, `operator new`, …

/-- Parse a demangled function name. -/
def parseDemangled (d : String) : Option DName := do
  let d := trimS (stripAbiTags d)
  let cs := d.toList.toArray
  -- the parameter list is the last top-level parenthesised group
  let close ← (List.range cs.size).reverse.find? fun i => cs[i]! == ')'
  let opn ← matchingOpen cs close
  let quals := String.ofList (cs.toList.drop (close + 1))
  let params := String.ofList ((cs.toList.drop (opn + 1)).take (close - opn - 1))
  let params := if (trimS params).isEmpty || trimS params == "void" then [] else splitTop params ','
  let pre := cs.toList.take opn
  let preS := String.ofList pre
  -- operator names may contain unbalanced `<`, `>`, spaces
  let opPos := (List.range pre.length).reverse.find? fun i =>
    (String.ofList (pre.drop i)).startsWith "operator" &&
      (i == 0 || pre[i - 1]! == ':' || pre[i - 1]! == ' ')
  match opPos with
  | some k =>
    let name := String.ofList (pre.drop k)
    let qualPart := pre.take k
    let qualPart := if qualPart.length ≥ 2 && qualPart.getLast? == some ':' then
        qualPart.take (qualPart.length - 2) else qualPart
    let qa := qualPart.toArray
    let qual := String.ofList (qualPart.drop (lastTokenStart qa qa.size))
    let sym := operatorSymbol (dropS name "operator".length)
    let fname := if (frontS sym).isAlpha then "operator " ++ sym else "operator" ++ sym
    return { qual := qual, fname := fname, params := params, quals := quals }
  | none =>
    let pa := pre.toArray
    let full := String.ofList (pre.drop (lastTokenStart pa pa.size))
    let comps := splitScope full
    let last := comps.getLast?.getD ""
    let qual := "::".intercalate (comps.take (comps.length - 1))
    let _ := preS
    return { qual := qual, fname := stripTemplate last, params := params, quals := quals }

/-! ### Types -/

/-- CIR type of a scalar C++ type name (`int`, `unsigned long`, `char*`, …). -/
def cppScalarTy (s : String) : Option Ty :=
  let s := trimS s
  if s.endsWith "*" then some (.ptr (.other (trimS (dropRightS s 1)))) else
  match s with
  | "bool" => some .bool
  | "char" | "signed char" => some (.int true 8)
  | "unsigned char" => some (.int false 8)
  | "short" => some (.int true 16)
  | "unsigned short" => some (.int false 16)
  | "int" => some (.int true 32)
  | "unsigned int" => some (.int false 32)
  | "long" | "long long" => some (.int true 64)
  | "unsigned long" | "unsigned long long" => some (.int false 64)
  | "float" => some (.float .single)
  | "double" => some (.float .double)
  | _ => none

/-- Element type of a contiguous iterator `X<T*, …>` or `X<T const*, …>`. -/
def iterElemTy (qual : String) : Option Ty := do
  let a ← (templateArgs qual).head?
  let a := trimS a
  guard (a.endsWith "*")
  let t := trimS (dropRightS a 1)
  let t := if t.endsWith " const" then trimS (dropRightS t 6) else t
  let t := if t.startsWith "const " then trimS (dropS t 6) else t
  cppScalarTy t

/-- Types the library models handle soundly as elements. -/
def scalarElem : Ty → Bool
  | .int .. | .bool | .float _ | .ptr _ => true
  | _ => false

def isPtr : Ty → Bool
  | .ptr _ => true
  | _ => false

def isInt : Ty → Bool
  | .int .. => true
  | _ => false

def isBoolTy : Ty → Bool
  | .bool => true
  | _ => false

def isVoid : Ty → Bool
  | .void => true
  | _ => false

def isRecordTy : Ty → Bool
  | .record _ => true
  | _ => false

def ptrToRecord? : Ty → Option String
  | .ptr (.record n) => some n
  | _ => none

/-- Pointer to `t` (compared structurally on scalars). -/
def ptrTo (p t : Ty) : Bool :=
  match p, t with
  | .ptr (.int s w), .int s' w' => s == s' && w == w'
  | .ptr .bool, .bool => true
  | .ptr (.float k), .float k' => k == k'
  | .ptr (.ptr _), .ptr _ => true
  | _, _ => false

/-- Same record type. -/
def sameRec (a b : Ty) : Bool :=
  match a, b with
  | .record x, .record y => x == y
  | .ptr (.record x), .ptr (.record y) => x == y
  | _, _ => false

/-- A contiguous iterator class (`std::__wrap_iter<T*>`, `__gnu_cxx::__normal_iterator<T*, C>`). -/
def isContigIterClass (n : String) : Bool :=
  let base := normalizeNs (stripTemplate n)
  base == "std::__wrap_iter" || base == "__gnu_cxx::__normal_iterator"

/-- An iterator parameter over elements of type `e`: `T*` / `const T*`, or a contiguous iterator
over `T`. -/
def iterOver (t e : Ty) : Bool :=
  ptrTo t e ||
    match t with
    | .record n => isContigIterClass n && (iterElemTy n).any fun x => ptrTo (.ptr x) e
    | _ => false

/-- A spelling of `char*` / `const char*`. -/
def charPtrSpelling (a : String) : Bool :=
  let a := trimS a
  a.endsWith "*" &&
    (let t := trimS (dropRightS a 1)
     let t := if t.endsWith " const" then trimS (dropRightS t 6) else t
     let t := if t.startsWith "const " then trimS (dropS t 6) else t
     t == "char")

/-- The iterator parameter of a `std::basic_string<char>` range constructor: a `char` pointer or a
contiguous iterator over `char` (`some false`), or a `std::reverse_iterator` over one
(`some true`). -/
def charIterKind? : Ty → Option Bool
  | t@(.ptr _) => if ptrTo t (.int true 8) then some false else none
  | .record n =>
    if isContigIterClass n then
      if iterElemTy n == some (.int true 8) then some false else none
    else if normalizeNs (stripTemplate n) == "std::reverse_iterator" then
      let a := (templateArgs n).head?.getD ""
      if charPtrSpelling a || isContigIterClass a && iterElemTy a == some (.int true 8) then some true
      else none
    else none
  | _ => none

/-- `basic_string(first, last[, alloc])` from the CIR parameters after `this` (`a`, `b`: one
iterator type). -/
def strRangeCtor? (a b : Ty) : Option Model := do
  guard (a == b)
  let rev ← charIterKind? a
  pure (.strCtorRange rev)

/-- An `allocator<…> const&` parameter. -/
def isAllocRef (a : Ty) : Bool :=
  (ptrToRecord? a).any fun r => normalizeNs (stripTemplate r) == "std::allocator"

/-- A `std::basic_string<char>` record, also under libc++'s and libstdc++'s typedef name
`std::string` (as clang names the record). -/
def isCharStringRec (n : String) : Bool :=
  let base := normalizeNs (stripTemplate n)
  base == "std::string" || base == "std::basic_string" && (templateArgs n).head? == some "char"

/-! ### Recognition -/

/-- Constructor kinds of a parameter written as `X const&` / `X&&`. -/
def isConstRef (p : String) : Bool := p.endsWith "const&" || p.endsWith "const &"
def isRvalRef (p : String) : Bool := p.endsWith "&&"

/-- The `std::vector<T>` models. -/
def recognizeVector (dn : DName) (e : Ty) (fi : FuncInfo) : Option Model := do
  guard (scalarElem e && !isBoolTy e)
  let ps := fi.params
  let this ← ps.head?
  guard (isPtr this)
  let n := ps.length
  let r := fi.ret
  match dn.fname with
  | "vector" =>
    match dn.params with
    | [] => guard (n == 1); pure (.vecCtor e)
    | [p] =>
      if p.startsWith "std::initializer_list" then
        guard (n == 2 && isRecordTy ps[1]!); pure (.vecInitListCtor e)
      else if p == "unsigned long" then
        guard (n == 2 && isInt ps[1]!); pure (.vecSizeCtor e)
      else if p.startsWith "std::" && isConstRef p then
        guard (n == 2 && sameRec this ps[1]!); pure (.vecCopyCtor e)
      else if p.startsWith "std::" && isRvalRef p then
        guard (n == 2 && sameRec this ps[1]!); pure (.vecMoveCtor e)
      else none
    | [p, q] =>
      if p.startsWith "std::initializer_list" && q.startsWith "std::allocator" then
        guard (n == 3 && isRecordTy ps[1]!); pure (.vecInitListCtor e)
      else if p == "unsigned long" && q.startsWith "std::allocator" then
        guard (n == 3 && isInt ps[1]!); pure (.vecSizeCtor e)
      else if p == "unsigned long" && isConstRef q then
        guard (n == 3 && isInt ps[1]! && ptrTo ps[2]! e); pure (.vecFillCtor e)
      else if p == q then
        guard (n == 3 && ps[1]! == ps[2]! && iterOver ps[1]! e); pure (.vecRangeCtor e)
      else none
    | [p, q, a] =>
      if p == "unsigned long" && isConstRef q && a.startsWith "std::allocator" then
        guard (n == 4 && isInt ps[1]! && ptrTo ps[2]! e); pure (.vecFillCtor e)
      else if p == q && a.startsWith "std::allocator" then
        guard (n == 4 && ps[1]! == ps[2]! && iterOver ps[1]! e); pure (.vecRangeCtor e)
      else none
    | _ => none
  | "~vector" => guard (n == 1); pure (.vecDtor e)
  | "operator=" =>
    let p ← dn.params.head?
    if p.startsWith "std::initializer_list" then
      guard (n == 2 && isRecordTy ps[1]! && sameRec this r); pure (.vecAssignInitList e)
    else do
      guard (n == 2 && sameRec this ps[1]!)
      if isRvalRef p then pure (.vecMoveAssign e)
      else if isConstRef p then pure (.vecCopyAssign e) else none
  | "assign" =>
    guard (n == 3 && isVoid r)
    match dn.params with
    | [p, q] =>
      if p == "unsigned long" && isConstRef q then
        guard (isInt ps[1]! && ptrTo ps[2]! e); pure (.vecAssignFill e)
      else
        guard (p == q && ps[1]! == ps[2]! && iterOver ps[1]! e); pure (.vecAssignRange e)
    | _ => none
  | "size" => guard (n == 1 && isInt r); pure (.vecSize e)
  | "empty" => guard (n == 1 && isBoolTy r); pure (.vecEmpty e)
  | "operator[]" => guard (n == 2 && isInt ps[1]! && ptrTo r e); pure (.vecIndex e)
  | "at" => guard (n == 2 && isInt ps[1]! && ptrTo r e); pure (.vecAt e)
  | "front" => guard (n == 1 && ptrTo r e); pure (.vecFront e)
  | "back" => guard (n == 1 && ptrTo r e); pure (.vecBack e)
  | "data" => guard (n == 1 && ptrTo r e); pure (.vecData e)
  | "begin" | "cbegin" => guard (n == 1 && isRecordTy r); pure (.vecBegin e)
  | "end" | "cend" => guard (n == 1 && isRecordTy r); pure (.vecEnd e)
  | "push_back" => guard (n == 2 && ptrTo ps[1]! e && isVoid r); pure (.vecPushBack e)
  | "emplace_back" =>
    -- one element: push_back's path (returning a reference since C++17); other constructor
    -- arguments are not modelled (the vector is a model's value, its libc++ body cannot run)
    if n == 2 && ptrTo ps[1]! e && isVoid r then pure (.vecPushBack e)
    else if n == 2 && ptrTo ps[1]! e && ptrTo r e then pure (.vecEmplaceBack e)
    else pure (.vecEmplaceOther e)
  | "pop_back" => guard (n == 1 && isVoid r); pure (.vecPopBack e)
  | "clear" => guard (n == 1 && isVoid r); pure (.vecClear e)
  | "resize" =>
    guard (isVoid r && (n == 2 && isInt ps[1]! || n == 3 && isInt ps[1]! && ptrTo ps[2]! e))
    pure (.vecResize e)
  | "reserve" => guard (n == 2 && isInt ps[1]! && isVoid r); pure (.vecReserve e)
  | "swap" => guard (n == 2 && sameRec this ps[1]! && isVoid r); pure (.vecSwap e)
  | _ => none

/-- An allocator spelling in a demangled parameter list. -/
def isAllocSpelling (p : String) : Bool :=
  p.startsWith "std::__1::allocator" || p.startsWith "std::allocator"

/-- libc++'s `std::vector<bool>` models: members of `recognizeVector`'s with `bool` elements, except
`operator[]` and `at`, which return libc++'s reference proxy, and `resize`, which takes its value
by copy (`Model.vecBool`). Iterators, `front`, `back`, `flip`, `assign(first, last)` and
`emplace_back` are not modelled: libc++'s code for them stops at the model's vector value (an
invalid read). -/
def recognizeVectorBool (dn : DName) (fi : FuncInfo) : Option Model := do
  let ps := fi.params
  let this ← ps.head?
  guard (isPtr this)
  let n := ps.length
  let r := fi.ret
  let e : Ty := .bool
  match dn.fname with
  | "vector" =>
    match dn.params with
    | [] => guard (n == 1); pure (.vecCtor e)
    | [p] =>
      if p.startsWith "std::initializer_list" then
        guard (n == 2 && isRecordTy ps[1]!); pure (.vecInitListCtor e)
      else if p == "unsigned long" then
        guard (n == 2 && isInt ps[1]!); pure (.vecSizeCtor e)
      else if isAllocSpelling p then
        guard (n == 2 && isAllocRef ps[1]!); pure (.vecCtor e)
      else if p.startsWith "std::" && isConstRef p then
        guard (n == 2 && sameRec this ps[1]!); pure (.vecCopyCtor e)
      else if p.startsWith "std::" && isRvalRef p then
        guard (n == 2 && sameRec this ps[1]!); pure (.vecMoveCtor e)
      else none
    | [p, q] =>
      if p.startsWith "std::initializer_list" && isAllocSpelling q then
        guard (n == 3 && isRecordTy ps[1]!); pure (.vecInitListCtor e)
      else if p == "unsigned long" && isAllocSpelling q then
        guard (n == 3 && isInt ps[1]!); pure (.vecSizeCtor e)
      else if p == "unsigned long" && isConstRef q then
        guard (n == 3 && isInt ps[1]! && ptrTo ps[2]! e); pure (.vecFillCtor e)
      else if p == q then
        guard (n == 3 && ps[1]! == ps[2]! && iterOver ps[1]! e); pure (.vecRangeCtor e)
      else none
    | [p, q, a] =>
      if p == "unsigned long" && isConstRef q && isAllocSpelling a then
        guard (n == 4 && isInt ps[1]! && ptrTo ps[2]! e); pure (.vecFillCtor e)
      else if p == q && isAllocSpelling a then
        guard (n == 4 && ps[1]! == ps[2]! && iterOver ps[1]! e); pure (.vecRangeCtor e)
      else none
    | _ => none
  | "~vector" => guard (n == 1); pure (.vecDtor e)
  | "operator=" =>
    let p ← dn.params.head?
    if p.startsWith "std::initializer_list" then
      guard (n == 2 && isRecordTy ps[1]! && sameRec this r); pure (.vecAssignInitList e)
    else do
      guard (n == 2 && sameRec this ps[1]!)
      if isRvalRef p then pure (.vecMoveAssign e)
      else if isConstRef p then pure (.vecCopyAssign e) else none
  | "assign" =>
    match dn.params with
    | [p, q] =>
      guard (n == 3 && isVoid r && p == "unsigned long" && isConstRef q && isInt ps[1]! && ptrTo ps[2]! e)
      pure (.vecAssignFill e)
    | _ => none
  | "size" => guard (n == 1 && isInt r); pure (.vecSize e)
  | "empty" => guard (n == 1 && isBoolTy r); pure (.vecEmpty e)
  | "operator[]" => guard (n == 2 && isInt ps[1]! && isRecordTy r); pure (.vecBool .index)
  | "at" => guard (n == 2 && isInt ps[1]! && isRecordTy r); pure (.vecBool .checkedIndex)
  | "push_back" => guard (n == 2 && ptrTo ps[1]! e && isVoid r); pure (.vecPushBack e)
  | "pop_back" => guard (n == 1 && isVoid r); pure (.vecPopBack e)
  | "clear" => guard (n == 1 && isVoid r); pure (.vecClear e)
  | "resize" => guard (n == 3 && isVoid r && isInt ps[1]! && isBoolTy ps[2]!); pure (.vecBool .resize)
  | "reserve" => guard (n == 2 && isInt ps[1]! && isVoid r); pure (.vecReserve e)
  | "swap" => guard (n == 2 && sameRec this ps[1]! && isVoid r); pure (.vecSwap e)
  | _ => none

/-- The members of libc++'s reference proxies of `std::vector<bool>` (`__bit_reference`,
`__bit_const_reference`) over the model's proxy record (`VecBoolOp`). -/
def recognizeBitRef (dn : DName) (fi : FuncInfo) : Option Model := do
  let ps := fi.params
  let this ← ps.head?
  guard (isPtr this)
  match dn.fname, ps with
  | "operator bool", [_] => guard (isBoolTy fi.ret); pure (.vecBool .get)
  | "operator=", [_, .bool] => pure (.vecBool .set)
  | "operator=", [_, o] => guard (sameRec this o); pure (.vecBool .assign)
  | "flip", [_] => guard (isVoid fi.ret); pure (.vecBool .flip)
  | _, _ => none

/-- Members of contiguous iterators (`__wrap_iter<T*>`, `__normal_iterator<T*, C>`). -/
def recognizeIterMember (dn : DName) (e : Ty) (fi : FuncInfo) : Option Model := do
  let ps := fi.params
  let this ← ps.head?
  guard (isPtr this)
  let n := ps.length
  let r := fi.ret
  match dn.fname with
  | "operator*" => guard (n == 1 && ptrTo r e); pure (.iterDeref e)
  | "operator->" => guard (n == 1 && ptrTo r e); pure (.iterDeref e)
  | "operator++" => guard (n == 1 && sameRec this r); pure (.iterInc e)   -- prefix only
  | "operator--" => guard (n == 1 && sameRec this r); pure (.iterDec e)   -- prefix only
  | "operator+" => guard (n == 2 && isInt ps[1]! && isRecordTy r); pure (.iterAdd e)
  | "base" => guard (n == 1 && isPtr r); pure (.iterBase e)
  | _ => none

/-- Free comparison/difference operators on two iterators. -/
def recognizeIterFree (dn : DName) (fi : FuncInfo) : Option Model := do
  let [a, b] := fi.params | none
  guard (isPtr a && sameRec a b)
  -- element type from the iterator class named in the parameters
  let p ← dn.params.head?
  let cls := trimS (dropRightWhileS p (fun c => c == '&' || c == ' '))
  let cls := if cls.endsWith " const" then trimS (dropRightS cls 6) else cls
  let base := normalizeNs (stripTemplate cls)
  guard (base == "std::__wrap_iter" || base == "__gnu_cxx::__normal_iterator")
  let e ← iterElemTy cls
  guard (scalarElem e)
  match dn.fname with
  | "operator==" => guard (isBoolTy fi.ret); pure (.iterEq e)
  | "operator!=" => guard (isBoolTy fi.ret); pure (.iterNe e)
  | "operator<" => guard (isBoolTy fi.ret); pure (.iterLt e)
  | "operator-" => guard (isInt fi.ret); pure (.iterDiff e)
  | _ => none

/-- The `std::basic_string<char>` models. -/
def recognizeString (dn : DName) (fi : FuncInfo) : Option Model := do
  let ps := fi.params
  let this ← ps.head?
  guard (isPtr this)
  let n := ps.length
  let r := fi.ret
  let charPtr (t : Ty) : Bool := ptrTo t (.int true 8)
  -- libc++ (`std::__1`), not libstdc++, whose T3 units' Gen stays as it is
  let libcxx := (splitScope dn.qual).take 2 == ["std", "__1"]
  match dn.fname with
  | "basic_string" =>
    -- decided on the CIR signature: c++filt mis-prints some of these
    -- constructors (`char const* …::basic_string<0>(allocator const&)`)
    match ps with
    | [_] => pure .strCtorDefault
    | [_, s] =>
      if charPtr s then pure .strCtorCStr
      else if sameRec this s then
        let p ← dn.params.head?
        if isRvalRef p then pure .strMoveCtor
        else if isConstRef p then pure .strCopyCtor else none
      else none
    | [_, s, a] =>
      -- `basic_string(char const*, allocator const&)`
      if charPtr s && (ptrToRecord? a).any (fun r => normalizeNs (stripTemplate r) == "std::allocator")
      then pure .strCtorCStr
      -- libc++'s `basic_string(n, c)`
      else if libcxx && isInt s && a == .int true 8 then pure .strCtorFill else none
    | [_, k, c, a] =>
      -- libc++'s `basic_string(n, c, allocator const&)` (c++filt: `…basic_string<0>(char, allocator const&)`)
      guard (libcxx && isInt k && c == .int true 8 && isAllocRef a); pure .strCtorFill
    | _ => none
  | "~basic_string" => guard (n == 1); pure .strDtor
  | "swap" => guard (n == 2 && sameRec this ps[1]! && isVoid r); pure .strSwap
  | "compare" =>
    guard (r == .int true 32)
    match dn.params with
    | ["char const*"] => guard (n == 2 && charPtr ps[1]!); pure .strCompareCStr
    | ["unsigned long", "unsigned long", "char const*", "unsigned long"] =>
      guard (n == 5 && isInt ps[1]! && isInt ps[2]! && charPtr ps[3]! && isInt ps[4]!); pure .strCompareSub
    | _ => none
  | "size" | "length" => guard (n == 1 && isInt r); pure .strSize
  | "empty" => guard (n == 1 && isBoolTy r); pure .strEmpty
  | "operator[]" => guard (n == 2 && isInt ps[1]! && charPtr r); pure .strIndex
  | "at" => guard (n == 2 && isInt ps[1]! && charPtr r); pure .strAt
  | "push_back" => guard (n == 2 && ps[1]! == .int true 8 && isVoid r); pure .strPushBack
  -- the characters stay; the capacity is not modelled, so as for a vector every element pointer
  -- and iterator is invalidated (a fresh generation, `Model.vecReserve`)
  | "reserve" => guard (n == 2 && isInt ps[1]! && isVoid r); pure (.vecReserve (.int true 8))
  | "append" | "operator+=" =>
    guard (n == 2 && sameRec this r)
    let p ← dn.params.head?
    if p == "char const*" then guard (charPtr ps[1]!); pure .strAppendCStr
    else if isConstRef p && p.startsWith "std::" then guard (sameRec this ps[1]!); pure .strAppend
    else none
  | "c_str" | "data" => guard (n == 1 && charPtr r); pure .strCStr
  | "begin" => guard (n == 1 && isRecordTy r); pure .strBegin
  | "end" => guard (n == 1 && isRecordTy r); pure .strEnd
  | "operator=" =>
    let p ← dn.params.head?
    guard (n == 2 && sameRec this ps[1]! && sameRec this r)
    if isRvalRef p then pure .strMoveAssign
    else if isConstRef p && p.startsWith "std::" then pure .strCopyAssign else none
  | _ => none

/-- Is a C++ type spelling a `std::basic_string<char, …>`? -/
def isStringSpelling (p : String) : Bool :=
  let cls := trimS (dropRightWhileS p (fun c => c == '&' || c == ' '))
  let cls := if cls.endsWith " const" then trimS (dropRightS cls 6) else cls
  normalizeNs (stripTemplate cls) == "std::basic_string" &&
    (templateArgs cls).head? == some "char"

/-- A spelling of libc++'s `std::vector<bool>` as a parameter (`const&`). -/
def isVecBoolSpelling (p : String) : Bool :=
  let cls := trimS (dropRightWhileS p (fun c => c == '&' || c == ' '))
  let cls := if cls.endsWith " const" then trimS (dropRightS cls 6) else cls
  stripTemplate cls == "std::__1::vector" && (templateArgs cls).head? == some "bool"

/-- The `std::optional<T>` models. -/
def recognizeOptional (dn : DName) (e : Ty) (fi : FuncInfo) : Option Model := do
  guard (scalarElem e)
  let ps := fi.params
  let this ← ps.head?
  guard (isPtr this)
  let n := ps.length
  let r := fi.ret
  match dn.fname with
  | "optional" =>
    match dn.params with
    | [] => guard (n == 1); pure (.optCtorNull e)
    | [p] =>
      if normalizeNs p == "std::nullopt_t" then guard (n == 2); pure (.optCtorNull e)
      else if n == 2 && ptrTo ps[1]! e then pure (.optCtorValue e)
      else if n == 2 && sameRec this ps[1]! && isConstRef p then pure (.optCopyCtor e)
      else none
    | _ => none
  | "has_value" | "operator bool" => guard (n == 1 && isBoolTy r); pure (.optHasValue e)
  | "operator*" | "operator->" => guard (n == 1 && ptrTo r e); pure (.optDeref e)
  | "value" => guard (n == 1 && ptrTo r e); pure (.optValue e)
  | "value_or" => guard (n == 2 && ptrTo ps[1]! e && r == e); pure (.optValueOr e)
  | _ => none

/-- The `std::unique_ptr<T>` models (default deleter only). -/
def recognizeUniquePtr (dn : DName) (e : Ty) (fi : FuncInfo) : Option Model := do
  guard (scalarElem e)
  let ps := fi.params
  let this ← ps.head?
  guard (isPtr this)
  let n := ps.length
  let r := fi.ret
  match dn.fname with
  | "unique_ptr" =>
    match dn.params with
    | [] => guard (n == 1); pure (.uptrCtorNull e)
    | [p] =>
      if p == "decltype(nullptr)" || normalizeNs p == "std::nullptr_t" then guard (n == 2); pure (.uptrCtorNull e)
      else if isRvalRef p && n == 2 && sameRec this ps[1]! then pure (.uptrMoveCtor e)
      else if n == 2 && ptrTo ps[1]! e then pure (.uptrCtorPtr e)
      else none
    | _ => none
  | "~unique_ptr" => guard (n == 1); pure (.uptrDtor e)
  | "get" => guard (n == 1 && ptrTo r e); pure (.uptrGet e)
  | "operator*" | "operator->" => guard (n == 1 && ptrTo r e); pure (.uptrDeref e)
  | "operator bool" => guard (n == 1 && isBoolTy r); pure (.uptrBool e)
  | "release" => guard (n == 1 && ptrTo r e); pure (.uptrRelease e)
  | "reset" => guard (n == 2 && ptrTo ps[1]! e && isVoid r); pure (.uptrReset e)
  | _ => none

/-- Free functions in namespace `std` / `__gnu_cxx`. -/
def recognizeFree (dn : DName) (fi : FuncInfo) : Option Model := do
  let ns := normalizeNs dn.qual
  guard (ns == "std" || ns == "__gnu_cxx")
  let ps := fi.params
  match dn.fname with
  | "min" | "max" =>
    let [a, b] := ps | none
    let .ptr t := a | none
    guard (isInt t && ptrTo b t && ptrTo fi.ret t)
    pure (if dn.fname == "min" then .stdMin t else .stdMax t)
  | "swap" =>
    let [a, b] := ps | none
    let .ptr t := a | none
    guard (scalarElem t && ptrTo b t && isVoid fi.ret)
    pure (.stdSwap t)
  | "move" =>
    let [a] := ps | none
    let .ptr t := a | none
    guard (scalarElem t && ptrTo fi.ret t)
    pure (.stdMove t)
  | "operator==" =>
    if dn.params.length == 2 && dn.params.all isStringSpelling then
      let [a, b] := ps | none
      guard (isPtr a && sameRec a b && isBoolTy fi.ret)
      pure .strEq
    else if dn.params.length == 2 && dn.params.all isVecBoolSpelling then
      -- `std::vector<bool>`'s, whose libc++ code walks its iterators
      let [a, b] := ps | none
      guard (isPtr a && sameRec a b && isBoolTy fi.ret)
      pure (.vecBool .eq)
    else recognizeIterFree dn fi
  | "operator!=" | "operator<" | "operator-" => recognizeIterFree dn fi
  | "operator+" =>
    -- libc++'s `operator+(char const*, basic_string<char> const&)`, which its library exports
    let [s, t] := ps | none
    let .record rn := fi.ret | none
    guard (dn.qual == "std::__1" && dn.params.head? == some "char const*" && (dn.params[1]?.any isStringSpelling) &&
      ptrTo s (.int true 8) && (ptrToRecord? t).any isCharStringRec && isCharStringRec rn)
    pure .strConcatCStr
  | "__concatenate_strings" =>
    -- libc++: `basic_string<char> __concatenate_strings(allocator<char> const&, string_view, string_view)`
    let [a, v, w] := ps | none
    let .record rn := fi.ret | none
    let .record vn := v | none
    guard (isAllocRef a && v == w && isCharStringRec rn)
    let vb := normalizeNs (stripTemplate vn)
    guard (vb == "std::string_view" || vb == "std::basic_string_view" && (templateArgs vn).head? == some "char")
    pure .strConcat
  | "operator<<" | "endl" | "flush" | "ends" =>
    -- stream output: the first parameter is a `std::basic_ostream<char>&`
    let p0 ← dn.params.head?
    guard (normalizeNs (stripTemplate p0) == "std::basic_ostream" &&
      (templateArgs p0).head? == some "char")
    let p1 := dn.params[1]?.getD ""
    pure (.ostreamOut (if p1 == "char const*" then 1
      else if isStringSpelling p1 then 2 else 0))
  | _ => none

/-- Recognition from the demangled name. -/
def recognizeDemangled (fi : FuncInfo) (dn : DName) : Option Model :=
  let base := normalizeNs (stripTemplate dn.qual)
  let targs := templateArgs dn.qual
  let elem? := targs.head?.bind cppScalarTy
  match base with
  | "std::vector" => elem?.bind fun e =>
    -- libc++'s `std::vector<bool>` (libstdc++'s keeps running its code)
    if isBoolTy e then (if dn.qual.startsWith "std::__1::" then recognizeVectorBool dn fi else none)
    else recognizeVector dn e fi
  | "std::__bit_reference" | "std::__bit_const_reference" =>
    match targs.head? with
    | some t =>
      if normalizeNs (stripTemplate t) == "std::vector" && (templateArgs t).head? == some "bool" then
        recognizeBitRef dn fi
      else none
    | none => none
  | "std::basic_string" => if targs.head? == some "char" then recognizeString dn fi else none
  | "std::basic_ostream" =>
    if targs.head? == some "char" &&
        ["operator<<", "put", "write", "flush"].contains dn.fname then
      some (.ostreamOut 0)
    else none
  | "std::__wrap_iter" | "__gnu_cxx::__normal_iterator" =>
    (iterElemTy dn.qual).bind fun e => if scalarElem e then recognizeIterMember dn e fi else none
  | "std::optional" | "std::__optional_storage_base" => elem?.bind fun e => recognizeOptional dn e fi
  | "std::unique_ptr" =>
    let delOk := match targs with
      | [_] => true
      | [_, d] => normalizeNs (stripTemplate d) == "std::default_delete"
      | _ => false
    if delOk then elem?.bind fun e => recognizeUniquePtr dn e fi else none
  | _ => recognizeFree dn fi

/-- Base class name and element type of a record name such as
`std::__1::unique_ptr<int, std::__1::default_delete<int>>`. -/
def recordClass (n : String) : String × Option Ty :=
  (normalizeNs (stripTemplate n), (templateArgs n).head?.bind cppScalarTy)

/-- Structural recognition when the symbol could not be demangled. -/
def recognizeMangledOnly (fi : FuncInfo) : Option Model := do
  let ps := fi.params
  -- libc++'s `std::__to_address` of a `__wrap_iter<T*>` (the overload through
  -- `operator->`, whose enable_if c++filt cannot demangle), as `std::sort`,
  -- `std::copy`, ... unwrap their iterators: the pointer the iterator holds,
  -- `end()` included, without a dereference (as `base()`)
  if fi.sym.startsWith "_ZNSt3__112__to_address" then
    let [a] := ps | none
    let cls ← ptrToRecord? a
    guard (normalizeNs (stripTemplate cls) == "std::__wrap_iter")
    let e ← iterElemTy cls
    guard (scalarElem e && ptrTo fi.ret e)
    return .iterBase e
  -- free `__gnu_cxx::operator==` / `operator!=` with a requires-clause
  if fi.sym.startsWith "_ZN9__gnu_cxxeq" || fi.sym.startsWith "_ZN9__gnu_cxxne" then
    let [a, b] := ps | none
    let cls ← ptrToRecord? a
    guard (sameRec a b && isBoolTy fi.ret)
    guard (normalizeNs (stripTemplate cls) == "__gnu_cxx::__normal_iterator")
    let e ← iterElemTy cls
    guard (scalarElem e)
    return (if fi.sym.startsWith "_ZN9__gnu_cxxeq" then .iterEq e else .iterNe e)
  let this ← ps.head?
  let cls ← ptrToRecord? this
  let (base, elem?) := recordClass cls
  -- constructors which c++filt cannot demangle: libstdc++'s with a requires-clause
  -- (`…Q26is_default_constructible…`): `basic_string()`, `basic_string(char const*[, alloc])`;
  -- libc++'s range constructors (enable_if): `basic_string(first, last[, alloc])`, whose
  -- record clang may name `std::string`
  if isCharStringRec cls && fi.special == .ctor then
    match ps with
    | [_] => return .strCtorDefault
    | [_, s] => if ptrTo s (.int true 8) then return .strCtorCStr else none
    | [_, s, a] =>
      if ptrTo s (.int true 8) && isAllocRef a then return .strCtorCStr
      else match strRangeCtor? s a with
        | some md => return md
        | none => none
    | [_, s, t, a] =>
      match isAllocRef a, strRangeCtor? s t with
      | true, some md => return md
      | _, _ => none
    | _ => none
  let e ← elem?
  guard (scalarElem e)
  -- libc++'s `vector<T>::assign(first, last)` (enable_if)
  if base == "std::vector" && fi.special == .none && (fi.sym.splitOn "E6assign").length > 1 then
    let [_, a, b] := ps | none
    guard (!isBoolTy e && a == b && iterOver a e && isVoid fi.ret)
    return .vecAssignRange e
  -- libc++'s `vector<T>(first, last[, alloc])` (enable_if), `std::vector<bool>`'s too
  if base == "std::vector" && fi.special == .ctor then
    let modelled := !isBoolTy e || cls.startsWith "std::__1::"
    match ps with
    | [_, a, b] =>
      guard (modelled && a == b && iterOver a e)
      return .vecRangeCtor e
    | [_, a, b, al] =>
      guard (modelled && a == b && iterOver a e && isAllocRef al)
      return .vecRangeCtor e
    | _ => none
  match base, fi.special with
  | "std::unique_ptr", .ctor =>
    match ps with
    | [_] => pure (.uptrCtorNull e)
    | [_, .ptr .void] => pure (.uptrCtorNull e)
    | [_, p] => if ptrTo p e then pure (.uptrCtorPtr e) else none
    | _ => none
  | "std::unique_ptr", .none =>
    -- `operator*` (`de`) of unique_ptr, constrained template in libc++
    guard (ps.length == 1 && ptrTo fi.ret e && (fi.sym.splitOn "Ede").length > 1)
    pure (.uptrDeref e)
  | "std::optional", .ctor =>
    match ps with
    | [_, p] => if ptrTo p e then pure (.optCtorValue e) else none
    | _ => none
  | _, _ => none

/-- `std::__1::__sort<std::__1::__less<T, T>&, T*>` for an arithmetic `T`, libc++'s
explicit instantiations (`<__algorithm/sort.h>`): the code letter of `T`. -/
def libcxxSortCode? (sym : String) : Option Char :=
  let cs := sym.toList
  let pre := "_ZNSt3__16__sortIRNS_6__lessI".toList
  let suf := "EEvT0_S5_T_".toList
  if cs.length = pre.length + 6 + suf.length && cs.take pre.length == pre &&
      cs.drop (pre.length + 6) == suf then
    match cs.drop pre.length |>.take 6 with
    | [a, b, 'E', 'E', 'P', c] =>
      if a == b && b == c && "cwahstijlmxyfde".toList.contains a then some a else none
    | _ => none
  else none

/-- A model of a library whose names the C and C++ standards do not reserve (C11 7.1.3 reserves
the C library's): libevent, POSIX (threads, scheduling, `strerror_r`, `ffs`, `lrand48`,
`seed48`); also glibc's `ffsl`, `ffsll` and `__errno_location`. A program may define such a
function itself, so the model attaches only to a declaration without a body
(`loadModuleFromString`). -/
def nonReservedModel : Model → Bool
  | .evbufferNew | .evbufferFree | .evbufferAdd | .evbufferLength | .evhttpAddHeader
  | .evhttpSendReply | .eventBaseLoopbreak | .pthreadSelf | .pthreadEqual
  | .pthreadSetschedparam | .schedPriority _ | .strerrorR | .errnoLocation => true
  | .lib (.ffs _) | .lib .lrand48 | .lib .seed48 => true
  | _ => false

/-- Model for a library function, or `none` (then its body is executed). -/
def recognize (info : FuncInfo) : Option Model :=
  match info.sym with
  | "abort" => some .abort
  | "__assert_fail" => some .assertFail
  | "_ZSt21__glibcxx_assert_failPKciS0_S0_" => some .assertFail
  -- libstdc++ error paths (functexcept.h): throw the library exception
  | "_ZSt17__throw_bad_allocv" => some (.libThrow "_ZTISt9bad_alloc")
  | "_ZSt28__throw_bad_array_new_lengthv" => some (.libThrow "_ZTISt20bad_array_new_length")
  | "_ZSt21__throw_bad_exceptionv" => some (.libThrow "_ZTISt13bad_exception")
  | "_ZSt16__throw_bad_castv" => some (.libThrow "_ZTISt8bad_cast")
  | "_ZSt18__throw_bad_typeidv" => some (.libThrow "_ZTISt10bad_typeid")
  | "_ZSt25__throw_bad_function_callv" => some (.libThrow "_ZTISt17bad_function_call")
  | "_ZSt19__throw_logic_errorPKc" => some (.libThrow "_ZTISt11logic_error")
  | "_ZSt20__throw_domain_errorPKc" => some (.libThrow "_ZTISt12domain_error")
  | "_ZSt24__throw_invalid_argumentPKc" => some (.libThrow "_ZTISt16invalid_argument")
  | "_ZSt20__throw_length_errorPKc" => some (.libThrow "_ZTISt12length_error")
  | "_ZSt20__throw_out_of_rangePKc" => some (.libThrow "_ZTISt12out_of_range")
  | "_ZSt24__throw_out_of_range_fmtPKcz" => some (.libThrow "_ZTISt12out_of_range")
  | "_ZSt21__throw_runtime_errorPKc" => some (.libThrow "_ZTISt13runtime_error")
  | "_ZSt19__throw_range_errorPKc" => some (.libThrow "_ZTISt11range_error")
  | "_ZSt22__throw_overflow_errorPKc" => some (.libThrow "_ZTISt14overflow_error")
  | "_ZSt23__throw_underflow_errorPKc" => some (.libThrow "_ZTISt15underflow_error")
  | "_ZSt20__throw_system_errori" => some (.libThrow "_ZTISt12system_error")
  | "_ZSt20__throw_future_errori" => some (.libThrow "_ZTISt12future_error")
  | "exit" => some .exit
  | "_Exit" => some (.exitNow false)
  | "quick_exit" => some (.exitNow true)
  | "_Znwm" | "_ZnwmSt11align_val_t" | "_Znam" | "_ZnamSt11align_val_t" => some .operatorNew
  | "_ZdlPv" | "_ZdlPvm" | "_ZdlPvSt11align_val_t" | "_ZdlPvmSt11align_val_t"
  | "_ZdaPv" | "_ZdaPvm" | "_ZdaPvSt11align_val_t" | "_ZdaPvmSt11align_val_t" => some .operatorDelete
  | "malloc" => some .malloc
  | "calloc" => some .calloc
  | "free" => some .free
  | "strlen" => some .strlen
  | "memset" => some .memset
  | "memcpy" => some .memcpy
  | "memmove" => some .memmove
  | "memcmp" => some .memcmp
  | "strcmp" => some .strcmp
  | "strncmp" => some .strncmp
  | "isdigit" | "isalpha" | "isalnum" | "isspace" | "isupper" | "islower" | "isxdigit"
  | "ispunct" | "isprint" | "toupper" | "tolower" => some (.ctype info.sym)
  | "setjmp" | "_setjmp" | "__sigsetjmp" | "__builtin_setjmp" => some .setjmp
  | "longjmp" | "_longjmp" | "siglongjmp" | "__longjmp_chk" | "__builtin_longjmp" => some .longjmp
  | "strcpy" => some .strcpy
  | "strncpy" =>
    match info.params with
    | [.ptr _, .ptr _, .int _ _] => some .strncpy
    | _ => none
  | "strcat" =>
    match info.params with
    | [.ptr _, .ptr _] => some .strcat
    | _ => none
  | "strchr" => some .strchr
  | "strrchr" =>
    match info.params with
    | [.ptr _, .int _ _] => some .strrchr
    | _ => none
  | "localeconv" => some .localeconv
  | "strdup" | "__strdup" => some .strdup
  | "getchar" => some .getchar
  | "fread" =>
    match info.params, info.ret with
    | [.ptr _, .int false 64, .int false 64, .ptr _], .int false 64 => some (.lib .fread)
    | _, _ => none
  | "fwrite" =>
    match info.params, info.ret with
    | [.ptr _, .int false 64, .int false 64, .ptr _], .int false 64 => some (.lib .fwrite)
    | _, _ => none
  | "fputs" =>
    match info.params, info.ret with
    | [.ptr (.int _ 8), .ptr _], .int true 32 => some (.lib .fputs)
    | _, _ => none
  | "ungetc" =>
    match info.params, info.ret with
    | [.int true 32, .ptr _], .int true 32 => some (.lib .ungetc)
    | _, _ => none
  | "fscanf" | "__isoc99_fscanf" | "__isoc23_fscanf" => some (.lib .fscanf)
  -- POSIX (`nonReservedModel`)
  | "ffs" =>
    match info.params, info.ret with
    | [.int _ 32], .int true 32 => some (.lib (.ffs 32))
    | _, _ => none
  | "ffsl" | "ffsll" =>
    match info.params, info.ret with
    | [.int _ 64], .int true 32 => some (.lib (.ffs 64))
    | _, _ => none
  | "lrand48" =>
    match info.params, info.ret with
    | [], .int true 64 => some (.lib .lrand48)
    | _, _ => none
  | "seed48" =>
    match info.params, info.ret with
    | [.ptr (.int false 16)], .ptr (.int false 16) => some (.lib .seed48)
    | _, _ => none
  | "fflush" =>
    match info.params, info.ret with
    | [.ptr _], .int true 32 => some .fflush
    | _, _ => none
  | "perror" =>
    match info.params, info.ret with
    | [.ptr (.int _ 8)], .void => some .perror
    | _, _ => none
  | "signal" =>
    match info.params, info.ret with
    | [.int true 32, .ptr _], .ptr _ => some .signal
    | _, _ => none
  | "memchr" =>
    match info.params, info.ret with
    | [.ptr _, .int true 32, .int false 64], .ptr _ => some .memchr
    | _, _ => none
  | "posix_memalign" =>
    match info.params, info.ret with
    | [.ptr (.ptr _), .int false 64, .int false 64], .int true 32 => some .posixMemalign
    | _, _ => none
  | "__cxa_pure_virtual" => some .pureVirtual
  | "rand" =>
    match info.params, info.ret with
    | [], .int true 32 => some (.rand false)
    | _, _ => none
  | "srand" =>
    match info.params, info.ret with
    | [.int false 32], .void => some (.rand true)
    | _, _ => none
  | "__cxa_atexit" => some (.atexit true)
  | "atexit" => some (.atexit false)
  | "at_quick_exit" => some .atQuickExit
  | "__cxa_guard_acquire" => some .guardAcquire
  | "__cxa_guard_release" => some .guardRelease
  | "__cxa_guard_abort" => some .guardAbort
  | "strtod" | "atof" => some (.strtod false)
  | "strtof" => some (.strtod true)
  | "strtol" | "strtoll" => some (.strtol true false)
  | "strtoul" | "strtoull" => some (.strtol false false)
  | "__isoc23_strtol" | "__isoc23_strtoll" => some (.strtol true true)
  | "__isoc23_strtoul" | "__isoc23_strtoull" => some (.strtol false true)
  | "atoi" | "atol" | "atoll" =>
    match info.params, info.ret with
    | [.ptr (.int _ 8)], .int true w => some (.atoi w)
    | _, _ => none
  | "sscanf" | "__isoc99_sscanf" | "__isoc23_sscanf" => some .sscanf
  | "scanf" | "__isoc99_scanf" | "__isoc23_scanf" => some .scanf
  | "snprintf" => some .snprintf
  | "realloc" => some .realloc
  | "sprintf" => some .sprintf
  | "printf" => some (.printf 0)
  | "fprintf" => some (.printf 1)
  | "vprintf" => some (.vprintf 0)
  | "vfprintf" => some (.vprintf 1)
  | "vsprintf" => some .vsprintf
  | "vsnprintf" => some .vsnprintf
  | "puts" => some .puts
  | "putchar" => some .putchar
  | "__ctype_b_loc" => some (.ctypeTable 0)
  | "__ctype_toupper_loc" => some (.ctypeTable 1)
  | "__ctype_tolower_loc" => some (.ctypeTable 2)
  | "_ZNSt11logic_errorC1EPKc" | "_ZNSt11logic_errorC2EPKc" | "_ZNSt11logic_errorD1Ev"
  | "_ZNSt11logic_errorD2Ev" | "_ZNSt13runtime_errorC1EPKc" | "_ZNSt13runtime_errorC2EPKc"
  | "_ZNSt13runtime_errorD1Ev" | "_ZNSt13runtime_errorD2Ev" | "_ZNSt20bad_array_new_lengthC1Ev"
  | "_ZNSt20bad_array_new_lengthC2Ev" | "_ZNSt20bad_array_new_lengthD1Ev"
  | "_ZNSt20bad_array_new_lengthD2Ev" | "_ZNSt12length_errorD1Ev" | "_ZNSt12length_errorD2Ev"
  | "_ZNSt12out_of_rangeD1Ev" | "_ZNSt12out_of_rangeD2Ev" | "_ZNSt16invalid_argumentD1Ev"
  | "_ZNSt16invalid_argumentD2Ev" | "_ZNSt9exceptionD1Ev" | "_ZNSt9exceptionD2Ev"
  | "_ZNSt9bad_allocC1Ev" | "_ZNSt9bad_allocD1Ev" | "_ZNSt9bad_allocD2Ev" => some .excNoop
  | "sqrt" | "pow" | "exp" | "log" | "log2" | "log10" | "sin" | "cos" | "tan" | "atan" | "atan2"
  | "floor" | "ceil" | "fabs" | "round" | "trunc" | "fmod" | "cbrt" | "fmin" | "fmax"
  | "asin" | "acos" | "sinh" | "cosh" | "tanh" | "asinh" | "acosh" | "atanh" | "exp2" =>
    some (.libm info.sym false)
  | "sqrtf" | "powf" | "expf" | "logf" | "log2f" | "log10f" | "sinf" | "cosf" | "tanf" | "atanf"
  | "atan2f" | "floorf" | "ceilf" | "fabsf" | "roundf" | "truncf" | "fmodf" | "cbrtf" | "fminf" | "fmaxf"
  | "asinf" | "acosf" | "sinhf" | "coshf" | "tanhf" | "asinhf" | "acoshf" | "atanhf" | "exp2f" =>
    some (.libm (String.ofList info.sym.toList.dropLast) true)
  | "__muldc3" | "__divdc3" =>
    match info.params, info.ret with
    | [.float .double, .float .double, .float .double, .float .double], .array (.float .double) 2 =>
      some (if info.sym == "__muldc3" then .mulc3 false else .divc3 false)
    | _, _ => none
  | "__mulsc3" | "__divsc3" =>
    match info.params, info.ret with
    | [.float .single, .float .single, .float .single, .float .single], .array (.float .single) 2 =>
      some (if info.sym == "__mulsc3" then .mulc3 true else .divc3 true)
    | _, _ => none
  | "hypot" =>
    match info.params, info.ret with
    | [.float .double, .float .double], .float .double => some (.hypot false)
    | _, _ => none
  | "hypotf" =>
    match info.params, info.ret with
    | [.float .single, .float .single], .float .single => some (.hypot true)
    | _, _ => none
  | "expm1" | "log1p" =>
    match info.params, info.ret with
    | [.float .double], .float .double => some (if info.sym == "expm1" then .expm1 else .log1p)
    | _, _ => none
  | "erf" | "erfc" | "tgamma" | "lgamma" =>
    match info.params, info.ret with
    | [.float .double], .float .double =>
      some (match info.sym with
        | "erf" => .erf
        | "erfc" => .erfc
        | "tgamma" => .tgamma
        | _ => .lgamma)
    | _, _ => none
  | "rint" | "nearbyint" => some (.rint false)
  | "rintf" | "nearbyintf" => some (.rint true)
  | "lrint" | "llrint" | "lrintf" | "llrintf" => some (.lrint info.sym)
  | "_ZNKSt9exception4whatEv" => some (.excWhat "std::exception")
  | "_ZNKSt9bad_alloc4whatEv" => some (.excWhat "std::bad_alloc")
  -- libevent 2.1 (`<event2/buffer.h>`, `<event2/http.h>`, `<event2/event.h>`)
  | "evbuffer_new" =>
    match info.params, info.ret with
    | [], .ptr (.record "evbuffer") => some .evbufferNew
    | _, _ => none
  | "evbuffer_free" =>
    match info.params, info.ret with
    | [.ptr (.record "evbuffer")], .void => some .evbufferFree
    | _, _ => none
  | "evbuffer_add" =>
    match info.params, info.ret with
    | [.ptr (.record "evbuffer"), .ptr _, .int false 64], .int true 32 => some .evbufferAdd
    | _, _ => none
  | "evbuffer_get_length" =>
    match info.params, info.ret with
    | [.ptr (.record "evbuffer")], .int false 64 => some .evbufferLength
    | _, _ => none
  | "evhttp_add_header" =>
    match info.params, info.ret with
    | [.ptr (.record "evkeyvalq"), .ptr (.int _ 8), .ptr (.int _ 8)], .int true 32 => some .evhttpAddHeader
    | _, _ => none
  | "evhttp_send_reply" =>
    match info.params, info.ret with
    | [.ptr (.record "evhttp_request"), .int true 32, .ptr (.int _ 8), .ptr (.record "evbuffer")], .void =>
      some .evhttpSendReply
    | _, _ => none
  | "event_base_loopbreak" =>
    match info.params, info.ret with
    | [.ptr (.record "event_base")], .int true 32 => some .eventBaseLoopbreak
    | _, _ => none
  -- POSIX threads (`pthread_t` is `unsigned long` in glibc)
  | "pthread_self" =>
    match info.params, info.ret with
    | [], .int false 64 => some .pthreadSelf
    | _, _ => none
  | "pthread_equal" =>
    match info.params, info.ret with
    | [.int false 64, .int false 64], .int true 32 => some .pthreadEqual
    | _, _ => none
  -- libc++'s library: `std::__1::__hash_memory(void const*, unsigned long)` and
  -- `std::__1::__next_prime(unsigned long)`
  | "_ZNSt3__113__hash_memoryEPKvm" =>
    match info.params, info.ret with
    | [.ptr _, .int false 64], .int false 64 => some (.lib .hashMemory)
    | _, _ => none
  | "_ZNSt3__112__next_primeEm" =>
    match info.params, info.ret with
    | [.int false 64], .int false 64 => some (.lib .nextPrime)
    | _, _ => none
  | "pthread_setschedparam" =>
    match info.params, info.ret with
    | [.int false 64, .int true 32, .ptr (.record "sched_param")], .int true 32 => some .pthreadSetschedparam
    | _, _ => none
  | "sched_get_priority_max" | "sched_get_priority_min" =>
    match info.params, info.ret with
    | [.int true 32], .int true 32 => some (.schedPriority (info.sym == "sched_get_priority_max"))
    | _, _ => none
  -- `errno`, the GNU `strerror_r` (the XSI one is `__xpg_strerror_r`), `time_t` is `long`
  | "__errno_location" =>
    match info.params, info.ret with
    | [], .ptr (.int true 32) => some .errnoLocation
    | _, _ => none
  | "strerror_r" =>
    match info.params, info.ret with
    | [.int true 32, .ptr (.int _ 8), .int false 64], .ptr (.int _ 8) => some .strerrorR
    | _, _ => none
  | "time" =>
    match info.params, info.ret with
    | [.ptr (.int true 64)], .int true 64 => some .time
    | _, _ => none
  | "ctime_r" =>
    match info.params, info.ret with
    | [.ptr (.int true 64), .ptr (.int _ 8)], .ptr (.int _ 8) => some .ctimeR
    | _, _ => none
  | _ =>
    if (libcxxSortCode? info.sym).isSome then
      match info.params, info.ret with
      | [.ptr t, .ptr t', .ptr _], .void => if t == t' then some (.sortLess t) else none
      | _, _ => none
    else if info.demangled.isEmpty then
      if info.sym.startsWith "_Z" then recognizeMangledOnly info else none
    else match parseDemangled info.demangled with
      | some dn => recognizeDemangled info dn
      | none => none

end CIR.Frontend
