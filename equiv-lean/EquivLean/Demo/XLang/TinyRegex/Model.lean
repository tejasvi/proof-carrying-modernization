/-!
# tiny-regex-c `re.c` @ f2632c6: a functional model with a UB flag

The model follows the C function by function, on byte arrays and indices:
* `compile` is `re_compile` from zero-initialized statics (`re_compiled[30]`, `ccl_buf[40]`); a
  trailing backslash writes nothing, so its entry keeps the stale (here: zero, `UNUSED`) type;
* `matchone` and the class helpers read bytes as signed `char`s (x86-64): `p.u.ch == c` fails for
  bytes >= 0x80, class characters and ranges compare signed; `isdigit`/`isalpha`/`isspace` read
  glibc's table, indexed from -128, so a negative `char` is in no class (and is not UB);
* `mpLoop` (the loop of `matchpattern`), `matchquestion`, `matchstar` (+ `starBack`) and
  `matchplus` (+ `plusBack`) are the mutual recursion of the C, terminating by pattern index, then
  text index;
* `reMatch` is `re_match`.
`*matchlength` is threaded through every call as in the C, where a failed attempt can leave it
changed for the next one.

Every place where the C has undefined behaviour in cirlean's semantics sets a bit of the `ub` mask of
the result: pointer arithmetic outside `0 ≤ index ≤ length` of the block, a read at or past the end
of a block (here: past the NUL of the pattern or the text), signed overflow.  The values computed
alongside are those of the C as gcc compiles it on x86-64 (for comparison with the binary).  `RE_DOT_MATCHES_NEWLINE` is 1 (`re.h`'s default): `.` matches every byte but NUL.
-/

namespace EquivLean.Demo.XLang.TinyRegex

/-! ## UB kinds: the bits of `ub` -/

/-- `matchstar`: `text--` at the first byte of the text (a pointer before the start of the array). -/
def ubStar : Nat := 1
/-- A read past the NUL of the pattern or the text, or outside `re_compiled` / `ccl_buf`. -/
def ubRead : Nat := 4
/-- `matchpattern`: `&pattern[2]` beyond one past the end of `re_compiled`. -/
def ubPtr : Nat := 8
/-- `int` overflow of `*matchlength` or `idx`. -/
def ubOverflow : Nat := 16

/-! ## Bytes and `int` -/

/-- The value of byte `b` as a (signed) `char`. -/
def sc (b : Nat) : Int := if b < 128 then b else (b : Int) - 256

/-- `isdigit` on the `char` holding byte `b`, C locale (bytes >= 0x80 are negative: in no class). -/
def isdigitC (b : Nat) : Bool := 48 ≤ b && b ≤ 57
def isalphaC (b : Nat) : Bool := (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122)
def isspaceC (b : Nat) : Bool := b == 32 || (9 ≤ b && b ≤ 13)

/-- `matchalphanum`: `(c == '_') || matchalpha(c) || matchdigit(c)`. -/
def matchalphanum (b : Nat) : Bool := b == 95 || isalphaC b || isdigitC b

def INT_MIN : Int := -2147483648
def INT_MAX : Int := 2147483647

/-- The overflow flag of an `int` result. -/
def chk (v : Int) : Nat := if INT_MIN ≤ v ∧ v ≤ INT_MAX then 0 else ubOverflow

/-! ## `regex_t` -/

def UNUSED : Nat := 0
def DOT : Nat := 1
def BEGIN : Nat := 2
def END : Nat := 3
def QUESTIONMARK : Nat := 4
def STAR : Nat := 5
def PLUS : Nat := 6
def CHAR : Nat := 7
def CHAR_CLASS : Nat := 8
def INV_CHAR_CLASS : Nat := 9
def DIGIT : Nat := 10
def NOT_DIGIT : Nat := 11
def ALPHA : Nat := 12
def NOT_ALPHA : Nat := 13
def WHITESPACE : Nat := 14
def NOT_WHITESPACE : Nat := 15

/-- A `regex_t`: `type` and the union `u`, as `ch` (`u.ch`) or `ccl` (`u.ccl`, an index into
`ccl_buf`). -/
structure Tok where
  type : Nat := 0
  ch : Nat := 0
  ccl : Nat := 0
deriving Repr, Inhabited, BEq

def MAXOBJ : Nat := 30
def MAXCCL : Nat := 40

/-- `s[i]` of the C string `s ++ [0]`; past the NUL: UB. -/
def rd (s : Array Nat) (i : Nat) : Nat × Nat :=
  if h : i < s.size then (s[i], 0) else if i = s.size then (0, 0) else (0, ubRead)

/-! ## `re_compile` -/

/-- The `[..]` copy loop of `re_compile`, `while ((pattern[++i] != ']') && (pattern[i] != '\0'))`,
with `i` the index before the next character: `none` is `return 0`; otherwise the index of the `]`
or NUL that ended it, `ccl_bufidx` and `ccl_buf`. -/
def cclCopy (p : Array Nat) (i bidx : Nat) (buf : Array Nat) :
    Option (Nat × Nat × Array Nat) × Nat :=
  if h : i + 1 < p.size then
    let c := p[i + 1]
    if c == 93 || c == 0 then (some (i + 1, bidx, buf), 0)
    else if c == 92 then
      -- `if (ccl_bufidx >= MAX_CHAR_CLASS_LEN - 1) return 0;`
      if bidx ≥ MAXCCL - 1 then (none, 0)
      else if h2 : i + 2 < p.size then
        -- `if (pattern[i+1] == 0) return 0;`, then the backslash and the escaped character
        if p[i + 2] == 0 then (none, 0)
        else cclCopy p (i + 2) (bidx + 2) ((buf.set! bidx c).set! (bidx + 1) p[i + 2])
      else if i + 2 = p.size then (none, 0) else (none, ubRead)
    else if bidx ≥ MAXCCL then (none, 0)
    else cclCopy p (i + 1) (bidx + 1) (buf.set! bidx c)
  else if i + 1 = p.size then (some (i + 1, bidx, buf), 0) else (none, ubRead)
termination_by p.size - i

/-- One pass of `re_compile`'s loop body at pattern index `i` (character `c` ≠ 0) and entry `j`:
`none` is `return 0`; otherwise the new `i` (before `if (pattern[i] == 0)` and `i += 1`),
`ccl_bufidx` and the two arrays. -/
def compStep (p : Array Nat) (i j bidx : Nat) (re : Array Tok) (buf : Array Nat) (c : Nat) :
    Option (Nat × Nat × Array Tok × Array Nat) × Nat :=
  let setT (t : Nat) : Array Tok := re.set! j { re[j]! with type := t }
  if c == 94 then (some (i, bidx, setT BEGIN, buf), 0)
  else if c == 36 then (some (i, bidx, setT END, buf), 0)
  else if c == 46 then (some (i, bidx, setT DOT, buf), 0)
  else if c == 42 then (some (i, bidx, setT STAR, buf), 0)
  else if c == 43 then (some (i, bidx, setT PLUS, buf), 0)
  else if c == 63 then (some (i, bidx, setT QUESTIONMARK, buf), 0)
  else if c == 92 then
    let (c1, u) := rd p (i + 1)
    if c1 != 0 then
      let re :=
        if c1 == 100 then setT DIGIT
        else if c1 == 68 then setT NOT_DIGIT
        else if c1 == 119 then setT ALPHA
        else if c1 == 87 then setT NOT_ALPHA
        else if c1 == 115 then setT WHITESPACE
        else if c1 == 83 then setT NOT_WHITESPACE
        else re.set! j { re[j]! with type := CHAR, ch := c1 }
      (some (i + 1, bidx, re, buf), u)
    -- '\\' as the last character: `re_compiled[j]` is left as it was
    else (some (i, bidx, re, buf), u)
  else if c == 91 then
    let begin := bidx
    let (c1, u1) := rd p (i + 1)
    if c1 == 94 then
      let re := setT INV_CHAR_CLASS
      let (c2, u2) := rd p (i + 2)
      if c2 == 0 then (none, u1 ||| u2)
      else
        match cclCopy p (i + 1) bidx buf with
        | (none, u3) => (none, u1 ||| u2 ||| u3)
        | (some (i, bidx, buf), u3) =>
          if bidx ≥ MAXCCL then (none, u1 ||| u2 ||| u3)
          else (some (i, bidx + 1, re.set! j { re[j]! with ccl := begin }, buf.set! bidx 0),
            u1 ||| u2 ||| u3)
    else
      let re := setT CHAR_CLASS
      match cclCopy p i bidx buf with
      | (none, u3) => (none, u1 ||| u3)
      | (some (i, bidx, buf), u3) =>
        if bidx ≥ MAXCCL then (none, u1 ||| u3)
        else (some (i, bidx + 1, re.set! j { re[j]! with ccl := begin }, buf.set! bidx 0),
          u1 ||| u3)
  else (some (i, bidx, re.set! j { re[j]! with type := CHAR, ch := c }, buf), 0)

/-- `re_compile`'s loop `while (pattern[i] != '\0' && (j+1 < MAX_REGEXP_OBJECTS))`, then the
`UNUSED` sentinel. -/
def compLoop (p : Array Nat) (i j bidx : Nat) (re : Array Tok) (buf : Array Nat) (ub : Nat) :
    Option (Array Tok × Array Nat) × Nat :=
  let (c, u) := rd p i
  let ub := ub ||| u
  if _h : c ≠ 0 ∧ j + 1 < MAXOBJ then
    match compStep p i j bidx re buf c with
    | (none, u') => (none, ub ||| u')
    | (some (i, bidx, re, buf), u') =>
      let (ci, u'') := rd p i
      if ci == 0 then (none, ub ||| u' ||| u'')
      else compLoop p (i + 1) (j + 1) bidx re buf (ub ||| u' ||| u'')
  else (some (re.set! j { re[j]! with type := UNUSED }, buf), ub)
termination_by MAXOBJ - j
decreasing_by omega

/-- `re_compile(p ++ [0])` from zero-initialized statics: `none` for a null result. -/
def compile (p : Array Nat) : Option (Array Tok × Array Nat) × Nat :=
  compLoop p 0 0 1 (Array.replicate MAXOBJ {}) (Array.replicate MAXCCL 0) 0

/-! ## `matchone` and the class helpers -/

/-- `ccl_buf[k]`. -/
def bget (B : Array Nat) (k : Nat) : Nat × Nat :=
  if h : k < B.size then (B[k], 0) else (0, ubRead)

/-- `matchrange(c, &ccl_buf[k])`. -/
def matchrange (B : Array Nat) (c k : Nat) : Bool × Nat :=
  if c == 45 then (false, 0)
  else
    let (s0, u0) := bget B k
    if s0 == 0 || s0 == 45 then (false, u0)
    else
      let (s1, u1) := bget B (k + 1)
      if s1 != 45 then (false, u0 ||| u1)
      else
        let (s2, u2) := bget B (k + 2)
        (s2 != 0 && decide (sc s0 ≤ sc c) && decide (sc c ≤ sc s2), u0 ||| u1 ||| u2)

def ismetachar (c : Nat) : Bool :=
  c == 115 || c == 83 || c == 119 || c == 87 || c == 100 || c == 68

/-- `matchmetachar(c, &ccl_buf[k])`. -/
def matchmetachar (B : Array Nat) (c k : Nat) : Bool × Nat :=
  let (s, u) := bget B k
  let r :=
    if s == 100 then isdigitC c
    else if s == 68 then !isdigitC c
    else if s == 119 then matchalphanum c
    else if s == 87 then !matchalphanum c
    else if s == 115 then isspaceC c
    else if s == 83 then !isspaceC c
    else c == s
  (r, u)

/-- `matchcharclass(c, &ccl_buf[k])`. -/
def matchcharclass (B : Array Nat) (c k : Nat) (ub : Nat) : Bool × Nat :=
  let (r, u) := matchrange B c k
  let ub := ub ||| u
  if r then (true, ub)
  else
    let (s0, u0) := bget B k
    let ub := ub ||| u0
    if s0 == 92 then
      -- `str += 1`
      let (m, u1) := matchmetachar B c (k + 1)
      let ub := ub ||| u1
      if m then (true, ub)
      else
        let (s1, u2) := bget B (k + 1)
        let ub := ub ||| u2
        if c == s1 && !ismetachar c then (true, ub)
        else if h : k + 1 < B.size then
          if B[k + 1] != 0 then matchcharclass B c (k + 2) ub else (false, ub)
        else (false, ub ||| ubRead)
    else if c == s0 then
      if c == 45 then
        -- `return ((str[-1] == '\0') || (str[1] == '\0'));`
        let (sm, u1) := if k = 0 then (0, ubRead) else bget B (k - 1)
        if sm == 0 then (true, ub ||| u1)
        else
          let (sp, u2) := bget B (k + 1)
          (sp == 0, ub ||| u1 ||| u2)
      else (true, ub)
    else if h : k < B.size then
      if B[k] != 0 then matchcharclass B c (k + 1) ub else (false, ub)
    else (false, ub ||| ubRead)
termination_by B.size - k

/-- The arrays a match runs on: `re_compiled`, `ccl_buf` and the text (without its NUL). -/
structure Ctx where
  P : Array Tok
  B : Array Nat
  T : Array Nat

/-- `matchone(p, c)` for the byte `c` (≠ 0). -/
def matchone (C : Ctx) (p : Tok) (c : Nat) : Bool × Nat :=
  if p.type == DOT then (true, 0)
  else if p.type == CHAR_CLASS then matchcharclass C.B c p.ccl 0
  else if p.type == INV_CHAR_CLASS then let (r, u) := matchcharclass C.B c p.ccl 0; (!r, u)
  else if p.type == DIGIT then (isdigitC c, 0)
  else if p.type == NOT_DIGIT then (!isdigitC c, 0)
  else if p.type == ALPHA then (matchalphanum c, 0)
  else if p.type == NOT_ALPHA then (!matchalphanum c, 0)
  else if p.type == WHITESPACE then (isspaceC c, 0)
  else if p.type == NOT_WHITESPACE then (!isspaceC c, 0)
  else ((p.ch : Int) == sc c, 0)

/-- The first loop of `matchstar` and `matchplus`:
`while ((text[0] != '\0') && matchone(p, *text)) { text++; (*matchlength)++; }`. -/
def advance (C : Ctx) (p : Tok) (ti : Nat) (ml : Int) (ub : Nat) : Nat × Int × Nat :=
  if h : ti < C.T.size then
    let c := C.T[ti]
    if c != 0 then
      let (m, u) := matchone C p c
      if m then advance C p (ti + 1) (ml + 1) (ub ||| u ||| chk (ml + 1))
      else (ti, ml, ub ||| u)
    else (ti, ml, ub)
  else if ti = C.T.size then (ti, ml, ub) else (ti, ml, ub ||| ubRead)
termination_by C.T.size - ti

/-! ## `matchpattern` and its helpers -/

/-- The result of a match function: its return value (≠ 0), `*matchlength` and the UB mask. -/
structure Res where
  ok : Bool
  ml : Int
  ub : Nat
deriving Repr, Inhabited

mutual

/-- The do-while loop of `matchpattern` at `pattern` = `&re_compiled[pi]`, `text` = `&T[ti]`;
`pre` is `*matchlength` on entry to `matchpattern`. -/
def mpLoop (C : Ctx) (pre : Int) (pi ti : Nat) (ml : Int) (ub : Nat) : Res :=
  if hpi : pi < C.P.size then
    let p0 := C.P[pi]
    if p0.type == UNUSED then
      matchquestion C p0 (pi + 2) ti ml (if pi + 2 ≤ C.P.size then ub else ub ||| ubPtr)
    else if hp1 : pi + 1 < C.P.size then
      let p1 := C.P[pi + 1]
      if p1.type == QUESTIONMARK then matchquestion C p0 (pi + 2) ti ml ub
      else if p1.type == STAR then matchstar C p0 (pi + 2) ti ml ub
      else if p1.type == PLUS then matchplus C p0 (pi + 2) ti ml ub
      else if p0.type == END && p1.type == UNUSED then
        let (c, u) := rd C.T ti
        ⟨c == 0, ml, ub ||| u⟩
      else
        let ml := ml + 1
        let ub := ub ||| chk ml
        let (c, u) := rd C.T ti
        let ub := ub ||| u
        if c != 0 then
          let (m, u') := matchone C p0 c
          if m then mpLoop C pre (pi + 1) (ti + 1) ml (ub ||| u')
          else ⟨false, pre, ub ||| u'⟩
        else ⟨false, pre, ub⟩
    else ⟨false, ml, ub ||| ubRead⟩
  else ⟨false, ml, ub ||| ubRead⟩
termination_by (4 * (C.P.size - pi) + 1, 0)

/-- `matchquestion(p, &re_compiled[pi], &T[ti], matchlength)`. -/
def matchquestion (C : Ctx) (p : Tok) (pi ti : Nat) (ml : Int) (ub : Nat) : Res :=
  if p.type == UNUSED then ⟨true, ml, ub⟩
  else
    let r := mpLoop C ml pi ti ml ub
    if r.ok then r
    else
      let (c, u) := rd C.T ti
      let ub := r.ub ||| u
      if c != 0 then
        let (m, u') := matchone C p c
        let ub := ub ||| u'
        if m then
          let r2 := mpLoop C r.ml pi (ti + 1) r.ml ub
          if r2.ok then ⟨true, r2.ml + 1, r2.ub ||| chk (r2.ml + 1)⟩ else ⟨false, r2.ml, r2.ub⟩
        else ⟨false, r.ml, ub⟩
      else ⟨false, r.ml, ub⟩
termination_by (4 * (C.P.size - pi) + 3, 0)

/-- `matchstar(p, &re_compiled[pi], &T[ti], matchlength)`. -/
def matchstar (C : Ctx) (p : Tok) (pi ti : Nat) (ml : Int) (ub : Nat) : Res :=
  let (ti', ml', ub') := advance C p ti ml ub
  starBack C pi ml ti ti' ml' ub'
termination_by (4 * (C.P.size - pi) + 3, 0)

/-- The second loop of `matchstar`,
`while (text >= prepoint) { if (matchpattern(pattern, text--, matchlength)) return 1; (*matchlength)--; }`,
then `*matchlength = prelen; return 0;`. -/
def starBack (C : Ctx) (pi : Nat) (prelen : Int) (pre ti : Nat) (ml : Int) (ub : Nat) : Res :=
  if pre ≤ ti then
    -- `text--` at the first byte of the text points before the array
    let ub := if ti = 0 then ub ||| ubStar else ub
    let r := mpLoop C ml pi ti ml ub
    if r.ok then r
    else
      let ml := r.ml - 1
      let ub := r.ub ||| chk ml
      if _h : ti = 0 then ⟨false, prelen, ub⟩
      else starBack C pi prelen pre (ti - 1) ml ub
  else ⟨false, prelen, ub⟩
termination_by (4 * (C.P.size - pi) + 2, ti)

/-- `matchplus(p, &re_compiled[pi], &T[ti], matchlength)`. -/
def matchplus (C : Ctx) (p : Tok) (pi ti : Nat) (ml : Int) (ub : Nat) : Res :=
  let (ti', ml', ub') := advance C p ti ml ub
  plusBack C pi ti ti' ml' ub'
termination_by (4 * (C.P.size - pi) + 3, 0)

/-- The second loop of `matchplus`,
`while (text > prepoint) { if (matchpattern(pattern, text--, matchlength)) return 1; (*matchlength)--; }`,
then `return 0;`. -/
def plusBack (C : Ctx) (pi pre ti : Nat) (ml : Int) (ub : Nat) : Res :=
  if _h : pre < ti then
    let r := mpLoop C ml pi ti ml ub
    if r.ok then r
    else plusBack C pi pre (ti - 1) (r.ml - 1) (r.ub ||| chk (r.ml - 1))
  else ⟨false, ml, ub⟩
termination_by (4 * (C.P.size - pi) + 2, ti)

end

/-! ## `re_matchp`, `re_match` -/

/-- The search loop of `re_matchp` (pattern not anchored); `idx` equals the text index `ti`. -/
def searchLoop (C : Ctx) (ti : Nat) (ml : Int) (ub : Nat) : Int × Int × Nat :=
  let r := mpLoop C ml 0 ti ml (ub ||| chk ti)
  if h : ti < C.T.size then
    let c := C.T[ti]
    if r.ok then (if c == 0 then -1 else ti, r.ml, r.ub)
    else if c != 0 then searchLoop C (ti + 1) r.ml r.ub
    else (-1, r.ml, r.ub)
  -- at the NUL a match returns -1 (`if (text[0] == '\0') return -1;`) and the loop ends
  else (-1, r.ml, r.ub ||| (if ti = C.T.size then 0 else ubRead))
termination_by C.T.size - ti

/-- `re_matchp(compiled, text, &matchlength)`: (return value, `matchlength`, UB mask). -/
def reMatchp (cp : Option (Array Tok × Array Nat)) (T : Array Nat) (ub : Nat) : Int × Int × Nat :=
  match cp with
  | none => (-1, 0, ub)
  | some (P, B) =>
    let C : Ctx := ⟨P, B, T⟩
    if (P.getD 0 {}).type == BEGIN then
      let r := mpLoop C 0 1 0 0 ub
      (if r.ok then 0 else -1, r.ml, r.ub)
    else searchLoop C 0 0 ub

/-- `re_match(p ++ [0], t ++ [0], &matchlength)` from program start (statics zero): the return
value, the final `matchlength`, and the UB mask (0: no UB). -/
def reMatch (p t : List Nat) : Int × Int × Nat :=
  let (cp, ub) := compile p.toArray
  reMatchp cp t.toArray ub

end EquivLean.Demo.XLang.TinyRegex
