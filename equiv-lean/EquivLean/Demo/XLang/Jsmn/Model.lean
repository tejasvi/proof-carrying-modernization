/-!
# jsmn: a functional model of `jsmn_parse`

zserge/jsmn @ 25647e6 (`jsmn.h`), default configuration (neither `JSMN_PARENT_LINKS` nor
`JSMN_STRICT`): one `jsmn_parse(parser, js, len, tokens, num_tokens)` call on a parser fresh from
`jsmn_init`, with `tokens != NULL`.  The model follows the C function by function:
`primScan`/`parsePrimitive` (`jsmn_parse_primitive`), `strScan`/`parseString`
(`jsmn_parse_string`, with the escapes and `\uXXXX`), `step` (one turn of `jsmn_parse`'s loop:
objects and arrays with the backward search for the open token, `toksuper`, `,` and `:`),
`mainLoop`, and `parse` (the final `JSMN_ERROR_PART` scan).

The input is the byte list `js` (bytes `< 256`; `len` is its length, and as in the C a NUL byte
ends the input) and `n = num_tokens`.  `parse js n = (ret, toks)` is the observation: `ret` is
`jsmn_parse`'s return value and `toks` the first `min (max ret 0) n` tokens of the array, that is
every token `jsmn_parse` filled when `ret ≥ 0` (then `ret = toks.length`), none when `ret < 0`.

The C reads bytes as (signed) `char`; the model reads them as numbers `0 ≤ b < 256`.  Both give the
same decisions: every comparison in `jsmn.h` is with an ASCII constant, and `js[pos] < 32 ||
js[pos] >= 127` holds for every byte `≥ 128` either way.
-/

namespace EquivLean.Demo.XLang.Jsmn

/-! ## Constants of `jsmn.h` -/

/-- `jsmntype_t`. -/
def UNDEFINED : Int := 0
def OBJECT : Int := 1
def ARRAY : Int := 2
def STRING : Int := 4
def PRIMITIVE : Int := 8

/-- `enum jsmnerr`. -/
def ERROR_NOMEM : Int := -1
def ERROR_INVAL : Int := -2
def ERROR_PART : Int := -3

/-- A token, `jsmntok_t` (`stop` is the C field `end`). -/
structure Tok where
  type : Int
  start : Int
  stop : Int
  size : Int
  deriving DecidableEq, Repr

/-- What `jsmn_alloc_token` leaves in a token (the type is set by the caller before any read). -/
def dflt : Tok := ⟨UNDEFINED, -1, -1, 0⟩

/-- An open token: `start != -1 && end == -1` (in the default configuration, an object or array
whose closing bracket has not been seen). -/
def isOpen (t : Tok) : Bool := t.start != -1 && t.stop == -1

/-- The parser and the filled part of the token array: `pos`, the tokens `tokens[0 .. toknext)`
(`toknext` is their number), `toksuper`. -/
structure St where
  pos : Nat
  toks : List Tok
  sup : Int
  deriving Repr

/-- `jsmn_init`. -/
def St.init : St := ⟨0, [], -1⟩

/-- The byte at `p` (0 past the end; the C only reads below `len`). -/
def byteAt (js : List Nat) (p : Nat) : Nat := js.getD p 0

/-- The C loop condition `pos < len && js[pos] != '\0'`. -/
def live (js : List Nat) (p : Nat) : Prop := p < js.length ∧ byteAt js p ≠ 0

instance (js : List Nat) (p : Nat) : Decidable (live js p) :=
  inferInstanceAs (Decidable (p < js.length ∧ byteAt js p ≠ 0))

/-- `tokens[i].size++`. -/
def incSize (toks : List Tok) (i : Nat) : List Tok :=
  toks.modify i fun t => { t with size := t.size + 1 }

/-- `tokens[toksuper].size++` when `toksuper != -1`. -/
def bumpSup (toks : List Tok) (sup : Int) : List Tok :=
  if sup = -1 then toks else incSize toks sup.toNat

/-- The backward search of the closing bracket: the largest index below `i` holding an open token. -/
def lastOpen (toks : List Tok) : Nat → Option Nat
  | 0 => none
  | i + 1 => if isOpen (toks.getD i dflt) then some i else lastOpen toks i

/-- The backward search of `,`: the largest index below `i` holding an open object or array. -/
def lastOpenCont (toks : List Tok) : Nat → Option Nat
  | 0 => none
  | i + 1 =>
    let t := toks.getD i dflt
    if (t.type = ARRAY ∨ t.type = OBJECT) ∧ isOpen t then some i else lastOpenCont toks i

/-! ## `jsmn_parse_primitive` -/

/-- The characters that end a primitive (non-strict mode: `:` too). -/
def primDelim (c : Nat) : Bool :=
  c == 58 || c == 9 || c == 13 || c == 10 || c == 32 || c == 44 || c == 93 || c == 125

/-- The scan of `jsmn_parse_primitive` from `p`: the position where the primitive ends (a
delimiter, the end of the input or a NUL), or `none` for a character outside `32 .. 126`. -/
def primScan (js : List Nat) (p : Nat) : Option Nat :=
  if h : live js p then
    let c := byteAt js p
    if primDelim c then some p
    else if c < 32 ∨ 127 ≤ c then none
    else primScan js (p + 1)
  else some p
termination_by js.length - p
decreasing_by exact Nat.sub_lt_sub_left h.1 (Nat.lt_succ_self p)

/-- `jsmn_parse_primitive` at `st.pos`: a `JSMN_PRIMITIVE` token `[st.pos, e)`, and `pos = e - 1`
as the C leaves it. -/
def parsePrimitive (js : List Nat) (n : Nat) (st : St) : Except Int St :=
  match primScan js st.pos with
  | none => .error ERROR_INVAL
  | some e =>
    if n ≤ st.toks.length then .error ERROR_NOMEM
    else .ok ⟨e - 1, st.toks ++ [⟨PRIMITIVE, st.pos, e, 0⟩], st.sup⟩

/-! ## `jsmn_parse_string` -/

/-- The characters allowed after a backslash, other than `u`. -/
def escChar (c : Nat) : Bool :=
  c == 34 || c == 47 || c == 92 || c == 98 || c == 102 || c == 114 || c == 110 || c == 116

/-- A hexadecimal digit. -/
def hexDigit (c : Nat) : Bool := (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 70) || (97 ≤ c && c ≤ 102)

/-- The scan of `jsmn_parse_string` from `p`, with `hex` digits of a `\uXXXX` still to read: the
position of the closing quote, `JSMN_ERROR_INVAL` (a bad escape or hex digit) or
`JSMN_ERROR_PART` (the input ends first). -/
def strScan (js : List Nat) (p hex : Nat) : Except Int Nat :=
  if h : live js p then
    let c := byteAt js p
    if 0 < hex then
      if hexDigit c then strScan js (p + 1) (hex - 1) else .error ERROR_INVAL
    else if c = 34 then .ok p
    else if c = 92 ∧ p + 1 < js.length then
      let e := byteAt js (p + 1)
      if escChar e then strScan js (p + 2) 0
      else if e = 117 then strScan js (p + 2) 4
      else .error ERROR_INVAL
    else strScan js (p + 1) 0
  else .error ERROR_PART
termination_by js.length - p
decreasing_by all_goals (have := h.1; omega)

/-- `jsmn_parse_string` at the opening quote `st.pos`: a `JSMN_STRING` token from `st.pos + 1` to
the closing quote, where `pos` is left. -/
def parseString (js : List Nat) (n : Nat) (st : St) : Except Int St :=
  match strScan js (st.pos + 1) 0 with
  | .error e => .error e
  | .ok q =>
    if n ≤ st.toks.length then .error ERROR_NOMEM
    else .ok ⟨q, st.toks ++ [⟨STRING, st.pos + 1, q, 0⟩], st.sup⟩

/-! ## `jsmn_parse` -/

/-- One turn of `jsmn_parse`'s loop on the byte at `st.pos`, including the final `pos++`. -/
def step (js : List Nat) (n : Nat) (st : St) : Except Int St :=
  let c := byteAt js st.pos
  if c = 123 ∨ c = 91 then
    -- `{` `[`: a new open token, a child of `toksuper`, which becomes `toksuper`
    if n ≤ st.toks.length then .error ERROR_NOMEM
    else
      .ok ⟨st.pos + 1,
        bumpSup st.toks st.sup ++ [⟨if c = 123 then OBJECT else ARRAY, st.pos, -1, 0⟩],
        st.toks.length⟩
  else if c = 125 ∨ c = 93 then
    -- `}` `]`: close the last open token (of the same type); `toksuper` becomes the open token
    -- below it, or -1
    match lastOpen st.toks st.toks.length with
    | none => .error ERROR_INVAL
    | some i =>
      let t := st.toks.getD i dflt
      if t.type ≠ (if c = 125 then OBJECT else ARRAY) then .error ERROR_INVAL
      else
        .ok ⟨st.pos + 1, st.toks.set i { t with stop := st.pos + 1 },
          match lastOpen st.toks i with
          | some j => j
          | none => -1⟩
  else if c = 34 then
    match parseString js n st with
    | .error e => .error e
    | .ok st' => .ok ⟨st'.pos + 1, bumpSup st'.toks st'.sup, st'.sup⟩
  else if c = 9 ∨ c = 13 ∨ c = 10 ∨ c = 32 then
    .ok ⟨st.pos + 1, st.toks, st.sup⟩
  else if c = 58 then
    -- `:`: `toksuper = toknext - 1`
    .ok ⟨st.pos + 1, st.toks, (st.toks.length : Int) - 1⟩
  else if c = 44 then
    -- `,`: after a key or a value, `toksuper` goes back to the open object or array
    let t := st.toks.getD st.sup.toNat dflt
    if st.sup ≠ -1 ∧ t.type ≠ ARRAY ∧ t.type ≠ OBJECT then
      .ok ⟨st.pos + 1, st.toks,
        match lastOpenCont st.toks st.toks.length with
        | some i => i
        | none => st.sup⟩
    else .ok ⟨st.pos + 1, st.toks, st.sup⟩
  else
    -- every other byte starts a primitive
    match parsePrimitive js n st with
    | .error e => .error e
    | .ok st' => .ok ⟨st'.pos + 1, bumpSup st'.toks st'.sup, st'.sup⟩

/-- `jsmn_parse`'s loop.  Every turn moves `pos` forward (`step_pos_lt`); the test of that is only
there to make the recursion visibly terminating. -/
def mainLoop (js : List Nat) (n : Nat) (st : St) : Except Int St :=
  if _h : live js st.pos then
    match step js n st with
    | .error e => .error e
    | .ok st' => if _h' : st.pos < st'.pos then mainLoop js n st' else .ok st'
  else .ok st
termination_by js.length - st.pos
decreasing_by have := _h.1; have := _h'; omega

/-- **The model**: `jsmn_parse(&p, js, js.length, tokens, n)` after `jsmn_init(&p)`, with `tokens`
an array of `n` tokens.  `ret` is the return value; the tokens are the first `min (max ret 0) n`
entries of the array after the call (all filled tokens when `ret ≥ 0`, none otherwise). -/
def parse (js : List Nat) (n : Nat) : Int × List Tok :=
  match mainLoop js n St.init with
  | .error e => (e, [])
  | .ok st => if st.toks.any isOpen then (ERROR_PART, []) else (st.toks.length, st.toks)

end EquivLean.Demo.XLang.Jsmn
