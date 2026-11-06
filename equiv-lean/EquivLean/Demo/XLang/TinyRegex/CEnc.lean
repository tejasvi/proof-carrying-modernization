import CIR
import EquivLean.Demo.XLang.TinyRegex.Model

/-!
# tiny-regex-c → model, C side: how cirlean stores the model's data

`re_compiled` is block 25 and `ccl_buf` block 24 of the module (function-local statics).  A
`regex_t` is `.agg [type, u]`, the union `u` as `.agg [u.ch, u.ccl]` with only its active member
defined (`tokV`); a C string is its bytes as `char`s then the NUL (`patL`).
-/

namespace EquivLean.Demo.XLang.TinyRegex.C

open CIR
open EquivLean.Demo.XLang.TinyRegex (Tok sc)

/-- A `regex_t` as cirlean stores it (`bc`: `ccl_buf`'s block). -/
def tokV (bc : Nat) (t : Tok) : Val :=
  if t.type = 8 ∨ t.type = 9 then .agg [.int t.type, .agg [.undef, .ptr (.loc bc [.idx t.ccl])]]
  else .agg [.int t.type, .agg [.int t.ch, .undef]]

/-- The model's token of a stored `regex_t`. -/
def decTok : Val → Tok
  | .agg [.int ty, .agg [.int ch, _]] => { type := ty.toNat, ch := ch.toNat }
  | .agg [.int ty, .agg [_, .ptr (.loc _ [.idx k])]] => { type := ty.toNat, ccl := k }
  | _ => {}

def decRe (L : List Val) : Array Tok := (L.map decTok).toArray

def decBuf (B : List Val) : Array Nat :=
  (B.map fun v => match v with | .int x => x.toNat | _ => 0).toArray

/-- A C string as cirlean holds it: its bytes as `char`s, then the NUL. -/
def patL (p : List Nat) : List Int := p.map (fun b => sc b) ++ [0]

end EquivLean.Demo.XLang.TinyRegex.C
