import CIR
import EquivLean.Demo.Gen.Cir.TinyRegex
import EquivLean.Demo.XLang.TinyRegex.Model

/-!
# tiny-regex-c → model, C side: the values of `re_compile`'s statics

`re_compile.ccl_buf` is global 24 and `re_compile.re_compiled` global 25 of the generated module
(`Module.initMem` allocates global `i` in block `i`).  A `regex_t` is `.agg [type, u]`; the union
`u` is `.agg [ch, ccl]` with its inactive member `.undef` (cirlean's union encoding; the
zero-initialised union has `ch` active).  `tokVal t` is the C value of the model's token `t`: the
class kinds hold `ccl` as a pointer into `ccl_buf`, all other kinds hold `ch`.
-/

namespace EquivLean.Demo.XLang.TinyRegex.C

open CIR EquivLean.Demo.Gen.Cir.TinyRegex
open EquivLean.Demo.XLang.TinyRegex

/-- Block of `re_compile.ccl_buf`. -/
abbrev bCcl : Nat := 24
/-- Block of `re_compile.re_compiled`. -/
abbrev bRe : Nat := 25

/-- The token kinds that hold a character class (`u.ccl`). -/
def isClassKind (k : Nat) : Bool := k == CHAR_CLASS || k == INV_CHAR_CLASS

/-- The C value of a `regex_t` described by the model's token `t`. -/
def tokVal (t : Tok) : Val :=
  if isClassKind t.type then .agg [.int t.type, .agg [.undef, .ptr (.loc bCcl [.idx t.ccl])]]
  else .agg [.int t.type, .agg [.int t.ch, .undef]]

/-- The value of `re_compiled`. -/
def reVal (re : Array Tok) : Val := .arr (re.toList.map tokVal)

/-- The value of `ccl_buf`. -/
def bufVal (buf : Array Nat) : Val := .arr (buf.toList.map fun (b : Nat) => Val.int (b : Int))

/-- The C string of the pattern `p` (bytes before the NUL): signed `char`s, then the NUL. -/
def patVal (p : List Nat) : Val := .arr ((p ++ [0]).map fun b => .int (sc b))

/-- The statics as zero-initialised at program start. -/
theorem reVal_zero :
    reVal (Array.replicate MAXOBJ {}) =
      .arr (List.replicate 30 (.agg [.int 0, .agg [.int 0, .undef]])) := by
  simp [reVal, tokVal, isClassKind, MAXOBJ, CHAR_CLASS, INV_CHAR_CLASS]

theorem bufVal_zero : bufVal (Array.replicate MAXCCL 0) = .arr (List.replicate 40 (.int 0)) := by
  simp [bufVal, MAXCCL]

end EquivLean.Demo.XLang.TinyRegex.C
