import EquivLean.Demo.Gen.Aeneas.TinyRegex.Funs
import EquivLean.Demo.XLang.TinyRegex.Model

/-!
# tiny-regex-c → Rust: the Rust values as model values

Shared by `RustMatch.lean` (the matcher group) and `RustCompile.lean` / `RustTop.lean`
(`re_compile`, `re_matchp`, `re_match`). Definitions as proposed by eq-aeneas (10-25 06:09Z).
-/

open Aeneas Aeneas.Std

namespace EquivLean.Demo.XLang.TinyRegex.Rust

def tok (o : tiny_regex.RegexObj) : Tok := { type := o.kind.val, ch := o.ch.val, ccl := o.ccl.val }

def ctx (re : tiny_regex.Regex) (text : Slice U8) : Ctx :=
  { P := (re.objs.val.map tok).toArray, B := (re.ccl_buf.val.map (·.val)).toArray,
    T := (text.val.map (·.val)).toArray }

/-- The model's unbounded int, wrapped (Rust wraps; equal when no `ubOverflow`). -/
def toI32 (v : Int) : I32 := ⟨BitVec.ofInt 32 v⟩

def res (r : Res) : Bool × I32 := (r.ok, toI32 r.ml)

def WF (re : tiny_regex.Regex) : Prop := (re.objs.val.getD 29 ⟨0#u8, 0#u8, 0#usize⟩).kind.val = 0

end EquivLean.Demo.XLang.TinyRegex.Rust
