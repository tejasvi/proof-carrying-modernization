import EquivLean.Demo.Gen.Aeneas.JsmnRs.Funs
import EquivLean.Demo.XLang.Jsmn.Model

/-!
# jsmn → safe Rust: the Rust run and its observation

The safe Rust translation (`examples/rust/jsmn_rs`, extracted by Charon + Aeneas into
`EquivLean.Demo.Gen.Aeneas.JsmnRs`) is called as the C is: `jsmn_init`, then one `jsmn_parse` on the
source bytes and an array of `num_tokens` tokens.  `rustObs` is the observation the model's
`parse` gives: the return value and the first `min (max ret 0) num_tokens` tokens.
-/

open Aeneas Aeneas.Std

namespace EquivLean.Demo.XLang.Jsmn

/-- An input: the source bytes and `num_tokens` (the C `unsigned int`). -/
abbrev Input := Slice U8 × U32

/-- The bytes of a slice, as the model's list. -/
def bytes (s : Slice U8) : List Nat := s.val.map (·.val)

/-- The tokens of the caller's array before the call (jsmn reads only the tokens it allocates). -/
def tokDflt : jsmn_rs.JsmnTok := ⟨.Undefined, 0#i32, 0#i32, 0#i32⟩

theorem usize_max_ge : 4294967295 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max_eq, U64.max_eq]

/-- The caller's array of `n` tokens. -/
def initToks (n : U32) : Slice jsmn_rs.JsmnTok :=
  Slice.from (List.replicate n.val tokDflt) (by
    have h1 := UScalar.hBounds n
    have h2 := usize_max_ge
    simp only [UScalarTy.U32_numBits_eq] at h1
    simp only [List.length_replicate]
    omega)

/-- The Rust side: `jsmn_init`, then `jsmn_parse` on the source and an array of `num_tokens`
tokens; the return value and the array after the call. -/
def rustRun (x : Input) : Result (I32 × Slice jsmn_rs.JsmnTok) := do
  let p ← jsmn_rs.jsmn_init
  let (r, _, toks) ← jsmn_rs.jsmn_parse p x.1 (initToks x.2)
  Result.ok (r, toks)

/-- `jsmntype_t`'s C value. -/
def typeCode : jsmn_rs.JsmnType → Int
  | .Undefined => UNDEFINED
  | .Object => OBJECT
  | .Array => ARRAY
  | .String => STRING
  | .Primitive => PRIMITIVE

/-- A Rust token as the model's token. -/
def toTok (t : jsmn_rs.JsmnTok) : Tok := ⟨typeCode t.typ, t.start.val, t.end.val, t.size.val⟩

/-- The observation of a Rust run with `n` tokens: the return value and the first
`min (max ret 0) n` tokens. -/
def rustObs (n : Nat) (y : I32 × Slice jsmn_rs.JsmnTok) : Int × List Tok :=
  (y.1.val, (y.2.val.take (min (max y.1.val 0).toNat n)).map toTok)

/-- The source has `2^28` bytes or more. -/
def Long (x : Input) : Prop := 2 ^ 28 ≤ x.1.val.length

end EquivLean.Demo.XLang.Jsmn
