import CIR
import Examples.Gen.Tokens

/-!
  An array of structs written through a pointer to one element
  (`Examples/cpp/tokens.cpp`): the token array of C parsers such as jsmn.
  The pointer `&toks[i]` is `.loc b [.idx i]` into the block that holds the
  array; a store to a member of that element rewrites element `i` of the
  array (`toks.set i …`).
-/

open CIR Gen.Tokens

set_option maxHeartbeats 4000000

namespace Examples.Tokens

/-- `fill_token(&toks[i], type, start, end)` overwrites element `i`. -/
@[cir_spec]
theorem fill_token_spec (b i : Nat) (toks : List Val) (o0 o1 o2 o3 : Val) (type start fin : Int)
    (k : BlockKind) (ty : Ty) (m : Mem)
    (hb : b < m.next) (ha : m.blocks b = some ⟨k, true, ty, .arr toks⟩) (hk : k ≠ .readonly)
    (ht : toks[i]? = some (.agg [o0, o1, o2, o3]))
    (htype : 0 ≤ type ∧ type ≤ 4294967295) (hstart : -2147483648 ≤ start ∧ start ≤ 2147483647)
    (hend : -2147483648 ≤ fin ∧ fin ≤ 2147483647)
    (hty : ∃ tlen, ty = .array (.record "tok") tlen) :
    Returns ctx fn_fill_token.sym [.ptr (.loc b [.idx i]), .int type, .int start, .int fin] m
      (fun v m' => v = none ∧
        m'.blocks b = some ⟨k, true, ty, .arr (toks.set i (.agg [.int type, .int start, .int fin, .int 0]))⟩ ∧
        Frame m m' [b]) := by
  obtain ⟨tlen, rfl⟩ := hty
  cir_start
  cir_vcg

end Examples.Tokens
