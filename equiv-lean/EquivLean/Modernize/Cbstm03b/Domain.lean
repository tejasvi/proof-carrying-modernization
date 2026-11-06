import EquivLean.Demo.Cobol.Cbstm03b.Prog

/-!
# CBSTM03B: the domain of the statements (written by hand)

coblean's `cbstm03b_call` covers every call. For a keyed READ of ACCTFILE it assumes that the key's first `k` bytes
decode as an unsigned number (`decodeNum`), and `decodeNum` (NUMPROC(NOPFD)) also accepts an overpunched last digit,
a last byte with a zone A–F (`{`, `A`–`I`, `}`, `J`–`R`, …), which the translations do not implement. Account keys
are digit strings in CardDemo, so the statements carry this domain: for a keyed READ of ACCTFILE, the key's first `k`
bytes are the CP037 digits `0xF0`–`0xF9`. This is the one part of the CBSTM03B statements that is not generated.
-/

open Cobol

namespace EquivLean.Modernize.Cbstm03b

open CardDemo.Cbstm03b (Files opReadK ddAcct)

/-- For a keyed READ of ACCTFILE, the key's first `k` bytes (`LK-M03B-KEY`, at 1219) are CP037 digits. The
arguments are the value binders of `cbstm03b_call`: the environment, the storage, the files, the key length `k`
and the key's value `v`. -/
def Domain (_env : Env) (m : Mem) (_fs : Files) (k _v : Int) : Prop :=
  m.read 1216 1 = [opReadK] → m.read 1208 8 = ddAcct → ∀ b ∈ m.read 1219 k.toNat, 240 ≤ b ∧ b ≤ 249

end EquivLean.Modernize.Cbstm03b
