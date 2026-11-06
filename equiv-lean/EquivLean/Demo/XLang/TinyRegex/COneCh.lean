import EquivLean.Demo.XLang.TinyRegex.CHelpers
import EquivLean.Demo.XLang.TinyRegex.CBase

/-!
# tiny-regex-c → model, C side: `matchone` on the non-class tokens

`matchone(p, c)` for a `regex_t` whose union has `u.ch` active (see `COne.lean`).
-/

open CIR CIR.Std EquivLean.Demo.Gen.Cir.TinyRegex

set_option maxHeartbeats 40000000

namespace EquivLean.Demo.XLang.TinyRegex.C

/-- The test of `matchone` for a token of a type other than the classes. -/
def oneChP (ty ch : Nat) (c : Int) : Prop :=
  if ty = 1 then True
  else if ty = 10 then digitP c else if ty = 11 then ¬ digitP c
  else if ty = 12 then alnumP c else if ty = 13 then ¬ alnumP c
  else if ty = 14 then spaceP c else if ty = 15 then ¬ spaceP c
  else (ch : Int) = c

set_option cir.inline false in
/-- `matchone(p, c)` for a token with `u.ch` active (every type but the classes). -/
@[cir_spec]
theorem matchone_ch_spec (ty ch : Nat) (c : Int) (m : Mem) (hc : -128 ≤ c ∧ c ≤ 127)
    (hty : ty < 256) (hch : ch < 256) (h8 : ty ≠ 8) (h9 : ty ≠ 9) :
    Returns ctx fn_matchone.sym [.agg [.int ty, .agg [.int ch, .undef]], .int c] m
      (fun r m' => (∃ v, r = some (.int v) ∧ -2147483648 ≤ v ∧ v ≤ 2147483647 ∧
        (v ≠ 0 ↔ oneChP ty ch c)) ∧ Frame m m' []) := by
  have cirH_c := hc
  unfold oneChP alnumP
  unfold alphaP digitP spaceP
  cir_start
  cir_vcg
  all_goals (try (first | omega | (split <;> (try simp_all) <;> omega) | (simp_all; omega)))

end EquivLean.Demo.XLang.TinyRegex.C
