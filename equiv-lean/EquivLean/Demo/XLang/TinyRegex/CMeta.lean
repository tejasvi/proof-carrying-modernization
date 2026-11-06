import EquivLean.Demo.XLang.TinyRegex.CHelpers
import EquivLean.Demo.XLang.TinyRegex.CBase

/-!
# tiny-regex-c → model, C side: `matchmetachar`

`matchmetachar(c, str)` with `str` = `&ccl_buf[k]` (block `bc` holding `xs.map .int`): the class of
`\d \D \w \W \s \S` named by `str[0]`, else `c == str[0]`.
-/

open CIR CIR.Std EquivLean.Demo.Gen.Cir.TinyRegex

set_option maxHeartbeats 40000000

namespace EquivLean.Demo.XLang.TinyRegex.C

set_option cir.inline false in
/-- `matchmetachar(c, &ccl_buf[k])`. -/
@[cir_spec]
theorem matchmetachar_spec (xs : List Int) (bc k : Nat) (c : Int) (kd : BlockKind) (tyc : Ty) (m : Mem)
    (hblk : m.blocks bc = some ⟨kd, true, tyc, .arr (xs.map .int)⟩)
    (htyc : ∃ es tlen, tyc = .array (.int es 8) tlen) (hbc : bc < m.next)
    (hc : -128 ≤ c ∧ c ≤ 127) (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255) (hk : k < xs.length) :
    Returns ctx fn_matchmetachar.sym [.int c, .ptr (.loc bc [.idx k])] m
      (fun r m' => (∃ v, r = some (.int v) ∧ -2147483648 ≤ v ∧ v ≤ 2147483647 ∧ (v ≠ 0 ↔ metaP c (xs.getD k 0))) ∧
        Frame m m' []) := by
  obtain ⟨es, tlen, rfl⟩ := htyc
  have cirH_c := hc
  have cirH_k0 : ((k : Int) + 0).toNat = k := by omega
  have cirH_g : ∀ (i : Nat) (h : i < xs.length), xs[i] = xs.getD i 0 := fun i h => getElem_eq_getD h
  have cirH_r0 := getD_range hxs k
  have cirH_s0 := s8_facts cirH_r0
  unfold metaP alnumP alphaP digitP spaceP
  cir_start
  cir_vcg
  all_goals (try (rcases s8_cases (xs.getD k 0) with ⟨h0, e0⟩ | ⟨h0, e0⟩ <;>
    (try simp only [e0] at *) <;> (try split) <;> (try split) <;> omega))

end EquivLean.Demo.XLang.TinyRegex.C
