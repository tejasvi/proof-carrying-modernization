import EquivLean.Demo.XLang.TinyRegex.CHelpers
import EquivLean.Demo.XLang.TinyRegex.CBase

/-!
# tiny-regex-c → model, C side: the class helpers

Contracts of `matchrange`, `matchmetachar` and `matchcharclass`, which read a class string in
`ccl_buf` through a `const char*` (`str` = `&ccl_buf[k]`).  `ccl_buf` is block `bc`, holding
`xs.map .int` (its bytes as `unsigned char`s, `0 ≤ x ≤ 255`); a `char` read of byte `x` gives
`s8 x` (cirlean's `loadTy`: the signed counterpart of the stored type, C11 6.5p7).
-/

open CIR CIR.Std EquivLean.Demo.Gen.Cir.TinyRegex

set_option maxHeartbeats 40000000

namespace EquivLean.Demo.XLang.TinyRegex.C

set_option cir.inline false in
/-- `matchrange(c, &ccl_buf[k])`. -/
@[cir_spec]
theorem matchrange_spec (xs : List Int) (bc k : Nat) (c : Int) (kd : BlockKind) (tyc : Ty) (m : Mem)
    (hblk : m.blocks bc = some ⟨kd, true, tyc, .arr (xs.map .int)⟩)
    (htyc : ∃ es tlen, tyc = .array (.int es 8) tlen) (hbc : bc < m.next)
    (hc : -128 ≤ c ∧ c ≤ 127) (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255)
    (hk : k < xs.length) (hk1 : c ≠ 45 → xs.getD k 0 ≠ 0 → xs.getD k 0 ≠ 45 → k + 1 < xs.length)
    (hk2 : c ≠ 45 → xs.getD k 0 ≠ 0 → xs.getD k 0 ≠ 45 → xs.getD (k + 1) 0 = 45 → k + 2 < xs.length) :
    Returns ctx fn_matchrange.sym [.int c, .ptr (.loc bc [.idx k])] m
      (fun r m' => (∃ v, r = some (.int v) ∧ -2147483648 ≤ v ∧ v ≤ 2147483647 ∧ (v ≠ 0 ↔ rangeP c xs k)) ∧ Frame m m' []) := by
  obtain ⟨es, tlen, rfl⟩ := htyc
  unfold rangeP
  have cirH_c := hc
  have cirH_k0 : ((k : Int) + 0).toNat = k := by omega
  have cirH_k1 : ((k : Int) + 1).toNat = k + 1 := by omega
  have cirH_k2 : ((k : Int) + 2).toNat = k + 2 := by omega
  have cirH_g : ∀ (i : Nat) (h : i < xs.length), xs[i] = xs.getD i 0 := fun i h => getElem_eq_getD h
  have cirH_r0 := getD_range hxs k
  have cirH_r1 := getD_range hxs (k + 1)
  have cirH_r2 := getD_range hxs (k + 2)
  have cirH_s0 := s8_facts cirH_r0
  have cirH_s1 := s8_facts cirH_r1
  have cirH_s2 := s8_facts cirH_r2
  cir_start
  cir_vcg
  all_goals (try (rcases s8_cases (xs.getD k 0) with ⟨h0, e0⟩ | ⟨h0, e0⟩ <;>
    rcases s8_cases (xs.getD (k + 2) 0) with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
    (try simp only [e0, e2] at *) <;> (try split) <;> (try split) <;> omega))

end EquivLean.Demo.XLang.TinyRegex.C
