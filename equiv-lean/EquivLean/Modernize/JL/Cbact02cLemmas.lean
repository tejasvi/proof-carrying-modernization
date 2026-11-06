-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbact02cLemmas.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CB`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbact02c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbact02cLemmas.lean

  The texts of the CBACT02C contracts in closed form, for linking them to other models of the
  records: a text of the field's length is displayed as it is (`fixStr_eq_self`); `zpadStr c n`
  is the last `n` decimal digits of `c` (`zpadStr_eq_map`), and a `long` holding `v ≥ 0` gives
  the digits of `v` (`zpadStr_ofInt`).
-/
import EquivLean.Modernize.JL.Cbact02cProg

open Jimple

namespace EquivLean.Modernize.JL

theorem fixStr_eq_map (s : JStr) : ∀ n, fixStr s n = (List.range n).map (fun i => s.getD i space)
  | 0 => rfl
  | n + 1 => by rw [fixStr, fixStr_eq_map s n, List.range_succ, List.map_append]; rfl

/-- A text of the field's length is displayed as it is. -/
theorem fixStr_eq_self {s : JStr} {n : Nat} (h : s.length = n) : fixStr s n = s := by
  subst h
  rw [fixStr_eq_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [h2]

/-- Digit `j` (from the right, from 0) of `c` is `c / 10 ^ j % 10`. -/
theorem zpadStr_eq_map : ∀ (n c : Nat),
    zpadStr c n = (List.range n).reverse.map (fun j => digitChar (c / 10 ^ j % 10))
  | 0, _ => rfl
  | n + 1, c => by
    rw [zpadStr, zpadStr_eq_map n (c / 10), List.range_succ_eq_map, List.reverse_cons,
      List.map_append, ← List.map_reverse, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
    · simp

theorem ofInt64_toNat {v : Int} (h0 : 0 ≤ v) (h1 : v < 2 ^ 63) :
    (BitVec.ofInt 64 v).toNat = v.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (by omega)]

/-- The digits of the value of a `long` holding `0 ≤ v < 2 ^ 63`. -/
theorem zpadStr_ofInt {v : Int} (n : Nat) (h0 : 0 ≤ v) (h1 : v < 2 ^ 63) :
    zpadStr (BitVec.ofInt 64 v).toNat n = zpadStr v.toNat n := by
  rw [ofInt64_toNat h0 h1]

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.fixStr_eq_self
#print axioms EquivLean.Modernize.JL.zpadStr_eq_map
#print axioms EquivLean.Modernize.JL.zpadStr_ofInt
