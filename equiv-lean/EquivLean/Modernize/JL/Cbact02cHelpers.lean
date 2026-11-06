-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbact02cHelpers.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CB`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbact02c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbact02cHelpers.lean

  `Cbact02c.spaces(int)` (`n` spaces) and `Cbact02c.zeroPad(long, int)` (the last `n` decimal
  digits of `v ≥ 0`, zero-padded), each with one loop invariant.
-/
import EquivLean.Modernize.JL.Cbact02cProg

open Jimple

namespace EquivLean.Modernize.JL

abbrev spacesRef : MethodRef := EquivLean.Modernize.Cbact02c.Java.Gen.Cbact02c.«spaces(int)».ref

def spacesSpec : Spec := Spec.of
  (fun args _ => ∃ n : I32, args = [.int n] ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (fixStr [] n.toInt.toNat)) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- At the loop head (statement 4): the builder holds `i` spaces. -/
def spacesInv : Invariants := [(4, fun args σ0 fr σ => ∀ n : I32, args = [.int n] →
  ∃ sb i, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int i) ∧ fr.get 2 = some (.ref sb) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (fixStr [] i.toInt.toNat)) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem spaces_vc : MethodVC EquivLean.Modernize.Cbact02c.Java.Gen.prog (fun _ => none) 0 spacesRef spacesSpec spacesInv 60 := by
  jverify [ite_nat_ne, spacesSpec, spacesInv, Grows, fixStr]

abbrev zeroPadRef : MethodRef := EquivLean.Modernize.Cbact02c.Java.Gen.Cbact02c.«zeroPad(long,int)».ref

def zeroPadSpec : Spec := Spec.of
  (fun args _ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧ 0 ≤ v.toInt ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (zpadStr v.toNat n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- At the loop head (statement 8): positions `i+1 …` of the array hold the digits written so
    far, and the rest of the number is `l`. -/
def zeroPadInv : Invariants := [(8, fun args σ0 fr σ => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
  ∃ arr i l xs, fr.get 4 = some (.int i) ∧ fr.get 1 = some (.long l) ∧ fr.get 6 = some (.ref arr) ∧
    σ.heap arr = some (.array (.prim .char) xs) ∧ xs.length = n.toInt.toNat ∧
    0 ≤ l.toInt ∧ -1 ≤ i.toInt ∧ i.toInt < n.toInt ∧
    zpadStr v.toNat n.toInt.toNat =
      zpadStr l.toNat (i.toInt + 1).toNat ++ Native.charsOf (xs.drop (i.toInt + 1).toNat) ∧
    σ0.next ≤ arr ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem zeroPad_vc : MethodVC EquivLean.Modernize.Cbact02c.Java.Gen.prog (fun _ => none) 0 zeroPadRef zeroPadSpec zeroPadInv 80 := by
  jverify [ite_nat_ne, zeroPadSpec, zeroPadInv, Grows, zpadStr, digitChar, sdiv10_toNat_of_nonneg, sdiv10_nonneg,
    digit_char, drop_set_self]

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.spaces_vc
#print axioms EquivLean.Modernize.JL.zeroPad_vc
