-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermSearch.lean (sha256 a35f55535663dcae...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaRunHelpers3
import Jimple.TermSplit

/-!
# CBACT04C → Java, termination: the searches `findAcct`, `findDisc` (thin VCs)

The thin twins of `findAcct_vc` and `findDisc_vc` (`JavaRunHelpers3`), case for case: each loop
counts its index `i` up to the array's length (below `2^31`), variant `2^31 - i` (`findAcct`: local
2, `findDisc`: local 6).
-/

open Jimple

-- as in the original: key comparisons (`lcmp`) split two ways, by `jlong_cmp_eq_zero_iff`
attribute [-jsimp] JLong.cmp_eq

namespace EquivLean.Modernize.Cbact04c.Java

/-- `findAcct`: `2^31 - i` (local `i` 2). -/
def findAcctVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 2 with
  | some (.int i) => (2147483648 - i.toInt).toNat
  | _ => 0

/-- `findDisc`: `2^31 - i` (local `i` 6). -/
def findDiscVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 6 with
  | some (.int i) => (2147483648 - i.toInt).toNat
  | _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem findAcct_thin (a : Addr) (key : I64) (et : JType) (xs : List Value) :
    ThinVC Gen.prog (fun _ => none) 0 findAcctRef (findAcctSpecG a key et xs)
      (findAcctInv a key xs) (fun _ => findAcctVar) 20 := by
  refine ⟨_, rfl, ?_⟩
  intro args σ0 hpre
  simp only [findAcctInv, Invariants.inst, List.map_cons, List.map_nil, List.lookup,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [findAcctSpecG, Spec.of, findAcctPreG] at hpre
  obtain ⟨rfl, hheap, hlen, hall, ⟨x0, hx0mem, hx0⟩⟩ := hpre
  refine ⟨?_, ?_⟩
  · jvc [findAcctVar]
  · intro fr σ h
    obtain ⟨i, h6, h3, h2, hi0, hilen, htake, rfl⟩ := h
    by_cases hc : (xs.length : Int) ≤ i.toInt
    · jvc [findAcctVar, jlong_cmp_eq_zero_iff]
    · have hn : i.toInt.toNat < xs.length := by omega
      obtain ⟨y, fs, n, hyeq, hyheap, hfid⟩ := hall xs[i.toInt.toNat] (List.getElem_mem hn)
      have hget : xs[i.toInt.toNat]? = some (.ref y) := by rw [List.getElem?_eq_getElem hn, hyeq]
      clear hall
      jvc [findAcctVar, jlong_cmp_eq_zero_iff]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem findDisc_thin (a : Addr) (len : I32) (gs ts : Addr) (g t : JStr) (cat : I64) (et : JType)
    (xs : List Value) :
    ThinVC Gen.prog (fun _ => none) 0 findDiscRef (findDiscSpecG a len gs ts g t cat et xs)
      (findDiscInv a len gs ts g t cat xs) (fun _ => findDiscVar) 30 := by
  refine ⟨_, rfl, ?_⟩
  intro args σ0 hpre
  simp only [findDiscInv, Invariants.inst, List.map_cons, List.map_nil, List.lookup,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [findDiscSpecG, Spec.of, findDiscPreG] at hpre
  obtain ⟨rfl, hheap, hlenx, hlen, hgs, hts, hall, ⟨x0, hx0mem, hx0⟩⟩ := hpre
  refine ⟨?_, ?_⟩
  · jvc [findDiscVar]
  · intro fr σ h
    obtain ⟨i, h3, h5, h7, h8, h1, h6, hi0, hilen, htake, rfl⟩ := h
    by_cases hc : (xs.length : Int) ≤ i.toInt
    · jvc [findDiscVar]
    · have hn : i.toInt.toNat < xs.length := by omega
      obtain ⟨y, fs, gv, tv, g', t', c', hyeq, hyheap, hfg, hgv, hft, htv, hfc⟩ :=
        hall xs[i.toInt.toNat] (List.getElem_mem hn)
      have hget : xs[i.toInt.toNat]? = some (.ref y) := by rw [List.getElem?_eq_getElem hn, hyeq]
      clear hall
      jvc [findDiscVar, jlong_cmp_eq_zero_iff]

end EquivLean.Modernize.Cbact04c.Java
