import EquivLean.Modernize.Cbtrn03c.JavaTop.PdEntry
import EquivLean.Modernize.Cbtrn03c.JavaTop.PdCalls
import EquivLean.Modernize.Cbtrn03c.JavaTop.Pd15
import EquivLean.Modernize.Cbtrn03c.JavaTop.Pd19n
import EquivLean.Modernize.Cbtrn03c.JavaTop.Pd19p
import EquivLean.Modernize.Cbtrn03c.JavaTop.Pd35n
import EquivLean.Modernize.Cbtrn03c.JavaTop.Pd35p
import EquivLean.Modernize.Cbtrn03c.JavaTop.Pd49n
import EquivLean.Modernize.Cbtrn03c.JavaTop.Pd49p
import EquivLean.Modernize.Cbtrn03c.JavaTop.PdGlue
import EquivLean.Modernize.Cbtrn03c.JavaTop.Glue2

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `processDetail` from its segments; its model contract

At the cuts after the keyed lookups (19, 35, 49), the index the lookup returned decides the path:
`-1` (the abend; `tranStep`'s `.error`), or the index of the record found (its object's fields).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

theorem ofInt32_toNat_small {i : Nat} (h : i < 2147483648) : (BitVec.ofInt 32 (i : Int)).toNat = i := by
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  omega

theorem getElem_of_getElem?_eq {l : List Value} {i : Nat} {v : Value} (h : l[i]? = some v)
    (hi : i < l.length) : l[i]'hi = v := by
  rw [List.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

theorem pd_vc (w ld lr c a2 a3 a4 : Addr) (d t : Rec) (s : Model.St) (xs ys cs : Recs) :
    MethodVC Gen.prog pdCallees.env 0 pdRef (pdSpecG w ld lr c a2 a3 a4 d t s xs ys cs)
      (pdInv w ld lr c a2 a3 a4 d t s xs ys cs) 120 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · exact pd_entry w ld lr c a2 a3 a4 d t s xs ys cs args σ0 hpre (TranFieldsI.intro hpre.2.2.1)
  intro p hp fr σ hI
  obtain ⟨-, -, -, htv, hdv, -, -, -, hxv, hyv, hcv, -, -⟩ := hpre
  simp only [pdInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hC, hW, hcard, hfirst⟩ := hI
    exact pd_c14 w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hcard hfirst
  · obtain ⟨hC, hW, hcard⟩ := hI
    exact pd_15 w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hcard
  · obtain ⟨hC, hW, hcard, y, hy, hys⟩ := hI
    exact pd_c18 w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hcard y hy hys hxv
  · obtain ⟨hC, hW, hcard, hi8⟩ := hI
    rcases findIdx_cases (fun x => Model.xCard x == Model.tCard t) xs with hneg | ⟨i, hpos⟩
    · exact pd_19n w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hi8 hneg
        (tranStep_xref_none hcard hneg)
    · obtain ⟨hil, -⟩ := findIdx_nat hpos
      obtain ⟨hco, hcs⟩ := cardStep_xref hcard hpos hil
      have hxf := hC.2.2.2.2.2.2.1
      obtain ⟨et, es, e, fs, ha2, hlen, hiles, hel, he, hacct⟩ := xref_elem hxf hxv hil
      have hix : i < 2147483648 := by have := xref_len hxf; omega
      exact pd_19p w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW i hpos
        (by have := xref_len hxf; omega) hi8 et es e fs ha2 hiles (getElem_of_getElem?_eq hel hiles)
        (ofInt32_toNat_small hix) he (xs[i]'hil) hacct (xacct_bound (hxv _ (List.getElem_mem hil)))
        hco hcs
  · obtain ⟨hC, hW, hcs, y, hy, hys⟩ := hI
    exact pd_c34 w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hcs y hy hys hyv
  · obtain ⟨hC, hW, hcs, hi8⟩ := hI
    rcases findIdx_cases (fun y => Model.yType y == Model.tType t) ys with hneg | ⟨i, hpos⟩
    · exact pd_35n w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hi8 hneg
        (tranStep_type_none (cs := cs) (d := d) hcs hneg)
    · obtain ⟨hil, -⟩ := findIdx_nat hpos
      have hyf := hC.2.2.2.2.2.2.2.1
      exact pd_35p w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hcs i hpos
        (by have := type_len hyf; omega) hi8
  · obtain ⟨hC, hW, hcs, hti, hi8, hl1, y, hy, hys⟩ := hI
    exact pd_c48 w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hcs hti hi8 hl1 y hy hys hcv
      (tcat_bound htv)
  · obtain ⟨hC, hW, hcs, hti, hi8, hi9⟩ := hI
    obtain ⟨i, hi⟩ : ∃ i : Nat, typeIdx ys (Model.tType t) = (i : Int) :=
      ⟨(typeIdx ys (Model.tType t)).toNat, by omega⟩
    rcases findIdx_cases (fun c => Model.cType c == Model.tType t && Model.cCat c == Model.tCat t)
        cs with hneg | ⟨j, hpos⟩
    · exact pd_49n w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW hi9 hneg (tcat_bound htv)
        (tranStep_cat_none (d := d) hcs hi hneg)
    · obtain ⟨htr, hil, hjl, hty, hca⟩ := tranStep_report (d := d) hcs hi hpos
      have hyf := hC.2.2.2.2.2.2.2.1
      have hcf := hC.2.2.2.2.2.2.2.2.1
      obtain ⟨et3, es3, e3, fs3, ha3, hlen3, hiles3, hel3, he3, hd3⟩ := type_elem hyf hyv hil
      obtain ⟨et4, es4, e4, fs4, ha4, hlen4, hjles4, hel4, he4, hd4⟩ := cat_elem hcf hcv hjl
      rw [hi] at hi8
      have hi9' : fr.get 9 = some (.int (BitVec.ofInt 32 (j : Int))) := by
        simpa only [catIdx, hpos] using hi9
      have hi32 : i < 2147483648 := by have := type_len hyf; omega
      have hj32 : j < 2147483648 := by have := cat_len hcf; omega
      exact pd_49p w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW htr
        (hty ▸ hyv _ (List.getElem_mem hil)) (hca ▸ hcv _ (List.getElem_mem hjl)) i j
        (by have := type_len hyf; omega) (by have := cat_len hcf; omega) hi8 hi9'
        et3 es3 e3 fs3 ha3 hiles3 (getElem_of_getElem?_eq hel3 hiles3) (ofInt32_toNat_small hi32) he3
        (hty ▸ hd3) et4 es4 e4 fs4 ha4 hjles4 (getElem_of_getElem?_eq hel4 hjles4)
        (ofInt32_toNat_small hj32) he4 (hca ▸ hd4)
  · obtain ⟨hC, hW, htr, htyv, hcav, ty, ca, hty, hca, htys, hcas⟩ := hI
    exact pd_c66 w ld lr c a2 a3 a4 d t s xs ys cs args σ0 fr σ hC hW htr htyv hcav ty ca hty hca htys
      hcas htv hdv

/-- **`processDetail` performs `Model.tranStep`** (given the callees' contracts). -/
theorem pd_sat (hV : Valid Gen.prog pdCallees.env) : Sat Gen.prog pdRef processDetailSpecM := by
  intro args σ o hpre hx
  obtain ⟨w, ld, lr, c, a2, a3, a4, d, s, t, xs, ys, cs, hargs, hws, htf, htv, hdv, hxf, hyf, hcf,
    hxv, hyv, hcv, hi1, hi2⟩ := hpre
  have key : ∀ w' ld' lr' c' a2' a3' a4' d' s' t' xs' ys' cs',
      args = [.ref w', .ref c', .ref a2', .ref a3', .ref a4'] → WsRel σ w' ld' lr' d' s' →
      TranFields σ c' t' → TranRecord.Valid t' → WsDateparmRecord.Valid d' →
      XrefFileAt σ a2' xs' → TrantypeFileAt σ a3' ys' → TrancatgFileAt σ a4' cs' →
      (∀ v ∈ xs', CardXrefRecord.Valid v) → (∀ v ∈ ys', TranTypeRecord.Valid v) →
      (∀ v ∈ cs', TranCatRecord.Valid v) →
      (pdSpecG w' ld' lr' c' a2' a3' a4' d' t' s' xs' ys' cs').post args σ o :=
    fun w' ld' lr' c' a2' a3' a4' d' s' t' xs' ys' cs' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
      MethodVC.sat_of_valid hV (pd_vc w' ld' lr' c' a2' a3' a4' d' t' s' xs' ys' cs') args σ o
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hi1, hi2⟩ hx
  cases o with
  | normal r σ' => exact fun w' ld' lr' c' a2' a3' a4' d' s' t' xs' ys' cs' h1 h2 h3 h4 h5 h6 h7 h8 h9
      h10 h11 => key w' ld' lr' c' a2' a3' a4' d' s' t' xs' ys' cs' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  | exc e σ' => exact key w ld lr c a2 a3 a4 d s t xs ys cs hargs hws htf htv hdv hxf hyf hcf hxv hyv hcv
  | wrong m => exact key w ld lr c a2 a3 a4 d s t xs ys cs hargs hws htf htv hdv hxf hyf hcf hxv hyv hcv

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.pd_sat
