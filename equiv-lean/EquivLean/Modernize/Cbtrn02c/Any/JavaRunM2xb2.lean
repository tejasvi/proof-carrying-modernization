import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM2xs
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunTac

/-!
# CBTRN02C → Java: `abend` with status 22; `writeTransaction` on any input (entry)
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem fieldsOf_setObj_ne' {σ : State} {a b : Addr} {o : Obj} (h : b ≠ a) :
    fieldsOf (σ.setObj a o) b = fieldsOf σ b := by
  simp only [fieldsOf, State.heap_setObj, if_neg h]

theorem fieldsOf_alloc_lt {σ : State} {a : Addr} (h : a < σ.next) (o : Obj) :
    fieldsOf (σ.alloc o).2 a = fieldsOf σ a := by
  simp only [fieldsOf, State.heap_alloc_of_lt h]

theorem refField_alloc_lt {σ : State} {a : Addr} (h : a < σ.next) (o : Obj) (k : FieldKey) :
    refField (σ.alloc o).2 a k = refField σ a k := by
  simp only [refField, fieldsOf_alloc_lt h]

theorem listOf_alloc_lt {σ : State} {a : Addr} (h : a < σ.next) (o : Obj) :
    listOf (σ.alloc o).2 a = listOf σ a := by
  simp only [listOf, State.heap_alloc_of_lt h]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem wt_entry (r wT lK : Addr) (σ0 : State)
    (hpre : writeTransactionSpecX.pre [.ref r, .ref wT, .ref lK] σ0) :
    WtWP [.ref r, .ref wT, .ref lK] σ0 0 (Frame.init true [.ref r, .ref wT, .ref lK]) σ0 := by
  obtain ⟨r', wT', lK', fsR, lT, lD, fsT, sId, idcs, ks, mK, ts, mT, ds, mD, hargs, hR, hRT, hRD,
    ⟨ab, hab⟩, hT, hallT, hid, hsId, hlK, hlen, hsh, hlT, hlD, hnd, i1, i2, i3⟩ := hpre
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl⟩ := hargs
  have e1 : fld σ0 wT trIdKey = .ref sId := fld_of hT hid
  have e2 : listOf σ0 lK = ks := listOf_of hlK
  have e3 : refField σ0 r ltKey = lT := refField_of hR hRT
  have e4 : refField σ0 r dispKey = lD := refField_of hR hRD
  have e5 : listOf σ0 lT = ts := listOf_of hlT
  have e6 : listOf σ0 lD = ds := listOf_of hlD
  have e7 : fieldsOf σ0 wT = fsT := fieldsOf_of hT
  have e8 : fieldsOf σ0 r = fsR := fieldsOf_of hR
  have hkeep := Hide.intro (And.intro e1 (And.intro e2 (And.intro e3 (And.intro e4 (And.intro e5
    (And.intro e6 (And.intro e7 e8)))))))
  clear e1 e2 e3 e4 e5 e6 e7 e8
  unfold WtWP
  jvc [wtCalleesX, findKeySig, findKeySpecF, findKeySpec, copyTranSig, copyTranSpecF, abendSig,
    abendSpec22, Grows, narrow_long, narrow_cls]
  · rename_i σ0 c _ _ _ _ _ _ _ _ _ _ _ _ hc1 hc2 _ _ hneg _ hrK σ1 y hyn hyo hsf hn1 hfr1 hi1 hy1 _
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := Hide.elim hkeep
    have hidx : wtIdx σ0 wT lK < 0 := by unfold wtIdx; rw [e1]; exact hneg
    have hwK : wT ≠ lK := by intro h; rw [h, hlK] at hT; cases hT
    rw [fieldsOf_setObj_ne' hwK] at hsf
    unfold wtPostX
    simp only [writeTransactionSpecX, Spec.of]
    intro r' wT' lK' hargs'
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs'
    obtain ⟨rfl, rfl, rfl⟩ := hargs'
    refine ⟨fun _ => ⟨rfl, y, _, mK + 1, mT + 1, ?_, ?_, hyn, by chain_simp, hsf, ?_⟩,
      fun h => absurd h (by omega), by cls_simp; simp only [*], by cls_simp; simp only [*],
      by cls_simp; simp only [*]⟩
    · rw [e2, e1]; chain_simp
    · rw [e3, e5]; chain_simp
    · rw [e3]
      refine ⟨by simp only [State.next_setObj] at *; jomega, fun z hz hzS => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hzS
      obtain ⟨hz1, hz2⟩ := hzS
      chain_simp
  · rename_i σ0 c _ _ _ _ _ _ _ _ _ _ _ _ hc1 hc2 _ _ σ1 y2 y3 hy2o hy3o hro hy2n hy3n hn1 hi1 hio1
      _ _ _ _ _ _ _ _
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := Hide.elim hkeep
    have hpos : 0 ≤ wtIdx σ0 wT lK := by unfold wtIdx; rw [e1]; omega
    have hrlt : r < σ0.next := State.lt_next_of_heap hR
    simp (disch := (simp only [State.next_alloc] at *; jomega)) only [refField_alloc_lt,
      listOf_alloc_lt, fieldsOf_alloc_lt] at h hro right
    unfold wtPostX
    simp only [writeTransactionSpecX, Spec.of]
    intro r' wT' lK' hargs'
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs'
    obtain ⟨rfl, rfl, rfl⟩ := hargs'
    refine ⟨fun h' => absurd h' (by omega), fun _ => ⟨rfl, σ0.next, y2, y3, _, h, by chain_simp,
      by chain_simp, by chain_simp, hro, Nat.le_refl _, by (try simp only [State.next_alloc] at *); jomega,
      by (try simp only [State.next_alloc] at *); jomega, ?_⟩, hi1, left, by rw [hio1, i1]⟩
    refine ⟨by (try simp only [State.next_alloc] at *); jomega, fun z hz hzS => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hzS
    obtain ⟨hz1, hz2⟩ := hzS
    chain_simp

end EquivLean.Modernize.Cbtrn02c.Java
