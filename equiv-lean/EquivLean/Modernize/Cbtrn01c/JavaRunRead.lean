import EquivLean.Modernize.Cbtrn01c.JavaRunState

/-!
# CBTRN01C → Java: a record read

The next record is read and displayed (`formatDalytran`); its lookups follow (`J60`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

theorem dalOk_alloc2 {σ : State} {c : Addr} {o1 o2 : Obj} (h : Hide (DalOk σ c)) :
    DalOk ((σ.alloc o1).2.alloc o2).2 c :=
  dalOk_of_grows (grows_trans (grows_alloc σ o1) (grows_alloc _ o2)) (Hide.elim h)

theorem dalLine_alloc2 {σ : State} {c : Addr} {o1 o2 : Obj} (h : Hide (DalOk σ c)) :
    dalLine ((σ.alloc o1).2.alloc o2).2 c = dalLine σ c :=
  dalLine_of_grows (grows_trans (grows_alloc σ o1) (grows_alloc _ o2)) (Hide.elim h)

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- The loop head, a record left: it is read and displayed. -/
theorem run_seg29_read (a1 a2 a3 a4 a5 a6 : Addr)
    (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State) (k : Nat) (res l c cs ci : Addr) (et1 : JType)
    (xs1 : List Value) (fsc fsR : List (FieldKey × Value)) (ys : List Value) (m : Nat)
    (hk : k < vals1.length)
    (f4 : fr.get 4 = some (.ref a5)) (f35 : fr.get 35 = some (.ref a3))
    (f5 : fr.get 5 = some (.int 0#32)) (f7 : fr.get 7 = some (.int 0#32))
    (f8 : fr.get 8 = some (.int 0#32)) (f9 : fr.get 9 = some (.ref res))
    (f10 : fr.get 10 = some (.ref a1)) (f11 : fr.get 11 = some (.ref l))
    (f17 : fr.get 17 = some (.int (BitVec.ofNat 32 k)))
    (ha1 : σ.heap a1 = some (.array et1 xs1)) (hlen1 : xs1.length < 2147483648)
    (hlen : xs1.length = vals1.length) (hkx : k < xs1.length) (hx : xs1[k]'hkx = .ref c)
    (L : JStr) (hL : L = jline (Model.DalytranRecord.textS vals1[k]))
    (hdal : DalOk σ c) (hline : dalLine σ c = L)
    (hc : σ.heap c = some (.plain dalCls fsc))
    (hcard : Fields.get fsc (dalCls, "dalytranCardNum") = some (.ref cs))
    (T I : List UInt8) (hT : T = Model.strOf (vals1[k].getD 10 default))
    (hI : I = Model.strOf (vals1[k].getD 0 default))
    (hcs : σ.heap cs = some (.str (cp037Str T)))
    (hid : Fields.get fsc (dalCls, "dalytranId") = some (.ref ci))
    (hci : σ.heap ci = some (.str (cp037Str I)))
    (hR1 : σ.heap res = some (.plain "Cbtrn01c$Result" fsR))
    (hR2 : Fields.get fsR ("Cbtrn01c$Result", "displays") = some (.ref l))
    (hR3 : Fields.get fsR ("Cbtrn01c$Result", "abended") = some (.int 0))
    (hres0 : σ0.next ≤ res) (hl0 : σ0.next ≤ l) (hrl : res ≠ l)
    (hg1 : σ0.next ≤ σ.next) (hg2 : ∀ x, x < σ0.next → σ.heap x = σ0.heap x)
    (hl : σ.heap l = some (.list .arrayList ys m))
    (hD : Hide (Forall2 (JStrAt σ) ys ((headL vals1 vals3 vals5 k false).map jline)))
    (hinit : σ.initOf "Cbtrn01c" = .done) :
    RunWP a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 29 fr σ := by
  have hcl : c ≠ l := by intro h; subst h; rw [hl] at hc; simp at hc
  have hcsl : cs ≠ l := by intro h; subst h; rw [hl] at hcs; simp at hcs
  have hcil : ci ≠ l := by intro h; subst h; rw [hl] at hci; simp at hci
  have hL' := Hide.intro hL
  have hT' := Hide.intro hT
  have hI' := Hide.intro hI
  clear hL hT hI
  have hdal' := Hide.intro hdal
  have hR1' := Hide.intro hR1
  have hg2' := Hide.intro hg2
  have hcs' := Hide.intro hcs
  have hci' := Hide.intro hci
  have hid' := Hide.intro hid
  clear hdal hR1 hg2 hcs hci hid
  unfold RunWP
  jvc [runInv, runSpecG, callees, spacesSig, digitsSig, formatDalytranSig, formatDalytranSpec,
    runArgs, inlineFuel, fields_get_cons, fields_get_nil, jstrLitT, dalOk_alloc2, dalLine_alloc2,
    dalCls, nat_mod_2_32, Grows]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip
  have hL := Hide.elim hL'
  have hR1 := Hide.elim hR1'
  have hg2 := Hide.elim hg2'
  have hcs := Hide.elim hcs'
  have hci := Hide.elim hci'
  have hid := Hide.elim hid'
  rw [Hide.elim hT'] at hcs
  rw [Hide.elim hI'] at hci
  have hres_lt := State.lt_next_of_heap hR1
  have hcs_lt := State.lt_next_of_heap hcs
  have hci_lt := State.lt_next_of_heap hci
  have hwl : w ≠ l := by
    intro h; subst h
    simp only [State.next_alloc, State.next_setObj] at *
    simp (disch := jomega) only [*, ite_false, addr_eq_false, Option.some.injEq, reduceCtorEq] at *
  refine J60.intro (k + 1) false (.ref c) res l 0 cs (Base.intro ?_ ?_ ?_ ?_ ?_ ?_ (by omega) ?_ ?_ ?_
    (fun h => by cases h) ?_ ?_ ⟨fsR, ?_, hR2, hR3⟩ hres0 hl0 hrl ⟨?_, fun y hy => ?_⟩ ?_)
    (fun _ => by omega) ?_ ?_ (Nat.zero_le _) ?_ ?_ ?_ ?_ ?_
  any_goals (trn_frame [f4, f5, f7, f8, f35, f9, f10, f11, f17, ofNat32_succ, JInt.ofBool]; done)
  · rw [curT_succ hk]
    exact ⟨c, fsc, cs, ci, rfl, by trn_chain, hcard, by trn_chain, hid, by trn_chain⟩
  · trn_chain
  · simp only [State.next_setObj]
    jomega
  · trn_chain
  · trn_chain
  · rw [befL_read hk]
    apply listAt_setObj (by simp only [State.next_alloc] at *; jomega) rfl
    rw [List.map_append, List.map_singleton]
    refine forall2_append (forall2_mono (fun v t h => ?_) (Hide.elim hD)) (.cons ⟨w, rfl, ?_⟩ .nil)
    · obtain ⟨y, rfl, hy⟩ := h
      have hy_lt := State.lt_next_of_heap hy
      have hyl : y ≠ l := by intro h; subst h; rw [hl] at hy; simp at hy
      exact ⟨y, rfl, by trn_chain⟩
    · rw [← hL]
      trn_chain
  · rw [curT_succ hk]
    trn_chain
  · intro z hz
    simp at hz

end EquivLean.Modernize.Cbtrn01c.Java
