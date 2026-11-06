import EquivLean.Modernize.Cbtrn01c.JavaRunState

/-!
# CBTRN01C → Java: the account search, no match

The two lines of an unknown account, back to the read loop (`J29`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- The account search ends without a match: the two lines of an unknown account. -/
theorem run_seg92_none (a1 a2 a3 a4 a5 a6 : Addr)
    (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State) (k : Nat) (e : Bool) (res l x cs ci : Addr)
    (et5 : JType) (xs5 : List Value) (fsx fsR : List (FieldKey × Value)) (ys : List Value)
    (m : Nat) (T I : List UInt8) (xv : List EquivLean.Cobol.Rec.FVal) (ac : Int)
    (hk : k ≤ vals1.length) (he : e = true → k = vals1.length)
    (f1 : fr.get 1 = some (.ref x))
    (f4 : fr.get 4 = some (.ref a5)) (f35 : fr.get 35 = some (.ref a3))
    (f5 : fr.get 5 = some (.int (JInt.ofBool e))) (f7 : fr.get 7 = some (.int (JInt.ofBool e)))
    (f8 : fr.get 8 = some (.int (JInt.ofBool e))) (f9 : fr.get 9 = some (.ref res))
    (f10 : fr.get 10 = some (.ref a1)) (f11 : fr.get 11 = some (.ref l))
    (f17 : fr.get 17 = some (.int (BitVec.ofNat 32 k)))
    (f18 : fr.get 18 = some (.int (BitVec.ofNat 32 vals5.length)))
    (f13 : fr.get 13 = some (.long (BitVec.ofInt 64 ac)))
    (f15 : fr.get 15 = some (.long (BitVec.ofInt 64 ac)))
    (f14 : fr.get 14 = some (.long 0)) (f32 : fr.get 32 = some .null)
    (ha5 : σ.heap a5 = some (.array et5 xs5)) (hlen5 : xs5.length < 2147483648)
    (hlen : xs5.length = vals5.length)
    (hT : T = Model.strOf ((curT vals1 k).getD 10 default))
    (hI : I = Model.strOf ((curT vals1 k).getD 0 default))
    (hAC : ac = Model.numOf (xv.getD 2 default)) (hacb : ac.natAbs < 100000000000)
    (hx : σ.heap x = some (.plain dalCls fsx))
    (hcard : Fields.get fsx (dalCls, "dalytranCardNum") = some (.ref cs))
    (hcs : σ.heap cs = some (.str (cp037Str T)))
    (hid : Fields.get fsx (dalCls, "dalytranId") = some (.ref ci))
    (hci : σ.heap ci = some (.str (cp037Str I)))
    (hR1 : σ.heap res = some (.plain "Cbtrn01c$Result" fsR))
    (hR2 : Fields.get fsR ("Cbtrn01c$Result", "displays") = some (.ref l))
    (hR3 : Fields.get fsR ("Cbtrn01c$Result", "abended") = some (.int 0))
    (hres0 : σ0.next ≤ res) (hl0 : σ0.next ≤ l) (hrl : res ≠ l)
    (hg1 : σ0.next ≤ σ.next) (hg2 : ∀ x, x < σ0.next → σ.heap x = σ0.heap x)
    (hl : σ.heap l = some (.list .arrayList ys m))
    (hD : Hide (Forall2 (JStrAt σ) ys ((befL vals1 vals3 vals5 k e ++ xrefL xv).map jline)))
    (hek : e = false → 1 ≤ k) (hfx : vals3.find? (cardMatch (curT vals1 k)) = some xv)
    (hno : NoAcct vals5 vals5.length xv)
    (hinit : σ.initOf "Cbtrn01c" = .done) :
    RunWP a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 92 fr σ := by
  have hres_lt := State.lt_next_of_heap hR1
  have hl_lt := State.lt_next_of_heap hl
  have hx_lt := State.lt_next_of_heap hx
  have hcs_lt := State.lt_next_of_heap hcs
  have hci_lt := State.lt_next_of_heap hci
  have hxl : x ≠ l := by intro h; subst h; rw [hl] at hx; simp at hx
  have hcsl : cs ≠ l := by intro h; subst h; rw [hl] at hcs; simp at hcs
  have hcil : ci ≠ l := by intro h; subst h; rw [hl] at hci; simp at hci
  have hT' := Hide.intro hT
  have hI' := Hide.intro hI
  have hAC' := Hide.intro hAC
  have hfx' := Hide.intro hfx
  clear hT hI hAC hfx
  have hR1' := Hide.intro hR1
  have hg2' := Hide.intro hg2
  have hno' := Hide.intro hno
  clear hR1 hg2 hno
  unfold RunWP
  jvc [runInv, runSpecG, callees, spacesSig, digitsSig, formatDalytranSig, digitsSpec,
    runArgs, inlineFuel, fields_get_cons, fields_get_nil, jstrLitT, dalCls, nat_mod_2_32,
    toInt_ofInt_of_natAbs, Grows, evalDynamic, concatRecipe, Native.valueOfArg, valueOfObj_eq,
    valueOfObjN_ref, Native.nObjStr, Native.primStr, JType.isRef]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip
  have hR1 := Hide.elim hR1'
  have hg2 := Hide.elim hg2'
  have hAC2 : Model.numOf (xv.getD 2 default) = ac := (Hide.elim hAC').symm
  have hfx := Hide.elim hfx'
  have hnone : vals5.find? (acctMatch xv) = none := find?_none_of_take (Hide.elim hno')
  refine J29.intro k e (.ref x) res l (Base.intro ?_ ?_ ?_ ?_ ?_ ?_ hk ?_ ?_ ?_ he ?_
    ⟨x, fsx, cs, ci, rfl, by trn_chain, hcard, by rw [Hide.elim hT'] at hcs; trn_chain, hid,
      by rw [Hide.elim hI'] at hci; trn_chain⟩
    ⟨fsR, ?_, hR2, hR3⟩ hres0 hl0 hrl ⟨?_, fun y hy => ?_⟩ ?_) ?_
  any_goals (trn_frame [f1, f4, f35, f5, f7, f8, f9, f10, f11, f17]; done)
  · trn_chain
  · simp only [State.next_alloc, State.next_setObj] at *
    jomega
  · trn_chain
  · trn_chain
  · rw [← befL_lookup hek hk, lookupText_some_none hfx hnone, ← List.append_assoc]
    apply listAt_setObj (by simp only [State.next_alloc] at *; jomega) rfl
    simp only [List.map_append, List.map_cons, List.map_nil, hAC2]
    have hD' := Hide.elim hD
    simp only [List.map_append] at hD'
    refine forall2_append (forall2_mono (fun v t h => ?_) hD')
      (.cons ⟨_, rfl, ?_⟩ (.cons ⟨_, rfl, ?_⟩ .nil))
    · obtain ⟨y, rfl, hy⟩ := h
      have hy_lt := State.lt_next_of_heap hy
      have hyl : y ≠ l := by intro h; subst h; rw [hl] at hy; simp at hy
      exact ⟨y, rfl, by trn_chain⟩
    · rw [line_invalid_acct]; trn_chain
    · rw [line_acct_not_found]; trn_chain

end EquivLean.Modernize.Cbtrn01c.Java
