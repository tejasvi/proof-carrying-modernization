import EquivLean.Modernize.Cbtrn01c.JavaRunState

/-!
# CBTRN01C → Java: the cross-reference search, a match

The four lines of the cross-reference record (two `digits` calls), then the account search
(`J92`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- The cross-reference search, record `i` matches: its lines, then the account search. -/
theorem run_seg60_found (a1 a2 a3 a4 a5 a6 : Addr)
    (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State) (k : Nat) (e : Bool) (res l x cs ci : Addr)
    (et3 : JType) (xs3 : List Value) (fsx fsR : List (FieldKey × Value)) (ys : List Value)
    (m : Nat) (T I X : List UInt8)
    (hk : k ≤ vals1.length) (he : e = true → k = vals1.length)
    (f1 : fr.get 1 = some (.ref x))
    (f4 : fr.get 4 = some (.ref a5)) (f35 : fr.get 35 = some (.ref a3))
    (f5 : fr.get 5 = some (.int (JInt.ofBool e))) (f7 : fr.get 7 = some (.int (JInt.ofBool e)))
    (f8 : fr.get 8 = some (.int (JInt.ofBool e))) (f9 : fr.get 9 = some (.ref res))
    (f10 : fr.get 10 = some (.ref a1)) (f11 : fr.get 11 = some (.ref l))
    (f17 : fr.get 17 = some (.int (BitVec.ofNat 32 k)))
    (i : Nat) (hi : i < vals3.length) (f16 : fr.get 16 = some (.int (BitVec.ofNat 32 i)))
    (xr xc : Addr) (fsx3 : List (FieldKey × Value)) (hi3 : i < xs3.length)
    (hx3 : xs3[i]'hi3 = .ref xr)
    (hxr : σ.heap xr = some (.plain xrefCls fsx3))
    (hxc : Fields.get fsx3 (xrefCls, "xrefCardNum") = some (.ref xc))
    (hxcs : σ.heap xc = some (.str (cp037Str X)))
    (heq : cp037Str T = cp037Str X)
    (cu ac : Int) (hcu : Fields.get fsx3 (xrefCls, "xrefCustId") = some (.long (BitVec.ofInt 64 cu)))
    (hac : Fields.get fsx3 (xrefCls, "xrefAcctId") = some (.long (BitVec.ofInt 64 ac)))
    (hcub : cu.natAbs < 1000000000) (hacb : ac.natAbs < 100000000000)
    (hCU : cu = Model.numOf (vals3[i].getD 1 default))
    (hAC : ac = Model.numOf (vals3[i].getD 2 default))
    (hm : cardMatch (curT vals1 k) vals3[i] = true)
    (f34 : fr.get 34 = some .null) (f12 : fr.get 12 = some (.long 0))
    (ha3 : σ.heap a3 = some (.array et3 xs3)) (hlen3 : xs3.length < 2147483648)
    (hlen : xs3.length = vals3.length)
    (hx : σ.heap x = some (.plain dalCls fsx))
    (cc : Addr) (hcard : Fields.get fsx (dalCls, "dalytranCardNum") = some (.ref cc))
    (hccs : σ.heap cc = some (.str (cp037Str T)))
    (hT : T = Model.strOf ((curT vals1 k).getD 10 default))
    (hI : I = Model.strOf ((curT vals1 k).getD 0 default))
    (hX : X = Model.strOf (vals3[i].getD 0 default))
    (hcs : σ.heap cs = some (.str (cp037Str T)))
    (hid : Fields.get fsx (dalCls, "dalytranId") = some (.ref ci))
    (hci : σ.heap ci = some (.str (cp037Str I)))
    (hR1 : σ.heap res = some (.plain "Cbtrn01c$Result" fsR))
    (hR2 : Fields.get fsR ("Cbtrn01c$Result", "displays") = some (.ref l))
    (hR3 : Fields.get fsR ("Cbtrn01c$Result", "abended") = some (.int 0))
    (hres0 : σ0.next ≤ res) (hl0 : σ0.next ≤ l) (hrl : res ≠ l)
    (hg1 : σ0.next ≤ σ.next) (hg2 : ∀ x, x < σ0.next → σ.heap x = σ0.heap x)
    (hl : σ.heap l = some (.list .arrayList ys m))
    (hD : Hide (Forall2 (JStrAt σ) ys ((befL vals1 vals3 vals5 k e).map jline)))
    (hek : e = false → 1 ≤ k) (f20 : fr.get 20 = some (.ref cs))
    (hno : NoCard vals3 i (curT vals1 k))
    (hinit : σ.initOf "Cbtrn01c" = .done) :
    RunWP a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 60 fr σ := by
  have hres_lt := State.lt_next_of_heap hR1
  have hl_lt := State.lt_next_of_heap hl
  have hx_lt := State.lt_next_of_heap hx
  have hcs_lt := State.lt_next_of_heap hcs
  have hci_lt := State.lt_next_of_heap hci
  have hxl : x ≠ l := by intro h; subst h; rw [hl] at hx; simp at hx
  have hcsl : cs ≠ l := by intro h; subst h; rw [hl] at hcs; simp at hcs
  have hcil : ci ≠ l := by intro h; subst h; rw [hl] at hci; simp at hci
  have hccl : cc ≠ l := by intro h; subst h; rw [hl] at hccs; simp at hccs
  have hcc_lt := State.lt_next_of_heap hccs
  have hxcl : xc ≠ l := by intro h; subst h; rw [hl] at hxcs; simp at hxcs
  have hxrl : xr ≠ l := by intro h; subst h; rw [hl] at hxr; simp at hxr
  have hxc_lt := State.lt_next_of_heap hxcs
  have hxr_lt := State.lt_next_of_heap hxr
  have hT' := Hide.intro hT
  have hI' := Hide.intro hI
  have hX' := Hide.intro hX
  have hm' := Hide.intro hm
  have hCU' := Hide.intro hCU
  have hAC' := Hide.intro hAC
  clear hT hI hX hm hCU hAC
  have hR1' := Hide.intro hR1
  have hg2' := Hide.intro hg2
  have hno' := Hide.intro hno
  clear hR1 hg2 hno
  unfold RunWP
  jvc [runInv, runSpecG, callees, spacesSig, digitsSig, formatDalytranSig, formatDalytranSpec,
    runArgs, inlineFuel, fields_get_cons, fields_get_nil, jstrLitT, dalCls, xrefCls, nat_mod_2_32,
    digitsSpec, toInt_ofInt_of_natAbs, Grows,
    evalDynamic,
    concatRecipe, Native.valueOfArg, valueOfObj_eq, valueOfObjN_ref, Native.nObjStr,
    Native.primStr, JType.isRef]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | exact ⟨_, _, ⟨rfl, rfl⟩, by rw [toInt_ofInt_of_natAbs (by jomega)]; jomega, by decide, by decide⟩
    | skip
  have hR1 := Hide.elim hR1'
  have hg2 := Hide.elim hg2'
  have hAC2 : Model.numOf (vals3[i].getD 2 default) = ac := (Hide.elim hAC').symm
  have hCU2 : Model.numOf (vals3[i].getD 1 default) = cu := (Hide.elim hCU').symm
  have hX2 : Model.strOf (vals3[i].getD 0 default) = X := (Hide.elim hX').symm
  have hfind : vals3.find? (cardMatch (curT vals1 k)) = some vals3[i] :=
    find?_of_take hi (Hide.elim hno') (Hide.elim hm')
  refine J92.intro k e (.ref x) res l 0 vals3[i] (Base.intro ?_ ?_ ?_ ?_ ?_ ?_ hk ?_ ?_ ?_ he ?_
    ⟨x, fsx, cc, ci, rfl, by trn_chain, hcard, by rw [Hide.elim hT'] at hccs; trn_chain, hid,
      by rw [Hide.elim hI'] at hci; trn_chain⟩
    ⟨fsR, ?_, hR2, hR3⟩ hres0 hl0 hrl ⟨?_, fun y hy => ?_⟩ ?_) hek hfind ?_ ?_ (Nat.zero_le _)
    ?_ ?_ ?_ ?_ (fun z hz => by simp at hz)
  any_goals (rw [hAC2]; trn_frame [f1, f4, f35, f5, f7, f8, f9, f10, f11, f17, f12]; done)
  any_goals (trn_frame [f1, f4, f35, f5, f7, f8, f9, f10, f11, f17, f12]; done)
  · trn_chain
  · simp only [State.next_alloc, State.next_setObj] at *
    jomega
  · trn_chain
  · trn_chain
  · apply listAt_setObj (by simp only [State.next_alloc] at *; jomega) rfl
    simp only [xrefL, List.map_append, List.map_cons, List.map_nil, hAC2, hCU2, hX2]
    refine forall2_append (forall2_mono (fun v t h => ?_) (Hide.elim hD))
      (.cons ⟨_, rfl, ?_⟩ (.cons ⟨_, rfl, ?_⟩ (.cons ⟨_, rfl, ?_⟩ (.cons ⟨_, rfl, ?_⟩ .nil))))
    · obtain ⟨y, rfl, hy⟩ := h
      have hy_lt := State.lt_next_of_heap hy
      have hyl : y ≠ l := by intro h; subst h; rw [hl] at hy; simp at hy
      exact ⟨y, rfl, by trn_chain⟩
    · rw [line_ok_xref]; trn_chain
    · rw [line_card_num]; trn_chain
    · rw [line_acct_id]; trn_chain
    · rw [line_cust_id]; trn_chain

end EquivLean.Modernize.Cbtrn01c.Java
