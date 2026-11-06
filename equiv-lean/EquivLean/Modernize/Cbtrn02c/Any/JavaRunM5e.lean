import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5q
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5r
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunMVX
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunWAb

/-!
# CBTRN02C → Java: the world after `updateTcatbal`, from its contract

`w39_create`/`w39_update`: `updateTcatbalSpec`'s postcondition (missing key / key found) at the
call of `postTransaction` gives `W` for `postCat` (the transport lemmas `W_tcat_create` and
`W_tcat_update`, fed with the values the contract states in terms of the heap).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem tmod_small11 (v : Int) (h : v.natAbs < 100000000000) : Int.tmod v 100000000000 = v := by
  rcases (show 0 ≤ v ∨ v < 0 by omega) with hv | hv
  · rw [Int.tmod_eq_emod_of_nonneg hv, Int.emod_eq_of_lt hv (by omega)]
  · have : Int.tmod (-v) 100000000000 = -v := by
      rw [Int.tmod_eq_emod_of_nonneg (by omega), Int.emod_eq_of_lt (by omega) (by omega)]
    rw [← Int.neg_neg v, Int.neg_tmod, this, Int.neg_neg]

theorem srem_ofInt_small {n : Int} (h : n.natAbs < 100000000000) :
    (BitVec.ofInt 64 n).srem 100000000000#64 = BitVec.ofInt 64 n := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_srem, toInt_ofInt_of_natAbs (by omega)]
  have hc : (100000000000#64 : BitVec 64).toInt = 100000000000 := by decide
  rw [hc, tmod_small11 n h]

/-- The heap values `updateTcatbal` reads, as the model's. -/
theorem ut_vals {σ : State} {A : Addrs} {d : Addr} {t x : List EquivLean.Cobol.Rec.FVal}
    (hd : JRecAt DalytranRecord dalCls σ (.ref d) t) (htv : DalytranRecord.Valid t)
    (hx : JRecAt CardXrefRecord xrCls σ (.ref A.wX) x) (hxv : CardXrefRecord.Valid x) :
    lng σ A.wX xAcctKey = BitVec.ofInt 64 (Model.xAcct x) ∧
    lng σ d dCatKey = BitVec.ofInt 64 (Model.tCat t) ∧
    lng σ d dAmtKey = BitVec.ofInt 64 (Model.tAmt t) ∧
    (∃ sty, fld σ d dTypeKey = .ref sty ∧ σ.heap sty = some (.str (cp037Str (Model.tType t)))) ∧
    argText σ (fld σ d dTypeKey) = cp037Str (Model.tType t) := by
  obtain ⟨⟨a, fsd, s0, s1, s3, s4, s7, s8, s9, s10, s11, s12, s13, hae, hdo, g0, t0, g1, t1, g2, g3,
    t3, g4, t4, g5, g6, g7, t7, g8, t8, g9, t9, g10, t10, g11, t11, g12, t12, g13, t13⟩, b0, b1, n2,
    b3, b4, n5, n6, b7, b8, b9, b10, b11, b12, b13, rfl, h2, h5, h6⟩ := dalobj_of_rec hd htv
  cases hae
  obtain ⟨⟨a', fsX, -, -, hxe, hxo, -, -, -, gx2, -⟩, xb0, xn1, xn2, xb3, rfl, -, hx2, -⟩ :=
    xobj_of_rec hx hxv
  cases hxe
  refine ⟨by simp [lng, fld, fieldsOf, hxo, gx2, nAt, Model.numOf, Model.xAcct],
    by simp [lng, fld, fieldsOf, hdo, g2, nAt, Model.numOf, Model.tCat],
    by simp [lng, fld, fieldsOf, hdo, g5, nAt, Model.numOf, Model.tAmt],
    ⟨s1, by simp [fld, fieldsOf, hdo, g1], by simpa [bAt, Model.strOf, Model.tType] using t1⟩,
    by simp [argText, strOfV, fld, fieldsOf, hdo, g1, t1, bAt, Model.strOf, Model.tType]⟩

/-- The world after `updateTcatbal` created the missing category record. -/
theorem w39_create {σ σ1 : State} {A : Addrs} {s : Model.St} {d : Addr}
    {t x : List EquivLean.Cobol.Rec.FVal}
    (hW : W σ A s) (hMV : MV s) (hd : JRecAt DalytranRecord dalCls σ (.ref d) t)
    (htv : DalytranRecord.Valid t) (hx : JRecAt CardXrefRecord xrCls σ (.ref A.wX) x)
    (hxv : CardXrefRecord.Valid x) (hlen : PtLen s) (hneg : utIdx σ d A.wX A.lC < 0)
    {sD y1 y2 : Addr} {fsC' fs1 fs2 : List (FieldKey × Value)} {m1 m2 m3 : Nat}
    (hD' : σ1.heap (refField σ A.r dispKey) =
      some (.list .arrayList (listOf σ (refField σ A.r dispKey) ++ [.ref sD]) m1))
    (hsD : σ1.heap sD = some (.str (noCatJ (lng σ A.wX xAcctKey) (argText σ (fld σ d dTypeKey))
      (lng σ d dCatKey))))
    (hwC' : σ1.heap A.wC = some (.plain "Cbtrn02c$TranCatBalRecord" fsC'))
    (f0 : Fields.get fsC' tcAcctKey = some (.long (lng σ A.wX xAcctKey)))
    (f1 : Fields.get fsC' tcTypeKey = some (fld σ d dTypeKey))
    (f2 : Fields.get fsC' tcCdKey = some (.long (lng σ d dCatKey)))
    (f3 : Fields.get fsC' tcBalKey = some (.long (BitVec.srem (lng σ d dAmtKey) 100000000000#64)))
    (f4 : Fields.get fsC' tcFillKey = Fields.get (fieldsOf σ A.wC) tcFillKey)
    (hC' : σ1.heap A.lC = some (.list .arrayList (listOf σ A.lC ++ [.ref y1]) m2))
    (hy1 : σ1.heap y1 = some (.plain "Cbtrn02c$TranCatBalRecord" fs1)) (hs1 : SameFields tcKeys fs1 fsC')
    (hCW' : σ1.heap (refField σ A.r cwKey) =
      some (.list .arrayList (listOf σ (refField σ A.r cwKey) ++ [.ref y2]) m3))
    (hy2 : σ1.heap y2 = some (.plain "Cbtrn02c$TranCatBalRecord" fs2)) (hs2 : SameFields tcKeys fs2 fsC')
    (hn1 : σ.next ≤ y1) (hn2 : σ.next ≤ y2) (hnD : σ.next ≤ sD)
    (hf : FrameS σ σ1 [A.wC, A.lC, refField σ A.r dispKey, refField σ A.r cwKey]) :
    W σ1 A (postCat s t x) ∧ FrameS σ σ1 [A.wC, A.lC, A.lD, A.lCW] := by
  have hW0 := hW
  obtain ⟨⟨fsR, hRo, r1, -, -, r4, -, -, -, -⟩, -⟩ := hW0
  have eD : refField σ A.r dispKey = A.lD := refField_of hRo r1
  have eCW : refField σ A.r cwKey = A.lCW := refField_of hRo r4
  rw [eD] at hD' hf
  rw [eCW] at hCW' hf
  obtain ⟨e1, e2, e3, ⟨sty, hfty, hsty⟩, e5⟩ := ut_vals hd htv hx hxv
  obtain ⟨-, htyl, hcatb, hcat0, -, -, hamtb, -⟩ := Glue.tranOf_valid htv
  obtain ⟨-, -, hxab, hxa0, -⟩ := Glue.xrefOf_valid hxv
  have hcatb' : (Model.tCat t).natAbs < 10000 := hcatb
  have hamtb' : (Model.tAmt t).natAbs < 100000000000 := hamtb
  have hxab' : (Model.xAcct x).natAbs < 100000000000 := hxab
  have ha : (Model.xAcct x).natAbs < 10 ^ 18 := by omega
  have hc : (Model.tCat t).natAbs < 10 ^ 18 := by omega
  rw [e1, e5, e2, noCatJ_eq _ _ _ ha hc] at hsD
  rw [e1] at f0
  rw [hfty] at f1
  rw [e2] at f2
  rw [e3, srem_ofInt_small hamtb'] at f3
  have hfind : Model.findCat s.cats (Model.xAcct x) (Model.tType t) (Model.tCat t) = none := by
    have h := utIdx_eq hW hMV hd htv hx hxv
    rw [h] at hneg
    exact firstIdx_neg_iff.1 hneg
  obtain ⟨hl1, hl2, -, hl4, -, -⟩ := hlen
  exact ⟨W_tcat_create hW hfind ⟨sty, rfl, hsty⟩ ha hc hamtb' hD' hsD hwC' f0 f1 f2 f3 f4 hC' hy1 hs1
    hCW' hy2 hs2 hn1 hn2 hnD hf ⟨by omega, hl2, by omega⟩, hf⟩

theorem FrameS.mono {σ σ' : State} {S S' : List Addr} (h : FrameS σ σ' S) (hS : ∀ z ∈ S, z ∈ S') :
    FrameS σ σ' S' :=
  ⟨h.1, fun z hz hzS => h.2 z hz (fun hm => hzS (hS z hm))⟩

/-- The world after `updateTcatbal` updated the category record found. -/
theorem w39_update {σ σ1 : State} {A : Addrs} {s : Model.St} {d : Addr}
    {t x : List EquivLean.Cobol.Rec.FVal}
    (hW : W σ A s) (hMV : MV s) (hd : JRecAt DalytranRecord dalCls σ (.ref d) t)
    (htv : DalytranRecord.Valid t) (hx : JRecAt CardXrefRecord xrCls σ (.ref A.wX) x)
    (hxv : CardXrefRecord.Valid x) (hlen : PtLen s) (hpos : 0 ≤ utIdx σ d A.wX A.lC)
    {y1 y2 : Addr} {fsA fs1 fs2 : List (FieldKey × Value)} {m2 m3 : Nat}
    (hfa : ∀ (a : ClassName) (b : String), (a, b) ∈ tcKeys → Fields.get fsA (a, b) =
      Fields.get (fieldsOf σ (objOf ((listOf σ A.lC)[(utIdx σ d A.wX A.lC).toNat]?.getD .null))) (a, b))
    (hwC' : σ1.heap A.wC = some (.plain "Cbtrn02c$TranCatBalRecord" (Fields.set fsA tcBalKey
      (.long (BitVec.srem (lng σ (objOf ((listOf σ A.lC)[(utIdx σ d A.wX A.lC).toNat]?.getD .null))
        tcBalKey + lng σ d dAmtKey) 100000000000#64)))))
    (hC' : σ1.heap A.lC = some (.list .arrayList
      ((listOf σ A.lC).set (utIdx σ d A.wX A.lC).toNat (.ref y1)) m2))
    (hy1 : σ1.heap y1 = some (.plain "Cbtrn02c$TranCatBalRecord" fs1))
    (hs1 : SameFields tcKeys fs1 (Fields.set fsA tcBalKey
      (.long (BitVec.srem (lng σ (objOf ((listOf σ A.lC)[(utIdx σ d A.wX A.lC).toNat]?.getD .null))
        tcBalKey + lng σ d dAmtKey) 100000000000#64))))
    (hCR' : σ1.heap (refField σ A.r crKey) =
      some (.list .arrayList (listOf σ (refField σ A.r crKey) ++ [.ref y2]) m3))
    (hy2 : σ1.heap y2 = some (.plain "Cbtrn02c$TranCatBalRecord" fs2))
    (hs2 : SameFields tcKeys fs2 (Fields.set fsA tcBalKey
      (.long (BitVec.srem (lng σ (objOf ((listOf σ A.lC)[(utIdx σ d A.wX A.lC).toNat]?.getD .null))
        tcBalKey + lng σ d dAmtKey) 100000000000#64))))
    (hn1 : σ.next ≤ y1) (hn2 : σ.next ≤ y2)
    (hf : FrameS σ σ1 [A.wC, A.lC, refField σ A.r crKey]) :
    W σ1 A (postCat s t x) ∧ FrameS σ σ1 [A.wC, A.lC, A.lCR] := by
  have hW0 := hW
  obtain ⟨⟨fsR, hRo, -, -, -, -, -, r6, -, -⟩, -, -, -, -, -, -, -, ⟨xs, m, hlC, hfC, -, -⟩, -⟩ := hW0
  have eCR : refField σ A.r crKey = A.lCR := refField_of hRo r6
  rw [eCR] at hCR' hf
  have hidx := utIdx_eq hW hMV hd htv hx hxv
  have hlo : listOf σ A.lC = xs := listOf_of hlC
  have hlt := firstIdx_lt (Model.catKey (Model.xAcct x) (Model.tType t) (Model.tCat t)) s.cats
  have hxl := forall2_length hfC
  have hjx : (utIdx σ d A.wX A.lC).toNat < xs.length := by omega
  obtain ⟨y, fsy, hyx, -⟩ := forall2_get hfC _ hjx (by omega)
  have hrec : (listOf σ A.lC).getD (utIdx σ d A.wX A.lC).toNat .null =
      .ref (objOf ((listOf σ A.lC)[(utIdx σ d A.wX A.lC).toNat]?.getD .null)) := by
    rw [hlo, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjx, Option.getD_some, hyx]
    rfl
  have hj : firstIdx (Model.catKey (Model.xAcct x) (Model.tType t) (Model.tCat t)) s.cats =
      ((utIdx σ d A.wX A.lC).toNat : Int) := by
    rw [Int.toNat_of_nonneg hpos, hidx]
  obtain ⟨-, -, -, -, -, -, hamtb, -⟩ := Glue.tranOf_valid htv
  have hamtb' : (Model.tAmt t).natAbs < 100000000000 := hamtb
  obtain ⟨-, -, e3, -, -⟩ := ut_vals hd htv hx hxv
  obtain ⟨-, -, hl3, -, -, -⟩ := hlen
  exact ⟨W_tcat_update hW hMV.2.1 hj hrec hamtb' e3 (fun k hk => hfa k.1 k.2 hk) hwC' hC' hy1 hs1 hCR'
    hy2 hs2 hn1 hn2 hf hl3, hf⟩

theorem NoStr.mono {σ : State} {S S' : List Addr} (h : NoStr σ S') (hS : ∀ z ∈ S, z ∈ S') :
    NoStr σ S := fun a ha t ht => h a (hS a ha) t ht

/-- None of the objects `postTransaction` may change is a string. -/
theorem noStr_W {σ : State} {A : Addrs} {s : Model.St} (hW : W σ A s) : NoStr σ (PtMod A) := by
  obtain ⟨-, ⟨xD, mD, hD, -⟩, ⟨xT, mT, hT, -⟩, ⟨xR, mR, hR, -⟩, ⟨xW, mW, hCW, -⟩, ⟨xA, mA, hAR, -⟩,
    ⟨xC, mC, hCR, -⟩, ⟨et, xa, haD, -⟩, ⟨xl, ml, hlC, -⟩, ⟨xk, mk, hK, -⟩, ⟨fX, hwX, -⟩, ⟨fA, hwA, -⟩,
    ⟨fC, hwC, -⟩, ⟨fT, hwT, -⟩, -⟩ := hW
  intro a ha t ht
  simp only [PtMod, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | (rw [hwT] at ht; cases ht) | (rw [hwC] at ht; cases ht) | (rw [hlC] at ht; cases ht)
    | (rw [hD] at ht; cases ht) | (rw [hCW] at ht; cases ht) | (rw [hCR] at ht; cases ht)
    | (rw [hwA] at ht; cases ht) | (rw [haD] at ht; cases ht) | (rw [hAR] at ht; cases ht)
    | (rw [hK] at ht; cases ht) | (rw [hT] at ht; cases ht)

/-- The invariant at statement 39 for the ghost values `p'`. -/
theorem pt39_body {p' : PG} {σ0 σ σ1 : State} {fr : Frame} {S1 : List Addr}
    (hL : PtLocs p' fr) (hW1 : W σ1 p'.A (postCat p'.s p'.t p'.x))
    (hfr0 : FrameS σ0 σ [p'.A.wT]) (hfr1 : FrameS σ σ1 S1)
    (hS1 : ∀ z ∈ S1, z ∈ [p'.A.wC, p'.A.lC, p'.A.lD, p'.A.lCW, p'.A.lCR])
    (hwTS1 : p'.A.wT ∉ S1) (hNS1 : NoStr σ S1)
    (hi : σ1.inits = σ0.inits) (hs : σ1.statics = σ0.statics)
    (htw : JRecAt TranRecord trCls σ (.ref p'.A.wT) (Model.tranVals p'.t p'.clk)) :
    PtLocs p' (fr.setLocal 12 (.int 0)) ∧ W σ1 p'.A (postCat p'.s p'.t p'.x) ∧
    FrameS σ0 σ1 [p'.A.wT, p'.A.wC, p'.A.lC, p'.A.lD, p'.A.lCW, p'.A.lCR] ∧ σ1.inits = σ0.inits ∧
    σ1.statics = σ0.statics ∧ JRecAt TranRecord trCls σ1 (.ref p'.A.wT) (Model.tranVals p'.t p'.clk) := by
  obtain ⟨l4, l2, l8, l5, l1, l11, l0, l6, l7⟩ := hL
  refine ⟨⟨by frame_simp [l4], by frame_simp [l2], by frame_simp [l8], by frame_simp [l5],
    by frame_simp [l1], by frame_simp [l11], by frame_simp [l0], by frame_simp [l6], by frame_simp [l7]⟩,
    hW1, FrameS.trans (hfr0.mono (by simp)) (hfr1.mono (fun z hz => by
      have := hS1 z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
      rcases this with h | h | h | h | h <;> simp [h])), hi, hs,
    jrecAt_frame htw hfr1 hNS1 (fun y hy hm => by cases hy; exact hwTS1 hm)⟩

/-- `tranWs` is none of the other objects `postTransaction` changes. -/
theorem wT_not_mem {σ : State} {A : Addrs} {s : Model.St} (hW : W σ A s) :
    A.wT ∉ [A.wC, A.lC, A.lD, A.lCW, A.lCR, A.wA, A.aD, A.lAR, A.lK, A.lT] := by
  obtain ⟨-, ⟨xD, mD, hD, -⟩, ⟨xT, mT, hT, -⟩, -, ⟨xW, mW, hCW, -⟩, ⟨xA, mA, hAR, -⟩,
    ⟨xC, mC, hCR, -⟩, ⟨et, xa, haD, -⟩, ⟨xl, ml, hlC, -⟩, ⟨xk, mk, hK, -⟩, -, ⟨fA, hwA, -⟩,
    ⟨fC, hwC, -⟩, ⟨fT, hwT, -⟩, -⟩ := hW
  intro hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h <;> rw [h] at hwT <;>
    first
    | (rw [hwC] at hwT; simp only [Option.some.injEq, Obj.plain.injEq] at hwT
       exact absurd hwT.1 (by decide))
    | (rw [hwA] at hwT; simp only [Option.some.injEq, Obj.plain.injEq] at hwT
       exact absurd hwT.1 (by decide))
    | (rw [hlC] at hwT; cases hwT) | (rw [hD] at hwT; cases hwT) | (rw [hCW] at hwT; cases hwT)
    | (rw [hCR] at hwT; cases hwT) | (rw [haD] at hwT; cases hwT) | (rw [hAR] at hwT; cases hwT)
    | (rw [hK] at hwT; cases hwT) | (rw [hT] at hwT; cases hwT)

/-- `acctWs` and the account table are none of the objects changed before statement 39. -/
theorem wA_not_mem {σ : State} {A : Addrs} {s : Model.St} (hW : W σ A s) :
    A.wA ∉ [A.wT, A.wC, A.lC, A.lD, A.lCW, A.lCR] ∧ A.aD ∉ [A.wT, A.wC, A.lC, A.lD, A.lCW, A.lCR] := by
  obtain ⟨-, ⟨xD, mD, hD, -⟩, -, -, ⟨xW, mW, hCW, -⟩, -, ⟨xC, mC, hCR, -⟩, ⟨et, xa, haD, -⟩,
    ⟨xl, ml, hlC, -⟩, -, -, ⟨fA, hwA, -⟩, ⟨fC, hwC, -⟩, ⟨fT, hwT, -⟩, -⟩ := hW
  constructor
  · intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h <;> rw [h] at hwA <;>
      first
      | (rw [hwT] at hwA; simp only [Option.some.injEq, Obj.plain.injEq] at hwA
         exact absurd hwA.1 (by decide))
      | (rw [hwC] at hwA; simp only [Option.some.injEq, Obj.plain.injEq] at hwA
         exact absurd hwA.1 (by decide))
      | (rw [hlC] at hwA; cases hwA) | (rw [hD] at hwA; cases hwA) | (rw [hCW] at hwA; cases hwA)
      | (rw [hCR] at hwA; cases hwA)
  · intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h <;> rw [h] at haD <;>
      first
      | (rw [hwT] at haD; cases haD) | (rw [hwC] at haD; cases haD)
      | (rw [hlC] at haD; cases haD) | (rw [hD] at haD; cases haD) | (rw [hCW] at haD; cases haD)
      | (rw [hCR] at haD; cases haD)

/-- The daily transaction record is none of the objects changed before statement 39. -/
theorem d_not_mem {σ : State} {A : Addrs} {s : Model.St} {d : Addr} {t : List EquivLean.Cobol.Rec.FVal}
    (hW : W σ A s) (hd : JRecAt DalytranRecord dalCls σ (.ref d) t) :
    d ∉ [A.wT, A.wC, A.lC, A.lD, A.lCW, A.lCR] := by
  obtain ⟨-, ⟨xD, mD, hD, -⟩, -, -, ⟨xW, mW, hCW, -⟩, -, ⟨xC, mC, hCR, -⟩, -,
    ⟨xl, ml, hlC, -⟩, -, -, -, ⟨fC, hwC, -⟩, ⟨fT, hwT, -⟩, -⟩ := hW
  obtain ⟨y, fs, hy, hdo, -⟩ := hd
  cases hy
  intro hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h <;> rw [h] at hdo <;>
    first
    | (rw [hwT] at hdo; simp only [Option.some.injEq, Obj.plain.injEq] at hdo
       exact absurd hdo.1 (by decide))
    | (rw [hwC] at hdo; simp only [Option.some.injEq, Obj.plain.injEq] at hdo
       exact absurd hdo.1 (by decide))
    | (rw [hlC] at hdo; cases hdo) | (rw [hD] at hdo; cases hdo) | (rw [hCW] at hdo; cases hdo)
    | (rw [hCR] at hdo; cases hdo)

/-- The world after `updateAccount` posted the transaction to the account. -/
theorem w40_of {σ σ1 : State} {A : Addrs} {s : Model.St} {d : Addr}
    {t a : List EquivLean.Cobol.Rec.FVal}
    (hW : W σ A s) (hMV : MV s) (hd : JRecAt DalytranRecord dalCls σ (.ref d) t)
    (htv : DalytranRecord.Valid t) (ha : JRecAt AccountRecord acCls σ (.ref A.wA) a)
    (hav : AccountRecord.Valid a) (ham : a ∈ s.accts) (hlen : s.acctRW.length + 1 < 2147483648)
    {y1 y2 : Addr} {fs1 fs2 : List (FieldKey × Value)} {m' : Nat}
    (hwA' : σ1.heap A.wA = some (.plain "Cbtrn02c$AccountRecord" (acctPostFs (fieldsOf σ A.wA)
      (lng' σ A.wA acBalKey) (lng' σ A.wA acCcKey) (lng' σ A.wA acCdKey) (lng' σ d dAmtKey'))))
    (hD' : σ1.heap A.aD = some (.array (.cls "Cbtrn02c$AccountRecord") ((arrOf σ A.aD).set
      (firstIdx (fun v => longFieldOf σ acctIdKey v == some (lng' σ A.wA acctIdKey)) (arrOf σ A.aD)).toNat
      (.ref y1))))
    (hy1 : σ1.heap y1 = some (.plain "Cbtrn02c$AccountRecord" fs1))
    (hs1 : SameFields acKeys fs1 (acctPostFs (fieldsOf σ A.wA) (lng' σ A.wA acBalKey)
      (lng' σ A.wA acCcKey) (lng' σ A.wA acCdKey) (lng' σ d dAmtKey')))
    (hAR' : σ1.heap (refField σ A.r arKey) =
      some (.list .arrayList (listOf σ (refField σ A.r arKey) ++ [.ref y2]) m'))
    (hy2 : σ1.heap y2 = some (.plain "Cbtrn02c$AccountRecord" fs2))
    (hs2 : SameFields acKeys fs2 (acctPostFs (fieldsOf σ A.wA) (lng' σ A.wA acBalKey)
      (lng' σ A.wA acCcKey) (lng' σ A.wA acCdKey) (lng' σ d dAmtKey')))
    (hn1 : σ.next ≤ y1) (hn2 : σ.next ≤ y2)
    (hf : FrameS σ σ1 [A.wA, A.aD, refField σ A.r arKey]) :
    W σ1 A (postAcc s t a) ∧ FrameS σ σ1 [A.wA, A.aD, A.lAR] := by
  have hW0 := hW
  obtain ⟨⟨fsR, hRo, -, -, -, -, r5, -, -, -⟩, -, -, -, -, -, -, ⟨et, xsA, hlA, hfA, -, -⟩, -⟩ := hW0
  have eAR : refField σ A.r arKey = A.lAR := refField_of hRo r5
  rw [eAR] at hAR' hf
  obtain ⟨⟨a0, fs, s1, s5, s6, s7, s10, s11, s12, hae, hao, g0, -⟩, n0, b1, n2, n3, n4, b5, b6, b7, n8,
    n9, b10, b11, b12, rfl, h0, -⟩ := acctobj_of_rec ha hav
  cases hae
  obtain ⟨⟨da, fsd, s0', s1', s3', s4', s7', s8', s9', s10', s11', s12', s13', hde, hdo, -, -, -, -, -, -,
    -, -, -, g5, -⟩, -⟩ := dalobj_of_rec hd htv
  cases hde
  have eid : lng' σ A.wA acctIdKey = BitVec.ofInt 64 (Model.aId [.num n0, .str b1, .num n2, .num n3,
      .num n4, .str b5, .str b6, .str b7, .num n8, .num n9, .str b10, .str b11, .str b12]) := by
    simp [lng', fld', fieldsOf, hao, g0, nAt, Model.aId, Model.numOf]
  have eamt : lng' σ d dAmtKey' = BitVec.ofInt 64 (Model.tAmt t) := by
    simp [lng', fld', fieldsOf, hdo, g5, nAt, Model.tAmt, Model.numOf]
  have earr : arrOf σ A.aD = xsA := by simp [arrOf, hlA]
  have hidx := acct_first hfA hMV.1 (Model.aId [.num n0, .str b1, .num n2, .num n3,
      .num n4, .str b5, .str b6, .str b7, .num n8, .num n9, .str b10, .str b11, .str b12])
    (by simpa [Model.aId, Model.numOf] using h0)
  have hnn : 0 ≤ firstIdx (fun b => Model.aId b == Model.aId [.num n0, .str b1, .num n2, .num n3,
      .num n4, .str b5, .str b6, .str b7, .num n8, .num n9, .str b10, .str b11, .str b12]) s.accts :=
    firstIdx_nonneg_of_mem ham (by simp)
  have hj : firstIdx (fun b => Model.aId b == Model.aId [.num n0, .str b1, .num n2, .num n3,
      .num n4, .str b5, .str b6, .str b7, .num n8, .num n9, .str b10, .str b11, .str b12]) s.accts =
      ((firstIdx (fun b => Model.aId b == Model.aId [.num n0, .str b1, .num n2, .num n3,
      .num n4, .str b5, .str b6, .str b7, .num n8, .num n9, .str b10, .str b11, .str b12]) s.accts).toNat :
        Int) := (Int.toNat_of_nonneg hnn).symm
  rw [← earr] at hidx
  rw [eid, hidx] at hD'
  rw [eamt] at hwA' hs1 hs2
  obtain ⟨-, -, -, -, -, -, hamtb, -⟩ := Glue.tranOf_valid htv
  exact ⟨W_acct hW ha hav hj hamtb hwA' hD' hy1 hs1 hAR' hy2 hs2 hn1 hn2 hf hlen, hf⟩

/-- The invariant at statement 40 for the ghost values `p'`. -/
theorem pt40_body {p' : PG} {σ0 σ σ1 : State} {fr : Frame}
    (hL : PtLocs p' fr) (hW1 : W σ1 p'.A (postAcc (postCat p'.s p'.t p'.x) p'.t p'.a))
    (hfr0 : FrameS σ0 σ [p'.A.wT, p'.A.wC, p'.A.lC, p'.A.lD, p'.A.lCW, p'.A.lCR])
    (hfr1 : FrameS σ σ1 [p'.A.wA, p'.A.aD, p'.A.lAR])
    (hwT : p'.A.wT ∉ [p'.A.wA, p'.A.aD, p'.A.lAR]) (hNS1 : NoStr σ [p'.A.wA, p'.A.aD, p'.A.lAR])
    (hi : σ1.inits = σ0.inits) (hs : σ1.statics = σ0.statics)
    (htw : JRecAt TranRecord trCls σ (.ref p'.A.wT) (Model.tranVals p'.t p'.clk))
    (hAd : ∃ xs, σ1.heap p'.A.aD = some (.array (.cls "Cbtrn02c$AccountRecord") xs)) :
    PtLocs p' fr ∧ W σ1 p'.A (postAcc (postCat p'.s p'.t p'.x) p'.t p'.a) ∧
    FrameS σ0 σ1 [p'.A.wT, p'.A.wC, p'.A.lC, p'.A.lD, p'.A.lCW, p'.A.lCR, p'.A.wA, p'.A.aD,
      p'.A.lAR] ∧ σ1.inits = σ0.inits ∧ σ1.statics = σ0.statics ∧
    JRecAt TranRecord trCls σ1 (.ref p'.A.wT) (Model.tranVals p'.t p'.clk) ∧
    (∃ xs, σ1.heap p'.A.aD = some (.array (.cls "Cbtrn02c$AccountRecord") xs)) :=
  ⟨hL, hW1, FrameS.trans (hfr0.mono (by simp)) (hfr1.mono (by simp)), hi, hs,
    jrecAt_frame htw hfr1 hNS1 (fun y hy hm => by cases hy; exact hwT hm), hAd⟩

theorem postAcc_postCat_tranW (s : Model.St) (t x a : List EquivLean.Cobol.Rec.FVal) :
    (postAcc (postCat s t x) t a).tranW = s.tranW := by
  unfold postAcc postCat; split <;> rfl

theorem postAcc_postCat_disp (s : Model.St) (t x a : List EquivLean.Cobol.Rec.FVal) :
    (postAcc (postCat s t x) t a).disp.length ≤ s.disp.length + 1 := by
  unfold postAcc postCat; split <;> simp

/-- The world after `writeTransaction` wrote a new transaction record. -/
theorem w41_tran {σ σ1 : State} {A : Addrs} {s : Model.St} {b0 : List UInt8}
    {rest : List EquivLean.Cobol.Rec.FVal}
    (hW : W σ A s) (htw : JRecAt TranRecord trCls σ (.ref A.wT) (.str b0 :: rest))
    {y : Addr} {fsy : List (FieldKey × Value)} {mK' mT' : Nat}
    (hK' : σ1.heap A.lK = some (.list .arrayList (listOf σ A.lK ++ [fld σ A.wT trIdKey]) mK'))
    (hT' : σ1.heap (refField σ A.r ltKey) =
      some (.list .arrayList (listOf σ (refField σ A.r ltKey) ++ [.ref y]) mT'))
    (hy : σ.next ≤ y) (hyo : σ1.heap y = some (.plain "Cbtrn02c$TranRecord" fsy))
    (hsame : SameFields trKeys fsy (fieldsOf σ A.wT))
    (hf : FrameS σ σ1 [A.lK, refField σ A.r ltKey]) (hlen : s.tranW.length + 1 < 2147483648) :
    W σ1 A { s with tranW := s.tranW ++ [.str b0 :: rest] } ∧ FrameS σ σ1 [A.lK, A.lT] := by
  have hW0 := hW
  obtain ⟨⟨fsR, hRo, -, r2, -, -, -, -, -, -⟩, -⟩ := hW0
  have eT : refField σ A.r ltKey = A.lT := refField_of hRo r2
  rw [eT] at hT' hf
  have htw0 := htw
  obtain ⟨w', fsT, hwe, hto, hfl⟩ := htw0
  have ew : w' = A.wT := (Value.ref.inj hwe).symm
  subst ew
  obtain ⟨sv, hsv, sId, rfl, hsId⟩ : ∃ sv, Fields.get fsT (trCls, "tranId") = some sv ∧
      ∃ sId, sv = .ref sId ∧ σ.heap sId = some (.str (cp037Str b0)) := by
    cases hfl with
    | cons j0 _ => exact j0
  have efld : fld σ A.wT trIdKey = .ref sId := fld_of hto hsv
  rw [efld] at hK'
  exact ⟨W_tran hW htw ⟨sId, rfl, hsId⟩ hK' hT' hy hyo hsame hf hlen, hf⟩

theorem jstr_err : JStr.ofString "ERROR WRITING TO TRANSACTION FILE" =
    [69#16, 82#16, 82#16, 79#16, 82#16, 32#16, 87#16, 82#16, 73#16, 84#16, 73#16, 78#16, 71#16, 32#16,
      84#16, 79#16, 32#16, 84#16, 82#16, 65#16, 78#16, 83#16, 65#16, 67#16, 84#16, 73#16, 79#16, 78#16,
      32#16, 70#16, 73#16, 76#16, 69#16] := by decide
theorem jstr_st22 : JStr.ofString "FILE STATUS IS: NNNN0022" =
    [70#16, 73#16, 76#16, 69#16, 32#16, 83#16, 84#16, 65#16, 84#16, 85#16, 83#16, 32#16, 73#16, 83#16,
      58#16, 32#16, 78#16, 78#16, 78#16, 78#16, 48#16, 48#16, 50#16, 50#16] := by decide
theorem jstr_abend : JStr.ofString "ABENDING PROGRAM" =
    [65#16, 66#16, 69#16, 78#16, 68#16, 73#16, 78#16, 71#16, 32#16, 80#16, 82#16, 79#16, 71#16, 82#16,
      65#16, 77#16] := by decide

/-- The outputs after `writeTransaction` abended on a written id. -/
theorem wab_of {σ σ1 : State} {A : Addrs} {s : Model.St} (hW : W σ A s) {y1 y2 y3 : Addr} {mD' : Nat}
    (hD' : σ1.heap (refField σ A.r dispKey) = some (.list .arrayList
      (listOf σ (refField σ A.r dispKey) ++ [.ref y1, .ref y2, .ref y3]) mD'))
    (h1 : σ1.heap y1 = some (.str [69#16, 82#16, 82#16, 79#16, 82#16, 32#16, 87#16, 82#16, 73#16,
      84#16, 73#16, 78#16, 71#16, 32#16, 84#16, 79#16, 32#16, 84#16, 82#16, 65#16, 78#16, 83#16, 65#16,
      67#16, 84#16, 73#16, 79#16, 78#16, 32#16, 70#16, 73#16, 76#16, 69#16]))
    (h2 : σ1.heap y2 = some (.str [70#16, 73#16, 76#16, 69#16, 32#16, 83#16, 84#16, 65#16, 84#16,
      85#16, 83#16, 32#16, 73#16, 83#16, 58#16, 32#16, 78#16, 78#16, 78#16, 78#16, 48#16, 48#16, 50#16,
      50#16]))
    (h3 : σ1.heap y3 = some (.str [65#16, 66#16, 69#16, 78#16, 68#16, 73#16, 78#16, 71#16, 32#16,
      80#16, 82#16, 79#16, 71#16, 82#16, 65#16, 77#16]))
    (hr : σ1.heap A.r = some (.plain "Cbtrn02c$Result" (Fields.set (fieldsOf σ A.r) abKey (.int 1#32))))
    (hf : FrameS σ σ1 [refField σ A.r dispKey, A.r]) (hlen : s.disp.length + 3 < 2147483648) :
    WAb σ1 A { s with disp := s.disp ++ Model.dupLines } := by
  have hW0 := hW
  obtain ⟨⟨fsR, hRo, r1, -⟩, -⟩ := hW0
  have eD : refField σ A.r dispKey = A.lD := refField_of hRo r1
  rw [eD] at hD' hf
  rw [← jstr_err] at h1
  rw [← jstr_st22] at h2
  rw [← jstr_abend] at h3
  exact W_dup hW hD' h1 h2 h3 hr hf hlen

end EquivLean.Modernize.Cbtrn02c.Java
