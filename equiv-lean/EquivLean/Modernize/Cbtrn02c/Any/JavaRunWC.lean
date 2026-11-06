import EquivLean.Modernize.Cbtrn02c.Any.JavaRunWT
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunMS
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunAR
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunMF
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunS3

/-!
# CBTRN02C → Java: the world after `updateTcatbal`

A category balance object from its five fields (`tcat_rec_of`), and the record texts of the
display line for a missing key.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- A category balance object holding `[n0, b1, n2, n3, b4]`, from its fields. -/
theorem tcat_rec_of {σ : State} {y : Addr} {fs : List (FieldKey × Value)} {n0 n2 n3 : Int}
    {b1 b4 : List UInt8} {v1 v4 : Value}
    (hy : σ.heap y = some (.plain "Cbtrn02c$TranCatBalRecord" fs))
    (h0 : Fields.get fs ("Cbtrn02c$TranCatBalRecord", "trancatAcctId") = some (.long (BitVec.ofInt 64 n0)))
    (h1 : Fields.get fs ("Cbtrn02c$TranCatBalRecord", "trancatTypeCd") = some v1)
    (hv1 : JStrAt σ v1 (cp037Str b1))
    (h2 : Fields.get fs ("Cbtrn02c$TranCatBalRecord", "trancatCd") = some (.long (BitVec.ofInt 64 n2)))
    (h3 : Fields.get fs ("Cbtrn02c$TranCatBalRecord", "tranCatBal") = some (.long (BitVec.ofInt 64 n3)))
    (h4 : Fields.get fs ("Cbtrn02c$TranCatBalRecord", "filler1") = some v4)
    (hv4 : JStrAt σ v4 (cp037Str b4)) :
    JRecAt TranCatBalRecord "Cbtrn02c$TranCatBalRecord" σ (.ref y)
      [.num n0, .str b1, .num n2, .num n3, .str b4] :=
  ⟨y, fs, rfl, hy, .cons h0 (.cons ⟨v1, h1, hv1⟩ (.cons h2 (.cons h3 (.cons ⟨v4, h4, hv4⟩ .nil))))⟩

theorem jline_txt_eq (s : String) : jline (Model.txt s) = (s.toList.map Char.toNat).map (BitVec.ofNat 16) := rfl

theorem noCat_text_pre : jline (Model.txt "TCATBAL record not found for key : ") =
    JStr.ofString "TCATBAL record not found for key : " := by decide
theorem noCat_text_post : jline (Model.txt ".. Creating.") = JStr.ofString ".. Creating." := by decide

/-- The display line for a missing key, as `updateTcatbal` builds it. -/
theorem noCatJ_eq (acct cd : Int) (ty : List UInt8) (ha : acct.natAbs < 10 ^ 18)
    (hc : cd.natAbs < 10 ^ 18) :
    noCatJ (BitVec.ofInt 64 acct) (cp037Str ty) (BitVec.ofInt 64 cd) =
      jline (Model.noCatLine acct ty cd) := by
  unfold noCatJ Model.noCatLine
  rw [toInt_ofInt_of_natAbs ha, toInt_ofInt_of_natAbs hc]
  simp only [jline_append, jline_zpad, jline_cp037, noCat_text_pre, noCat_text_post,
    List.append_assoc]

theorem replaceFirst_eq_set {α : Type} (p : α → Bool) (x : α) :
    ∀ (l : List α) (j : Nat), firstIdx p l = j → Model.replaceFirst p x l = l.set j x
  | [], j, h => by simp [firstIdx] at h <;> omega
  | y :: ys, j, h => by
    unfold firstIdx at h
    rw [List.findIdx?_cons] at h
    by_cases hy : p y = true
    · simp only [hy, ↓reduceIte] at h
      have : j = 0 := by omega
      subst this
      simp [Model.replaceFirst, hy]
    · simp only [Bool.not_eq_true] at hy
      simp only [hy, Bool.false_eq_true, ↓reduceIte] at h
      cases hf : ys.findIdx? p with
      | none => rw [hf] at h; simp at h <;> omega
      | some i =>
        rw [hf] at h
        simp only [Option.map_some] at h
        have hj : j = i + 1 := by omega
        subst hj
        simp only [Model.replaceFirst, hy, Bool.false_eq_true, ↓reduceIte, List.set_cons_succ]
        congr 1
        exact replaceFirst_eq_set p x ys i (by unfold firstIdx; rw [hf])

theorem noStr_S4 {σ : State} {w l1 l2 l3 : Addr} {c : ClassName} {fs : List (FieldKey × Value)}
    {xs1 xs2 xs3 : List Value} {m1 m2 m3 : Nat} (hw : σ.heap w = some (.plain c fs))
    (h1 : σ.heap l1 = some (.list .arrayList xs1 m1)) (h2 : σ.heap l2 = some (.list .arrayList xs2 m2))
    (h3 : σ.heap l3 = some (.list .arrayList xs3 m3)) : NoStr σ [w, l1, l2, l3] := by
  intro a ha t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · rw [hw] at ht; cases ht
  · rw [h1] at ht; cases ht
  · rw [h2] at ht; cases ht
  · rw [h3] at ht; cases ht

/-- The world after `updateTcatbal` when the key is missing (a record is created). -/
theorem W_tcat_create {σ σ' : State} {A : Addrs} {s : Model.St} {t x : List FV}
    (hW : W σ A s) (hfind : Model.findCat s.cats (Model.xAcct x) (Model.tType t) (Model.tCat t) = none)
    {sty : Addr} (hty : JStrAt σ (.ref sty) (cp037Str (Model.tType t)))
    (ha : (Model.xAcct x).natAbs < 10 ^ 18) (hc : (Model.tCat t).natAbs < 10 ^ 18)
    (hamt : (Model.tAmt t).natAbs < 100000000000)
    {sD y1 y2 : Addr} {fsC' fs1 fs2 : List (FieldKey × Value)} {m1 m2 m3 : Nat}
    (hD' : σ'.heap A.lD = some (.list .arrayList (listOf σ A.lD ++ [.ref sD]) m1))
    (hsD : σ'.heap sD = some (.str (jline (Model.noCatLine (Model.xAcct x) (Model.tType t) (Model.tCat t)))))
    (hwC' : σ'.heap A.wC = some (.plain "Cbtrn02c$TranCatBalRecord" fsC'))
    (f0 : Fields.get fsC' tcAcctKey = some (.long (BitVec.ofInt 64 (Model.xAcct x))))
    (f1 : Fields.get fsC' tcTypeKey = some (.ref sty))
    (f2 : Fields.get fsC' tcCdKey = some (.long (BitVec.ofInt 64 (Model.tCat t))))
    (f3 : Fields.get fsC' tcBalKey = some (.long (BitVec.ofInt 64 (Model.tAmt t))))
    (f4 : Fields.get fsC' tcFillKey = Fields.get (fieldsOf σ A.wC) tcFillKey)
    (hC' : σ'.heap A.lC = some (.list .arrayList (listOf σ A.lC ++ [.ref y1]) m2))
    (hy1 : σ'.heap y1 = some (.plain "Cbtrn02c$TranCatBalRecord" fs1)) (hs1 : SameFields tcKeys fs1 fsC')
    (hCW' : σ'.heap A.lCW = some (.list .arrayList (listOf σ A.lCW ++ [.ref y2]) m3))
    (hy2 : σ'.heap y2 = some (.plain "Cbtrn02c$TranCatBalRecord" fs2)) (hs2 : SameFields tcKeys fs2 fsC')
    (hn1 : σ.next ≤ y1) (hn2 : σ.next ≤ y2) (hnD : σ.next ≤ sD)
    (hf : FrameS σ σ' [A.wC, A.lC, A.lD, A.lCW])
    (hlen : s.cats.length + 1 < 2147483648 ∧ s.catW.length + 1 < 2147483648 ∧
      s.disp.length + 1 < 2147483648) :
    W σ' A (postCat s t x) := by
  have hW0 := hW
  obtain ⟨hR, hD, hT, hRj, hCW, hAR, hCR, hA, hC, hK, hwX, hwA, hwC, hwT, hfC, hfT, hnd⟩ := hW
  obtain ⟨xsD, mD, hlD, hfD, hnD0⟩ := hD
  obtain ⟨xsC, mC, hlC, hfC0, hwsC, hnC⟩ := hC
  obtain ⟨xsW, mW, hlW, hfW0, hwsW, hnW⟩ := hCW
  obtain ⟨fsC, hwCo, hkC⟩ := hwC
  obtain ⟨fsF, sv, hwF, hsv, hsvs⟩ := hfC
  rw [hwCo] at hwF; cases hwF
  have hS : NoStr σ [A.wC, A.lC, A.lD, A.lCW] := noStr_S4 hwCo hlC hlD hlW
  have hN : NoRec σ A.ws [A.wC, A.lC, A.lD, A.lCW] := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · left; simp [Addrs.ws]
    · right; intro c fs h; rw [hlC] at h; cases h
    · right; intro c fs h; rw [hlD] at h; cases h
    · right; intro c fs h; rw [hlW] at h; cases h
  have hnd0 := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨n1, n2, n3, n4, n5, n6, n7⟩, ⟨n8, n9, n10, n11, n12, n13⟩, ⟨n14, n15, n16, n17, n18⟩,
    ⟨n19, n20, n21, n22⟩, ⟨n23, n24, n25⟩, ⟨n26, n27⟩, n28, -⟩ := hnd
  -- objects outside S
  have plS : ∀ {w c fs}, σ.heap w = some (.plain c fs) → c ≠ "Cbtrn02c$TranCatBalRecord" →
      w ∉ [A.wC, A.lC, A.lD, A.lCW] := by
    intro w c fs hw hc' hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact ne_of_plain_cls hw hwCo hc' rfl
    · rw [hw] at hlC; cases hlC
    · rw [hw] at hlD; cases hlD
    · rw [hw] at hlW; cases hlW
  have lsS : ∀ {l xs m}, σ.heap l = some (.list .arrayList xs m) → l ≠ A.lC → l ≠ A.lD →
      l ≠ A.lCW → l ∉ [A.wC, A.lC, A.lD, A.lCW] := by
    intro l xs m hl h1 h2 h3 hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · rw [hl] at hwCo; cases hwCo
    · exact h1 rfl
    · exact h2 rfl
    · exact h3 rfl
  -- the new category record
  have hsv' : JStrAt σ' sv (cp037Str s.catFill) := jstrAt_frame hsvs hf hS
  have hty' : JStrAt σ' (.ref sty) (cp037Str (Model.tType t)) := jstrAt_frame hty hf hS
  have hfill : Fields.get fsC' tcFillKey = some sv := by rw [f4, fieldsOf_of hwCo]; exact hsv
  have rec_of : ∀ {y fsy}, σ'.heap y = some (.plain "Cbtrn02c$TranCatBalRecord" fsy) →
      SameFields tcKeys fsy fsC' →
      JRecAt TranCatBalRecord "Cbtrn02c$TranCatBalRecord" σ' (.ref y)
        [.num (Model.xAcct x), .str (Model.tType t), .num (Model.tCat t), .num (Model.tAmt t),
          .str s.catFill] := by
    intro y fsy hy hsy
    exact tcat_rec_of hy (by rw [hsy _ (by simp [tcKeys]), f0]) (by rw [hsy _ (by simp [tcKeys]), f1])
      hty' (by rw [hsy _ (by simp [tcKeys]), f2]) (by rw [hsy _ (by simp [tcKeys]), f3])
      (by rw [hsy _ (by simp [tcKeys]), hfill]) hsv'
  simp only [postCat, hfind]
  refine ⟨hR.frame hf (by obtain ⟨fs, h, -⟩ := hR; exact plS h (by decide)), ?_,
    hT.frame hf hS hN ?_,
    hRj.frame hf hS hN ?_, ?_, hAR.frame hf hS hN ?_, hCR.frame hf hS hN ?_, hA.frame hf hS hN ?_,
    ?_, hK.frame hf hS ?_, hwX.frame hf ?_, hwA.frame hf ?_, ?_, hwT.frame hf ?_, ?_,
    hfT.frame hf hS ?_, hnd0⟩
  · -- the display list
    rw [listOf_of hlD] at hD'
    refine ⟨xsD ++ [.ref sD], m1, hD', ?_, ?_⟩
    · simp only [List.map_append, List.map_singleton]
      exact forall2_append ⟨sD, rfl, hsD⟩ (forall2_imp (fun _ _ h => jstrAt_frame h hf hS) hfD)
    · have := forall2_length hfD
      simp only [List.length_append, List.length_singleton, List.length_map] at *
      omega
  · obtain ⟨xs, m, h, -⟩ := hT; exact lsS h n12 (Ne.symm n1) n9
  · obtain ⟨xs, m, h, -⟩ := hRj; exact lsS h n17 (Ne.symm n2) n14
  · -- TCATBAL writes
    rw [listOf_of hlW] at hCW'
    refine ⟨xsW ++ [.ref y2], m3, hCW', ?_, ?_, ?_⟩
    · refine forall2_append (rec_of hy2 hs2) ?_
      refine forall2_imp_mem (fun v hv val hr => jrecAt_frame hr hf hS ?_) hfW0
      rintro z rfl hz
      rcases hN z hz with hws | hnp
      · exact hwsW _ hv z hws rfl
      · obtain ⟨z', fs, hz', hzo, _⟩ := hr; cases hz'; exact hnp _ _ hzo
    · intro v hv w hw'
      rcases List.mem_append.mp hv with hv | hv
      · exact hwsW v hv w hw'
      · simp only [List.mem_singleton] at hv; subst hv; exact fresh_not_ws hW0 hn2 w hw'
    · have := forall2_length hfW0
      simp only [List.length_append, List.length_singleton] at *
      omega
  · obtain ⟨xs, m, h, -⟩ := hAR; exact lsS h n24 (Ne.symm n4) (Ne.symm n19)
  · obtain ⟨xs, m, h, -⟩ := hCR; exact lsS h n26 (Ne.symm n5) (Ne.symm n20)
  · obtain ⟨et, xs, h, -⟩ := hA
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h' | h' | h' | h' <;> rw [h'] at h
    · rw [hwCo] at h; cases h
    · rw [hlC] at h; cases h
    · rw [hlD] at h; cases h
    · rw [hlW] at h; cases h
  · -- the category file
    rw [listOf_of hlC] at hC'
    refine ⟨xsC ++ [.ref y1], m2, hC', ?_, ?_, ?_⟩
    · refine forall2_append (rec_of hy1 hs1) ?_
      refine forall2_imp_mem (fun v hv val hr => jrecAt_frame hr hf hS ?_) hfC0
      rintro z rfl hz
      rcases hN z hz with hws | hnp
      · exact hwsC _ hv z hws rfl
      · obtain ⟨z', fs, hz', hzo, _⟩ := hr; cases hz'; exact hnp _ _ hzo
    · intro v hv w hw'
      rcases List.mem_append.mp hv with hv | hv
      · exact hwsC v hv w hw'
      · simp only [List.mem_singleton] at hv; subst hv; exact fresh_not_ws hW0 hn1 w hw'
    · have := forall2_length hfC0
      simp only [List.length_append, List.length_singleton] at *
      omega
  · obtain ⟨xs, m, h, -⟩ := hK; exact lsS h (Ne.symm n28) (Ne.symm n7) (Ne.symm n22)
  · obtain ⟨fs, h, -⟩ := hwX; exact plS h (by decide)
  · obtain ⟨fs, h, -⟩ := hwA; exact plS h (by decide)
  · refine ⟨fsC', hwC', ?_⟩
    intro k hk
    have : k ∈ tcKeys := by rwa [show keysOf TranCatBalRecord "Cbtrn02c$TranCatBalRecord" = tcKeys by decide] at hk
    simp only [tcKeys, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl
    · simp [f0]
    · simp [f1]
    · simp [f2]
    · simp [f3]
    · simp [hfill]
  · obtain ⟨fs, h, -⟩ := hwT; exact plS h (by decide)
  · exact ⟨fsC', sv, hwC', hfill, hsv'⟩
  · obtain ⟨fs, sv', h, -⟩ := hfT; exact plS h (by decide)

theorem tcatBal_fmt : CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt.signed = true ∧
    CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt.usage = .display ∧
    CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt.digits = 11 := by decide

theorem lng_of {σ : State} {w : Addr} {c : ClassName} {fs : List (FieldKey × Value)} {k : FieldKey}
    {v : I64} (hw : σ.heap w = some (.plain c fs)) (hk : Fields.get fs k = some (.long v)) :
    lng σ w k = v := by
  simp [lng, fld, fieldsOf, hw, hk]

/-- The world after `updateTcatbal` when the key is at index `j` (the record is updated). -/
theorem W_tcat_update {σ σ' : State} {A : Addrs} {s : Model.St} {t x : List FV} {j : Nat} {rec : Addr}
    (hW : W σ A s) (hval : ∀ c ∈ s.cats, TranCatBalRecord.Valid c)
    (hj : firstIdx (Model.catKey (Model.xAcct x) (Model.tType t) (Model.tCat t)) s.cats = j)
    (hrec : (listOf σ A.lC).getD j .null = .ref rec)
    (hamtv : (Model.tAmt t).natAbs < 100000000000)
    {d : Addr} (hamt : lng σ d dAmtKey = BitVec.ofInt 64 (Model.tAmt t))
    {y1 y2 : Addr} {fsA fs1 fs2 : List (FieldKey × Value)} {m2 m3 : Nat}
    (hfa : ∀ k ∈ tcKeys, Fields.get fsA k = Fields.get (fieldsOf σ rec) k)
    (hwC' : σ'.heap A.wC = some (.plain "Cbtrn02c$TranCatBalRecord" (Fields.set fsA tcBalKey
      (.long ((lng σ rec tcBalKey + lng σ d dAmtKey).srem 100000000000#64)))))
    (hC' : σ'.heap A.lC = some (.list .arrayList ((listOf σ A.lC).set j (.ref y1)) m2))
    (hy1 : σ'.heap y1 = some (.plain "Cbtrn02c$TranCatBalRecord" fs1))
    (hs1 : SameFields tcKeys fs1 (Fields.set fsA tcBalKey
      (.long ((lng σ rec tcBalKey + lng σ d dAmtKey).srem 100000000000#64))))
    (hCR' : σ'.heap A.lCR = some (.list .arrayList (listOf σ A.lCR ++ [.ref y2]) m3))
    (hy2 : σ'.heap y2 = some (.plain "Cbtrn02c$TranCatBalRecord" fs2))
    (hs2 : SameFields tcKeys fs2 (Fields.set fsA tcBalKey
      (.long ((lng σ rec tcBalKey + lng σ d dAmtKey).srem 100000000000#64))))
    (hn1 : σ.next ≤ y1) (hn2 : σ.next ≤ y2) (hf : FrameS σ σ' [A.wC, A.lC, A.lCR])
    (hlen : s.catRW.length + 1 < 2147483648) :
    W σ' A (postCat s t x) := by
  have hW0 := hW
  obtain ⟨hR, hD, hT, hRj, hCW, hAR, hCR, hA, hC, hK, hwX, hwA, hwC, hwT, hfC, hfT, hnd⟩ := hW
  obtain ⟨xsC, mC, hlC, hfC0, hwsC, hnC⟩ := hC
  obtain ⟨xsR, mR, hlR, hfR0, hwsR, hnR⟩ := hCR
  obtain ⟨fsC, hwCo, hkC⟩ := hwC
  rw [listOf_of hlC] at hrec hC'
  rw [listOf_of hlR] at hCR'
  -- the record at index j
  have hjl : j < s.cats.length := by
    have h1 := firstIdx_lt (Model.catKey (Model.xAcct x) (Model.tType t) (Model.tCat t)) s.cats
    omega
  have hjx : j < xsC.length := by rw [forall2_length hfC0]; exact hjl
  have hxj : xsC[j] = .ref rec := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjx, Option.getD_some] at hrec; exact hrec
  have hrc : JRecAt TranCatBalRecord "Cbtrn02c$TranCatBalRecord" σ (.ref rec) s.cats[j] := by
    have := forall2_get hfC0 j hjx hjl; rwa [hxj] at this
  have hvalid : TranCatBalRecord.Valid s.cats[j] := hval _ (List.getElem_mem hjl)
  have hfind : Model.findCat s.cats (Model.xAcct x) (Model.tType t) (Model.tCat t) = some s.cats[j] := by
    obtain ⟨hi, hf⟩ := find?_of_firstIdx_nonneg (p := Model.catKey (Model.xAcct x) (Model.tType t)
      (Model.tCat t)) (l := s.cats) (by rw [hj]; omega)
    unfold Model.findCat; rw [hf]; simp [hj]
  obtain ⟨⟨r', fsr, s1, s4, hre, hro, g0, g1, t1, g2, g3, g4, t4⟩, n0, b1, n2, n3, b4, hceq, a0, a2, a3⟩ :=
    tcatobj_of_rec hrc hvalid
  cases hre
  simp only [nAt, bAt, hceq, Model.strOf, Model.numOf, List.getD_cons_zero, List.getD_cons_succ] at g0 g2 g3 t1 t4
  have hS : NoStr σ [A.wC, A.lC, A.lCR] := by
    intro b hb tt ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · rw [hwCo] at ht; cases ht
    · rw [hlC] at ht; cases ht
    · rw [hlR] at ht; cases ht
  have hN : NoRec σ A.ws [A.wC, A.lC, A.lCR] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · left; simp [Addrs.ws]
    · right; intro c fs h; rw [hlC] at h; cases h
    · right; intro c fs h; rw [hlR] at h; cases h
  have hstr : ∀ v tt, JStrAt σ v tt → JStrAt σ' v tt := fun v tt h => jstrAt_frame h hf hS
  -- the new balance
  have hbal : (lng σ rec tcBalKey + lng σ d dAmtKey).srem 100000000000#64 =
      BitVec.ofInt 64 (Cobol.Sem.fitNum {} CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt (n3 + Model.tAmt t)).2 := by
    rw [lng_of hro g3, hamt, fitNum_signed_display tcatBal_fmt.1 tcatBal_fmt.2.1, tcatBal_fmt.2.2]
    have := srem_add_ofInt n3 (Model.tAmt t) 100000000000 (by decide) (by decide) (by omega) (by omega)
    simpa using this
  rw [hbal] at hwC' hs1 hs2
  -- the updated record
  have hfr : fieldsOf σ rec = fsr := fieldsOf_of hro
  rw [hfr] at hfa
  have newrec : ∀ {y fsy}, σ'.heap y = some (.plain "Cbtrn02c$TranCatBalRecord" fsy) →
      SameFields tcKeys fsy (Fields.set fsA tcBalKey (.long (BitVec.ofInt 64
        (Cobol.Sem.fitNum {} CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt (n3 + Model.tAmt t)).2))) →
      JRecAt TranCatBalRecord "Cbtrn02c$TranCatBalRecord" σ' (.ref y)
        [.num n0, .str b1, .num n2,
          .num (Cobol.Sem.fitNum {} CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt (n3 + Model.tAmt t)).2, .str b4] := by
    intro y fsy hy hsy
    refine tcat_rec_of hy ?_ ?_ (hstr _ _ ⟨s1, rfl, t1⟩) ?_ ?_ ?_ (hstr _ _ ⟨s4, rfl, t4⟩)
    · rw [hsy _ (by simp [tcKeys])]; simp (config := { decide := true }) only [Fields.get_set, ↓reduceIte]
      rw [hfa _ (by simp [tcKeys]), g0]
    · rw [hsy _ (by simp [tcKeys])]; simp (config := { decide := true }) only [Fields.get_set, ↓reduceIte]
      rw [hfa _ (by simp [tcKeys]), g1]
    · rw [hsy _ (by simp [tcKeys])]; simp (config := { decide := true }) only [Fields.get_set, ↓reduceIte]
      rw [hfa _ (by simp [tcKeys]), g2]
    · rw [hsy _ (by simp [tcKeys])]; simp (config := { decide := true }) only [Fields.get_set, ↓reduceIte]
    · rw [hsy _ (by simp [tcKeys])]; simp (config := { decide := true }) only [Fields.get_set, ↓reduceIte]
      rw [hfa _ (by simp [tcKeys]), g4]
  have hnd0 := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨n1, n2', n3', n4, n5, n6, n7⟩, ⟨n8, n9, n10, n11, n12, n13⟩, ⟨n14, n15, n16, n17, n18⟩,
    ⟨n19, n20, n21, n22⟩, ⟨n23, n24, n25⟩, ⟨n26, n27⟩, n28, -⟩ := hnd
  have plS : ∀ {w c fs}, σ.heap w = some (.plain c fs) → c ≠ "Cbtrn02c$TranCatBalRecord" →
      w ∉ [A.wC, A.lC, A.lCR] := by
    intro w c fs hw hc' hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact ne_of_plain_cls hw hwCo hc' rfl
    · rw [hw] at hlC; cases hlC
    · rw [hw] at hlR; cases hlR
  have lsS : ∀ {l xs m}, σ.heap l = some (.list .arrayList xs m) → l ≠ A.lC → l ≠ A.lCR →
      l ∉ [A.wC, A.lC, A.lCR] := by
    intro l xs m hl h1 h2 hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [hl] at hwCo; cases hwCo
    · exact h1 rfl
    · exact h2 rfl
  simp only [postCat, hfind]
  rw [replaceFirst_eq_set _ _ _ j hj]
  simp only [hceq, List.set_cons_succ, List.set_cons_zero, Model.cBal, Model.cFill, Model.numOf,
    Model.strOf, List.getD_cons_zero, List.getD_cons_succ]
  refine ⟨hR.frame hf (by obtain ⟨fs, h, -⟩ := hR; exact plS h (by decide)),
    hD.frame hf hS (by obtain ⟨xs, m, h, -⟩ := hD; exact lsS h n6 n5),
    hT.frame hf hS hN (by obtain ⟨xs, m, h, -⟩ := hT; exact lsS h n12 n11),
    hRj.frame hf hS hN (by obtain ⟨xs, m, h, -⟩ := hRj; exact lsS h n17 n16),
    hCW.frame hf hS hN (by obtain ⟨xs, m, h, -⟩ := hCW; exact lsS h n21 n20),
    hAR.frame hf hS hN (by obtain ⟨xs, m, h, -⟩ := hAR; exact lsS h n24 n23), ?_,
    hA.frame hf hS hN ?_, ?_,
    hK.frame hf hS (by obtain ⟨xs, m, h, -⟩ := hK; exact lsS h (Ne.symm n28) (Ne.symm n27)),
    hwX.frame hf (by obtain ⟨fs, h, -⟩ := hwX; exact plS h (by decide)),
    hwA.frame hf (by obtain ⟨fs, h, -⟩ := hwA; exact plS h (by decide)), ?_,
    hwT.frame hf (by obtain ⟨fs, h, -⟩ := hwT; exact plS h (by decide)), ?_,
    hfT.frame hf hS (by obtain ⟨fs, sv, h, -⟩ := hfT; exact plS h (by decide)), hnd0⟩
  · -- TCATBAL rewrites
    refine ⟨xsR ++ [.ref y2], m3, hCR', ?_, ?_, ?_⟩
    · refine forall2_append (newrec hy2 hs2) ?_
      refine forall2_imp_mem (fun v hv val hr => jrecAt_frame hr hf hS ?_) hfR0
      rintro z rfl hz
      rcases hN z hz with hws | hnp
      · exact hwsR _ hv z hws rfl
      · obtain ⟨z', fs, hz', hzo, _⟩ := hr; cases hz'; exact hnp _ _ hzo
    · intro v hv w hw'
      rcases List.mem_append.mp hv with hv | hv
      · exact hwsR v hv w hw'
      · simp only [List.mem_singleton] at hv; subst hv; exact fresh_not_ws hW0 hn2 w hw'
    · have := forall2_length hfR0
      simp only [List.length_append, List.length_singleton] at *
      omega
  · obtain ⟨et, xs, h, -⟩ := hA
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h' | h' | h' <;> rw [h'] at h
    · rw [hwCo] at h; cases h
    · rw [hlC] at h; cases h
    · rw [hlR] at h; cases h
  · -- the category file
    refine ⟨xsC.set j (.ref y1), m2, hC', ?_, ?_, ?_⟩
    · refine forall2_set (newrec hy1 hs1) j ?_
      refine forall2_imp_mem (fun v hv val hr => jrecAt_frame hr hf hS ?_) hfC0
      rintro z rfl hz
      rcases hN z hz with hws | hnp
      · exact hwsC _ hv z hws rfl
      · obtain ⟨z', fs, hz', hzo, _⟩ := hr; cases hz'; exact hnp _ _ hzo
    · intro v hv w hw'
      rcases List.mem_or_eq_of_mem_set hv with hv | hv
      · exact hwsC v hv w hw'
      · subst hv; exact fresh_not_ws hW0 hn1 w hw'
    · simp only [List.length_set]; exact hnC
  · -- tcatWs
    refine ⟨_, hwC', ?_⟩
    rw [show keysOf TranCatBalRecord "Cbtrn02c$TranCatBalRecord" = tcKeys by decide]
    apply allSome_set
    intro k hk
    rw [hfa k hk]
    simp only [tcKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [g0, g1, g2, g3, g4]
  · -- the FILLER of tcatWs: the record's
    refine ⟨_, .ref s4, hwC', ?_, hstr _ _ ⟨s4, rfl, t4⟩⟩
    simp (config := { decide := true }) only [Fields.get_set, ↓reduceIte]
    rw [hfa _ (by simp [tcKeys]), g4]

end EquivLean.Modernize.Cbtrn02c.Java
