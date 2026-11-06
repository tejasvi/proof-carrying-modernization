import EquivLean.Modernize.Cbtrn02c.Any.JavaRunWC
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunAP

/-!
# CBTRN02C → Java: the world after `updateAccount`

`W_acct`: after `updateAccount` posted the amount into `acctWs` (holding the account `a`),
replaced the account at index `j` of `acctData` by a copy, and appended another copy to
ACCOUNT's rewrites, the state holds the model state with the account posted (`postAcc`).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem noStr_S3 {σ : State} {w a l : Addr} {c : ClassName} {fs : List (FieldKey × Value)}
    {et : JType} {xs1 xs2 : List Value} {m : Nat} (hw : σ.heap w = some (.plain c fs))
    (ha : σ.heap a = some (.array et xs1)) (hl : σ.heap l = some (.list .arrayList xs2 m)) :
    NoStr σ [w, a, l] := by
  intro b hb t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · rw [hw] at ht; cases ht
  · rw [ha] at ht; cases ht
  · rw [hl] at ht; cases ht

theorem keysOf_acct : keysOf AccountRecord "Cbtrn02c$AccountRecord" = acKeys := by decide

theorem allSome_acctPostFs {fs : List (FieldKey × Value)} {bal cc cdb amt : I64}
    (h : AllSome acKeys fs) : AllSome acKeys (acctPostFs fs bal cc cdb amt) := by
  unfold acctPostFs
  split <;> exact allSome_set _ _ (allSome_set _ _ h)

/-- The world after `updateAccount`. -/
theorem W_acct {σ σ' : State} {A : Addrs} {s : Model.St} {t a : List EquivLean.Cobol.Rec.FVal} {j : Nat}
    (hW : W σ A s) (hwa : JRecAt AccountRecord "Cbtrn02c$AccountRecord" σ (.ref A.wA) a)
    (hav : AccountRecord.Valid a)
    (hj : firstIdx (fun b => Model.aId b == Model.aId a) s.accts = j)
    (hamt : (Model.tAmt t).natAbs < 100000000000)
    {y1 y2 : Addr} {fs1 fs2 : List (FieldKey × Value)} {m' : Nat}
    (hwA' : σ'.heap A.wA = some (.plain "Cbtrn02c$AccountRecord" (acctPostFs (fieldsOf σ A.wA)
      (lng' σ A.wA acBalKey) (lng' σ A.wA acCcKey) (lng' σ A.wA acCdKey)
      (BitVec.ofInt 64 (Model.tAmt t)))))
    (hD' : σ'.heap A.aD = some (.array (.cls "Cbtrn02c$AccountRecord") ((arrOf σ A.aD).set j (.ref y1))))
    (hy1 : σ'.heap y1 = some (.plain "Cbtrn02c$AccountRecord" fs1))
    (hs1 : SameFields acKeys fs1 (acctPostFs (fieldsOf σ A.wA) (lng' σ A.wA acBalKey)
      (lng' σ A.wA acCcKey) (lng' σ A.wA acCdKey) (BitVec.ofInt 64 (Model.tAmt t))))
    (hAR' : σ'.heap A.lAR = some (.list .arrayList (listOf σ A.lAR ++ [.ref y2]) m'))
    (hy2 : σ'.heap y2 = some (.plain "Cbtrn02c$AccountRecord" fs2))
    (hs2 : SameFields acKeys fs2 (acctPostFs (fieldsOf σ A.wA) (lng' σ A.wA acBalKey)
      (lng' σ A.wA acCcKey) (lng' σ A.wA acCdKey) (BitVec.ofInt 64 (Model.tAmt t))))
    (hn1 : σ.next ≤ y1) (hn2 : σ.next ≤ y2) (hf : FrameS σ σ' [A.wA, A.aD, A.lAR])
    (hlen : s.acctRW.length + 1 < 2147483648) :
    W σ' A (postAcc s t a) := by
  have hW0 := hW
  obtain ⟨hR, hD, hT, hRj, hCW, hAR, hCR, hA, hC, hK, hwX, hwA, hwC, hwT, hfC, hfT, hnd⟩ := hW
  obtain ⟨et, xsA, hlA, hfA, hwsA, hnA⟩ := hA
  obtain ⟨xsR, mR, hlR, hfR, hwsR, hnR⟩ := hAR
  obtain ⟨fsW, hwAo, hkW⟩ := hwA
  have hS : NoStr σ [A.wA, A.aD, A.lAR] := noStr_S3 hwAo hlA hlR
  have hN : NoRec σ A.ws [A.wA, A.aD, A.lAR] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · left; simp [Addrs.ws]
    · right; intro c fs h; rw [hlA] at h; cases h
    · right; intro c fs h; rw [hlR] at h; cases h
  have hnd0 := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨n1, n2, n3, n4, n5, n6, n7⟩, ⟨n8, n9, n10, n11, n12, n13⟩, ⟨n14, n15, n16, n17, n18⟩,
    ⟨n19, n20, n21, n22⟩, ⟨n23, n24, n25⟩, ⟨n26, n27⟩, n28, -⟩ := hnd
  have plS : ∀ {w c fs}, σ.heap w = some (.plain c fs) → c ≠ "Cbtrn02c$AccountRecord" →
      w ∉ [A.wA, A.aD, A.lAR] := by
    intro w c fs hw hc' hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact ne_of_plain_cls hw hwAo hc' rfl
    · rw [hw] at hlA; cases hlA
    · rw [hw] at hlR; cases hlR
  have lsS : ∀ {l xs m}, σ.heap l = some (.list .arrayList xs m) → l ≠ A.lAR →
      l ∉ [A.wA, A.aD, A.lAR] := by
    intro l xs m hl h1 hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [hl] at hwAo; cases hwAo
    · rw [hl] at hlA; cases hlA
    · exact h1 rfl
  have hstr : ∀ v t, JStrAt σ v t → JStrAt σ' v t := fun v t h => jstrAt_frame h hf hS
  have newrec : ∀ {y fsy}, σ'.heap y = some (.plain "Cbtrn02c$AccountRecord" fsy) →
      SameFields acKeys fsy (acctPostFs (fieldsOf σ A.wA) (lng' σ A.wA acBalKey)
        (lng' σ A.wA acCcKey) (lng' σ A.wA acCdKey) (BitVec.ofInt 64 (Model.tAmt t))) →
      JRecAt AccountRecord "Cbtrn02c$AccountRecord" σ' (.ref y) (Model.postAcct a (Model.tAmt t)) :=
    fun hy hsy => acct_post_rec hwa hav hy hsy hamt hstr
  have hjl : j < s.accts.length := by
    have h1 := firstIdx_lt (fun b => Model.aId b == Model.aId a) s.accts
    have h2 : (0 : Int) ≤ firstIdx (fun b => Model.aId b == Model.aId a) s.accts := by rw [hj]; omega
    omega
  unfold postAcc
  rw [replaceFirst_eq_set _ _ _ j hj]
  refine ⟨hR.frame hf (by obtain ⟨fs, h, -⟩ := hR; exact plS h (by decide)),
    hD.frame hf hS (by obtain ⟨xs, m, h, -⟩ := hD; exact lsS h n4),
    hT.frame hf hS hN (by obtain ⟨xs, m, h, -⟩ := hT; exact lsS h n10),
    hRj.frame hf hS hN (by obtain ⟨xs, m, h, -⟩ := hRj; exact lsS h n15),
    hCW.frame hf hS hN (by obtain ⟨xs, m, h, -⟩ := hCW; exact lsS h n19), ?_,
    hCR.frame hf hS hN (by obtain ⟨xs, m, h, -⟩ := hCR; exact lsS h (Ne.symm n23)), ?_,
    hC.frame hf hS hN (by obtain ⟨xs, m, h, -⟩ := hC; exact lsS h (Ne.symm n24)),
    hK.frame hf hS (by obtain ⟨xs, m, h, -⟩ := hK; exact lsS h (Ne.symm n25)),
    hwX.frame hf (by obtain ⟨fs, h, -⟩ := hwX; exact plS h (by decide)), ?_,
    hwC.frame hf (by obtain ⟨fs, h, -⟩ := hwC; exact plS h (by decide)),
    hwT.frame hf (by obtain ⟨fs, h, -⟩ := hwT; exact plS h (by decide)),
    hfC.frame hf hS (by obtain ⟨fs, sv, h, -⟩ := hfC; exact plS h (by decide)),
    hfT.frame hf hS (by obtain ⟨fs, sv, h, -⟩ := hfT; exact plS h (by decide)), hnd0⟩
  · -- ACCOUNT rewrites
    rw [listOf_of hlR] at hAR'
    refine ⟨xsR ++ [.ref y2], m', hAR', ?_, ?_, ?_⟩
    · refine forall2_append (newrec hy2 hs2) ?_
      refine forall2_imp_mem (fun v hv val hr => jrecAt_frame hr hf hS ?_) hfR
      rintro z rfl hz
      rcases hN z hz with hws | hnp
      · exact hwsR _ hv z hws rfl
      · obtain ⟨z', fs, hz', hzo, _⟩ := hr; cases hz'; exact hnp _ _ hzo
    · intro v hv w hw'
      rcases List.mem_append.mp hv with hv | hv
      · exact hwsR v hv w hw'
      · simp only [List.mem_singleton] at hv; subst hv; exact fresh_not_ws hW0 hn2 w hw'
    · have := forall2_length hfR
      simp only [List.length_append, List.length_singleton] at *
      omega
  · -- the account table
    rw [arrOf_of hlA] at hD'
    refine ⟨.cls "Cbtrn02c$AccountRecord", xsA.set j (.ref y1), ?_, ?_, ?_, ?_⟩
    · exact hD'
    · refine forall2_set (newrec hy1 hs1) j ?_
      refine forall2_imp_mem (fun v hv val hr => jrecAt_frame hr hf hS ?_) hfA
      rintro z rfl hz
      rcases hN z hz with hws | hnp
      · exact hwsA _ hv z hws rfl
      · obtain ⟨z', fs, hz', hzo, _⟩ := hr; cases hz'; exact hnp _ _ hzo
    · intro v hv w hw'
      rcases List.mem_or_eq_of_mem_set hv with hv | hv
      · exact hwsA v hv w hw'
      · subst hv; exact fresh_not_ws hW0 hn1 w hw'
    · simp only [List.length_set]; exact hnA
  · -- acctWs
    refine ⟨_, hwA', ?_⟩
    rw [keysOf_acct]
    apply allSome_acctPostFs
    rw [fieldsOf_of hwAo]
    rw [keysOf_acct] at hkW
    exact hkW

end EquivLean.Modernize.Cbtrn02c.Java
