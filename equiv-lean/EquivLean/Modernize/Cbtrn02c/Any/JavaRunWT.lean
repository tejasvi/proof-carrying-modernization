import EquivLean.Modernize.Cbtrn02c.Any.JavaRunWR
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunF

/-!
# CBTRN02C → Java: the world after a transaction is written

`W_tran`: after `writeTransaction` added the id string of `tranWs` to `tranKeys` and a copy of
`tranWs` (holding the transaction record `tv`) to TRANSACT, the state holds the model state with
`tv` written.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem noStr_lists {σ : State} {l1 l2 : Addr} {xs1 xs2 : List Value} {m1 m2 : Nat}
    (h1 : σ.heap l1 = some (.list .arrayList xs1 m1)) (h2 : σ.heap l2 = some (.list .arrayList xs2 m2)) :
    NoStr σ [l1, l2] := by
  intro a ha t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · rw [h1] at ht; cases ht
  · rw [h2] at ht; cases ht

theorem noRec_lists {σ : State} {ws : List Addr} {l1 l2 : Addr} {xs1 xs2 : List Value} {m1 m2 : Nat}
    (h1 : σ.heap l1 = some (.list .arrayList xs1 m1)) (h2 : σ.heap l2 = some (.list .arrayList xs2 m2)) :
    NoRec σ ws [l1, l2] := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  right
  rcases ha with rfl | rfl
  · exact fun c fs hc => by rw [h1] at hc; cases hc
  · exact fun c fs hc => by rw [h2] at hc; cases hc

theorem not_mem_pair {a b c : Addr} (h1 : a ≠ b) (h2 : a ≠ c) : a ∉ [b, c] := by
  simp [h1, h2]

theorem ws_lt {σ : State} {A : Addrs} {s : Model.St} (hW : W σ A s) : ∀ w ∈ A.ws, w < σ.next := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hwX, hwA, hwC, hwT, -⟩ := hW
  intro w hw
  simp only [Addrs.ws, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · obtain ⟨fs, h, -⟩ := hwX; exact State.lt_next_of_heap h
  · obtain ⟨fs, h, -⟩ := hwA; exact State.lt_next_of_heap h
  · obtain ⟨fs, h, -⟩ := hwC; exact State.lt_next_of_heap h
  · obtain ⟨fs, h, -⟩ := hwT; exact State.lt_next_of_heap h

theorem fresh_not_ws {σ : State} {A : Addrs} {s : Model.St} (hW : W σ A s) {y : Addr}
    (hy : σ.next ≤ y) : ∀ w ∈ A.ws, Value.ref y ≠ .ref w := by
  intro w hw heq
  injection heq with heq
  subst heq
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (ws_lt hW _ hw) hy)

theorem keysOf_tran : keysOf TranRecord "Cbtrn02c$TranRecord" = trKeys := by decide

/-- The world after `writeTransaction`. -/
theorem W_tran {σ σ' : State} {A : Addrs} {s : Model.St} {tv : List EquivLean.Cobol.Rec.FVal}
    (hW : W σ A s) (hwT : JRecAt TranRecord "Cbtrn02c$TranRecord" σ (.ref A.wT) tv)
    {sId : Addr} (hsId : JStrAt σ (.ref sId) (tidJ tv)) {y : Addr} {fsy : List (FieldKey × Value)}
    {mK' mT' : Nat}
    (hK' : σ'.heap A.lK = some (.list .arrayList (listOf σ A.lK ++ [.ref sId]) mK'))
    (hT' : σ'.heap A.lT = some (.list .arrayList (listOf σ A.lT ++ [.ref y]) mT'))
    (hy : σ.next ≤ y) (hyo : σ'.heap y = some (.plain "Cbtrn02c$TranRecord" fsy))
    (hsame : SameFields trKeys fsy (fieldsOf σ A.wT)) (hf : FrameS σ σ' [A.lK, A.lT])
    (hlen : s.tranW.length + 1 < 2147483648) :
    W σ' A { s with tranW := s.tranW ++ [tv] } := by
  have hW0 := hW
  obtain ⟨hR, hD, hT, hRj, hCW, hAR, hCR, hA, hC, hK, hwX, hwA, hwC, hwT0, hfC, hfT, hnd⟩ := hW
  obtain ⟨xsK, mK, hlK, hfK, hnK⟩ := hK
  obtain ⟨xsT, mT, hlT, hfT0, hwsT, hnT⟩ := hT
  have hS := noStr_lists hlK hlT
  have hN : NoRec σ A.ws [A.lK, A.lT] := noRec_lists hlK hlT
  have hnd0 := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨n1, n2, n3, n4, n5, n6, n7⟩, ⟨n8, n9, n10, n11, n12, n13⟩, ⟨n14, n15, n16, n17, n18⟩,
    ⟨n19, n20, n21, n22⟩, ⟨n23, n24, n25⟩, ⟨n26, n27⟩, n28, -⟩ := hnd
  have pl : ∀ {w c fs}, σ.heap w = some (.plain c fs) → w ∉ [A.lK, A.lT] := by
    intro w c fs hw
    exact not_mem_pair (ne_of_plain_list hw hlK) (ne_of_plain_list hw hlT)
  refine ⟨hR.frame hf (by obtain ⟨fs, h, -⟩ := hR; exact pl h),
    hD.frame hf hS (not_mem_pair n7 n1), ?_, hRj.frame hf hS hN (not_mem_pair n18 (Ne.symm n8)),
    hCW.frame hf hS hN (not_mem_pair n22 (Ne.symm n9)), hAR.frame hf hS hN (not_mem_pair n25 (Ne.symm n10)),
    hCR.frame hf hS hN (not_mem_pair n27 (Ne.symm n11)), ?_,
    hC.frame hf hS hN (not_mem_pair n28 (Ne.symm n12)), ?_,
    hwX.frame hf (by obtain ⟨fs, h, -⟩ := hwX; exact pl h),
    hwA.frame hf (by obtain ⟨fs, h, -⟩ := hwA; exact pl h),
    hwC.frame hf (by obtain ⟨fs, h, -⟩ := hwC; exact pl h),
    hwT0.frame hf (by obtain ⟨fs, h, -⟩ := hwT0; exact pl h),
    hfC.frame hf hS (by obtain ⟨fs, sv, h, -⟩ := hfC; exact pl h),
    hfT.frame hf hS (by obtain ⟨fs, sv, h, -⟩ := hfT; exact pl h), hnd0⟩
  · -- TRANSACT
    rw [listOf_of hlT] at hT'
    refine ⟨xsT ++ [.ref y], mT', hT', ?_, ?_, ?_⟩
    · refine forall2_append ?_ ?_
      · obtain ⟨z, fsz, hz, hzo, hzf⟩ := hwT
        cases hz
        refine jrecAt_copy ⟨A.wT, fsz, rfl, hzo, hzf⟩ hzo hyo ?_ (fun v t h => jstrAt_frame h hf hS)
        intro f hfm
        have hk : ("Cbtrn02c$TranRecord", f.jname) ∈ trKeys := by
          rw [← keysOf_tran]; exact List.mem_map_of_mem hfm
        rw [hsame _ hk, fieldsOf_of hzo]
      · refine forall2_imp_mem (fun v hv val hr => jrecAt_frame hr hf hS ?_) hfT0
        rintro x rfl hx
        obtain ⟨z, fs, hz, hzo, _⟩ := hr
        cases hz
        exact pl hzo hx
    · intro v hv w hw'
      rcases List.mem_append.mp hv with hv | hv
      · exact hwsT v hv w hw'
      · simp only [List.mem_singleton] at hv
        subst hv
        exact fresh_not_ws hW0 hy w hw'
    · have := forall2_length hfT0
      simp only [List.length_append, List.length_singleton] at *
      omega
  · exact hA.frame hf hS hN (by
      obtain ⟨et, xs1, h, -⟩ := hA
      intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm
      · rw [hm, hlK] at h; cases h
      · rw [hm, hlT] at h; cases h)
  · -- the ids
    rw [listOf_of hlK] at hK'
    refine ⟨xsK ++ [.ref sId], mK', hK', ?_, ?_⟩
    · simp only [List.map_append, List.map_singleton]
      refine forall2_append (jstrAt_frame hsId hf hS) ?_
      exact forall2_imp (fun _ _ h => jstrAt_frame h hf hS) hfK
    · have := forall2_length hfK
      simp only [List.length_append, List.length_singleton, List.length_map] at *
      omega

end EquivLean.Modernize.Cbtrn02c.Java
