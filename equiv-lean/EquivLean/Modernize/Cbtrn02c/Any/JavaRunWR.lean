import EquivLean.Modernize.Cbtrn02c.Any.JavaRunW

/-!
# CBTRN02C → Java: the world after a reject

`W_reject`: after `writeReject` added a reject record (the record's bytes and the trailer as CP037
strings) to the DALYREJS list, the state holds the model state with the reject.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem ne_of_plain_list {σ : State} {a b : Addr} {c : ClassName} {fs : List (FieldKey × Value)}
    {lk : ListKind} {xs : List Value} {m : Nat} (ha : σ.heap a = some (.plain c fs))
    (hb : σ.heap b = some (.list lk xs m)) : a ≠ b := by
  rintro rfl; rw [ha] at hb; cases hb

theorem noStr_list {σ : State} {l : Addr} {lk : ListKind} {xs : List Value} {m : Nat}
    (h : σ.heap l = some (.list lk xs m)) : NoStr σ [l] := by
  intro a ha t ht
  simp only [List.mem_singleton] at ha
  subst ha; rw [h] at ht; cases ht

theorem noRec_list {σ : State} {ws : List Addr} {l : Addr} {lk : ListKind} {xs : List Value} {m : Nat}
    (h : σ.heap l = some (.list lk xs m)) : NoRec σ ws [l] := by
  intro a ha
  simp only [List.mem_singleton] at ha
  subst ha
  exact Or.inr (fun c fs hc => by rw [h] at hc; cases hc)

theorem not_mem_single {a b : Addr} (h : a ≠ b) : a ∉ [b] := by
  simp [h]

/-- The world after `writeReject`. -/
theorem W_reject {σ σ' : State} {A : Addrs} {s : Model.St} {t : List EquivLean.Cobol.Rec.FVal}
    {code : Int} {desc : List UInt8} (hW : W σ A s) {xs : List Value} {m : Nat}
    (hl : σ.heap A.lR = some (.list .arrayList xs m)) {y : Addr} {fsy : List (FieldKey × Value)}
    {t1 t2 : Addr} {m' : Nat} (hl' : σ'.heap A.lR = some (.list .arrayList (xs ++ [.ref y]) m'))
    (hy : σ.next ≤ y) (hyo : σ'.heap y = some (.plain "Cbtrn02c$RejectRecord" fsy))
    (h1 : Fields.get fsy ("Cbtrn02c$RejectRecord", "rejectTranData") = some (.ref t1))
    (ht1 : σ'.heap t1 = some (.str (cp037Str (Model.DalytranRecord.encode t))))
    (h2 : Fields.get fsy ("Cbtrn02c$RejectRecord", "validationTrailer") = some (.ref t2))
    (ht2 : σ'.heap t2 = some (.str (cp037Str (CardDemo.Cbtrn02c.trailer code desc))))
    (hf : FrameS σ σ' [A.lR]) (hlen : s.rejW.length + 1 < 2147483648) :
    W σ' A (s.reject t code desc) := by
  obtain ⟨hR, hD, hT, hRj, hCW, hAR, hCR, hA, hC, hK, hwX, hwA, hwC, hwT, hfC, hfT, hnd⟩ := hW
  have hS := noStr_list hl
  have hN : NoRec σ A.ws [A.lR] := noRec_list hl
  have hnd0 := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨n1, n2, n3, n4, n5, n6, n7⟩, ⟨n8, n9, n10, n11, n12, n13⟩, ⟨n14, n15, n16, n17, n18⟩,
    ⟨n19, n20, n21, n22⟩, ⟨n23, n24, n25⟩, ⟨n26, n27⟩, n28, -⟩ := hnd
  have hr : A.r ∉ [A.lR] := by
    obtain ⟨fs, h, -⟩ := hR
    exact not_mem_single (ne_of_plain_list h hl)
  have hw : ∀ {w c keys}, WSObj σ w c keys → w ∉ [A.lR] := by
    intro w c keys hws
    obtain ⟨fs, h, -⟩ := hws
    exact not_mem_single (ne_of_plain_list h hl)
  refine ⟨hR.frame hf hr, hD.frame hf hS (not_mem_single n2),
    hT.frame hf hS hN (not_mem_single n8), ?_, hCW.frame hf hS hN (not_mem_single (Ne.symm n14)),
    hAR.frame hf hS hN (not_mem_single (Ne.symm n15)),
    hCR.frame hf hS hN (not_mem_single (Ne.symm n16)), ?_,
    hC.frame hf hS hN (not_mem_single (Ne.symm n17)), hK.frame hf hS (not_mem_single (Ne.symm n18)),
    hwX.frame hf (hw hwX), hwA.frame hf (hw hwA), hwC.frame hf (hw hwC), hwT.frame hf (hw hwT),
    hfC.frame hf hS (hw hwC), hfT.frame hf hS (hw hwT), ?_⟩
  · -- the reject list
    obtain ⟨xs0, m0, hl0, hfs, hws, hn⟩ := hRj
    rw [hl] at hl0; cases hl0
    refine ⟨xs ++ [.ref y], m', hl', ?_, ?_, ?_⟩
    · refine forall2_append ?_ ?_
      · refine ⟨y, fsy, rfl, hyo, ?_⟩
        exact .cons ⟨_, h1, t1, rfl, ht1⟩ (.cons ⟨_, h2, t2, rfl, ht2⟩ .nil)
      · refine forall2_imp_mem (fun v hv val hrv => jrecAt_frame hrv hf hS ?_) hfs
        rintro x rfl hx
        simp only [List.mem_singleton] at hx
        subst hx
        obtain ⟨z, fs, hz, hzo, _⟩ := hrv
        cases hz
        rw [hl] at hzo; cases hzo
    · intro v hv w hw'
      rcases List.mem_append.mp hv with hv | hv
      · exact hws v hv w hw'
      · simp only [List.mem_singleton] at hv
        subst hv
        have hlt : w < σ.next := by
          simp only [Addrs.ws, List.mem_cons, List.not_mem_nil, or_false] at hw'
          rcases hw' with rfl | rfl | rfl | rfl
          · obtain ⟨fs, h, -⟩ := hwX; exact State.lt_next_of_heap h
          · obtain ⟨fs, h, -⟩ := hwA; exact State.lt_next_of_heap h
          · obtain ⟨fs, h, -⟩ := hwC; exact State.lt_next_of_heap h
          · obtain ⟨fs, h, -⟩ := hwT; exact State.lt_next_of_heap h
        intro heq
        injection heq with heq
        subst heq
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hy)
    · have := forall2_length hfs
      simp only [List.length_append, List.length_singleton] at *
      omega
  · exact hA.frame hf hS hN (by
      obtain ⟨et, xs1, h, -⟩ := hA
      intro hm
      simp only [List.mem_singleton] at hm
      rw [hm, hl] at h; cases h)
  · exact hnd0

theorem ne_of_plain_cls {σ : State} {a b : Addr} {c1 c2 : ClassName} {fs1 fs2 : List (FieldKey × Value)}
    (ha : σ.heap a = some (.plain c1 fs1)) (hb : σ.heap b = some (.plain c2 fs2)) (hc : c1 ≠ c2) :
    a ≠ b := by
  rintro rfl; rw [ha] at hb; cases hb; exact hc rfl

theorem noStr_plain {σ : State} {S : List Addr} (h : ∀ a ∈ S, ∃ c fs, σ.heap a = some (.plain c fs)) :
    NoStr σ S := by
  intro a ha t ht
  obtain ⟨c, fs, hc⟩ := h a ha
  rw [hc] at ht; cases ht

/-- The world after `validateTran`: only `xrefWs` and `acctWs` changed, and they still have
their fields. -/
theorem W_vt {σ σ' : State} {A : Addrs} {s : Model.St} (hW : W σ A s)
    (hf : FrameS σ σ' [A.wX, A.wA])
    (hX : WSObj σ' A.wX "Cbtrn02c$CardXrefRecord" (keysOf CardXrefRecord "Cbtrn02c$CardXrefRecord"))
    (hA' : WSObj σ' A.wA "Cbtrn02c$AccountRecord" (keysOf AccountRecord "Cbtrn02c$AccountRecord")) :
    W σ' A s := by
  obtain ⟨hR, hD, hT, hRj, hCW, hAR, hCR, hA, hC, hK, hwX, hwA, hwC, hwT, hfC, hfT, hnd⟩ := hW
  obtain ⟨fsX, hxo, -⟩ := hwX
  obtain ⟨fsA, hao, -⟩ := hwA
  have hS : NoStr σ [A.wX, A.wA] := noStr_plain (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨_, _, hxo⟩
    · exact ⟨_, _, hao⟩)
  have hN : NoRec σ A.ws [A.wX, A.wA] := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    left
    rcases ha with rfl | rfl <;> simp [Addrs.ws]
  have nl : ∀ {l : Addr} {xs m}, σ.heap l = some (.list .arrayList xs m) → l ∉ [A.wX, A.wA] := by
    intro l xs m hl hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · rw [hxo] at hl; cases hl
    · rw [hao] at hl; cases hl
  have lr : ∀ {l s cls ws vals}, LRec σ l s cls ws vals → l ∉ [A.wX, A.wA] := by
    intro l s cls ws vals h
    obtain ⟨xs, m, hl, -⟩ := h
    exact nl hl
  have ls : ∀ {l strs}, LStr σ l strs → l ∉ [A.wX, A.wA] := by
    intro l strs h
    obtain ⟨xs, m, hl, -⟩ := h
    exact nl hl
  have pl : ∀ {w c fs}, σ.heap w = some (.plain c fs) → c ≠ "Cbtrn02c$CardXrefRecord" →
      c ≠ "Cbtrn02c$AccountRecord" → w ∉ [A.wX, A.wA] := by
    intro w c fs hw h1 h2 hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ne_of_plain_cls hw hxo h1 rfl
    · exact ne_of_plain_cls hw hao h2 rfl
  refine ⟨hR.frame hf (by obtain ⟨fs, h, -⟩ := hR; exact pl h (by decide) (by decide)),
    hD.frame hf hS (ls hD), hT.frame hf hS hN (lr hT), hRj.frame hf hS hN (lr hRj),
    hCW.frame hf hS hN (lr hCW), hAR.frame hf hS hN (lr hAR), hCR.frame hf hS hN (lr hCR),
    hA.frame hf hS hN ?_, hC.frame hf hS hN (lr hC), hK.frame hf hS (ls hK), hX, hA',
    hwC.frame hf (by obtain ⟨fs, h, -⟩ := hwC; exact pl h (by decide) (by decide)),
    hwT.frame hf (by obtain ⟨fs, h, -⟩ := hwT; exact pl h (by decide) (by decide)),
    hfC.frame hf hS (by obtain ⟨fs, sv, h, -⟩ := hfC; exact pl h (by decide) (by decide)),
    hfT.frame hf hS (by obtain ⟨fs, sv, h, -⟩ := hfT; exact pl h (by decide) (by decide)), hnd⟩
  obtain ⟨et, xs, hl, -⟩ := hA
  intro hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h
  · rw [h, hxo] at hl; cases hl
  · rw [h, hao] at hl; cases hl

end EquivLean.Modernize.Cbtrn02c.Java
