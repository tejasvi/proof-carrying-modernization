import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVtH

/-!
# CBTRN02C → Java: `validateTran`, the account search

The inputs are determined by the heap (`vtd_det`, `vtin_det`); `vt_ret101`: no account of the
cross-reference, reason 101; `vt17_of`: statement 17 after `assignAccount` copied the account found.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem forall2_refl_mem {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, R a a) → Forall2 R l l
  | [], _ => .nil
  | a :: _, h => .cons (h a List.mem_cons_self)
      (forall2_refl_mem (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem firstIdx_congr_mem {α : Type} {p q : α → Bool} {l : List α} (h : ∀ a ∈ l, p a = q a) :
    firstIdx p l = firstIdx q l :=
  firstIdx_congr (forall2_refl_mem h)

theorem acctShapes_setObj_cls {σ : State} {a : Addr} {o : Obj} {xs : List Value} (h : AcctShapes σ xs)
    (ha : ∀ fs, σ.heap a ≠ some (.plain "Cbtrn02c$AccountRecord" fs)) :
    AcctShapes (σ.setObj a o) xs := by
  intro v hv
  obtain ⟨x, fs, l, rfl, hx, hl⟩ := h v hv
  have hne : x ≠ a := by
    rintro rfl
    exact ha fs hx
  exact ⟨x, fs, l, rfl, by rw [State.heap_setObj, if_neg hne]; exact hx, hl⟩

/-- The daily transaction's fields that `validateTran` reads are determined by the heap. -/
theorem vtd_det {σ : State} {d : Addr} {t t' : List EquivLean.Cobol.Rec.FVal} (h : VtD σ d t)
    (h' : VtD σ d t') :
    Model.tCard t = Model.tCard t' ∧ Model.tAmt t = Model.tAmt t' ∧ Model.tOrig t = Model.tOrig t' := by
  obtain ⟨fsd, sc, so, hdo, hdc, hsc, hda, hdt, hso, -, hamt⟩ := h
  obtain ⟨fsd', sc', so', hdo', hdc', hsc', hda', hdt', hso', -, hamt'⟩ := h'
  rw [hdo] at hdo'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hdo'
  subst hdo'
  rw [hdc] at hdc'
  simp only [Option.some.injEq, Value.ref.injEq] at hdc'
  subst hdc'
  rw [hdt] at hdt'
  simp only [Option.some.injEq, Value.ref.injEq] at hdt'
  subst hdt'
  rw [hsc] at hsc'
  rw [hso] at hso'
  rw [hda] at hda'
  simp only [Option.some.injEq, Obj.str.injEq, Value.long.injEq] at hsc' hso' hda'
  exact ⟨cp037Str_inj hsc', ofInt_inj (by omega) (by omega) hda', cp037Str_inj hso'⟩

/-- The cross-reference file and the account table are determined by the heap. -/
theorem vtin_det {σ : State} {xA aD wX wA : Addr}
    {v2 a2 v2' a2' : List (List EquivLean.Cobol.Rec.FVal)}
    (h : VtIn σ xA aD wX wA v2 a2) (h' : VtIn σ xA aD wX wA v2' a2') : v2 = v2' ∧ a2 = a2' := by
  obtain ⟨etX, xsX, etA, xsA, hxA, -, -, hfX, hvX, -, haD, -, -, hfA, hvA, -⟩ := h
  obtain ⟨etX', xsX', etA', xsA', hxA', -, -, hfX', hvX', -, haD', -, -, hfA', hvA', -⟩ := h'
  rw [hxA] at hxA'
  rw [haD] at haD'
  simp only [Option.some.injEq, Obj.array.injEq] at hxA' haD'
  obtain ⟨-, rfl⟩ := hxA'
  obtain ⟨-, rfl⟩ := haD'
  exact ⟨forall2_jrec_det noBin_xref hfX hfX' hvX hvX', forall2_jrec_det noBin_acct hfA hfA' hvA hvA'⟩

theorem vreason_congr {xr ac : List (List EquivLean.Cobol.Rec.FVal)} {t t' : List EquivLean.Cobol.Rec.FVal}
    (h1 : Model.tCard t = Model.tCard t') (h2 : Model.tAmt t = Model.tAmt t')
    (h3 : Model.tOrig t = Model.tOrig t') : vreason xr ac t = vreason xr ac t' := by
  unfold vreason
  rw [h1, h2, h3]

/-- The search of the account table in the state after `assignXref`: that of the table. -/
theorem acct_first_after {σ0 : State} {wX aD : Addr} {fsX fsX' : List (FieldKey × Value)}
    {etA : JType} {xsA : List Value} {accts : List (List EquivLean.Cobol.Rec.FVal)} {id : Int}
    (hX : σ0.heap wX = some (.plain "Cbtrn02c$CardXrefRecord" fsX))
    (haD : σ0.heap aD = some (.array etA xsA))
    (hfA : Forall2 (JRecAt AccountRecord "Cbtrn02c$AccountRecord" σ0) xsA accts)
    (hvA : ∀ a ∈ accts, AccountRecord.Valid a) (hid : id.natAbs < 10 ^ 18) :
    firstIdx (fun v1 => longFieldOf (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')) acctIdKey v1 ==
        some (BitVec.ofInt 64 id)) (arrOf (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')) aD) =
      firstIdx (fun a => Model.aId a == id) accts := by
  have hwX : wX < σ0.next := State.lt_next_of_heap hX
  have haDX : aD ≠ wX := by
    intro h
    rw [h, hX] at haD
    cases haD
  have harr : arrOf (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')) aD = xsA := by
    apply arrOf_of
    rw [State.heap_setObj_of_lt hwX, if_neg haDX]
    exact haD
  rw [harr, ← acct_first hfA hvA id hid]
  apply firstIdx_congr_mem
  intro v1 hv1
  obtain ⟨a, -, hr⟩ := forall2_ex_mem hfA v1 hv1
  obtain ⟨z, fsz, rfl, hz, -⟩ := hr
  have hzX : z ≠ wX := by
    intro h
    rw [h, hX] at hz
    simp at hz
  rw [longFieldOf_setObj hzX]

/-- No account of the cross-reference found: the reject reason is 101. -/
theorem vt_ret101 {d xA aD wX wA : Addr} {σ0 : State} {fsX fsX' : List (FieldKey × Value)} {v : I64}
    {etA : JType} {xsA : List Value} {t : List EquivLean.Cobol.Rec.FVal}
    {vals2 accts : List (List EquivLean.Cobol.Rec.FVal)}
    (hX : σ0.heap wX = some (.plain "Cbtrn02c$CardXrefRecord" fsX))
    (haD : σ0.heap aD = some (.array etA xsA))
    (hkX : AllSome xrKeys fsX' ∧ ∃ t' vals2' accts' x, VtD σ0 d t' ∧
      VtIn σ0 xA aD wX wA vals2' accts' ∧ Model.findXref vals2' (Model.tCard t') = some x ∧
      JRecAt CardXrefRecord xrCls (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')) (.ref wX) x ∧
      v = BitVec.ofInt 64 (Model.xAcct x))
    (hneg : ¬0 ≤ firstIdx (fun v1 => longFieldOf (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX'))
      acctIdKey v1 == some v) (arrOf (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')) aD))
    (hD : VtD σ0 d t) (hIn : VtIn σ0 xA aD wX wA vals2 accts) :
    vreason vals2 accts t = 101 := by
  obtain ⟨-, t', vals2', accts', x, hD', hIn', hfx, hjx, rfl⟩ := hkX
  obtain ⟨e1, -, -⟩ := vtd_det hD' hD
  obtain ⟨rfl, rfl⟩ := vtin_det hIn' hIn
  have hIn0 := hIn'
  obtain ⟨etX', xsX', etA', xsA', -, -, -, -, hvX, -, haD', -, -, hfA, hvA, -⟩ := hIn0
  have e : xsA = xsA' := by
    rw [haD] at haD'
    simp only [Option.some.injEq, Obj.array.injEq] at haD'
    exact haD'.2
  subst e
  have hvx := hvX x (List.mem_of_find?_eq_some hfx)
  obtain ⟨-, b0, n1, n2, b3, hxe, -, hn2, -⟩ := xobj_of_rec hjx hvx
  have hxa : (Model.xAcct x).natAbs < 10 ^ 18 := by
    subst hxe
    exact hn2
  rw [acct_first_after hX haD hfA hvA hxa] at hneg
  have hn := find?_of_firstIdx_neg (Int.not_le.mp hneg)
  have hfx' : Model.findXref vals2' (Model.tCard t) = some x := by rw [← e1]; exact hfx
  simp only [vreason, hfx']
  unfold Model.findAcct
  rw [hn]

/-- **Statement 17**: `assignAccount` copied the account found into `acctWs`. -/
theorem vt17_of {d xA aD wX wA y : Addr} {σ0 : State} {fr : Frame}
    {fsX fsA fsX' fsy fs' : List (FieldKey × Value)} {v : I64} {etA : JType} {xsA : List Value}
    (hX : σ0.heap wX = some (.plain "Cbtrn02c$CardXrefRecord" fsX))
    (hA : σ0.heap wA = some (.plain "Cbtrn02c$AccountRecord" fsA))
    (haD : σ0.heap aD = some (.array etA xsA)) (hwXA : wA ≠ wX)
    (hkX : AllSome xrKeys fsX' ∧ ∃ t vals2 accts x, VtD σ0 d t ∧
      VtIn σ0 xA aD wX wA vals2 accts ∧ Model.findXref vals2 (Model.tCard t) = some x ∧
      JRecAt CardXrefRecord xrCls (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')) (.ref wX) x ∧
      v = BitVec.ofInt 64 (Model.xAcct x))
    (hidx : 0 ≤ firstIdx (fun v1 => longFieldOf (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX'))
      acctIdKey v1 == some v) (arrOf (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')) aD))
    (hyx : xsA[(firstIdx (fun v1 => longFieldOf (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX'))
      acctIdKey v1 == some v) (arrOf (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')) aD)).toNat]? =
        some (.ref y))
    (hyo : σ0.heap y = some (.plain "Cbtrn02c$AccountRecord" fsy))
    (hk : ∀ (a : ClassName) (b : String), (a, b) ∈ acKeys → Fields.get fs' (a, b) =
      Fields.get (fieldsOf (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')) y) (a, b))
    (f2 : fr.get 2 = some (.ref d)) (f5 : fr.get 5 = some (.ref wA)) :
    vt17 [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0 fr
      ((σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')).setObj wA
        (.plain "Cbtrn02c$AccountRecord" fs')) := by
  intro d0 xA0 aD0 wX0 wA0 he
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
  obtain ⟨hallX, t, vals2, accts, x, hD, hIn, hfx, hjx, rfl⟩ := hkX
  have hIn0 := hIn
  obtain ⟨etX', xsX', etA', xsA', -, -, -, -, hvX, -, haD', -, -, hfA, hvA, -⟩ := hIn0
  have e : xsA = xsA' := by
    rw [haD] at haD'
    simp only [Option.some.injEq, Obj.array.injEq] at haD'
    exact haD'.2
  subst e
  have hvx := hvX x (List.mem_of_find?_eq_some hfx)
  obtain ⟨-, b0, n1, n2, b3, hxe, -, hn2, -⟩ := xobj_of_rec hjx hvx
  have hxa : (Model.xAcct x).natAbs < 10 ^ 18 := by
    subst hxe
    exact hn2
  rw [acct_first_after hX haD hfA hvA hxa] at hidx
  have hwX : wX < σ0.next := State.lt_next_of_heap hX
  have hwA : wA < σ0.next := State.lt_next_of_heap hA
  have haDX : aD ≠ wX := by
    intro h
    rw [h, hX] at haD
    cases haD
  have harr : arrOf (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')) aD = xsA := by
    apply arrOf_of
    rw [State.heap_setObj_of_lt hwX, if_neg haDX]
    exact haD
  rw [acct_first_after hX haD hfA hvA hxa] at hyx
  obtain ⟨hi, hfind⟩ := find?_of_firstIdx_nonneg hidx
  have hl := forall2_length hfA
  have hix : (firstIdx (fun a => Model.aId a == Model.xAcct x) accts).toNat < xsA.length := by
    omega
  rw [List.getElem?_eq_getElem hix, Option.some.injEq] at hyx
  have hrec := forall2_get hfA _ hix hi
  rw [hyx] at hrec
  have hva := hvA _ (List.getElem_mem hi)
  obtain ⟨⟨a', fsa, s1, s5, s6, s7, s10, s11, s12, hae, ha', g0, g1, gs1, g2, g3, g4, g5, gs5, g6, gs6,
    g7, gs7, g8, g9, g10, gs10, g11, gs11, g12, gs12⟩, -⟩ := acctobj_of_rec hrec hva
  cases hae
  rw [hyo] at ha'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at ha'
  subst ha'
  have hyX : y ≠ wX := by
    intro h
    rw [h, hX] at hyo
    simp at hyo
  have hfo : fieldsOf (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')) y = fsy := by
    apply fieldsOf_of
    rw [State.heap_setObj_of_lt hwX, if_neg hyX]
    exact hyo
  rw [hfo] at hk
  have hs6X : s6 ≠ wX := by
    intro h
    rw [h, hX] at gs6
    cases gs6
  have hs6A : s6 ≠ wA := by
    intro h
    rw [h, hA] at gs6
    cases gs6
  have hσA : ((σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')).setObj wA
      (.plain "Cbtrn02c$AccountRecord" fs')).heap wA = some (.plain "Cbtrn02c$AccountRecord" fs') := by
    rw [State.heap_setObj_of_lt (by rw [State.next_setObj]; exact hwA), if_pos rfl]
  have hkf : ∀ f ∈ AccountRecord.fields, Fields.get fs' ("Cbtrn02c$AccountRecord", f.jname) =
      Fields.get fsy ("Cbtrn02c$AccountRecord", f.jname) := by
    intro f hf
    rw [hk _ _ (by rw [← keysOf_acct2]; exact List.mem_map_of_mem hf)]
  have hAw : ∀ t', (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')).heap wA ≠ some (.str t') := by
    intro t' h'
    rw [State.heap_setObj_of_lt hwX, if_neg hwXA, hA] at h'
    cases h'
  have hstr : ∀ v t, JStrAt σ0 v t → JStrAt ((σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')).setObj
      wA (.plain "Cbtrn02c$AccountRecord" fs')) v t := by
    intro v t h
    exact jstrAt_setObj (jstrAt_setObj h (fun t' h' => by rw [hX] at h'; cases h')) hAw
  refine ⟨fsX', fs', _, _, _, s6, _, f2, f5, rfl, ?_, ?_, ?_, ?_, gs6, hs6X, hs6A,
    Hide.intro ⟨hallX, ?_, t, vals2, accts, x, _, hD, hIn, hfx, hfind, ?_, ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [hk _ _ (by decide)]
    exact g8
  · rw [hk _ _ (by decide)]
    exact g9
  · rw [hk _ _ (by decide)]
    exact g3
  · rw [hk _ _ (by decide)]
    exact g6
  · intro k hk'
    obtain ⟨a, b⟩ := k
    rw [hk a b hk']
    exact (allSome_of_jrecT hrec hyo) (a, b) (by rw [keysOf_acct2]; exact hk')
  · exact jrecAt_setObj hjx (Ne.symm hwXA) hAw
  · exact jrecAt_copy hrec hyo hσA hkf hstr

end EquivLean.Modernize.Cbtrn02c.Java
