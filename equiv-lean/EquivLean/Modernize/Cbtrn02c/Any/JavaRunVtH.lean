import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVt0

/-!
# CBTRN02C → Java: `validateTran`, facts at the returns and cut points

`vt_ret100`: no cross-reference of the card, reason 100; `vt11_of`: statement 11 after
`assignXref` copied the cross-reference found.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- No cross-reference of the transaction's card: the reject reason is 100. -/
theorem vt_ret100 {σ : State} {sc xA : Addr} {et : JType} {xs : List Value}
    {vals2 accts : List (List EquivLean.Cobol.Rec.FVal)} {t t' : List EquivLean.Cobol.Rec.FVal}
    (hneg : ¬0 ≤ firstIdx (fun v => strFieldOf σ xrefCardKey v == some (argText σ (.ref sc)))
      (arrOf σ xA))
    (hsc : σ.heap sc = some (.str (cp037Str (Model.tCard t))))
    (hfX : Forall2 (JRecAt CardXrefRecord "Cbtrn02c$CardXrefRecord" σ) xs vals2)
    (hxA : σ.heap xA = some (.array et xs))
    (hvX : ∀ x ∈ vals2, CardXrefRecord.Valid x) (hc : Model.tCard t' = Model.tCard t) :
    vreason vals2 accts t' = 100 := by
  rw [arrOf_of hxA, argText_of hsc, xref_first hfX hvX] at hneg
  have hn := find?_of_firstIdx_neg (p := fun x => Model.xCard x == Model.tCard t) (l := vals2)
    (by omega)
  have hf : Model.findXref vals2 (Model.tCard t') = none := by
    unfold Model.findXref
    rw [hc]
    exact hn
  unfold vreason
  rw [hf]

/-- **Statement 11**: `assignXref` copied the cross-reference found into `xrefWs`. -/
theorem vt11_of {d xA aD wX wA sc y : Addr} {σ0 : State} {fr : Frame}
    {t : List EquivLean.Cobol.Rec.FVal} {vals2 accts : List (List EquivLean.Cobol.Rec.FVal)}
    {fsX fsy fs' : List (FieldKey × Value)} {etX : JType} {xsX : List Value}
    (hD : VtD σ0 d t) (hIn : VtIn σ0 xA aD wX wA vals2 accts)
    (hsc : σ0.heap sc = some (.str (cp037Str (Model.tCard t))))
    (hxA : σ0.heap xA = some (.array etX xsX))
    (hX : σ0.heap wX = some (.plain "Cbtrn02c$CardXrefRecord" fsX))
    (hidx : 0 ≤ firstIdx (fun v => strFieldOf σ0 xrefCardKey v == some (argText σ0 (.ref sc)))
      (arrOf σ0 xA))
    (hyx : xsX[(firstIdx (fun v => strFieldOf σ0 xrefCardKey v == some (argText σ0 (.ref sc)))
      (arrOf σ0 xA)).toNat]? = some (.ref y))
    (hyo : σ0.heap y = some (.plain "Cbtrn02c$CardXrefRecord" fsy))
    (hk : ∀ (a : ClassName) (b : String), (a, b) ∈ xrKeys →
      Fields.get fs' (a, b) = Fields.get (fieldsOf σ0 y) (a, b))
    (f2 : fr.get 2 = some (.ref d)) (f1 : fr.get 1 = some (.ref xA)) (f0 : fr.get 0 = some (.ref aD))
    (f9 : fr.get 9 = some (.ref wX)) (f5 : fr.get 5 = some (.ref wA)) :
    vt11 [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0 fr
      (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fs')) := by
  intro d0 xA0 aD0 wX0 wA0 he
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
  have hIn0 := hIn
  obtain ⟨etX', xsX', etA, xsA, hxA', -, -, hfX, hvX, -⟩ := hIn0
  have e : xsX = xsX' := by
    rw [hxA] at hxA'
    simp only [Option.some.injEq, Obj.array.injEq] at hxA'
    exact hxA'.2
  subst e
  rw [arrOf_of hxA, argText_of hsc, xref_first hfX hvX] at hidx hyx
  obtain ⟨hi, hfind⟩ := find?_of_firstIdx_nonneg hidx
  have hl := forall2_length hfX
  have hix : (firstIdx (fun x => Model.xCard x == Model.tCard t) vals2).toNat < xsX.length := by
    omega
  rw [List.getElem?_eq_getElem hix, Option.some.injEq] at hyx
  have hrec := forall2_get hfX _ hix hi
  rw [hyx] at hrec
  have hvx := hvX _ (List.getElem_mem hi)
  obtain ⟨⟨a', fsa, s0, s3, hae, ha', g0, gs0, g1, g2, g3, gs3⟩, -⟩ := xobj_of_rec hrec hvx
  cases hae
  rw [hyo] at ha'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at ha'
  subst ha'
  have hwX : wX < σ0.next := State.lt_next_of_heap hX
  have hσX : (σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fs')).heap wX =
      some (.plain "Cbtrn02c$CardXrefRecord" fs') := by
    rw [State.heap_setObj_of_lt hwX, if_pos rfl]
  have hkf : ∀ f ∈ CardXrefRecord.fields, Fields.get fs' ("Cbtrn02c$CardXrefRecord", f.jname) =
      Fields.get fsy ("Cbtrn02c$CardXrefRecord", f.jname) := by
    intro f hf
    rw [hk _ _ (by rw [← keysOf_xref2]; exact List.mem_map_of_mem hf), fieldsOf_of hyo]
  refine ⟨fs', _, f2, f1, f0, f9, f5, rfl, ?_,
    Hide.intro ⟨?_, t, vals2, accts, _, hD, hIn, hfind, ?_, rfl⟩⟩
  · rw [hk _ _ (by decide), fieldsOf_of hyo]
    exact g2
  · intro k hk'
    obtain ⟨a, b⟩ := k
    rw [hk a b hk', fieldsOf_of hyo]
    exact (allSome_of_jrecT hrec hyo) (a, b) (by rw [keysOf_xref2]; exact hk')
  · exact jrecAt_copy hrec hyo hσX hkf
      (fun v s h => jstrAt_setObj h (fun t' h' => by rw [hX] at h'; cases h'))

end EquivLean.Modernize.Cbtrn02c.Java
