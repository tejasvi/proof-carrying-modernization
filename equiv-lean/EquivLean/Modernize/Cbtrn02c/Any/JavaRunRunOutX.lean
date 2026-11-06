import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunX83

/-!
# CBTRN02C → Java: `run`'s outputs at the exit

`post_exit`: after the three exit lines (the counts and the end line) and the return code, the
`Result` holds the outputs of `Model.runX` (those of `Model.run` when no transaction stopped the
run).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem toInt_ofNat64 {m : Nat} (h : m < 9223372036854775808) : (BitVec.ofNat 64 m).toInt = m := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  split <;> omega

theorem toInt_ofNat32 {m : Nat} (h : m < 2147483648) : (BitVec.ofNat 32 m).toInt = m := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  split <;> omega

theorem jline_proc : jline (Model.txt "TRANSACTIONS PROCESSED :") =
    JStr.ofString "TRANSACTIONS PROCESSED :" := by decide
theorem jline_rej : jline (Model.txt "TRANSACTIONS REJECTED  :") =
    JStr.ofString "TRANSACTIONS REJECTED  :" := by decide
theorem jline_end : jline (Model.txt "END OF EXECUTION OF PROGRAM CBTRN02C") =
    JStr.ofString "END OF EXECUTION OF PROGRAM CBTRN02C" := by decide

/-- `Model.run`'s outputs from the state after the last transaction. -/
theorem G.out_eq (g : G) : g.out =
    { disp := (g.st g.trans.length).disp ++
        [Model.txt "TRANSACTIONS PROCESSED :" ++ zpad 9 g.trans.length,
         Model.txt "TRANSACTIONS REJECTED  :" ++ zpad 9 (g.st g.trans.length).rejects,
         Model.txt "END OF EXECUTION OF PROGRAM CBTRN02C"],
      tranW := (g.st g.trans.length).tranW, rejW := (g.st g.trans.length).rejW,
      catW := (g.st g.trans.length).catW, acctRW := (g.st g.trans.length).acctRW,
      catRW := (g.st g.trans.length).catRW,
      rc := if 0 < (g.st g.trans.length).rejects then 4 else 0 } := by
  rw [G.st_length]
  rfl

/-- The counts at the exit: fewer rejected than processed transactions, fewer than `2^27`. -/
theorem exit_facts {g : G} {σ0 : State} (hpre : RunPreGX g g.args σ0) :
    (g.st g.trans.length).rejects ≤ g.trans.length ∧ g.trans.length < 134217728 := by
  obtain ⟨-, hin, -⟩ := hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hb⟩ := hin
  obtain ⟨-, -, -, -, -, -, hrj, -⟩ := G.lb g (Nat.le_refl _)
  exact ⟨hrj, by omega⟩

/-- **The outputs at the exit.** -/
theorem post_exit {g : G} {σ σ' : State} {A : Addrs} {xsL : List Value} {mL : Nat}
    {y1 y2 y3 : Addr} {mD' : Nat} {fs' : List (FieldKey × Value)}
    (hW : W σ A (g.st g.trans.length))
    (hstx : g.stx g.trans.length = ⟨g.st g.trans.length, false⟩)
    (hlD : σ.heap A.lD = some (.list .arrayList xsL mL))
    (hD' : σ'.heap A.lD = some (.list .arrayList (xsL ++ [.ref y1, .ref y2, .ref y3]) mD'))
    (h1 : σ'.heap y1 =
      some (.str (JStr.ofString "TRANSACTIONS PROCESSED :" ++ zpadJ g.trans.length 9)))
    (h2 : σ'.heap y2 =
      some (.str (JStr.ofString "TRANSACTIONS REJECTED  :" ++ zpadJ (g.st g.trans.length).rejects 9)))
    (h3 : σ'.heap y3 = some (.str (JStr.ofString "END OF EXECUTION OF PROGRAM CBTRN02C")))
    (hr : σ'.heap A.r = some (.plain "Cbtrn02c$Result" fs'))
    (hfs : ∀ f, f ≠ "returnCode" →
      Fields.get fs' ("Cbtrn02c$Result", f) = Fields.get (fieldsOf σ A.r) ("Cbtrn02c$Result", f))
    (hrc : Fields.get fs' ("Cbtrn02c$Result", "returnCode") =
      some (.int (BitVec.ofInt 32 (if 0 < (g.st g.trans.length).rejects then 4 else 0))))
    (hf : FrameS σ σ' [A.lD, A.r]) :
    RunPostGX g (some (.ref A.r)) σ' := by
  have ho := G.outX_exit g hstx
  obtain ⟨hR, hD, hT, hRj, hCW, hAR, hCR, -, -, -, -, -, -, -, -, -, hnd⟩ := hW
  obtain ⟨fsR, hr0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := hR
  obtain ⟨xsD, mD, hlD0, hfD, -⟩ := hD
  rw [hlD] at hlD0
  simp only [Option.some.injEq, Obj.list.injEq, true_and] at hlD0
  obtain ⟨rfl, -⟩ := hlD0
  have hS : NoStr σ [A.lD, A.r] := by
    intro a ha t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · rw [hlD] at ht; cases ht
    · rw [hr0] at ht; cases ht
  have hN : ∀ cls, cls ≠ "Cbtrn02c$Result" → NoRecC σ A.ws cls [A.lD, A.r] := by
    intro cls hc a ha
    right
    intro fs h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · rw [hlD] at h; cases h
    · rw [hr0] at h
      simp only [Option.some.injEq, Obj.plain.injEq] at h
      exact hc h.1.symm
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨n1, n2, n3, n4, n5, -, -⟩, -⟩ := hnd
  have pr : ∀ {l xs m}, σ.heap l = some (.list .arrayList xs m) → l ≠ A.r := by
    intro l xs m hl h
    rw [h, hr0] at hl
    cases hl
  have nm : ∀ {l xs m}, σ.heap l = some (.list .arrayList xs m) → l ≠ A.lD → l ∉ [A.lD, A.r] :=
    fun hl hD => not_mem_pair hD (pr hl)
  rw [fieldsOf_of hr0] at hfs
  have hout := G.out_eq g
  refine ⟨A.r, fs', A.lD, .arrayList, xsL ++ [.ref y1, .ref y2, .ref y3], mD', rfl, hr, ?_, hD', ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try rw [ho]) <;> (try dsimp only) <;> (try rw [hout]) <;>
    (try dsimp only)
  · rw [hfs _ (by decide)]; exact g1
  · simp only [List.map_append, List.map_cons, List.map_nil, jline_append, jline_proc, jline_rej,
      jline_end, jline_zpad]
    exact forall2_app (.cons ⟨y1, rfl, h1⟩ (.cons ⟨y2, rfl, h2⟩ (.cons ⟨y3, rfl, h3⟩ .nil)))
      (forall2_imp (fun _ _ h => jstrAt_frame h hf hS) hfD)
  · obtain ⟨xs, m, hl, -⟩ := id hT
    exact listOf_of_lrec (by rw [hfs _ (by decide)]; exact g2)
      (LRec.frameC hT hf hS (hN _ (by decide)) (nm hl (Ne.symm n1)))
  · obtain ⟨xs, m, hl, -⟩ := id hRj
    exact listOf_of_lrec (by rw [hfs _ (by decide)]; exact g3)
      (LRec.frameC hRj hf hS (hN _ (by decide)) (nm hl (Ne.symm n2)))
  · obtain ⟨xs, m, hl, -⟩ := id hCW
    exact listOf_of_lrec (by rw [hfs _ (by decide)]; exact g4)
      (LRec.frameC hCW hf hS (hN _ (by decide)) (nm hl (Ne.symm n3)))
  · obtain ⟨xs, m, hl, -⟩ := id hAR
    exact listOf_of_lrec (by rw [hfs _ (by decide)]; exact g5)
      (LRec.frameC hAR hf hS (hN _ (by decide)) (nm hl (Ne.symm n4)))
  · obtain ⟨xs, m, hl, -⟩ := id hCR
    exact listOf_of_lrec (by rw [hfs _ (by decide)]; exact g6)
      (LRec.frameC hCR hf hS (hN _ (by decide)) (nm hl (Ne.symm n5)))
  · exact hrc
  · rw [hfs _ (by decide)]; exact g8

end EquivLean.Modernize.Cbtrn02c.Java
