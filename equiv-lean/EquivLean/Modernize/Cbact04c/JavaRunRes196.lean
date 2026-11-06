import EquivLean.Modernize.Cbact04c.JavaRunRes172

/-!
# CBACT04C → Java, `run`: the interest rate (statements 196–198)

`st_succ_eq`: the model state after record `i` is the interest part `stFin` at the rate of the
copied disclosure group record, after the account part `stSel`. `j85_of`: the loop head for the
next record (cut point 85).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

theorem trec_eq {g : G} {n : Nat} (hn : n < g.tcat.length) : g.trec n = g.tcat[n] := by
  simp [G.trec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

/-- **One record of the model**, in the phases of the loop body. -/
theorem st_succ_eq (g : G) {n : Nat} (hn : n < g.tcat.length) :
    g.st (n + 1) = stFin g.parm g.clk (Model.dRate (discOf g (stSel g.xrefs (g.st n) (g.trec n))
      (g.trec n))) (stSel g.xrefs (g.st n) (g.trec n)) (g.trec n) := by
  rw [G.st_succ g hn, ← trec_eq hn]
  simp only [G.step]
  rw [step_eq]
  rfl

/-- **The loop head for the next record** (cut point 85). -/
theorem j85_of {g : G} {σ0 σ : State} {fr' : Frame} {i : I32} {hp : Hp}
    {acctV xrefV lastV : Value} (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt)
    (hlen : g.tcat.length < 2147483647) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32)))
    (f12 : fr'.get 12 = some (.long (BitVec.ofInt 64 (g.st (i.toInt.toNat + 1)).total)))
    (f3 : fr'.get 3 = some (.int 0#32)) (hsome : (g.st (i.toInt.toNat + 1)).lastId.isSome)
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (g.st (i.toInt.toNat + 1)).k)))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some acctV)
    (f17 : fr'.get 17 = some xrefV) (f4 : fr'.get 4 = some (.int 0#32))
    (f5 : fr'.get 5 = some (.int 0#32))
    (hheap : Hide (LoopHeap g σ0 σ hp (g.st (i.toInt.toNat + 1)) acctV xrefV lastV)) :
    J85 g g.args σ0 fr' σ := by
  have hi1 := i32_toInt_add_one i hi0 (by omega)
  have hn1 : (i + 1#32).toInt.toNat = i.toInt.toNat + 1 := by omega
  refine ⟨i + 1#32, hp, acctV, xrefV, lastV, by omega, by omega, hlocs, f22, ?_, ?_, ?_, f25, f16,
    f17, f4, f5, ?_⟩
  · rw [hn1]; exact f12
  · rw [hn1, hsome]; exact f3
  · rw [hn1]; exact f14
  · rw [hn1]; exact hheap

/-- The interest rate field of a valid disclosure group record object. -/
theorem disRate_field {σ : State} {v : Value} {d : List FV}
    (h : JRecAt DisGroupRecord "Cbact04c$DisGroupRecord" σ v d) (hv : DisGroupRecord.Valid d) :
    ∃ x fs, v = .ref x ∧ σ.heap x = some (.plain "Cbact04c$DisGroupRecord" fs) ∧
      Fields.get fs ("Cbact04c$DisGroupRecord", "disIntRate") =
        some (.long (BitVec.ofInt 64 (Model.dRate d))) ∧
      -1000000 < Model.dRate d ∧ Model.dRate d < 1000000 := by
  obtain ⟨x, fs, rfl, hx, hf⟩ := jrec_obj h
  have hk := jfield_num hf hv (i := 3) (by decide) (fmt := {digits := 6, scale := 2, signed := true})
    (by decide)
  rw [show (DisGroupRecord.fields.getD 3 default).jname = "disIntRate" from rfl] at hk
  have r := holds_display rfl (valid_num hv (i := 3) (by decide)
    (fmt := {digits := 6, scale := 2, signed := true}) (by decide)).2
  simp only [Nat.reducePow] at r
  have a0 := Int.natAbs_eq (Model.numOf (d.getD 3 default))
  exact ⟨x, fs, rfl, hx, hk, by simp only [Model.dRate]; omega, by simp only [Model.dRate]; omega⟩

/-- The disclosure group record of the account part is a record of the input. -/
theorem discOf_valid {g : G} (hv : ∀ d ∈ g.discs, DisGroupRecord.Valid d) (s : Model.St)
    (t : List FV) (hex : ∃ jd, g.discs.findIdx? (fun d => Model.dGrp d == Model.aGrp s.acct &&
      Model.dType d == Model.tType t && Model.dCat d == Model.tCat t) = some jd) :
    DisGroupRecord.Valid (discOf g s t) := by
  obtain ⟨jd, hjd⟩ := hex
  obtain ⟨hjl, hd⟩ := discOf_eq hjd
  rw [hd]
  exact hv _ (List.getElem_mem hjl)

end EquivLean.Modernize.Cbact04c.Java
