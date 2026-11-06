import EquivLean.Modernize.Cbstm03a.JavaSpec
import EquivLean.Modernize.Cbstm03a.Java.RunTotal
import EquivLean.Modernize.Cbstm03a.Java.Clinit.Clinit
import EquivLean.Modernize.Cbstm03a.Java.JRunHL
import EquivLean.Modernize.Cbstm03a.Java.TopBridge
import EquivLean.Modernize.Cbstm03a.JavaProof
import EquivLean.Bridge.Jimple.Init

/-!
# CBSTM03A → Java: `runSpec` (the generated statement's contract) from `runSpecJ`

`runSpec_of_J`: `run` satisfies `JavaSpec.runSpec` when it satisfies `runSpecJ` (the contract against `jRunR`,
`Java/RunVC.lean`), given
* the record bridges: an input file of field values (`TrnxFileAt` …, valid records) holds the records
  `vals.map fT` … in the form `runSpecJ` reads them (`RecsAt TrnxAtN` …);
* the model: on the statement's domain, `jRunR` of those records has `Model.run`'s outputs (`jline` of each line,
  `abended`);
* `ClinitRan` gives the `CP037` table (`CP037At`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

/-- The `Result` of `ResAt` in the form of `runSpec`'s postcondition. -/
theorem runPost_of_resAt {σ' : State} {res : Addr} {disp st ht : List JStr} {ab : Bool} {o : Model.Out}
    (h : ResAt σ' res disp st ht ab) (hd : disp = o.disp.map jline) (hs : st = o.stmtWrites.map jline)
    (hh : ht = o.htmlWrites.map jline) (ha : ab = o.abended) :
    ∃ fs l k xs mods lw1 kw1 ws1 mw1 lw2 kw2 ws2 mw2,
      σ'.heap res = some (.plain "Cbstm03a$Result" fs) ∧
      Fields.get fs ("Cbstm03a$Result", "displays") = some (.ref l) ∧
      σ'.heap l = some (.list k xs mods) ∧
      Forall2 (JStrAt σ') xs (o.disp.map jline) ∧
      Fields.get fs ("Cbstm03a$Result", "stmtFileWrites") = some (.ref lw1) ∧
      σ'.heap lw1 = some (.list kw1 ws1 mw1) ∧
      Forall2 (JStrAt σ') ws1 (o.stmtWrites.map jline) ∧
      Fields.get fs ("Cbstm03a$Result", "htmlFileWrites") = some (.ref lw2) ∧
      σ'.heap lw2 = some (.list kw2 ws2 mw2) ∧
      Forall2 (JStrAt σ') ws2 (o.htmlWrites.map jline) ∧
      Fields.get fs ("Cbstm03a$Result", "abended") = some (.int (if o.abended then 1 else 0)) := by
  obtain ⟨ld, ls, lh, fs, h1, h2, h3, h4, h5, -, -, -, ⟨xs, m, hx1, hx2⟩, ⟨ws1, m1, hw1, hw2⟩,
    ⟨ws2, m2, hv1, hv2⟩⟩ := h
  subst hd hs hh ha
  exact ⟨fs, ld, .arrayList, xs, m, ls, .arrayList, ws1, m1, lh, .arrayList, ws2, m2, h1, h2, hx1, hx2, h3, hw1,
    hw2, h4, hv1, hv2, h5⟩

/-- **`runSpec` from `runSpecJ`**, the record bridges, the model equation and the `CP037` table. -/
theorem runSpec_of_J
    (fT : List EquivLean.Cobol.Rec.FVal → TrnxR) (fX : List EquivLean.Cobol.Rec.FVal → XrefR)
    (fC : List EquivLean.Cobol.Rec.FVal → CustR) (fA : List EquivLean.Cobol.Rec.FVal → AcctR)
    (hT : ∀ σ a vals, TrnxFileAt σ a vals → (∀ v ∈ vals, TrnxRecord.Valid v) → RecsAt TrnxAtN σ a (vals.map fT))
    (hX : ∀ σ a vals, XrefFileAt σ a vals → (∀ v ∈ vals, CardXrefRecord.Valid v) →
      RecsAt XrefAtN σ a (vals.map fX))
    (hC : ∀ σ a vals, CustFileAt σ a vals → (∀ v ∈ vals, CustomerRecord.Valid v) →
      RecsAt CustAtN σ a (vals.map fC))
    (hA : ∀ σ a vals, AcctFileAt σ a vals → (∀ v ∈ vals, AccountRecord.Valid v) →
      RecsAt AcctAtN σ a (vals.map fA))
    (hM : ∀ vals1 vals2 vals3 vals4, (∀ v ∈ vals1, TrnxRecord.Valid v) → (∀ v ∈ vals2, CardXrefRecord.Valid v) →
      (∀ v ∈ vals3, CustomerRecord.Valid v) → (∀ v ∈ vals4, AccountRecord.Valid v) →
      EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4 →
      (jRunR (vals1.map fT) (vals2.map fX) (vals3.map fC) (vals4.map fA)).disp =
          (Model.run vals1 vals2 vals3 vals4).disp.map jline ∧
        (jRunR (vals1.map fT) (vals2.map fX) (vals3.map fC) (vals4.map fA)).stmt =
          (Model.run vals1 vals2 vals3 vals4).stmtWrites.map jline ∧
        (jRunR (vals1.map fT) (vals2.map fX) (vals3.map fC) (vals4.map fA)).html =
          (Model.run vals1 vals2 vals3 vals4).htmlWrites.map jline ∧
        (jRunR (vals1.map fT) (vals2.map fX) (vals3.map fC) (vals4.map fA)).ab =
          (Model.run vals1 vals2 vals3 vals4).abended)
    (hcp : ∀ σ, ClinitRan Gen.prog "Cbstm03a" σ → CP037At σ)
    (hJ : Sat Gen.prog runRefA runSpecJ) : Sat Gen.prog runRef runSpec := by
  -- the ghost values of `runSpecJ` for given field values
  have hpre : ∀ args σ vals1 vals2 vals3 vals4, RunIn args σ vals1 vals2 vals3 vals4 →
      ClinitRan Gen.prog "Cbstm03a" σ → σ.initOf "Cbstm03a$Result" = .done →
      ∃ a1 a2 a3 a4, RunPre ⟨a1, a2, a3, a4, vals1.map fT, vals2.map fX, vals3.map fC, vals4.map fA⟩ args σ := by
    intro args σ vals1 vals2 vals3 vals4 hin hcl hres
    obtain ⟨a1, a2, a3, a4, rfl, h1, h2, h3, h4, v1, v2, v3, v4, -, -⟩ := hin
    exact ⟨a1, a2, a3, a4, rfl, hT σ a1 vals1 h1 v1, hX σ a2 vals2 h2 v2, hC σ a3 vals3 h3 v3,
      hA σ a4 vals4 h4 v4, hcp σ hcl, hres⟩
  intro args σ o h hm
  obtain ⟨vals1, vals2, vals3, vals4, hin, hcl, hres, -, -, -, -⟩ := h
  obtain ⟨a1, a2, a3, a4, hg⟩ := hpre args σ vals1 vals2 vals3 vals4 hin hcl hres
  have hJo := hJ args σ o ⟨_, hg⟩ hm
  cases o with
  | normal r σ' =>
    simp only [runSpecJ, Spec.of] at hJo
    intro w1 w2 w3 w4 hin'
    obtain ⟨b1, b2, b3, b4, hg'⟩ := hpre args σ w1 w2 w3 w4 hin' hcl hres
    obtain ⟨res, hr, hR⟩ := hJo _ hg'
    obtain ⟨_, _, _, _, _, _, _, _, _, u1, u2, u3, u4, hD', _⟩ := hin'
    obtain ⟨e1, e2, e3, e4⟩ := hM w1 w2 w3 w4 u1 u2 u3 u4 hD'
    obtain ⟨fs, l, k, xs, mods, lw1, kw1, ws1, mw1, lw2, kw2, ws2, mw2, p⟩ :=
      runPost_of_resAt (o := Model.run w1 w2 w3 w4) hR e1 e2 e3 e4
    exact ⟨res, fs, l, k, xs, mods, lw1, kw1, ws1, mw1, lw2, kw2, ws2, mw2, hr, p⟩
  | exc e σ' => simp only [runSpecJ, Spec.of] at hJo
  | wrong msg => simp only [runSpecJ, Spec.of] at hJo

/-- **`runSpec` from `runSpecJ`**, the record bridges and the model equation (the `CP037` table from `ClinitRan`
by `cp037At_of_clinitRan`). -/
theorem runSpec_of_J' (fT : List EquivLean.Cobol.Rec.FVal → TrnxR) (fX : List EquivLean.Cobol.Rec.FVal → XrefR)
    (fC : List EquivLean.Cobol.Rec.FVal → CustR) (fA : List EquivLean.Cobol.Rec.FVal → AcctR)
    (hT : ∀ σ a vals, TrnxFileAt σ a vals → (∀ v ∈ vals, TrnxRecord.Valid v) → RecsAt TrnxAtN σ a (vals.map fT))
    (hX : ∀ σ a vals, XrefFileAt σ a vals → (∀ v ∈ vals, CardXrefRecord.Valid v) →
      RecsAt XrefAtN σ a (vals.map fX))
    (hC : ∀ σ a vals, CustFileAt σ a vals → (∀ v ∈ vals, CustomerRecord.Valid v) →
      RecsAt CustAtN σ a (vals.map fC))
    (hA : ∀ σ a vals, AcctFileAt σ a vals → (∀ v ∈ vals, AccountRecord.Valid v) →
      RecsAt AcctAtN σ a (vals.map fA))
    (hM : ∀ vals1 vals2 vals3 vals4, (∀ v ∈ vals1, TrnxRecord.Valid v) → (∀ v ∈ vals2, CardXrefRecord.Valid v) →
      (∀ v ∈ vals3, CustomerRecord.Valid v) → (∀ v ∈ vals4, AccountRecord.Valid v) →
      EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4 →
      (jRunR (vals1.map fT) (vals2.map fX) (vals3.map fC) (vals4.map fA)).disp =
          (Model.run vals1 vals2 vals3 vals4).disp.map jline ∧
        (jRunR (vals1.map fT) (vals2.map fX) (vals3.map fC) (vals4.map fA)).stmt =
          (Model.run vals1 vals2 vals3 vals4).stmtWrites.map jline ∧
        (jRunR (vals1.map fT) (vals2.map fX) (vals3.map fC) (vals4.map fA)).html =
          (Model.run vals1 vals2 vals3 vals4).htmlWrites.map jline ∧
        (jRunR (vals1.map fT) (vals2.map fX) (vals3.map fC) (vals4.map fA)).ab =
          (Model.run vals1 vals2 vals3 vals4).abended)
    (hJ : Sat Gen.prog runRefA runSpecJ) : Sat Gen.prog runRef runSpec :=
  runSpec_of_J fT fX fC fA hT hX hC hA hM (fun _ h => cp037At_of_clinitRan h) hJ

/-- **`run` terminates on every input of `runSpec`**, from its termination on `runSpecJ`'s inputs and the record
bridges. -/
theorem runSpec_term_of (fT : List EquivLean.Cobol.Rec.FVal → TrnxR) (fX : List EquivLean.Cobol.Rec.FVal → XrefR)
    (fC : List EquivLean.Cobol.Rec.FVal → CustR) (fA : List EquivLean.Cobol.Rec.FVal → AcctR)
    (hT : ∀ σ a vals, TrnxFileAt σ a vals → (∀ v ∈ vals, TrnxRecord.Valid v) → RecsAt TrnxAtN σ a (vals.map fT))
    (hX : ∀ σ a vals, XrefFileAt σ a vals → (∀ v ∈ vals, CardXrefRecord.Valid v) →
      RecsAt XrefAtN σ a (vals.map fX))
    (hC : ∀ σ a vals, CustFileAt σ a vals → (∀ v ∈ vals, CustomerRecord.Valid v) →
      RecsAt CustAtN σ a (vals.map fC))
    (hA : ∀ σ a vals, AcctFileAt σ a vals → (∀ v ∈ vals, AccountRecord.Valid v) →
      RecsAt AcctAtN σ a (vals.map fA))
    (hterm : ∀ args σ, runSpecJ.pre args σ → MTerm Gen.prog runRefA args σ) :
    ∀ args σ, runSpec.pre args σ → MTerm Gen.prog runRef args σ := by
  intro args σ h
  obtain ⟨vals1, vals2, vals3, vals4, hin, hcl, hres, -, -, -, -⟩ := h
  obtain ⟨a1, a2, a3, a4, rfl, h1, h2, h3, h4, v1, v2, v3, v4, -, -⟩ := hin
  exact hterm _ σ ⟨⟨a1, a2, a3, a4, vals1.map fT, vals2.map fX, vals3.map fC, vals4.map fA⟩, rfl,
    hT σ a1 vals1 h1 v1, hX σ a2 vals2 h2 v2, hC σ a3 vals3 h3 v3, hA σ a4 vals4 h4 v4, cp037At_of_clinitRan hcl,
    hres⟩

/-- The model equation of `runSpec_of_J'` from the record-level model: `jRunT = jRunHL` under `DomainT`
(`JRunHLStmt`), the statement's domain gives `DomainT` (`hdom`), and `jRunHL` of the records has `Model.run`'s
outputs (`hMHL`). -/
theorem modelEq_of_HL (fT : List EquivLean.Cobol.Rec.FVal → TrnxR) (fX : List EquivLean.Cobol.Rec.FVal → XrefR)
    (fC : List EquivLean.Cobol.Rec.FVal → CustR) (fA : List EquivLean.Cobol.Rec.FVal → AcctR)
    (hHL : JRunHLStmt)
    (hdom : ∀ vals1 vals2 vals3 vals4, (∀ v ∈ vals1, TrnxRecord.Valid v) →
      EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4 →
      DomainT (((vals1.map fT).map trnxTextR).map (recOf · 350)))
    (hMHL : ∀ vals1 vals2 vals3 vals4, (∀ v ∈ vals1, TrnxRecord.Valid v) →
      (∀ v ∈ vals2, CardXrefRecord.Valid v) → (∀ v ∈ vals3, CustomerRecord.Valid v) →
      (∀ v ∈ vals4, AccountRecord.Valid v) → EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4 →
      (jRunHL ((vals1.map fT).map trnxTextR) ((vals2.map fX).map xrefTextR) ((vals3.map fC).map custTextR)
          ((vals4.map fA).map acctTextR)).disp = (Model.run vals1 vals2 vals3 vals4).disp.map jline ∧
        (jRunHL ((vals1.map fT).map trnxTextR) ((vals2.map fX).map xrefTextR) ((vals3.map fC).map custTextR)
          ((vals4.map fA).map acctTextR)).stmt = (Model.run vals1 vals2 vals3 vals4).stmtWrites.map jline ∧
        (jRunHL ((vals1.map fT).map trnxTextR) ((vals2.map fX).map xrefTextR) ((vals3.map fC).map custTextR)
          ((vals4.map fA).map acctTextR)).html = (Model.run vals1 vals2 vals3 vals4).htmlWrites.map jline ∧
        (jRunHL ((vals1.map fT).map trnxTextR) ((vals2.map fX).map xrefTextR) ((vals3.map fC).map custTextR)
          ((vals4.map fA).map acctTextR)).ab = (Model.run vals1 vals2 vals3 vals4).abended) :
    ∀ vals1 vals2 vals3 vals4, (∀ v ∈ vals1, TrnxRecord.Valid v) → (∀ v ∈ vals2, CardXrefRecord.Valid v) →
      (∀ v ∈ vals3, CustomerRecord.Valid v) → (∀ v ∈ vals4, AccountRecord.Valid v) →
      EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4 →
      (jRunR (vals1.map fT) (vals2.map fX) (vals3.map fC) (vals4.map fA)).disp =
          (Model.run vals1 vals2 vals3 vals4).disp.map jline ∧
        (jRunR (vals1.map fT) (vals2.map fX) (vals3.map fC) (vals4.map fA)).stmt =
          (Model.run vals1 vals2 vals3 vals4).stmtWrites.map jline ∧
        (jRunR (vals1.map fT) (vals2.map fX) (vals3.map fC) (vals4.map fA)).html =
          (Model.run vals1 vals2 vals3 vals4).htmlWrites.map jline ∧
        (jRunR (vals1.map fT) (vals2.map fX) (vals3.map fC) (vals4.map fA)).ab =
          (Model.run vals1 vals2 vals3 vals4).abended := by
  intro vals1 vals2 vals3 vals4 v1 v2 v3 v4 hD
  have e : jRunR (vals1.map fT) (vals2.map fX) (vals3.map fC) (vals4.map fA) =
      jRunHL ((vals1.map fT).map trnxTextR) ((vals2.map fX).map xrefTextR) ((vals3.map fC).map custTextR)
        ((vals4.map fA).map acctTextR) :=
    hHL _ _ _ _ (hdom vals1 vals2 vals3 vals4 v1 hD)
  rw [e]
  exact hMHL vals1 vals2 vals3 vals4 v1 v2 v3 v4 hD

/-- **Total correctness of `run` for `runSpec`**: on every input, an outcome exists and every outcome satisfies
`runSpec`. -/
theorem runSpec_total_of (hsat : Sat Gen.prog runRef runSpec)
    (hterm : ∀ args σ, runSpec.pre args σ → MTerm Gen.prog runRef args σ) :
    ∀ args σ, runSpec.pre args σ →
      (∃ o, MExec Gen.prog runRef args σ o) ∧ ∀ o, MExec Gen.prog runRef args σ o → runSpec.post args σ o :=
  total_of_sat_mterm hsat hterm

/-! ## With equiv-lean's record bridges and model equation (`Java/TopBridge.lean`) -/

/-- **`run` satisfies the statement's contract** once it satisfies `runSpecJ`. -/
theorem runSpec_sat_of (hJ : Sat Gen.prog runRefA runSpecJ) : Sat Gen.prog runRef runSpec :=
  runSpec_of_J' trnxROf xrefROf custROf acctROf
    (fun _ _ _ h hv => trnxFileAt_to_recsAt h hv) (fun _ _ _ h hv => xrefFileAt_to_recsAt h hv)
    (fun _ _ _ h hv => custFileAt_to_recsAt h hv) (fun _ _ _ h hv => acctFileAt_to_recsAt h hv)
    (fun v1 v2 v3 v4 h1 h2 h3 h4 hD => jRunR_eq_model v1 v2 v3 v4 h1 h2 h3 h4 hD) hJ

/-- **CBSTM03A → Java, the generated statement**, from `run`'s contract `runSpecJ`. -/
theorem statement_of_runSpecJ (hJ : Sat Gen.prog runRefA runSpecJ) : Statement :=
  statement_of_sat (runSpec_sat_of hJ)

/-- **`run` terminates on the statement's inputs**, from its termination on `runSpecJ`'s inputs. -/
theorem runSpec_term_of_J (hterm : ∀ args σ, runSpecJ.pre args σ → MTerm Gen.prog runRefA args σ) :
    ∀ args σ, runSpec.pre args σ → MTerm Gen.prog runRef args σ :=
  runSpec_term_of trnxROf xrefROf custROf acctROf
    (fun _ _ _ h hv => trnxFileAt_to_recsAt h hv) (fun _ _ _ h hv => xrefFileAt_to_recsAt h hv)
    (fun _ _ _ h hv => custFileAt_to_recsAt h hv) (fun _ _ _ h hv => acctFileAt_to_recsAt h hv) hterm

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.runSpec_of_J

#print axioms EquivLean.Modernize.Cbstm03a.Java.runSpec_of_J'
#print axioms EquivLean.Modernize.Cbstm03a.Java.runSpec_term_of
#print axioms EquivLean.Modernize.Cbstm03a.Java.runSpec_total_of
#print axioms EquivLean.Modernize.Cbstm03a.Java.modelEq_of_HL
#print axioms EquivLean.Modernize.Cbstm03a.Java.runSpec_sat_of
#print axioms EquivLean.Modernize.Cbstm03a.Java.statement_of_runSpecJ
#print axioms EquivLean.Modernize.Cbstm03a.Java.runSpec_term_of_J
