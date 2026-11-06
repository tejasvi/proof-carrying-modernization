import EquivLean.Modernize.Cbstm03a.Java.RecBridge
import EquivLean.Modernize.Cbstm03a.Java.ModelEq

/-!
# CBSTM03A → Java: `jRunR` on `trnxROf` / `xrefROf` / `custROf` / `acctROf` equals `Model.run`
-/

open Cobol Cobol.StmCore EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03a.StmBridge EquivLean.Modernize.Cbstm03a.Model

namespace EquivLean.Modernize.Cbstm03a.Java

theorem map_trnxTextR_trnxROf {vals1 : List (List EquivLean.Cobol.Rec.FVal)}
    (hv1 : ∀ v ∈ vals1, TrnxRecord.Valid v) :
    (vals1.map trnxROf).map trnxTextR =
      (vals1.map TrnxRecord.encode).map (fun r => jline (r.map cp037Code)) := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun v hv => trnxTextR_eq (hv1 v hv)

theorem map_xrefTextR_xrefROf {vals2 : List (List EquivLean.Cobol.Rec.FVal)}
    (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v) :
    (vals2.map xrefROf).map xrefTextR =
      (vals2.map CardXrefRecord.encode).map (fun r => jline (r.map cp037Code)) := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun v hv => xrefTextR_eq (hv2 v hv)

theorem map_custTextR_custROf {vals3 : List (List EquivLean.Cobol.Rec.FVal)}
    (hv3 : ∀ v ∈ vals3, CustomerRecord.Valid v) :
    (vals3.map custROf).map custTextR =
      (vals3.map CustomerRecord.encode).map (fun r => jline (r.map cp037Code)) := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun v hv => custTextR_eq (hv3 v hv)

theorem map_acctTextR_acctROf {vals4 : List (List EquivLean.Cobol.Rec.FVal)}
    (hv4 : ∀ v ∈ vals4, AccountRecord.Valid v) :
    (vals4.map acctROf).map acctTextR =
      (vals4.map AccountRecord.encode).map (fun r => jline (r.map cp037Code)) := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun v hv => acctTextR_eq (hv4 v hv)

/-- **`jRunR` on `trnxROf` / `xrefROf` / `custROf` / `acctROf` equals `Model.run` under `Domain`.** -/
theorem jRunR_eq_model (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal))
    (hv1 : ∀ v ∈ vals1, TrnxRecord.Valid v)
    (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, CustomerRecord.Valid v)
    (hv4 : ∀ v ∈ vals4, AccountRecord.Valid v)
    (hD : EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4) :
    let jr := jRunR (vals1.map trnxROf) (vals2.map xrefROf) (vals3.map custROf) (vals4.map acctROf)
    let mr := Model.run vals1 vals2 vals3 vals4
    jr.disp = mr.disp.map jline ∧
    jr.stmt = mr.stmtWrites.map jline ∧
    jr.html = mr.htmlWrites.map jline ∧
    jr.ab = mr.abended := by
  dsimp only
  unfold jRunR
  rw [map_trnxTextR_trnxROf hv1, map_xrefTextR_xrefROf hv2,
      map_custTextR_custROf hv3, map_acctTextR_acctROf hv4]
  exact jRunT_eq_model vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 hD

#print axioms jRunR_eq_model

end EquivLean.Modernize.Cbstm03a.Java
