import Cobol
open Cobol

/-! De-editing checks (`Sem.deEdit`), decided by the kernel on concrete pictures
(`scripts/lean1.sh tests/DeEdit.lean`). -/

/-- NC222A MOV-TEST-F2-3: `PIC $(4)9.99CR`, -123.45 edited (` $123.45CR`) de-edits to -123.45. -/
theorem deEdit_nc222a_3 :
    let pic := [ESym.cs, .cs, .cs, .cs, .nine, .dot, .nine, .nine, .cr]
    ((Edit.edit Config.ibm pic false (-12345) 2).bind
      (fun bs => (Sem.deEdit Config.ibm pic false bs).toOption)) = some (-12345, 2) := by
  decide +kernel

/-- NC222A MOV-TEST-F2-4: `PIC --9B.99B99/99`, -42.9876 edited (`-42 .98 76/00`) de-edits to
-42.987600. -/
theorem deEdit_nc222a_4 :
    let pic := [ESym.minus, .minus, .nine, .b, .dot, .nine, .nine, .b, .nine, .nine, .slash, .nine, .nine]
    ((Edit.edit Config.ibm pic false (-42987600) 6).bind
      (fun bs => (Sem.deEdit Config.ibm pic false bs).toOption)) = some (-42987600, 6) := by
  decide +kernel

/-- Every value of `PIC -Z9` (-99 to 99) is de-edited back from its editing. -/
theorem deEdit_edit_minus_z9 : ∀ i : Fin 199,
    let pic := [ESym.minus, .z, .nine]
    ((Edit.edit Config.ibm pic false ((i : Int) - 99) 0).bind
      (fun bs => (Sem.deEdit Config.ibm pic false bs).toOption)) = some ((i : Int) - 99, 0) := by
  decide +kernel

/-- `VALUE ZERO` in `PIC ZZ9.99` (`000000`): no value edits to it, `invalidData`. -/
theorem deEdit_valzero_invalid :
    (match Sem.deEdit Config.ibm [ESym.z, .z, .nine, .dot, .nine, .nine] false
        (Config.ibm.encodeAscii "000000") with
      | .error .invalidData => true
      | _ => false) = true := by
  decide +kernel

#print axioms deEdit_nc222a_3
#print axioms deEdit_nc222a_4
#print axioms deEdit_edit_minus_z9
#print axioms deEdit_valzero_invalid
