import Cobol
open Cobol

/-! Larger de-editing checks (`scripts/lean1.sh tests/DeEdit2.lean`): every value of a picture is
de-edited back from its editing, decided by the kernel. -/

/-- Every value of `PIC -Z9.9` (-99.9 to 99.9). -/
theorem deEdit_edit_minus_z9_9 : ∀ i : Fin 1999,
    let pic := [ESym.minus, .z, .nine, .dot, .nine]
    ((Edit.edit Config.ibm pic false ((i : Int) - 999) 1).bind
      (fun bs => (Sem.deEdit Config.ibm pic false bs).toOption)) = some ((i : Int) - 999, 1) := by
  decide +kernel

/-- Every value of `PIC $$9.9CR` (-99.9 to 99.9): floating currency symbol, CR. -/
theorem deEdit_edit_cs_cr : ∀ i : Fin 1999,
    let pic := [ESym.cs, .cs, .nine, .dot, .nine, .cr]
    ((Edit.edit Config.ibm pic false ((i : Int) - 999) 1).bind
      (fun bs => (Sem.deEdit Config.ibm pic false bs).toOption)) = some ((i : Int) - 999, 1) := by
  decide +kernel

#print axioms deEdit_edit_minus_z9_9
#print axioms deEdit_edit_cs_cr
