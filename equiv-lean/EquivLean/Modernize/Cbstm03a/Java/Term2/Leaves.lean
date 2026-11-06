import EquivLean.Modernize.Cbstm03a.Java.Term2.Defs

/-!
# CBSTM03A → Java, termination: the helpers without calls and loops

`cardOff`, `tranOff`, `slotIndex`, `slotStart`, `slotLen`, `setTrct`, `getTrct`, `seqRead`: straight-line code
(no calls, no loops): the termination VC has no cut points and no contracts (`jterm`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

open EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem cardOff_tvc : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 cardOffRef cardOffSpec [] 20 := by
  jterm [cardOffSpec]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem tranOff_tvc : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 tranOffRef tranOffSpec [] 20 := by
  jterm [tranOffSpec]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem slotIndex_tvc : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 slotIndexRef slotIndexSpec [] 30 := by
  jterm [slotIndexSpec]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem slotStart_tvc : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 slotStartRef slotStartSpec [] 30 := by
  jterm [slotStartSpec]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem slotLen_tvc : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 slotLenRef slotLenSpec [] 20 := by
  jterm [slotLenSpec]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem setTrct_tvc : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 setTrctRef setTrctSpec [] 30 := by
  jterm [setTrctSpec]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem getTrct_tvc : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 getTrctRef getTrctSpec [] 30 := by
  jterm [getTrctSpec]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem seqRead_tvc : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 seqReadRef seqReadSpec [] 30 := by
  jterm [seqReadSpec]

theorem cardOff_term : ∀ args σ, cardOffSpec.pre args σ → MTerm Gen.prog cardOffRef args σ :=
  TermVC.mterm (Jimple.valid_none _) (contractTerm_none _ _) cardOff_tvc
theorem tranOff_term : ∀ args σ, tranOffSpec.pre args σ → MTerm Gen.prog tranOffRef args σ :=
  TermVC.mterm (Jimple.valid_none _) (contractTerm_none _ _) tranOff_tvc
theorem slotIndex_term : ∀ args σ, slotIndexSpec.pre args σ → MTerm Gen.prog slotIndexRef args σ :=
  TermVC.mterm (Jimple.valid_none _) (contractTerm_none _ _) slotIndex_tvc
theorem slotStart_term : ∀ args σ, slotStartSpec.pre args σ → MTerm Gen.prog slotStartRef args σ :=
  TermVC.mterm (Jimple.valid_none _) (contractTerm_none _ _) slotStart_tvc
theorem slotLen_term : ∀ args σ, slotLenSpec.pre args σ → MTerm Gen.prog slotLenRef args σ :=
  TermVC.mterm (Jimple.valid_none _) (contractTerm_none _ _) slotLen_tvc
theorem setTrct_term : ∀ args σ, setTrctSpec.pre args σ → MTerm Gen.prog setTrctRef args σ :=
  TermVC.mterm (Jimple.valid_none _) (contractTerm_none _ _) setTrct_tvc
theorem getTrct_term : ∀ args σ, getTrctSpec.pre args σ → MTerm Gen.prog getTrctRef args σ :=
  TermVC.mterm (Jimple.valid_none _) (contractTerm_none _ _) getTrct_tvc
theorem seqRead_term : ∀ args σ, seqReadSpec.pre args σ → MTerm Gen.prog seqReadRef args σ :=
  TermVC.mterm (Jimple.valid_none _) (contractTerm_none _ _) seqRead_tvc

end EquivLean.Modernize.Cbstm03a.Java.Term2

namespace EquivLean.Modernize.Cbstm03a.Java

open Term2

set_option maxHeartbeats 4000000 in
theorem cardOff_cterm : ContractTerm Gen.prog cardOffSig cardOffSpec := by jcontract_term [cardOff_term]
set_option maxHeartbeats 4000000 in
theorem tranOff_cterm : ContractTerm Gen.prog tranOffSig tranOffSpec := by jcontract_term [tranOff_term]
set_option maxHeartbeats 4000000 in
theorem slotIndex_cterm : ContractTerm Gen.prog slotIndexSig slotIndexSpec := by jcontract_term [slotIndex_term]
set_option maxHeartbeats 4000000 in
theorem slotStart_cterm : ContractTerm Gen.prog slotStartSig slotStartSpec := by jcontract_term [slotStart_term]
set_option maxHeartbeats 4000000 in
theorem slotLen_cterm : ContractTerm Gen.prog slotLenSig slotLenSpec := by jcontract_term [slotLen_term]
set_option maxHeartbeats 4000000 in
theorem setTrct_cterm : ContractTerm Gen.prog setTrctSig setTrctSpec := by jcontract_term [setTrct_term]
set_option maxHeartbeats 4000000 in
theorem getTrct_cterm : ContractTerm Gen.prog getTrctSig getTrctSpec := by jcontract_term [getTrct_term]
set_option maxHeartbeats 4000000 in
theorem seqRead_cterm : ContractTerm Gen.prog seqReadSig seqReadSpec := by jcontract_term [seqRead_term]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.cardOff_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.tranOff_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.slotIndex_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.slotStart_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.slotLen_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.setTrct_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.getTrct_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.seqRead_cterm
