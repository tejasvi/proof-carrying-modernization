import EquivLean.Modernize.Cbstm03a.Java.Mem.LeafA
import EquivLean.Modernize.Cbstm03a.Java.Mem.LeafB
import EquivLean.Modernize.Cbstm03a.Java.Mem.RdFinal

/-!
# CBSTM03A → Java, table memory: the contracts as `Sat` facts

The leaf methods (no callees) by `MethodVC.sat`. `memRead` against its callees (`spaces` with `spacesSpecI`,
proved elsewhere; `slotIndex`, `slotLen`, `slotStart` here), given its three open loop segments.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)
open EquivLean.Modernize.Cbstm03a.Java.Mem

namespace EquivLean.Modernize.Cbstm03a.Java

theorem cardOff_sat : Sat Gen.prog cardOffRef cardOffSpec := MethodVC.sat cardOff_vc
theorem tranOff_sat : Sat Gen.prog tranOffRef tranOffSpec := MethodVC.sat tranOff_vc
theorem seqRead_sat : Sat Gen.prog seqReadRef seqReadSpec := MethodVC.sat seqRead_vc
theorem setTrct_sat : Sat Gen.prog setTrctRef setTrctSpec := MethodVC.sat setTrct_vc
theorem getTrct_sat : Sat Gen.prog getTrctRef getTrctSpec := MethodVC.sat getTrct_vc
theorem slotIndex_sat : Sat Gen.prog slotIndexRef slotIndexSpec := MethodVC.sat slotIndex_vc
theorem slotStart_sat : Sat Gen.prog slotStartRef slotStartSpec := MethodVC.sat slotStart_vc
theorem slotLen_sat : Sat Gen.prog slotLenRef slotLenSpec := MethodVC.sat slotLen_vc

/-- `memRead`'s callee table holds, given `spaces`. -/
theorem rdCallees_valid (hsp : Sat Gen.prog spacesRef spacesSpecI) : Valid Gen.prog rdCallees.env :=
  Contracts.valid_of_ok (by
    intro p hp
    simp only [rdCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact (by jcontract_ok [hsp])
    · exact (by jcontract_ok [slotIndex_sat])
    · exact (by jcontract_ok [slotLen_sat])
    · exact (by jcontract_ok [slotStart_sat]))

/-- `memRead`'s contract, given `spaces` and the four open segments. -/
theorem memRead_sat_of (hsp : Sat Gen.prog spacesRef spacesSpecI) (hP : RdPastSeg) (hR : RdPreSeg) (hN : RdN38Seg)
    (hS : RdS38Seg) : Sat Gen.prog memReadRef memReadSpec :=
  MethodVC.sat_of_valid (rdCallees_valid hsp) (memRead_vc_of hP hR hN hS)

/-- `memRead`'s contract, given `spaces` (`spacesSpecI`). -/
theorem memRead_sat (hsp : Sat Gen.prog spacesRef spacesSpecI) : Sat Gen.prog memReadRef memReadSpec :=
  MethodVC.sat_of_valid (rdCallees_valid hsp) memRead_vc

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.cardOff_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.tranOff_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.seqRead_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.setTrct_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.getTrct_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.memRead_sat_of
#print axioms EquivLean.Modernize.Cbstm03a.Java.memRead_sat
