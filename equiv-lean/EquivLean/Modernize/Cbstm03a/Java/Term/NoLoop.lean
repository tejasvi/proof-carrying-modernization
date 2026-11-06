import EquivLean.Modernize.Cbstm03a.Java.Term.Lemmas

/-!
# CBSTM03A → Java, termination: helpers without loops or calls

`cardOff`, `tranOff`, `slotIndex`, `slotStart`, `slotLen`, `trunc11`, `setTrct`, `getTrct`, `seqRead`: straight-line
code; direct termination VCs (`TermVC`, no cut point), contracts with postcondition `True`. Preconditions: the
arguments' types (arrays `null` or arrays; `seqRead`'s status array an `int` array).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Term

abbrev cardOffRef : MethodRef := Gen.Cbstm03a.«cardOff(long)».ref
abbrev tranOffRef : MethodRef := Gen.Cbstm03a.«tranOff(long,long)».ref
abbrev slotIndexRef : MethodRef := Gen.Cbstm03a.«slotIndex(long)».ref
abbrev slotStartRef : MethodRef := Gen.Cbstm03a.«slotStart(int)».ref
abbrev slotLenRef : MethodRef := Gen.Cbstm03a.«slotLen(int)».ref
abbrev trunc11Ref : MethodRef := Gen.Cbstm03a.«trunc11(long)».ref
abbrev setTrctRef : MethodRef := Gen.Cbstm03a.«setTrct(long[],long,long)».ref
abbrev getTrctRef : MethodRef := Gen.Cbstm03a.«getTrct(long[],long)».ref
abbrev seqReadRef : MethodRef := Gen.Cbstm03a.«seqRead(java.lang.String[],int[])».ref

def cardOffSig : MethodSig := ⟨"Cbstm03a", .prim .long, "cardOff", [.prim .long]⟩
def tranOffSig : MethodSig := ⟨"Cbstm03a", .prim .long, "tranOff", [.prim .long, .prim .long]⟩
def slotIndexSig : MethodSig := ⟨"Cbstm03a", .prim .int, "slotIndex", [.prim .long]⟩
def slotStartSig : MethodSig := ⟨"Cbstm03a", .prim .long, "slotStart", [.prim .int]⟩
def slotLenSig : MethodSig := ⟨"Cbstm03a", .prim .int, "slotLen", [.prim .int]⟩
def trunc11Sig : MethodSig := ⟨"Cbstm03a", .prim .long, "trunc11", [.prim .long]⟩
def setTrctSig : MethodSig := ⟨"Cbstm03a", .void, "setTrct", [.array (.prim .long), .prim .long, .prim .long]⟩
def getTrctSig : MethodSig := ⟨"Cbstm03a", .prim .long, "getTrct", [.array (.prim .long), .prim .long]⟩
def seqReadSig : MethodSig :=
  ⟨"Cbstm03a", .cls "java.lang.String", "seqRead", [.array (.cls "java.lang.String"), .array (.prim .int)]⟩

/-- `null` or an array of element type `t`. -/
def ArrOf (σ : State) (t : JType) (v : Value) : Prop :=
  v = .null ∨ ∃ a xs, v = .ref a ∧ σ.heap a = some (.array t xs)

/-- `null` or an `int` array. -/
def IntArr (σ : State) (v : Value) : Prop :=
  v = .null ∨ ∃ (a : Addr) (ks : List I32), v = .ref a ∧ σ.heap a = some (.array (.prim .int) (ks.map Value.int))

def cardOffSpecT : Spec := ⟨fun args _ => ∃ c : I64, args = [.long c], fun _ _ _ => True⟩
def tranOffSpecT : Spec := ⟨fun args _ => ∃ c t : I64, args = [.long c, .long t], fun _ _ _ => True⟩
def slotIndexSpecT : Spec := ⟨fun args _ => ∃ o : I64, args = [.long o], fun _ _ _ => True⟩
def slotStartSpecT : Spec := ⟨fun args _ => ∃ i : I32, args = [.int i], fun _ _ _ => True⟩
def slotLenSpecT : Spec := ⟨fun args _ => ∃ i : I32, args = [.int i], fun _ _ _ => True⟩
def trunc11SpecT : Spec := ⟨fun args _ => ∃ v : I64, args = [.long v], fun _ _ _ => True⟩
def setTrctSpecT : Spec :=
  ⟨fun args σ => ∃ (tv : Value) (c v : I64), args = [tv, .long c, .long v] ∧ ArrOf σ (.prim .long) tv, fun _ _ _ => True⟩
def getTrctSpecT : Spec :=
  ⟨fun args σ => ∃ (tv : Value) (c : I64), args = [tv, .long c] ∧ ArrOf σ (.prim .long) tv, fun _ _ _ => True⟩
def seqReadSpecT : Spec :=
  ⟨fun args σ => ∃ tv sv, args = [tv, sv] ∧ ArrOf σ (.cls "java.lang.String") tv ∧ IntArr σ sv, fun _ _ _ => True⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem cardOff_tvcT : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 cardOffRef cardOffSpecT [] 20 := by
  jterm [cardOffSpecT]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem tranOff_tvcT : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 tranOffRef tranOffSpecT [] 20 := by
  jterm [tranOffSpecT]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem slotIndex_tvcT : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 slotIndexRef slotIndexSpecT [] 30 := by
  jterm [slotIndexSpecT]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem slotStart_tvcT : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 slotStartRef slotStartSpecT [] 30 := by
  jterm [slotStartSpecT]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem slotLen_tvcT : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 slotLenRef slotLenSpecT [] 20 := by
  jterm [slotLenSpecT]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem trunc11_tvcT : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 trunc11Ref trunc11SpecT [] 30 := by
  jterm [trunc11SpecT]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem setTrct_tvcT : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 setTrctRef setTrctSpecT [] 30 := by
  jterm [setTrctSpecT, ArrOf, findHandler]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem getTrct_tvcT : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 getTrctRef getTrctSpecT [] 30 := by
  jterm [getTrctSpecT, ArrOf, findHandler]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem seqRead_tvcT : TermVC Gen.prog (fun _ => none) (fun _ => 0) 1 0 seqReadRef seqReadSpecT [] 30 := by
  jterm [seqReadSpecT, ArrOf, IntArr, getElem?_map_int, findHandler]

theorem cardOff_termT : ∀ args σ, cardOffSpecT.pre args σ → MTerm Gen.prog cardOffRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _) cardOff_tvcT
theorem tranOff_termT : ∀ args σ, tranOffSpecT.pre args σ → MTerm Gen.prog tranOffRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _) tranOff_tvcT
theorem slotIndex_termT : ∀ args σ, slotIndexSpecT.pre args σ → MTerm Gen.prog slotIndexRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _) slotIndex_tvcT
theorem slotStart_termT : ∀ args σ, slotStartSpecT.pre args σ → MTerm Gen.prog slotStartRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _) slotStart_tvcT
theorem slotLen_termT : ∀ args σ, slotLenSpecT.pre args σ → MTerm Gen.prog slotLenRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _) slotLen_tvcT
theorem trunc11_termT : ∀ args σ, trunc11SpecT.pre args σ → MTerm Gen.prog trunc11Ref args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _) trunc11_tvcT
theorem setTrct_termT : ∀ args σ, setTrctSpecT.pre args σ → MTerm Gen.prog setTrctRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _) setTrct_tvcT
theorem getTrct_termT : ∀ args σ, getTrctSpecT.pre args σ → MTerm Gen.prog getTrctRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _) getTrct_tvcT
theorem seqRead_termT : ∀ args σ, seqReadSpecT.pre args σ → MTerm Gen.prog seqReadRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _) seqRead_tvcT

set_option maxHeartbeats 4000000 in
theorem cardOff_ctermT : ContractTerm Gen.prog cardOffSig cardOffSpecT := by jcontract_term [cardOff_termT]
set_option maxHeartbeats 4000000 in
theorem tranOff_ctermT : ContractTerm Gen.prog tranOffSig tranOffSpecT := by jcontract_term [tranOff_termT]
set_option maxHeartbeats 4000000 in
theorem slotIndex_ctermT : ContractTerm Gen.prog slotIndexSig slotIndexSpecT := by jcontract_term [slotIndex_termT]
set_option maxHeartbeats 4000000 in
theorem slotStart_ctermT : ContractTerm Gen.prog slotStartSig slotStartSpecT := by jcontract_term [slotStart_termT]
set_option maxHeartbeats 4000000 in
theorem slotLen_ctermT : ContractTerm Gen.prog slotLenSig slotLenSpecT := by jcontract_term [slotLen_termT]
set_option maxHeartbeats 4000000 in
theorem trunc11_ctermT : ContractTerm Gen.prog trunc11Sig trunc11SpecT := by jcontract_term [trunc11_termT]
set_option maxHeartbeats 4000000 in
theorem setTrct_ctermT : ContractTerm Gen.prog setTrctSig setTrctSpecT := by jcontract_term [setTrct_termT]
set_option maxHeartbeats 4000000 in
theorem getTrct_ctermT : ContractTerm Gen.prog getTrctSig getTrctSpecT := by jcontract_term [getTrct_termT]
set_option maxHeartbeats 4000000 in
theorem seqRead_ctermT : ContractTerm Gen.prog seqReadSig seqReadSpecT := by jcontract_term [seqRead_termT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.cardOff_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.tranOff_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.slotIndex_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.slotStart_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.slotLen_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.trunc11_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.setTrct_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.getTrct_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.seqRead_ctermT
