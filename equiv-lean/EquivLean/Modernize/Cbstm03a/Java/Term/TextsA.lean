import EquivLean.Modernize.Cbstm03a.Java.Term.Fix
import EquivLean.Modernize.Cbstm03a.Java.Term.Zu

/-!
# CBSTM03A → Java, termination: the record texts (`xrefText`, `trnxText`)

No loops: field reads of the record and calls of `fix`, `zu`, `zs`, `spaces`, then one concatenation. The string
fields' facts are stated at the entry state (`StrArg σ₀`); `fix` is called through `fixGSpecT` (`fixSpecT`'s
precondition for any earlier state `σ₀` the current state grows from, `strArg_grows`), so that no case split on
the fields' nullness is needed. Frame contracts (the record `null` or an object whose string fields are string
arguments and whose numeric fields are `long`s; `Cbstm03a` initialized): a new string of the record's length,
`GrowsT`; exceptions (from `zu`/`zs`'s frame contracts) with `GrowsT`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Term

theorem strArg_grows {σ₀ σ : State} {v : Value} (hg : Grows σ₀ σ) (h : StrArg σ₀ v) : StrArg σ v := by
  rcases h with h | ⟨x, s, rfl, hx, hl⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, s, rfl, (hg.2 x (State.lt_next_of_heap hx)).trans hx, hl⟩

/-- `fixSpecT` with the string argument's facts at an earlier state `σ₀`. -/
def fixGSpecT : Spec := Spec.of
  (fun args σ => ∃ sv n σ₀, args = [sv, .int n] ∧ Grows σ₀ σ ∧ StrArg σ₀ sv ∧ 0 ≤ n.toInt ∧
    n.toInt ≤ 1073741824 ∧ InitA σ)
  (fun args σ r σ' => ∀ sv n, args = [sv, .int n] →
    (∃ x s, r = some (.ref x) ∧ σ'.heap x = some (.str s) ∧ s.length = n.toInt.toNat) ∧ GrowsT σ σ')

theorem fixG_pre {args : List Value} {σ : State} (h : fixGSpecT.pre args σ) : fixSpecT.pre args σ := by
  obtain ⟨sv, n, σ₀, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨sv, n, h1, strArg_grows h2 h3, h4, h5, h6⟩

theorem fixG_satT : Sat Gen.prog fixRef fixGSpecT := fun args σ o hpre hx => fix_satT args σ o (fixG_pre hpre) hx
theorem fixG_ctermT : ContractTerm Gen.prog fixSig fixGSpecT := ContractTerm.mono fix_ctermT fun _ _ h => fixG_pre h
set_option maxHeartbeats 4000000 in
theorem fixG_okT : ContractOK Gen.prog fixSig fixGSpecT := by jcontract_ok [fixG_satT]

/-- A record argument: `null`, or an object of class `cls` whose fields `ss` hold string arguments and whose
    fields `ls` hold `long`s. -/
def RecArg (σ : State) (cls : ClassName) (ss ls : List String) (v : Value) : Prop :=
  v = .null ∨ ∃ a fs, v = .ref a ∧ σ.heap a = some (.plain cls fs) ∧
    (∀ f ∈ ss, ∃ w, Fields.get fs (cls, f) = some w ∧ StrArg σ w) ∧
    (∀ f ∈ ls, ∃ l : I64, Fields.get fs (cls, f) = some (.long l))

abbrev xrefSs : List String := ["xrefCardNum", "filler1"]
abbrev xrefLs : List String := ["xrefCustId", "xrefAcctId"]
abbrev trnxSs : List String := ["trnxCardNum", "trnxId", "trnxTypeCd", "trnxSource", "trnxDesc",
  "trnxMerchantName", "trnxMerchantCity", "trnxMerchantZip", "trnxOrigTs", "trnxProcTs", "filler1"]
abbrev trnxLs : List String := ["trnxCatCd", "trnxAmt", "trnxMerchantId"]

abbrev xrefTextRef : MethodRef := Gen.Cbstm03a.«xrefText(Cbstm03a$CardXrefRecord)».ref
abbrev trnxTextRef : MethodRef := Gen.Cbstm03a.«trnxText(Cbstm03a$TrnxRecord)».ref
def xrefTextSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "xrefText", [.cls "Cbstm03a$CardXrefRecord"]⟩
def trnxTextSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "trnxText", [.cls "Cbstm03a$TrnxRecord"]⟩

/-- A record text: the record's class and fields, the text's length. -/
def textSpecT (cls : ClassName) (ss ls : List String) (len : Nat) : Spec := Spec.of
  (fun args σ => ∃ rv, args = [rv] ∧ RecArg σ cls ss ls rv ∧ InitA σ)
  (fun _ σ r σ' => StrResL σ r σ' len ∧ GrowsT σ σ')
  (fun _ σ e σ' => GrowsT σ σ' ∧ ∃ o, σ'.heap e = some o)

def textCalleesT : Contracts :=
  [(fixSig, fixGSpecT), (zuSig, zuSpecT), (zsSig, zsSpecT), (spacesSig, spacesSpecT)]

theorem textCalleesT_ok : ∀ p ∈ textCalleesT, ContractOK Gen.prog p.1 p.2 := by
  simp only [textCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨fixG_okT, zu_okT, zs_okT, spaces_okT⟩
theorem textCalleesT_term : ∀ p ∈ textCalleesT, ContractTerm Gen.prog p.1 p.2 := by
  simp only [textCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨fixG_ctermT, zu_ctermT, zs_ctermT, spaces_ctermT⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem xrefText_vcT : MethodVC Gen.prog textCalleesT.env 0 xrefTextRef
    (textSpecT "Cbstm03a$CardXrefRecord" xrefSs xrefLs 50) [] 40 := by
  set_option jimple.modelContracts true in
  jverify [ite_nat_ne, findHandler, textSpecT, RecArg, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true, textCalleesT, fixSig, fixGSpecT, zuSig, zuSpecT, zsSig, zsSpecT, spacesSig, spacesSpecT, StrResL,
    GrowsT, Grows]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem xrefText_thinT : ThinVC Gen.prog textCalleesT.env 0 xrefTextRef
    (textSpecT "Cbstm03a$CardXrefRecord" xrefSs xrefLs 50) [] (fun _ _ _ _ _ => 0) 40 := by
  set_option jimple.modelContracts true in
  jthin [ite_nat_ne, findHandler, textSpecT, RecArg, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true, textCalleesT, fixSig, fixGSpecT, zuSig, zuSpecT, zsSig, zsSpecT, spacesSig, spacesSpecT, StrResL,
    GrowsT, Grows]

theorem xrefText_termT : ∀ args σ, (textSpecT "Cbstm03a$CardXrefRecord" xrefSs xrefLs 50).pre args σ →
    MTerm Gen.prog xrefTextRef args σ :=
  mterm_of_thin textCalleesT_ok textCalleesT_term xrefText_vcT xrefText_thinT
theorem xrefText_satT : Sat Gen.prog xrefTextRef (textSpecT "Cbstm03a$CardXrefRecord" xrefSs xrefLs 50) :=
  sat_of_table textCalleesT_ok xrefText_vcT

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem trnxText_vcT : MethodVC Gen.prog textCalleesT.env 0 trnxTextRef
    (textSpecT "Cbstm03a$TrnxRecord" trnxSs trnxLs 350) [] 60 := by
  set_option jimple.modelContracts true in
  jverify [ite_nat_ne, findHandler, textSpecT, RecArg, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true, textCalleesT, fixSig, fixGSpecT, zuSig, zuSpecT, zsSig, zsSpecT, spacesSig, spacesSpecT, StrResL,
    GrowsT, Grows]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem trnxText_thinT : ThinVC Gen.prog textCalleesT.env 0 trnxTextRef
    (textSpecT "Cbstm03a$TrnxRecord" trnxSs trnxLs 350) [] (fun _ _ _ _ _ => 0) 60 := by
  set_option jimple.modelContracts true in
  jthin [ite_nat_ne, findHandler, textSpecT, RecArg, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true, textCalleesT, fixSig, fixGSpecT, zuSig, zuSpecT, zsSig, zsSpecT, spacesSig, spacesSpecT, StrResL,
    GrowsT, Grows]

theorem trnxText_termT : ∀ args σ, (textSpecT "Cbstm03a$TrnxRecord" trnxSs trnxLs 350).pre args σ →
    MTerm Gen.prog trnxTextRef args σ :=
  mterm_of_thin textCalleesT_ok textCalleesT_term trnxText_vcT trnxText_thinT
theorem trnxText_satT : Sat Gen.prog trnxTextRef (textSpecT "Cbstm03a$TrnxRecord" trnxSs trnxLs 350) :=
  sat_of_table textCalleesT_ok trnxText_vcT

set_option maxHeartbeats 4000000 in
theorem xrefText_ctermT : ContractTerm Gen.prog xrefTextSig (textSpecT "Cbstm03a$CardXrefRecord" xrefSs xrefLs 50) := by
  jcontract_term [xrefText_termT]
set_option maxHeartbeats 4000000 in
theorem xrefText_okT : ContractOK Gen.prog xrefTextSig (textSpecT "Cbstm03a$CardXrefRecord" xrefSs xrefLs 50) := by
  jcontract_ok [xrefText_satT]
set_option maxHeartbeats 4000000 in
theorem trnxText_ctermT : ContractTerm Gen.prog trnxTextSig (textSpecT "Cbstm03a$TrnxRecord" trnxSs trnxLs 350) := by
  jcontract_term [trnxText_termT]
set_option maxHeartbeats 4000000 in
theorem trnxText_okT : ContractOK Gen.prog trnxTextSig (textSpecT "Cbstm03a$TrnxRecord" trnxSs trnxLs 350) := by
  jcontract_ok [trnxText_satT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.xrefText_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.xrefText_okT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.trnxText_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.trnxText_okT
