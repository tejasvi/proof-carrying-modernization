/-
  Examples/CardDemo/Cbact02cTermHelpers.lean

  Termination of CBACT02C's helpers (`Jimple/Termination.lean`): `fix`, `spaces` and `zeroPad`
  keep their correctness invariants with the variants `n - i`, `n - i` and `i + 1` (the digit index
  runs down to `-1`); `formatCard` has no loop. Each callee's termination is linked as a
  `ContractTerm` (`jcontract_term`); the contracts themselves hold by `Cbact02cLink`. `run` is in
  `Cbact02cTermRun`.
-/
import Examples.CardDemo.Cbact02cLink

open Jimple

namespace Examples.CardDemo

/-! ### The helpers -/

def fixVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0, fr.get 2 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem fix_tvc :
    TermVC CB.prog (fun _ => none) (fun _ => 0) 0 0 fixRef fixSpec (fixInv.withVariant fixVar) 60 := by
  jterm [ite_nat_ne, fixSpec, fixInv, fixVar, StrOk, argText, Grows, fixStr]

theorem fix_term : ∀ args σ, fixSpec.pre args σ → MTerm CB.prog fixRef args σ :=
  TermVC.mterm (valid_none _) (contractTerm_none _ _) fix_tvc

def spacesVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0, fr.get 1 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_tvc :
    TermVC CB.prog (fun _ => none) (fun _ => 0) 0 0 spacesRef spacesSpec (spacesInv.withVariant spacesVar) 60 := by
  jterm [ite_nat_ne, spacesSpec, spacesInv, spacesVar, Grows, fixStr]

theorem spaces_term : ∀ args σ, spacesSpec.pre args σ → MTerm CB.prog spacesRef args σ :=
  TermVC.mterm (valid_none _) (contractTerm_none _ _) spaces_tvc

def zeroPadVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 4 with
  | some (.int i) => (i.toInt + 1).toNat
  | _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem zeroPad_tvc :
    TermVC CB.prog (fun _ => none) (fun _ => 0) 0 0 zeroPadRef zeroPadSpec (zeroPadInv.withVariant zeroPadVar) 80 := by
  jterm [ite_nat_ne, zeroPadSpec, zeroPadInv, zeroPadVar, Grows, zpadStr, digitChar, sdiv10_toNat_of_nonneg,
    sdiv10_nonneg, digit_char, drop_set_self]

theorem zeroPad_term : ∀ args σ, zeroPadSpec.pre args σ → MTerm CB.prog zeroPadRef args σ :=
  TermVC.mterm (valid_none _) (contractTerm_none _ _) zeroPad_tvc

theorem fix_cterm : ContractTerm CB.prog fixSig fixSpec := by jcontract_term [fix_term]
theorem spaces_cterm : ContractTerm CB.prog spacesSig spacesSpec := by jcontract_term [spaces_term]
theorem zeroPad_cterm : ContractTerm CB.prog zeroPadSig zeroPadSpec := by jcontract_term [zeroPad_term]

/-! ### `formatCard` (no loop) -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem formatCard_tvc :
    TermVC CB.prog fcCallees.env (fun _ => 0) 1 0 formatCardRef formatCardSpec [] 80 := by
  jterm [ite_nat_ne, formatCardSpec, fcCallees, fixSig, zeroPadSig, fixSpec, zeroPadSpec, CardOk, StrField,
    LongField, StrOk, cardLine, fieldOf, fieldLong, argText, cardCls, Grows]

theorem formatCard_term : ∀ args σ, formatCardSpec.pre args σ → MTerm CB.prog formatCardRef args σ :=
  TermVC.mterm (Contracts.valid_of_ok (by
      intro p hp
      simp only [fcCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact fix_ok
      · exact zeroPad_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [fcCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact fix_cterm
      · exact zeroPad_cterm) _ _) formatCard_tvc

theorem formatCard_cterm : ContractTerm CB.prog formatCardSig formatCardSpec := by
  jcontract_term [formatCard_term]

end Examples.CardDemo

#print axioms Examples.CardDemo.formatCard_cterm
