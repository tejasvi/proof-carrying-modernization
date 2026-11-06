import EquivLean.Modernize.Cbstm03b.Java.Term.Trnx
import EquivLean.Modernize.Cbstm03b.Java.Term.KeySubF

/-!
# CBSTM03B → Java, termination: the callees of the keyed procedures

`custProc` and `acctProc` call `status2`, `fit`, `keySub`, `spaces` (and `acctProc` `zeroPad`). Their termination
VCs answer these calls by contracts that hold and terminate: `status2SpecF`, `fitSpecF` (fresh results),
`keySubSpecT` (`Term.KeySubF`: a new string of at most 25 characters), `spacesSpec`, `zeroPadSpec`. The
tables are closed terms: the symbolic executor evaluates their lookups (a table with free variables stalls it).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03b.Java

theorem keySubT_sat : Sat Gen.prog keySubRef keySubSpecT := keySubT_vc.sat

theorem keySubT_term : ∀ args σ, keySubSpecT.pre args σ → MTerm Gen.prog keySubRef args σ := by
  intro args σ hpre
  obtain ⟨q, skey, fs, key, kl, h0, h1, h2, h3, h4, h5, h6, h7⟩ := hpre
  exact keySubG_term q skey fs key kl args σ ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

theorem spaces_satT : Sat Gen.prog spacesRef spacesSpec := spaces_vc.sat
theorem zeroPad_satT : Sat Gen.prog zeroPadRef zeroPadSpec := zeroPad_vc.sat

set_option maxHeartbeats 4000000 in
theorem keySubT_okT : ContractOK Gen.prog keySubSig keySubSpecT := by jcontract_ok [keySubT_sat]
set_option maxHeartbeats 4000000 in
theorem spaces_okT : ContractOK Gen.prog spacesSig spacesSpec := by jcontract_ok [spaces_satT]
set_option maxHeartbeats 4000000 in
theorem zeroPad_okT : ContractOK Gen.prog zeroPadSig zeroPadSpec := by jcontract_ok [zeroPad_satT]

set_option maxHeartbeats 4000000 in
theorem keySubT_cterm : ContractTerm Gen.prog keySubSig keySubSpecT := by jcontract_term [keySubT_term]

/-- The callee contracts of `custProc`'s termination VC. -/
def custCalleesT : Contracts :=
  [(status2Sig, status2SpecF), (fitSig, fitSpecF), (keySubSig, keySubSpecT), (spacesSig, spacesSpec)]

/-- The callee contracts of `acctProc`'s termination VC. -/
def acctCalleesT : Contracts :=
  [(status2Sig, status2SpecF), (fitSig, fitSpecF), (keySubSig, keySubSpecT), (spacesSig, spacesSpec),
    (zeroPadSig, zeroPadSpec)]

theorem custCalleesT_valid : Valid Gen.prog custCalleesT.env := by
  apply Contracts.valid_of_ok
  simp only [custCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨status2F_okT, fitF_okT, keySubT_okT, spaces_okT⟩

theorem acctCalleesT_valid : Valid Gen.prog acctCalleesT.env := by
  apply Contracts.valid_of_ok
  simp only [acctCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨status2F_okT, fitF_okT, keySubT_okT, spaces_okT, zeroPad_okT⟩

theorem custCalleesT_term :
    ∀ sig S, (custCalleesT.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [custCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨status2F_cterm, fitF_cterm, keySubT_cterm, spaces_cterm⟩) _ _

theorem acctCalleesT_term :
    ∀ sig S, (acctCalleesT.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [acctCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨status2F_cterm, fitF_cterm, keySubT_cterm, spaces_cterm, zeroPad_cterm⟩) _ _

/-! ## Heaps: what a keyed procedure keeps -/

theorem ne_of_str_plain {σ : State} {x y : Addr} {s : JStr} {c : ClassName} {fs : List (FieldKey × Value)}
    (hx : σ.heap x = some (.str s)) (hy : σ.heap y = some (.plain c fs)) : x ≠ y := by
  intro e
  rw [e, hy] at hx
  cases hx

/-- The objects of `σ0` other than `y0` are unchanged in `σ`. -/
theorem keeps_heap {σ0 σ : State} {y0 x : Addr} {o : Obj} (hk : Keeps (fun x => x = y0) σ0 σ)
    (hx : σ0.heap x = some o) (hne : x ≠ y0) : σ.heap x = some o := by
  rw [hk.2 x (State.lt_next_of_heap hx) hne, hx]

/-- `Keeps A σ0 σ` for a state built by allocations, callees (`GrowsK`) and updates of `A`'s objects from `σ0` or
from a state kept by a `Kept` hypothesis. -/
macro "keepsK_tac" : tactic => `(tactic| repeat (first | exact keeps_refl _ _ | exact Kept.elim (by assumption) | (refine keeps_setObj' ?_ rfl) | (refine keeps_alloc' ?_) | (refine keeps_grows' ?_ (growsK_elim (by assumption)))))

end EquivLean.Modernize.Cbstm03b.Java
