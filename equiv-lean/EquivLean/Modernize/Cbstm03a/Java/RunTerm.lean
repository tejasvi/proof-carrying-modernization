import EquivLean.Modernize.Cbstm03a.Java.RunVC

/-!
# CBSTM03A → Java: `run`'s termination VC (thin, with variants), by segment

`TermVC.of_thin` turns `run`'s partial-correctness VC (`run_vc_of`) and a thin VC with the same invariants into its
termination VC. The thin VC: from each cut point, every path to a cut point decreases the variant `runVar`, and no
call is stuck (callee postconditions are assumed, preconditions come from the partial-correctness VC).

`runVar`: one measure for all cut points, ordered by phase: the four text loops (`X12 > X24 > X37 > X52`, each plus
the entries left), the load loop (`X80` plus the records left, read from `trnxSt[0]`), then per cross-reference
record (`(2^31 − xrefSt[0]) · M`): the customer search (`C3` plus the keys left), the account search (`C4` plus
the texts left), the cards loop (`K` per card left, `+ 1`) and the transactions loop (the transactions left
within the current card's `K`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

/-- The `int` in local `i` (0 otherwise). -/
def locI (fr : Frame) (i : Nat) : Int :=
  match fr.get i with
  | some (.int v) => v.toInt
  | _ => 0

/-- The `long` in local `i` (0 otherwise). -/
def locL (fr : Frame) (i : Nat) : Int :=
  match fr.get i with
  | some (.long v) => v.toInt
  | _ => 0

/-- The first element of the `int[]` in local `i` (0 otherwise). -/
def arr0 (σ : State) (fr : Frame) (i : Nat) : Int :=
  match fr.get i with
  | some (.ref a) =>
    match σ.heap a with
    | some (.array _ (.int v :: _)) => v.toInt
    | _ => 0
  | _ => 0

/-! The weights: `N` bounds every count, `K` the transactions of a card (`cnt < 10000`), `C4` the cards loop
(`crCnt < 10000`), `C3` the account search, `M` one cross-reference record; `X80` the load loop, then the text
loops. -/
def vN : Nat := 2147483648
def vK : Nat := 10002
def vC4 : Nat := 10001 * vK + 2
def vC3 : Nat := vC4 + vN + 1
def vM : Nat := vC3 + vN + 1
def vX80 : Nat := vN * vM + 1
def vX52 : Nat := vX80 + vN + 1
def vX37 : Nat := vX52 + vN + 1
def vX24 : Nat := vX37 + vN + 1
def vX12 : Nat := vX24 + vN + 1

/-- The variant of `run` at cut point `pc`. -/
def runVar (pc : Nat) (_args : List Value) (_σ0 : State) (fr : Frame) (σ : State) : Nat :=
  match pc with
  | 12 => vX12 + ((vN : Int) - locI fr 28).toNat
  | 24 => vX24 + ((vN : Int) - locI fr 29).toNat
  | 37 => vX37 + ((vN : Int) - locI fr 30).toNat
  | 52 => vX52 + ((vN : Int) - locI fr 26).toNat
  | 80 => vX80 + ((vN : Int) - arr0 σ fr 1).toNat
  | 117 => ((vN : Int) - arr0 σ fr 2).toNat * vM
  | 140 => ((vN : Int) - arr0 σ fr 2).toNat * vM + vC3 + (locI fr 27 - locI fr 26).toNat
  | 153 => ((vN : Int) - arr0 σ fr 2).toNat * vM + vC4 + (locI fr 28 - locI fr 26).toNat
  | 168 => ((vN : Int) - arr0 σ fr 2).toNat * vM + (locL fr 18 + 1 - locL fr 17).toNat * vK + 1
  | 179 => ((vN : Int) - arr0 σ fr 2).toNat * vM + (locL fr 18 - locL fr 17).toNat * vK +
      (locL fr 19 + 2 - locL fr 22).toNat + 1
  | _ => 0

/-- The thin paths of `run` from statement `pc`, the cut points asserting a variant below `v`. -/
@[irreducible] def runThinWP (g : RunG) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State)
    (v : Nat) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA
    ((runInv g).map fun q => (q.1, fun fr' σ' => runVar q.1 args σ0 fr' σ' < v)) (fun _ => True) 300 pc fr σ

/-- The thin entry path (statements 0 … 12; the cut point asserts nothing). -/
def RunThinEntry (g : RunG) : Prop :=
  ∀ args σ0, RunPre g args σ0 →
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA
      ((runInv g).map fun p => (p.1, fun _ _ => True)) (fun _ => True) 300 0 (Frame.init true args) σ0

/-- The thin paths from cut point `pc` with invariant `I`: the variant decreases. -/
def RunThinCut (g : RunG) (pc : Nat) (I : RunG → List Value → State → Frame → State → Prop) : Prop :=
  ∀ args σ0, RunPre g args σ0 → ∀ fr σ, I g args σ0 fr σ →
    runThinWP g args σ0 pc fr σ (runVar pc args σ0 fr σ)

/-- The thin paths of all segments. -/
structure RunThinSegs (g : RunG) : Prop where
  entry : RunThinEntry g
  c12 : RunThinCut g 12 inv12
  c24 : RunThinCut g 24 inv24
  c37 : RunThinCut g 37 inv37
  c52 : RunThinCut g 52 inv52
  c80 : RunThinCut g 80 inv80
  c117 : RunThinCut g 117 inv117
  c140 : RunThinCut g 140 inv140
  c153 : RunThinCut g 153 inv153
  c168 : RunThinCut g 168 inv168
  c179 : RunThinCut g 179 inv179

set_option maxRecDepth 20000 in
theorem run_thin_of (g : RunG) (h : RunThinSegs g) :
    ThinVC Gen.prog runCallees.env 1 runRefA (runSpecG g) (runInv g) runVar 300 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · exact h.entry args σ0 hpre
  · intro p hp fr σ hI
    simp only [runInv, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have e := h.c12 args σ0 hpre fr σ hI; unfold runThinWP at e; exact e
    · have e := h.c24 args σ0 hpre fr σ hI; unfold runThinWP at e; exact e
    · have e := h.c37 args σ0 hpre fr σ hI; unfold runThinWP at e; exact e
    · have e := h.c52 args σ0 hpre fr σ hI; unfold runThinWP at e; exact e
    · have e := h.c80 args σ0 hpre fr σ hI; unfold runThinWP at e; exact e
    · have e := h.c117 args σ0 hpre fr σ hI; unfold runThinWP at e; exact e
    · have e := h.c140 args σ0 hpre fr σ hI; unfold runThinWP at e; exact e
    · have e := h.c153 args σ0 hpre fr σ hI; unfold runThinWP at e; exact e
    · have e := h.c168 args σ0 hpre fr σ hI; unfold runThinWP at e; exact e
    · have e := h.c179 args σ0 hpre fr σ hI; unfold runThinWP at e; exact e

/-- `run`'s termination VC at rank `r` (the callee contracts all of lower rank). -/
theorem run_termvc_of (g : RunG) {rank : MethodSig → Nat} {r : Nat}
    (hΓ : runCallees.env.below rank r = runCallees.env) (h : RunSegs g) (ht : RunThinSegs g) :
    TermVC Gen.prog runCallees.env rank r 1 runRefA (runSpecG g) ((runInv g).withVariants runVar) 300 :=
  TermVC.of_thin hΓ (run_vc_of g h) (run_thin_of g ht)

end EquivLean.Modernize.Cbstm03a.Java
