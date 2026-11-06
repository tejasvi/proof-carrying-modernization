import EquivLean.Modernize.Cbstm03a.Java.RunInv

/-!
# CBSTM03A → Java: `run`'s verification conditions from its segments, and its contract

`run_vc_of`: the `MethodVC` of `run` against `runSpecG g` with the invariants `runInv g`, from the entry path and
the paths of the ten cut points (`CbARun1` … `CbARun4`). `run_sat_of`: its contract given the callee contracts.
`runSpecJ`: the contract without ghost values (`∃ g` in the precondition, `∀ g` in the postcondition).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

/-- The paths of all segments. -/
structure RunSegs (g : RunG) : Prop where
  entry : RunEntryVC g
  c12 : RunCutVC g 12 inv12
  c24 : RunCutVC g 24 inv24
  c37 : RunCutVC g 37 inv37
  c52 : RunCutVC g 52 inv52
  c80 : RunCutVC g 80 inv80
  c117 : RunCutVC g 117 inv117
  c140 : RunCutVC g 140 inv140
  c153 : RunCutVC g 153 inv153
  c168 : RunCutVC g 168 inv168
  c179 : RunCutVC g 179 inv179

set_option maxRecDepth 20000 in
theorem run_vc_of (g : RunG) (h : RunSegs g) :
    MethodVC Gen.prog runCallees.env 1 runRefA (runSpecG g) (runInv g) 300 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · have e := h.entry args σ0 hpre
    unfold runWP at e
    exact e
  · intro p hp fr σ hI
    simp only [runInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have e := h.c12 args σ0 hpre fr σ hI; unfold runWP at e; exact e
    · have e := h.c24 args σ0 hpre fr σ hI; unfold runWP at e; exact e
    · have e := h.c37 args σ0 hpre fr σ hI; unfold runWP at e; exact e
    · have e := h.c52 args σ0 hpre fr σ hI; unfold runWP at e; exact e
    · have e := h.c80 args σ0 hpre fr σ hI; unfold runWP at e; exact e
    · have e := h.c117 args σ0 hpre fr σ hI; unfold runWP at e; exact e
    · have e := h.c140 args σ0 hpre fr σ hI; unfold runWP at e; exact e
    · have e := h.c153 args σ0 hpre fr σ hI; unfold runWP at e; exact e
    · have e := h.c168 args σ0 hpre fr σ hI; unfold runWP at e; exact e
    · have e := h.c179 args σ0 hpre fr σ hI; unfold runWP at e; exact e

theorem run_sat_of (g : RunG) (hV : Valid Gen.prog runCallees.env) (h : RunSegs g) :
    Sat Gen.prog runRefA (runSpecG g) :=
  MethodVC.sat_of_valid hV (run_vc_of g h)

/-- **The contract of `run`**: for inputs described by some ghost values, the `Result` holds `jRunR`'s outputs
for every such description. -/
def runSpecJ : Spec := Spec.of
  (fun args σ => ∃ g, RunPre g args σ)
  (fun args σ r σ' => ∀ g, RunPre g args σ →
     ∃ res, r = some (.ref res) ∧ ResAt σ' res g.F.disp g.F.stmt g.F.html g.F.ab)

theorem runSpecJ_of_ghost {P : Program} {m : MethodRef} (h : ∀ g, Sat P m (runSpecG g)) :
    Sat P m runSpecJ := by
  intro args σ o hpre hm
  obtain ⟨g, hg⟩ := hpre
  cases o with
  | normal r σ' => exact fun g' hg' => h g' args σ (.normal r σ') hg' hm
  | exc e σ' => exact (h g args σ (.exc e σ') hg hm).elim
  | wrong msg => exact (h g args σ (.wrong msg) hg hm).elim

end EquivLean.Modernize.Cbstm03a.Java
