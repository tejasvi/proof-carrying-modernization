-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermSeg70.lean (sha256 f56dbdc3d2d46e62...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaRunSeg70
import EquivLean.Modernize.Cbact04c.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg70`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_tseg70 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (hpre : RunPreG g g.args σ0) (h : JI70 g g.args σ0 fr σ)
    (c71 : cuts.lookup 71 = none) (c72 : cuts.lookup 72 = none) (c73 : cuts.lookup 73 = none)
    (c74 : cuts.lookup 74 = none) (c75 : cuts.lookup 75 = none) (c76 : cuts.lookup 76 = none)
    (c77 : cuts.lookup 77 = none) (c78 : cuts.lookup 78 = none) (c79 : cuts.lookup 79 = none)
    (c80 : cuts.lookup 80 = none) (c81 : cuts.lookup 81 = none) (c82 : cuts.lookup 82 = none)
    (c83 : cuts.lookup 83 = none) (c84 : cuts.lookup 84 = none)
    (c85 : cuts.lookup 85 = some (fun fr' σ' => runVs B 85 g.args σ0 fr' σ' < runVs B 70 g.args σ0 fr σ)) :
    RunThinWPc g σ0 cuts 70 fr σ := by
  obtain ⟨res, ld, lw, lr, A, acctV, T, ⟨f1, f36, f40, f8, f37, f24, f10, f19, f20, f21, f41, ht,
    hres, hdisp, hw, hr, hr0, hd0, hw0, hl0, hA0, hd1, hd2, hd3, hg, hin⟩, f16, f38, hT0, htr, v17,
    f17⟩ := h
  obtain ⟨-, ⟨b1, b2, b3, b4, q1, c1, hargs, -, -, -, -, hext, hclk, hcl, -, -, -, -, hvl, -⟩, -⟩ :=
    hpre
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨px, fsP, hpx, hpxh, hpf⟩ := jrec_obj hext
  cases hpx
  obtain ⟨pd, hpd, hpds⟩ := jfield_str hpf hvl (i := 1) (by decide) (j := false) (by decide)
  have hpdl := (valid_str hvl (i := 1) (by decide) (j := false) (by decide)).2
  rw [show (ExternalParms.fields.getD 1 default).jname = "parmDate" from rfl] at hpd
  obtain ⟨cx, hcx, hcxh⟩ := hclk
  cases hcx
  have hpxh' := heap_of_grows hg hpxh
  have hpds' := heap_of_grows hg hpds
  have hcxh' := heap_of_grows hg hcxh
  have hpl : (cp037Str (Model.strOf (g.link.getD 1 default))).length = 10 := by
    rw [cp037Str_len, hpdl]; rfl
  have hcl' : (cp037Str g.clk).length = 21 := by rw [cp037Str_len, hcl]
  generalize hP : cp037Str (Model.strOf (g.link.getD 1 default)) = P at hpds' hpl
  generalize hC : cp037Str g.clk = C at hcxh' hcl'
  have hP' := Hide.intro hP
  have hC' := Hide.intro hC
  have hg' := Hide.intro hg
  have hin' := Hide.intro hin
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hin
  clear hP hC hg hext hpf hvl hpdl hpxh hpds hcxh hcl
  unfold RunThinWPc
  jvc [runSpecG, runC, inlineFuel, Grows, spacesSig, spacesSpec, fixLenSig, fixLenF, argAddr, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
