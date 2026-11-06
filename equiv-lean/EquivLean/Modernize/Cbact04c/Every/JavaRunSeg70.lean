import EquivLean.Modernize.Cbact04c.Every.JavaRunResInit2
import EquivLean.Modernize.Cbact04c.Every.JavaRunSpecEqs

/-!
# CBACT04C → Java, `run`: statements 70–84 (the last strings, the parameters, the loop's start)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg70 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreG g g.args σ0) (h : JI70 g g.args σ0 fr σ)
    (c71 : cuts.lookup 71 = none) (c72 : cuts.lookup 72 = none) (c73 : cuts.lookup 73 = none)
    (c74 : cuts.lookup 74 = none) (c75 : cuts.lookup 75 = none) (c76 : cuts.lookup 76 = none)
    (c77 : cuts.lookup 77 = none) (c78 : cuts.lookup 78 = none) (c79 : cuts.lookup 79 = none)
    (c80 : cuts.lookup 80 = none) (c81 : cuts.lookup 81 = none) (c82 : cuts.lookup 82 = none)
    (c83 : cuts.lookup 83 = none) (c84 : cuts.lookup 84 = none)
    (c85 : cuts.lookup 85 = some (J85 g g.args σ0)) :
    RunWPc g σ0 cuts 70 fr σ := by
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
  unfold RunWPc
  jvc [runSpecG, runC, inlineFuel, Grows, spacesSig, spacesSpec, fixLenSig, fixLenF, argAddr]
  apply j85_init (acctV := acctV) (v17 := v17) ht hres hdisp hw hr hr0 hd0 hw0 hl0 hA0 hd1 hd2 hd3
    (Hide.elim hg') (Hide.elim hin') hT0 htr (Hide.elim hP') (Hide.elim hC')
  case f26 => first | (frame_simp []; done) | (frame_simp []; rfl)
  case f24 => first | (frame_simp []; done) | (frame_simp []; rfl)
  case f25 => first | (frame_simp []; done) | (frame_simp []; rfl)
  case ha => exact ⟨by jomega, fun x hx _ => by chain_simp⟩
  case hi => assumption
  case hy1 => chain_simp
  case hy2 => chain_simp
  case hw' => chain_simp
  all_goals frame_simp [f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f16, f17]

end EquivLean.Modernize.Cbact04c.Java
