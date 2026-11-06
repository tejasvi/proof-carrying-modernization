import EquivLean.Modernize.Cbtrn02c.Any.JavaRunPL3

/-!
# CBTRN02C → Java: the first visit of the main loop

`j65_init`: after the four work-storage records are built and the counters set, the main loop's
invariant holds with no transaction processed (`G.st 0 = Model.init`).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem G.st_zero (g : G) : g.st 0 = Model.init g.accts g.cats := by simp [G.st]

theorem j65_init {g : G} {σ0 σ : State} {fr : Frame} {lC lK wX wA wC wT : Addr}
    (hin : RunIn g.args σ0 g.trans g.xrefs g.accts g.cats g.clk)
    (hloc : LocsP g σ0 fr lC lK) (f6 : fr.get 6 = some (.ref wX)) (f13 : fr.get 13 = some (.ref wA))
    (f29 : fr.get 29 = some (.ref wC)) (f28 : fr.get 28 = some (.ref wT))
    (f14 : fr.get 14 = some (.int 0#32)) (f4 : fr.get 4 = some (.int 0#32))
    (f9 : fr.get 9 = some (.long 0#64)) (f10 : fr.get 10 = some (.long 0#64))
    (hP : PreL g σ0 σ lC lK)
    (hX : WSObj σ wX xrCls (keysOf CardXrefRecord xrCls))
    (hA : WSObj σ wA acCls (keysOf AccountRecord acCls))
    (hC : WSObj σ wC tcCls (keysOf TranCatBalRecord tcCls))
    (hT : WSObj σ wT trCls (keysOf TranRecord trCls))
    (hFC : WSFill σ wC tcCls (Model.sp 22)) (hFT : WSFill σ wT trCls (Model.sp 20))
    (h1 : lK < wX) (h2 : wX < wA) (h3 : wA < wC) (h4 : wC < wT) (hS : StateP σ0 σ) :
    J65 g g.args σ0 fr σ := by
  obtain ⟨hg, hinits, hstat, hinit⟩ := hS
  have hW := W_init hin hP hX hA hC hT hFC hFT h1 h2 h3 h4 hg
  obtain ⟨a1, a2, a3, a4, cs, hargs, ⟨et1, xs1, h1h, hl1, hf1⟩, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨f32, f0, f16, f31, f8, f11, f12⟩ := hloc
  refine ⟨A0 σ0 lC lK wX wA wC wT, 0, 0#32, 0#32, 0#64, 0#64, et1, xs1,
    ⟨f32, f0, f16, f31, f8, f11, f12, f6, f13, f29, f28⟩, f14, f4, f9, f10, heap_of_grows hg h1h,
    forall2_length hf1, by decide, Nat.zero_le _, Or.inl rfl, by decide, ?_, ?_, hg, hinits, hstat,
    hinit⟩
  · rw [G.st_zero]; rfl
  · rw [G.st_zero]; exact Hide.intro hW

end EquivLean.Modernize.Cbtrn02c.Java
