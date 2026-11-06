import EquivLean.Modernize.Cbact04c.Every.JavaRunRes232

/-!
# CBACT04C → Java, `run`: statements 232–241 (the DB2 timestamps)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

theorem clk_len_of_pre {g : G} {args : List Value} {σ0 : State} (h : RunPreG g args σ0) :
    g.clk.length = 21 := by
  obtain ⟨-, ⟨b1, b2, b3, b4, q1, c1, -, -, -, -, -, -, -, hl, -⟩, -⟩ := h
  exact hl

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg232 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreG g g.args σ0) (h : J232 g g.args σ0 fr σ)
    (c233 : cuts.lookup 233 = none) (c234 : cuts.lookup 234 = none) (c235 : cuts.lookup 235 = none)
    (c236 : cuts.lookup 236 = none) (c237 : cuts.lookup 237 = none) (c238 : cuts.lookup 238 = none)
    (c239 : cuts.lookup 239 = none) (c240 : cuts.lookup 240 = none) (c241 : cuts.lookup 241 = none)
    (c242 : cuts.lookup 242 = some (J242 g g.args σ0)) :
    RunWPc g σ0 cuts 232 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb, hstop⟩, f3, f11,
    f12, f14, f25, f16, f17, hheap, hrate⟩, hset⟩ := h
  have hcl := clk_len_of_pre hpre
  clear hpre
  obtain ⟨fsT, hT, hset11⟩ := Hide.elim hset
  have hL := Hide.elim hheap
  obtain ⟨-, -, -, -, -, -, -, -, htr, -, hclk⟩ := hL.1
  obtain ⟨c, hcV, hch⟩ := hclk
  obtain ⟨fs0, hT0, hTk, -, -⟩ := id htr
  rw [hT] at hT0
  cases hT0
  obtain ⟨w11, hw11⟩ := hTk "tranOrigTs" (by decide)
  obtain ⟨w12, hw12⟩ := hTk "tranProcTs" (by decide)
  have hinit : Inits σ := hL.1.2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  rw [hcV] at f24
  have hT' := Hide.intro hT
  have hset11' := Hide.intro hset11
  have htr' := Hide.intro htr
  clear hset11 htr hTk hset hL
  unfold RunWPc
  jvc [runSpecG, runC, Grows, fields_get_set, narrow_cls, narrow_long, cp037Str_len, evalDynamic,
    concatRecipe, Native.valueOfArg, Native.valueOfObj, Native.valueOfObjN, Native.nObjStr, Native.primStr,
    JType.isRef]
  all_goals try (exfalso; revert hcond; simp [cp037Str_len, hcl])
  apply j242_of (d := σ.next + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) hn hi0 hstop
  case hheap => exact hheap
  case htcb => exact htcb
  case hT => exact Hide.elim hT'
  case hset => exact Hide.intro ⟨fsT, Hide.elim hT', Hide.elim hset11'⟩
  case hlocs => locs_tac
  case f22 => frame_simp [f22]
  case f6 => frame_simp [f6]
  case f4 => frame_simp [f4]
  case f5 => frame_simp [f5]
  case f3 => frame_simp [f3]
  case f11 => frame_simp [f11]
  case f12 => frame_simp [f12]
  case f14 => frame_simp [f14]
  case f25 => frame_simp [f25]
  case f16 => frame_simp [f16]
  case f17 => frame_simp [f17]
  case hrate => exact hrate
  case hag => exact (agree_setObj_mem (agree_setObj_mem (agree_alloc (agree_alloc (agree_alloc
    (agree_alloc (agree_alloc (agree_alloc (agree_alloc (agree_alloc (agree_alloc
    (agree_refl σ [hp.T]) _) _) _) _) _) _) _) _) _) (List.mem_singleton_self _) _)
    (List.mem_singleton_self _) _)
  case hi2 => rfl
  case hT2 => exact heap_setObj_self' (heap_setObj_self' (heap_of_grows (grows_trans (grows_trans
    (grows_trans (grows_trans (grows_trans (grows_trans (grows_trans (grows_trans (grows_alloc _ _)
    (grows_alloc _ _)) (grows_alloc _ _)) (grows_alloc _ _)) (grows_alloc _ _)) (grows_alloc _ _))
    (grows_alloc _ _)) (grows_alloc _ _)) (grows_alloc _ _)) (Hide.elim hT')))
  case hd =>
    have hne : σ.next + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ hp.T := by jomega
    rw [heap_setObj_other hne, heap_setObj_other hne, State.heap_alloc,
      ite_eq_left (by simp [State.next_alloc]), db2ts_java hcl]
    simp [List.getElem?_eq_getElem, cp037Str_len, hcl]

end EquivLean.Modernize.Cbact04c.Java
