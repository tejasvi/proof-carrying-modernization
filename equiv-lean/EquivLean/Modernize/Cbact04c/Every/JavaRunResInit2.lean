import EquivLean.Modernize.Cbact04c.Every.JavaRunResInit

/-!
# CBACT04C → Java, `run`: the loop head before the first category record (cut 85, record 0)
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-- The cut at 85 for record 0, after statements 70–84 (no object of `σ` changed). -/
theorem j85_init {g : G} {σ0 σ σ' : State} {fr' : Frame} {res ld lw lr A T y1 y2 w : Addr}
    {acctV v17 : Value} {P C : JStr}
    (ht : Hide (TableAt σ A g.accts [])) (hres : Hide (ResAt σ ⟨res, ld, lw, lr, A, 0, .null, .null⟩))
    (hdisp : Hide (DispAt σ ld (Model.init g.accts).disp))
    (hw : Hide (RecsAt TranRecord "Cbact04c$TranRecord" σ lw [] []))
    (hr : Hide (RecsAt AccountRecord "Cbact04c$AccountRecord" σ lr [] []))
    (hr0 : σ0.next ≤ res) (hd0 : σ0.next ≤ ld) (hw0 : σ0.next ≤ lw) (hl0 : σ0.next ≤ lr)
    (hA0 : σ0.next ≤ A) (hd1 : ld ≠ lw) (hd2 : ld ≠ lr) (hd3 : lw ≠ lr) (hg : Grows σ0 σ)
    (hin : Inits σ) (hT0 : σ0.next ≤ T) (htr : Hide (TranOk σ T))
    (hP : cp037Str (Model.strOf (g.link.getD 1 default)) = P) (hC : cp037Str g.clk = C)
    (ha : Agree σ σ' []) (hi : σ'.inits = σ.inits)
    (hy1 : σ'.heap y1 = some (.str P)) (hy2 : σ'.heap y2 = some (.str C))
    (hw' : σ'.heap w = some (.str (spJ 11)))
    (f1 : fr'.get 1 = some (.ref g.a1)) (f36 : fr'.get 36 = some (.ref g.a2))
    (f40 : fr'.get 40 = some (.ref g.a3)) (f8 : fr'.get 8 = some (.ref g.a4))
    (f37 : fr'.get 37 = some (.ref g.p1)) (f10 : fr'.get 10 = some (.ref res))
    (f19 : fr'.get 19 = some (.int (BitVec.ofNat 32 g.tcat.length)))
    (f20 : fr'.get 20 = some (.int (BitVec.ofNat 32 g.xrefs.length)))
    (f21 : fr'.get 21 = some (.int (BitVec.ofNat 32 g.discs.length)))
    (f41 : fr'.get 41 = some (.ref A)) (f38 : fr'.get 38 = some (.ref T))
    (f26 : fr'.get 26 = some (.ref y1)) (f24 : fr'.get 24 = some (.ref y2))
    (f22 : fr'.get 22 = some (.int 0#32)) (f12 : fr'.get 12 = some (.long 0#64))
    (f3 : fr'.get 3 = some (.int 1#32)) (f14 : fr'.get 14 = some (.long 0#64))
    (f25 : fr'.get 25 = some (.ref w)) (f16 : fr'.get 16 = some acctV)
    (f17 : fr'.get 17 = some v17) (f4 : fr'.get 4 = some (.int 0#32))
    (f5 : fr'.get 5 = some (.int 0#32)) :
    J85 g g.args σ0 fr' σ' := by
  have hn := noStr_nil σ
  have hz : (0#32 : I32).toInt.toNat = 0 := by decide
  have hMW : ∀ (cls : ClassName), ∀ a ∈ ([] : List Addr), a ∈ ([] : List Addr) ∨
      ∀ fs, σ.heap a ≠ some (.plain cls fs) := fun _ _ h => absurd h List.not_mem_nil
  obtain ⟨wxs, wm, hlw, hwx, -⟩ := Hide.elim hw
  cases hwx
  refine ⟨0#32, ⟨res, ld, lw, lr, A, T, .ref y1, .ref y2⟩, acctV, v17, .ref w, by decide,
    by simp, ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩, f22, ?_, ?_, ?_, f25,
    f16, f17, f4, f5, ?_⟩
  · rw [hz, G.st_zero]; exact f12
  · rw [hz, G.st_zero]; exact f3
  · rw [hz, G.st_zero]; exact f14
  rw [hz, G.st_zero]
  refine ⟨?_, rfl⟩
  exact Hide.intro ⟨⟨grows_trans hg ⟨ha.1, fun x hx => ha.2 x hx List.not_mem_nil⟩,
    inits_of_eq hi hin, ⟨hr0, hd0, hw0, hl0, hA0, hT0, hd1, hd2, hd3⟩,
    resAt_agree (resAt_congr (Hide.elim hres)) ha List.not_mem_nil,
    dispAt_agree (Hide.elim hdisp) ha hn List.not_mem_nil,
    ⟨[], wm, by rw [ha.2 lw (State.lt_next_of_heap hlw) List.not_mem_nil, hlw], .nil,
      fun _ h => absurd h List.not_mem_nil⟩,
    recsAt_agree (Hide.elim hr) ha hn List.not_mem_nil (hMW _),
    tableAt_agree (Hide.elim ht) ha hn List.not_mem_nil (hMW _),
    tranOk_agree (Hide.elim htr) ha hn List.not_mem_nil,
    ⟨y1, rfl, by rw [hy1, ← hP]; rfl⟩, ⟨y2, rfl, by rw [hy2, ← hC]⟩⟩,
    fun h => absurd h (by simp [Model.init]), fun h => absurd h (by simp [Model.init]),
    ⟨w, rfl, hw'⟩, fun h => absurd h (by simp [Model.init])⟩

end EquivLean.Modernize.Cbact04c.Java
