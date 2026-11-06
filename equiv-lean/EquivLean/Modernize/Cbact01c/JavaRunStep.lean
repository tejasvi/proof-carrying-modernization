import EquivLean.Modernize.Cbact01c.JavaRunState

/-!
# CBACT01C → Java: one record of the read loop, on the model's side

`mst vals (k + 1)` is one `Model.step` more; the texts the record methods write for the record
`v` are the model's lines; the outputs grow by them (`outsB_step`).
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

theorem mst_succ {vals : List (List EquivLean.Cobol.Rec.FVal)} {k : Nat}
    {v : List EquivLean.Cobol.Rec.FVal} (hv : vals[k]? = some v) :
    mst vals (k + 1) = Model.step (mst vals k) v := by
  unfold mst
  rw [List.take_succ, hv, Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem mst_length {vals : List (List EquivLean.Cobol.Rec.FVal)} :
    mst vals vals.length = vals.foldl Model.step Model.init := by
  unfold mst; rw [List.take_length]

theorem forall2_append' {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β} {c : List α} {d : List β}, Forall2 R a b → Forall2 R c d →
      Forall2 R (a ++ c) (b ++ d)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h' => .cons h (forall2_append' t h')

/-- Line `i < 12` of `displayAcctRecord`, as the model's line. -/
theorem dispLine_glue {σ : Jimple.State} {c : Addr} {v : List EquivLean.Cobol.Rec.FVal}
    (h : AcctAt σ c v) (i : Nat) (hi : i < 12) :
    dispLine σ c i = jline ((Model.lines v).getD i []) := by
  have hl : (Model.lines v).length = 15 := by simp [Model.lines]
  rw [dispLine, dispLines_glue h, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_take, if_pos hi, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

theorem fixStr_nil_drop : (fixStr [] 20).drop 8 = fixStr [] 12 := by
  rw [fixStr_nil, fixStr_nil, List.drop_replicate]

/-- The facts of the loop invariant before the first record: the start line only. -/
theorem runData_init {σ0 σ : Jimple.State} {vals : List (List EquivLean.Cobol.Rec.FVal)} {x : Addr}
    (hx : σ.heap x = some (.str (JStr.ofString "START OF EXECUTION OF PROGRAM CBACT01C")))
    (hb : σ0.next + 4 < x) :
    RunData σ0 vals σ 0 0#64 (fixStr [] 20) [.ref x] [] [] [] := by
  refine ⟨rfl, fixStr_length _ _, fixStr_nil_drop, ?_, .nil, .nil, .nil⟩
  simp only [mst, List.take_zero, List.foldl_nil, Model.init, List.map_cons, List.map_nil]
  refine .cons ⟨x, rfl, hb, ?_⟩ .nil
  rw [hx, jline_txt _ (by decide)]

/-- The facts of the loop invariant survive steps that change nothing above the lists. -/
theorem RunData.grows {σ0 σ σ' : Jimple.State} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    {k : Nat} {cd : I64} {s : JStr} {ys1 ys2 ys3 ys4 : List Value}
    (hg : GrowsAbove (σ0.next + 4) σ σ') (h : RunData σ0 vals σ k cd s ys1 ys2 ys3 ys4) :
    RunData σ0 vals σ' k cd s ys1 ys2 ys3 ys4 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.grows hg⟩

/-- At the end of the file: the outputs of `Model.run`, with the end line. -/
theorem runPost_of {σ0 σ σ' : Jimple.State} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    {cd : I64} {s : JStr} {ys1 ys2 ys3 ys4 : List Value} {fs : List (FieldKey × Value)} {y : Addr}
    {m1 m2 m3 m4 : Nat}
    (h : RunData σ0 vals σ vals.length cd s ys1 ys2 ys3 ys4) (hg : GrowsAbove (σ0.next + 4) σ σ')
    (hy : σ'.heap y = some (.str (JStr.ofString "END OF EXECUTION OF PROGRAM CBACT01C")))
    (hyb : σ0.next + 4 < y)
    (hR : σ'.heap σ0.next = some (.plain resCls fs))
    (hR1 : Fields.get fs (resCls, "displays") = some (.ref (σ0.next + 1)))
    (hR2 : Fields.get fs (resCls, "outFileWrites") = some (.ref (σ0.next + 2)))
    (hR3 : Fields.get fs (resCls, "arryFileWrites") = some (.ref (σ0.next + 3)))
    (hR4 : Fields.get fs (resCls, "vbrcFileWrites") = some (.ref (σ0.next + 4)))
    (hR5 : Fields.get fs (resCls, "abended") = some (.int 0))
    (hl1 : σ'.heap (σ0.next + 1) = some (.list .arrayList (ys1 ++ [.ref y]) m1))
    (hl2 : σ'.heap (σ0.next + 2) = some (.list .arrayList ys2 m2))
    (hl3 : σ'.heap (σ0.next + 3) = some (.list .arrayList ys3 m3))
    (hl4 : σ'.heap (σ0.next + 4) = some (.list .arrayList ys4 m4)) :
    RunPost vals (some (.ref σ0.next)) σ' := by
  obtain ⟨-, -, -, hO⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := hO.grows hg
  rw [mst_length] at h1 h2 h3 h4
  refine ⟨σ0.next, fs, rfl, hR, ⟨_, _, _, _, hR1, hl1, ?_⟩, ⟨_, _, _, _, hR2, hl2, ?_⟩,
    ⟨_, _, _, _, hR3, hl3, ?_⟩, ⟨_, _, _, _, hR4, hl4, ?_⟩, hR5⟩
  · simp only [Model.run, List.map_append, List.map_cons, List.map_nil]
    refine forall2_append' (forall2_mono' (fun _ _ h => h.strAt) h1) (.cons ⟨y, rfl, ?_⟩ .nil)
    rw [hy, jline_txt _ (by decide)]
  · exact forall2_mono' (fun _ _ h => h.recAt) h2
  · exact forall2_mono' (fun _ _ h => h.recOccAt) h3
  · exact forall2_mono' (fun _ _ h => h.strAt) h4

/-- One record read: the facts of the loop invariant after it, from the outputs it adds. -/
theorem runData_step {σ0 σ σ' : Jimple.State} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    {k : Nat} {cd cd' : I64} {s s' : JStr} {ys1 ys2 ys3 ys4 L1 L4 : List Value} {o2 o3 : Value}
    {v : List EquivLean.Cobol.Rec.FVal}
    (hD : RunData σ0 vals σ k cd s ys1 ys2 ys3 ys4) (hv : vals[k]? = some v)
    (hG : GrowsAbove (σ0.next + 4) σ σ')
    (hcd : cd' = BitVec.ofInt 64 (if Model.aCycDebit v = 0 then 252500 else (mst vals k).cd))
    (hs1 : s'.length = 20) (hs2 : s'.drop 8 = fixStr [] 12)
    (h1 : Forall2 (JStrB σ' (σ0.next + 4)) L1 ((Model.lines v).map jline))
    (h2 : JRecB OutAcctRec outCls σ' (σ0.next + 4) o2
      (Model.outVals v (if Model.aCycDebit v = 0 then 252500 else (mst vals k).cd)))
    (h3 : JRecOccB ArrArrayRec arrCls σ' (σ0.next + 4) o3 (Model.arrVals v))
    (h4 : Forall2 (JStrB σ' (σ0.next + 4)) L4
      [jline (Model.VbrcRec1.textS (Model.vb1 v)), jline (Model.VbrcRec2.textS (Model.vb2 v))]) :
    RunData σ0 vals σ' (k + 1) cd' s' (ys1 ++ L1) (ys2 ++ [o2]) (ys3 ++ [o3]) (ys4 ++ L4) := by
  obtain ⟨-, -, -, hO⟩ := hD
  obtain ⟨g1, g2, g3, g4⟩ := hO.grows hG
  refine ⟨?_, hs1, hs2, ?_, ?_, ?_, ?_⟩
  · rw [hcd, mst_succ hv]; rfl
  · rw [mst_succ hv]; simp only [Model.step, List.map_append]; exact forall2_append' g1 h1
  · rw [mst_succ hv]; simp only [Model.step]; exact forall2_append' g2 (.cons h2 .nil)
  · rw [mst_succ hv]; simp only [Model.step]; exact forall2_append' g3 (.cons h3 .nil)
  · rw [mst_succ hv]; simp only [Model.step, List.map_append, List.map_cons, List.map_nil]
    exact forall2_append' g4 h4

theorem GrowsAbove.refl (B : Addr) (σ : Jimple.State) : GrowsAbove B σ σ :=
  ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

theorem GrowsAbove.of_alloc (B : Addr) (σ : Jimple.State) (o : Obj) : GrowsAbove B σ (σ.alloc o).2 :=
  ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun x _ hx => State.heap_alloc_of_lt hx o⟩

theorem GrowsAbove.of_setObj {B L : Addr} (σ : Jimple.State) (o : Obj) (hL : L ≤ B) :
    GrowsAbove B σ (σ.setObj L o) :=
  ⟨by rw [State.next_setObj]; exact Nat.le_refl _, fun x hb _ => by
    rw [State.heap_setObj, if_neg (by intro h; subst h; exact absurd hL (Nat.not_le.mpr hb))]⟩

theorem toNat_of_toInt_eq {i : I32} {n : Nat} (h : i.toInt = n) : i.toNat = n := by
  have := BitVec.toInt_eq_toNat_cond i
  split at this <;> omega

/-- The `OutAcctRec` of a record method survives steps that change nothing above `B`. -/
theorem OutRecJ.grows {B : Addr} {σ' σ'' σ0 : Jimple.State} {o c nb : Addr} {dt : JStr} {cd : I64}
    (hg : GrowsAbove B σ' σ'') (hb : B < nb) (ho : B < o) (h : OutRecJ σ' o σ0 c dt cd nb) :
    OutRecJ σ'' o σ0 c dt cd nb := by
  obtain ⟨fs, hfs, g0, ⟨x1, g1, hb1, hx1⟩, g2, g3, g4, ⟨x5, g5, hb5, hx5⟩, ⟨x6, g6, hb6, hx6⟩,
    ⟨x7, g7, hb7, hx7⟩, g8, g9, ⟨x10, g10, hb10, hx10⟩⟩ := h
  exact ⟨fs, hg.heap ho hfs, g0, ⟨x1, g1, hb1, hg.heap (Nat.lt_of_lt_of_le hb hb1) hx1⟩, g2, g3, g4,
    ⟨x5, g5, hb5, hg.heap (Nat.lt_of_lt_of_le hb hb5) hx5⟩,
    ⟨x6, g6, hb6, hg.heap (Nat.lt_of_lt_of_le hb hb6) hx6⟩,
    ⟨x7, g7, hb7, hg.heap (Nat.lt_of_lt_of_le hb hb7) hx7⟩, g8, g9,
    ⟨x10, g10, hb10, hg.heap (Nat.lt_of_lt_of_le hb hb10) hx10⟩⟩

/-- The `ArrArrayRec` of a record method survives steps that change nothing above `B`. -/
theorem ArrRecJ.grows {B : Addr} {σ' σ'' σ0 : Jimple.State} {o c nb : Addr}
    (hg : GrowsAbove B σ' σ'') (hb : B < nb) (ho : B < o) (h : ArrRecJ σ' o σ0 c nb) :
    ArrRecJ σ'' o σ0 c nb := by
  obtain ⟨fs, hfs, g0, ⟨a1, et1, g1, hb1, ha1⟩, ⟨a2, et2, g2, hb2, ha2⟩, ⟨x, g3, hbx, hx⟩⟩ := h
  exact ⟨fs, hg.heap ho hfs, g0, ⟨a1, et1, g1, hb1, hg.heap (Nat.lt_of_lt_of_le hb hb1) ha1⟩,
    ⟨a2, et2, g2, hb2, hg.heap (Nat.lt_of_lt_of_le hb hb2) ha2⟩,
    ⟨x, g3, hbx, hg.heap (Nat.lt_of_lt_of_le hb hbx) hx⟩⟩

/-- The cycle debit of the record: its `long`, zero exactly when the model's is. -/
theorem cycDebit_of {σ0 : Jimple.State} {c : Addr} {v : List EquivLean.Cobol.Rec.FVal}
    {fsc : List (FieldKey × Value)} {dbt : I64} (hA : AcctAt σ0 c v)
    (hc : σ0.heap c = some (.plain acctCls fsc))
    (hf : Fields.get fsc (acctCls, "acctCurrCycDebit") = some (.long dbt)) :
    dbt = BitVec.ofInt 64 (Model.aCycDebit v) ∧ (Model.aCycDebit v).natAbs < 10 ^ 12 := by
  obtain ⟨n0, n2, n3, n4, n8, n9, b1, b5, b6, b7, b10, b11, b12, rfl, -, -, -, -, -, -, e9,
    -, -, -, -, -, -, -, -, -, -, -, -, h9, -⟩ := acctAt_flat hA
  rw [fieldLong_of hc hf] at e9
  exact ⟨e9, h9⟩

theorem ofInt64_eq_zero {n : Int} (h : n.natAbs < 10 ^ 12) : (BitVec.ofInt 64 n = 0#64) ↔ n = 0 := by
  constructor
  · intro he
    have := congrArg BitVec.toInt he
    rw [toInt_ofInt64 (by omega)] at this
    simpa using this
  · rintro rfl; rfl

/-- The date after `cobdatft`: twenty characters, the last twelve spaces. -/
theorem cobOut_date {i s : JStr} (hi : 10 ≤ i.length) (hs1 : s.length = 20)
    (hs2 : s.drop 8 = fixStr [] 12) :
    (cobOut i s).length = 20 ∧ (cobOut i s).drop 8 = fixStr [] 12 := by
  have hs : s = s.take 8 ++ fixStr [] 12 := by rw [← hs2, List.take_append_drop]
  rw [hs, cobOut_spaces (by simp [hs1])]
  have h8 := cob8_length hi
  exact ⟨by rw [List.length_append, h8, fixStr_length],
    by rw [List.drop_left' h8]⟩

theorem ite_lt_of {α : Sort _} {a b : Nat} {x y : α} (h : a < b) :
    (if a < b then x else y) = x := if_pos h

/-- A heap read through the states of the symbolic execution: allocations, updates and the
callees' frame conditions among the hypotheses; address facts by `jomega`. -/
macro "rchain" : tactic => `(tactic| (
  simp (config := { decide := true }) (disch := jomega) only [State.heap_alloc, State.heap_setObj,
    State.next_alloc, State.next_setObj, ite_true, ite_false, reduceIte, Jimple.ite_nat_ne,
    ite_lt_of, State.heap_alloc_of_lt, State.heap_setObj_of_lt, jstrLit, resCls, *]
  try rfl))

end EquivLean.Modernize.Cbact01c.Java
