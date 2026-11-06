import EquivLean.Modernize.Cbact04c.JavaRunRes224

/-!
# CBACT04C → Java, `run`: closing the cut at 242 (the DB2 timestamps)
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

theorem cp037Str_len (bs : List UInt8) : (cp037Str bs).length = bs.length := by
  simp [cp037Str]

set_option maxRecDepth 100000 in
theorem cp037Unit_96 : cp037Unit 96 = 45#16 := by decide
set_option maxRecDepth 100000 in
theorem cp037Unit_75 : cp037Unit 75 = 46#16 := by decide
set_option maxRecDepth 100000 in
theorem cp037Unit_240 : cp037Unit 240 = 48#16 := by decide

theorem take_four {α : Type} (l : List α) (h : 4 ≤ l.length) :
    l.take 4 = [l[0]'(by omega), l[1]'(by omega), l[2]'(by omega), l[3]'(by omega)] := by
  match l, h with
  | a :: b :: c :: d :: _, _ => rfl

theorem drop_take_two {α : Type} (l : List α) (m : Nat) (h : m + 2 ≤ l.length) :
    (l.drop m).take 2 = [l[m]'(by omega), l[m + 1]'(by omega)] := by
  induction m generalizing l with
  | zero =>
    match l, h with
    | a :: b :: _, _ => rfl
  | succ m ih =>
    match l, h with
    | a :: t, h =>
      simp only [List.drop_succ_cons, List.getElem_cons_succ]
      exact ih t (by simp at h; omega)

/-- `Z-GET-DB2-FORMAT-TIMESTAMP` of a 21-character clock reading is what `run` concatenates. -/
theorem db2ts_java {c : List UInt8} (hc : c.length = 21) :
    cp037Str (CardDemo.Cbact04c.db2ts c) =
      [(cp037Str c)[0]'(by simp [cp037Str, hc]), (cp037Str c)[1]'(by simp [cp037Str, hc]),
        (cp037Str c)[2]'(by simp [cp037Str, hc]), (cp037Str c)[3]'(by simp [cp037Str, hc]), 45#16,
        (cp037Str c)[4]'(by simp [cp037Str, hc]), (cp037Str c)[5]'(by simp [cp037Str, hc]), 45#16,
        (cp037Str c)[6]'(by simp [cp037Str, hc]), (cp037Str c)[7]'(by simp [cp037Str, hc]), 45#16,
        (cp037Str c)[8]'(by simp [cp037Str, hc]), (cp037Str c)[9]'(by simp [cp037Str, hc]), 46#16,
        (cp037Str c)[10]'(by simp [cp037Str, hc]), (cp037Str c)[11]'(by simp [cp037Str, hc]), 46#16,
        (cp037Str c)[12]'(by simp [cp037Str, hc]), (cp037Str c)[13]'(by simp [cp037Str, hc]), 46#16,
        (cp037Str c)[14]'(by simp [cp037Str, hc]), (cp037Str c)[15]'(by simp [cp037Str, hc]),
        48#16, 48#16, 48#16, 48#16] := by
  unfold CardDemo.Cbact04c.db2ts
  rw [take_four c (by omega), drop_take_two c 4 (by omega), drop_take_two c 6 (by omega),
    drop_take_two c 8 (by omega), drop_take_two c 10 (by omega), drop_take_two c 12 (by omega),
    drop_take_two c 14 (by omega)]
  simp only [cp037Str, List.map_append, List.map_cons, List.map_nil, List.getElem_map,
    cp037Unit_96, cp037Unit_75, cp037Unit_240, List.cons_append, List.nil_append]

/-- The cut at 242: both timestamps of `T` hold the DB2 timestamp of the clock. -/
theorem j242_of {g : G} {σ0 σ σ2 : State} {fr' : Frame} {i : I32} {hp : Hp}
    {tcbV acctV xrefV lastV : Value} {fsT : List (FieldKey × Value)} {d : Addr}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt)
    (hheap : Hide (LoopHeap g σ0 σ hp (sel g i.toInt.toNat) acctV xrefV lastV))
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ tcbV
      (g.trec i.toInt.toNat)))
    (hT : σ.heap hp.T = some (.plain "Cbact04c$TranRecord" fsT))
    (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some tcbV)
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32))
    (f11 : fr'.get 11 = some (.long (BitVec.ofInt 64 (amtOf g i.toInt.toNat))))
    (f12 : fr'.get 12 = some (.long (BitVec.ofInt 64 (totOf g i.toInt.toNat))))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (kOf g i.toInt.toNat))))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some acctV)
    (f17 : fr'.get 17 = some xrefV)
    (hrate : rateOf g i.toInt.toNat ≠ 0)
    (hset : Hide (TranSet σ hp.T 11 (tvals g i.toInt.toNat)))
    (hag : Agree σ σ2 [hp.T]) (hi2 : σ2.inits = σ.inits)
    (hT2 : σ2.heap hp.T = some (.plain "Cbact04c$TranRecord"
      (Fields.set (Fields.set fsT ("Cbact04c$TranRecord", "tranOrigTs") (.ref d))
        ("Cbact04c$TranRecord", "tranProcTs") (.ref d))))
    (hd : σ2.heap d = some (.str (cp037Str (CardDemo.Cbact04c.db2ts g.clk)))) :
    J242 g g.args σ0 fr' σ2 := by
  have hL := Hide.elim hheap
  obtain ⟨-, -, -, -, -, -, -, -, htr, -⟩ := hL.1
  have hTstr : ∀ x s, σ.heap x = some (.str s) → x ∉ [hp.T] := by
    intro x s hx hm; rw [List.mem_singleton] at hm; subst hm; rw [hT] at hx; cases hx
  have hok2 : TranOk σ2 hp.T := by
    obtain ⟨fs0, h1, h2, ⟨d0, s, h3, h4, h5, h6⟩, ⟨f, h7, h8⟩⟩ := htr
    rw [hT] at h1
    cases h1
    refine ⟨_, hT2, fun k hk => ?_, ⟨d0, s, ?_, ?_, h5, h6⟩, ⟨f, ?_, ?_⟩⟩
    · simp only [fields_get_set]
      split
      · exact ⟨_, rfl⟩
      split
      · exact ⟨_, rfl⟩
      · exact h2 k hk
    · simp only [fields_get_set]; simpa using h3
    · rw [hag.2 d0 (State.lt_next_of_heap h4) (hTstr d0 _ h4), h4]
    · simp only [fields_get_set]; simpa using h7
    · rw [hag.2 f (State.lt_next_of_heap h8) (hTstr f _ h8), h8]
  have hL2 := loopHeap_agreeT hL hT hag hok2 hi2
  have hn2' : NoStr σ [hp.T] := fun w hw' st hst => hTstr w st hst hw'
  have htcb2 : JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ2 tcbV (g.trec i.toInt.toNat) := by
    have hr := Hide.elim htcb
    obtain ⟨x, fsx, hx, hxh, -⟩ := id hr
    subst hx
    exact jrecAt_agree hr hag hn2' (not_T_of_cls hT hxh (by decide))
  have hk11 : (TranRecord.fields.take 11).map (·.jname) =
      ["tranId", "tranTypeCd", "tranCatCd", "tranSource", "tranDesc", "tranAmt",
        "tranMerchantId", "tranMerchantName", "tranMerchantCity", "tranMerchantZip",
        "tranCardNum"] := by decide
  have hs11 := tranSet_agree (Hide.elim hset) hT hag hT2 (by
    rw [hk11]
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [fields_get_set])
  have hl := tvals_length g i.toInt.toNat
  have hs12 := tranSet_extend hs11 hT2 (by decide) hl (by
    refine ⟨.ref d, by simp [fields_get_set], d, rfl, ?_⟩
    try simp only [tvals, Model.tranVals, List.getD_cons_succ, List.getD_cons_zero]
    exact hd)
  have hs13 := tranSet_extend hs12 hT2 (by decide) hl (by
    refine ⟨.ref d, by simp [fields_get_set], d, rfl, ?_⟩
    try simp only [tvals, Model.tranVals, List.getD_cons_succ, List.getD_cons_zero]
    exact hd)
  exact ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨⟨hn, hi0, hlocs, f22, f6, f4, f5, Hide.intro htcb2⟩, f3,
    f11, f12, f14, f25, f16, f17, Hide.intro hL2, hrate⟩, Hide.intro hs13⟩

end EquivLean.Modernize.Cbact04c.Java
