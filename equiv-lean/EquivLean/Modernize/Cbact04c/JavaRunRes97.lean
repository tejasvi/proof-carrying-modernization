import EquivLean.Modernize.Cbact04c.JavaRunRes89
import EquivLean.Modernize.Cbact04c.JavaRunPost
import EquivLean.Modernize.Cbact04c.JavaRunModelRun

/-!
# CBACT04C → Java, `run`: statements 97–107 (same account? first record? post the previous account)

What the segment reads: the inputs' facts (`inFacts_of_pre`), the current account object
(`acct_facts`), the text of the last account id (`last_facts`).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

theorem inFacts_of_pre {g : G} {args : List Value} {σ0 : State} (h : RunPreG g args σ0) :
    InFacts g := by
  obtain ⟨-, ⟨b1, b2, b3, b4, q1, c1, -, -, -, -, -, -, -, -, hv1, -, hv3, -, -, hdom⟩, -⟩ := h
  exact ⟨hv1, hv3, hdom⟩

/-- The current account (once a record was read) is a valid record of the table. -/
theorem acct_valid {g : G} {s : Model.St} (hst : StInv g s) {id : Int} (hl : s.lastId = some id) :
    AccountRecord.Valid s.acct := by
  obtain ⟨hid, -, hval, hcur, -⟩ := hst
  obtain ⟨hacc, -, hexg, -, -⟩ := hcur id hl
  have hex' := exists_aId_of_map hid hexg
  rw [hacc]
  exact hval _ (Model.findAcct_spec s.accts id hex').1

/-- The balance of a valid account record is below `10^12`. -/
theorem aBal_range {a : List FV} (hv : AccountRecord.Valid a) :
    -1000000000000 < Model.aBal a ∧ Model.aBal a < 1000000000000 := by
  have r := holds_display rfl (valid_num hv (i := 2) (by decide)
    (fmt := {digits := 12, scale := 2, signed := true}) (by decide)).2
  simp only [Nat.reducePow] at r
  have a0 := Int.natAbs_eq (Model.numOf (a.getD 2 default))
  simp only [Model.aBal]
  omega

/-- What statements 102–107 read and write of the current account object. -/
def AcctFacts (σ0 σ : State) (acctV : Value) (acct : List FV) (ac : Addr)
    (fsa : List (FieldKey × Value)) : Prop :=
  acctV = .ref ac ∧ σ.heap ac = some (.plain "Cbact04c$AccountRecord" fsa) ∧
    Fields.get fsa ("Cbact04c$AccountRecord", "acctCurrBal") =
      some (.long (BitVec.ofInt 64 (Model.aBal acct))) ∧
    (∃ w, Fields.get fsa ("Cbact04c$AccountRecord", "acctCurrCycCredit") = some w) ∧
    (∃ w, Fields.get fsa ("Cbact04c$AccountRecord", "acctCurrCycDebit") = some w) ∧
    σ0.next ≤ ac

theorem acct_facts {g : G} {σ0 σ : State} {hp : Hp} {s : Model.St} {acctV xrefV lastV : Value}
    (hL : LoopHeap g σ0 σ hp s acctV xrefV lastV) (hst : StInv g s) {id : Int}
    (hl : s.lastId = some id) : ∃ ac fsa, AcctFacts σ0 σ acctV s.acct ac fsa := by
  obtain ⟨-, ha, -, -, hfr⟩ := hL
  have hsome : s.lastId.isSome := by rw [hl]; rfl
  have hrec := ha hsome
  have hv := acct_valid hst hl
  obtain ⟨ac, fsa, rfl, hac, hf⟩ := jrec_obj hrec
  have hpres := present_keys accountRecord_jnames hf
  refine ⟨ac, fsa, rfl, hac, ?_, hpres _ (by decide), hpres _ (by decide), hfr hsome ac rfl⟩
  exact jfield_num hf hv (i := 2) (by decide) (fmt := {digits := 12, scale := 2, signed := true})
    (by decide)

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

/-! ## The three exits of statements 97–107 -/

theorem stRw_none {s : Model.St} {t : List FV} (hl : s.lastId = none) : stRw s t = disp1 s t := by
  simp [stRw, disp1, hl]

theorem stSel_same {xrefs : List (List FV)} {s : Model.St} {t : List FV}
    (hl : s.lastId = some (Model.tAcct t)) : stSel xrefs s t = disp1 s t := by
  simp [stSel, hl]

/-- **First record** (no previous account): on to reading its account (cut point 125). -/
theorem j125_of_first {g : G} {σ0 σ σ1 : State} {fr : Frame} {i : I32} {hp : Hp} {y : Addr}
    {acctV xrefV lastV : Value} {v11 v27 v2 : Value}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr)
    (f22 : fr.get 22 = some (.int (i + 1#32))) (f6 : fr.get 6 = some (.ref y))
    (f4 : fr.get 4 = some (.int 0#32)) (f5 : fr.get 5 = some (.int 0#32))
    (f14 : fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)))
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y)
      (g.trec i.toInt.toNat)))
    (hheap : Hide (LoopHeap g σ0 σ hp (disp1 (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) acctV
      xrefV lastV))
    (hl : (g.st i.toInt.toNat).lastId = none) (hg : Grows σ σ1) (hi : σ1.inits = σ.inits) :
    J125 g g.args σ0 ((((fr.setLocal 11 v11).setLocal 27 v27).setLocal 2 v2).setLocal 3
      (.int 0#32)) σ1 := by
  have hc : CoreHeap g σ0 σ hp (disp1 (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) [] := by
    have h1 := (Hide.elim hheap).1
    simp only [curAcct, disp1, hl, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h1
    exact h1
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  refine ⟨i, hp, .ref y, ⟨hn, hi0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
    ?_, ?_⟩, by rw [hl]; simp, ?_, ?_, ?_⟩
  all_goals first
    | (frame_simp [f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24, f14, f4, f5, f22,
        f6]; done)
    | skip
  · exact Hide.intro (jrecAt_grows hg (Hide.elim htcb))
  · rw [stRw_none hl]
    exact Hide.intro (coreHeap_grows hc hg hi)

/-- **The same account as the previous record**: on to the interest part (cut point 172). -/
theorem j172_of_same {g : G} {σ0 σ σ1 : State} {fr : Frame} {i : I32} {hp : Hp} {y : Addr}
    {acctV xrefV lastV : Value} {v11 v27 v2 : Value}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr)
    (f22 : fr.get 22 = some (.int (i + 1#32))) (f6 : fr.get 6 = some (.ref y))
    (f4 : fr.get 4 = some (.int 0#32)) (f5 : fr.get 5 = some (.int 0#32))
    (f12 : fr.get 12 = some (.long (BitVec.ofInt 64 (g.st i.toInt.toNat).total)))
    (f3 : fr.get 3 = some (.int (if (g.st i.toInt.toNat).lastId.isSome then 0#32 else 1#32)))
    (f14 : fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)))
    (f25 : fr.get 25 = some lastV) (f16 : fr.get 16 = some acctV) (f17 : fr.get 17 = some xrefV)
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y)
      (g.trec i.toInt.toNat)))
    (hheap : Hide (LoopHeap g σ0 σ hp (disp1 (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) acctV
      xrefV lastV))
    (hl : (g.st i.toInt.toNat).lastId = some (Model.tAcct (g.trec i.toInt.toNat)))
    (hg : Grows σ σ1) (hi : σ1.inits = σ.inits) :
    J172 g g.args σ0 (((fr.setLocal 11 v11).setLocal 27 v27).setLocal 2 v2) σ1 := by
  have hsel := stSel_same (xrefs := g.xrefs) hl
  rw [hl] at f3
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  refine ⟨i, hp, .ref y, acctV, xrefV, lastV, ⟨hn, hi0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [hsel]; frame_simp [f12, f14, disp1]; done)
    | (frame_simp [f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24, f14, f4, f5, f22,
        f6, f3, f25, f16, f17, Option.isSome_some]; done)
    | skip
  · exact Hide.intro (jrecAt_grows hg (Hide.elim htcb))
  · rw [hsel]
    exact Hide.intro (loopHeap_grows (Hide.elim hheap) hg hi)

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

/-- A record object of another class is kept by a write to the account object `ac`. -/
theorem jrecAt_setObj_acct {s : Schema} {cls : ClassName} {σ : State} {y ac : Addr}
    {vals : List FV} {fs : List (FieldKey × Value)} (h : JRecAt s cls σ (.ref y) vals)
    (hac : σ.heap ac = some (.plain "Cbact04c$AccountRecord" fs))
    (hcls : cls ≠ "Cbact04c$AccountRecord") (o : Obj) : JRecAt s cls (σ.setObj ac o) (.ref y) vals := by
  have hn : NoStr σ [ac] := by
    intro w hw st hst
    rw [List.mem_singleton] at hw
    subst hw
    rw [hac] at hst
    cases hst
  obtain ⟨x, fsy, hx, hy, -⟩ := id h
  cases hx
  exact jrecAt_agree h (agree_setObj_mem (agree_refl σ [ac]) (List.mem_singleton_self ac) o) hn
    (fun hm => hcls (by rw [List.mem_singleton] at hm; subst hm; rw [hac] at hy; cases hy; rfl))

/-- **The previous account posted** (statements 102–107): the cut point 108. -/
theorem j108_of_post {g : G} {σ0 σ σ1 : State} {fr' : Frame} {i : I32} {hp : Hp} {y : Addr}
    {acctV xrefV lastV : Value} {ac : Addr} {fsa : List (FieldKey × Value)} {nb z1 z2 : I64}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some (.ref y))
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)))
    (f16 : fr'.get 16 = some acctV)
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y)
      (g.trec i.toInt.toNat)))
    (hheap : Hide (LoopHeap g σ0 σ hp (disp1 (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) acctV
      xrefV lastV))
    {id : Int} (hl : (g.st i.toInt.toNat).lastId = some id)
    (hne : id ≠ Model.tAcct (g.trec i.toInt.toNat))
    (hacc : AcctFacts σ0 σ acctV (g.st i.toInt.toNat).acct ac fsa)
    (hg : Grows σ σ1) (hi : σ1.inits = σ.inits)
    (hnb : nb = BitVec.ofInt 64 (Int.tmod (Model.aBal (g.st i.toInt.toNat).acct +
      (g.st i.toInt.toNat).total) (10 ^ 12)))
    (hz1 : z1 = BitVec.ofInt 64 0) (hz2 : z2 = BitVec.ofInt 64 0) :
    J108 g g.args σ0 fr'
      (((σ1.setObj ac (.plain "Cbact04c$AccountRecord" (Fields.set fsa
          ("Cbact04c$AccountRecord", "acctCurrBal") (.long nb)))).setObj ac
        (.plain "Cbact04c$AccountRecord" (Fields.set (Fields.set fsa
          ("Cbact04c$AccountRecord", "acctCurrBal") (.long nb))
          ("Cbact04c$AccountRecord", "acctCurrCycCredit") (.long z1)))).setObj ac
        (.plain "Cbact04c$AccountRecord" (Fields.set (Fields.set (Fields.set fsa
          ("Cbact04c$AccountRecord", "acctCurrBal") (.long nb))
          ("Cbact04c$AccountRecord", "acctCurrCycCredit") (.long z1))
          ("Cbact04c$AccountRecord", "acctCurrCycDebit") (.long z2)))) := by
  subst hnb hz1 hz2
  obtain ⟨rfl, hac, -, -, -, h0⟩ := hacc
  have hL := Hide.elim hheap
  have hsome : (g.st i.toInt.toNat).lastId.isSome := by rw [hl]; rfl
  have hc : CoreHeap g σ0 σ hp (disp1 (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) [ac] := by
    have h1 := hL.1
    simp only [curAcct, disp1, hl, Option.isSome_some, ↓reduceIte, addrOf] at h1
    exact h1
  have hrec : JRecAt AccountRecord "Cbact04c$AccountRecord" σ (.ref ac) (g.st i.toInt.toNat).acct :=
    hL.2.1 hsome
  have hac1 : σ1.heap ac = some (.plain "Cbact04c$AccountRecord" fsa) := heap_of_grows hg hac
  have hc1 := coreHeap_grows hc hg hi
  have hrec1 := jrecAt_grows hg hrec
  have htcb1 := jrecAt_grows hg (Hide.elim htcb)
  refine ⟨i, hp, .ref y, .ref ac, ⟨hn, hi0, hlocs, f22, f6, f4, f5, ?_⟩, hsome, ?_, f3, f14, f16, ?_,
    ?_⟩
  · refine Hide.intro (jrecAt_setObj_acct (jrecAt_setObj_acct (jrecAt_setObj_acct htcb1 hac1
      (by decide) _) (heap_setObj_self' hac1) (by decide) _)
      (heap_setObj_self' (heap_setObj_self' hac1)) (by decide) _)
  · rw [hl]
    intro h
    exact hne (Option.some.inj h)
  · exact Hide.intro (coreHeap_setObj_acct (coreHeap_setObj_acct (coreHeap_setObj_acct hc1 hac1 h0 _)
      (heap_setObj_self' hac1) h0 _) (heap_setObj_self' (heap_setObj_self' hac1)) h0 _)
  · exact Hide.intro (jrecAt_posted hrec1 hac1)

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

/-! ## The comparison of `fmtU (acctId, 11)` with the last account text -/

theorem spJ_ne_zpadJ (d : Nat) : ∀ n, spJ 11 ≠ zpadJ d n := by
  intro n h
  have hl := congrArg List.length h
  rw [spJ_length, zpadJ_length] at hl
  subst hl
  exact zpadJ_ne_spJ d 11 (by decide) h.symm

theorem zpadJ_ne_of_ne {c d : Nat} (hc : c < 10 ^ 11) (hd : d < 10 ^ 11) (h : c ≠ d) :
    ∀ n, zpadJ c 11 ≠ zpadJ d n := by
  intro n he
  have hl := congrArg List.length he
  rw [zpadJ_length, zpadJ_length] at hl
  subst hl
  exact h (zpadJ_inj 11 c d hc hd he)

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

/-- **Another account than the previous record's** (statements 97–101): the cut point 102. -/
theorem j102_of_ne {g : G} {σ0 σ σ1 : State} {fr : Frame} {i : I32} {hp : Hp} {y : Addr}
    {acctV xrefV lastV : Value} {v11 v27 v2 : Value}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr)
    (f22 : fr.get 22 = some (.int (i + 1#32))) (f6 : fr.get 6 = some (.ref y))
    (f4 : fr.get 4 = some (.int 0#32)) (f5 : fr.get 5 = some (.int 0#32))
    (f12 : fr.get 12 = some (.long (BitVec.ofInt 64 (g.st i.toInt.toNat).total)))
    (f3 : fr.get 3 = some (.int 0#32))
    (f14 : fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)))
    (f16 : fr.get 16 = some acctV)
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y)
      (g.trec i.toInt.toNat)))
    (hheap : Hide (LoopHeap g σ0 σ hp (disp1 (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) acctV
      xrefV lastV))
    (hsome : (g.st i.toInt.toNat).lastId.isSome)
    (hne : (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)))
    (hg : Grows σ σ1) (hi : σ1.inits = σ.inits) :
    J102 g g.args σ0 (((fr.setLocal 11 v11).setLocal 27 v27).setLocal 2 v2) σ1 := by
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  refine ⟨i, hp, .ref y, acctV, xrefV, lastV, ⟨hn, hi0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, hsome, hne, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (frame_simp [f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24, f12, f3, f14, f16,
        f4, f5, f22, f6]; done)
    | skip
  · exact Hide.intro (jrecAt_grows hg (Hide.elim htcb))
  · exact Hide.intro (loopHeap_grows (Hide.elim hheap) hg hi)

end EquivLean.Modernize.Cbact04c.Java
