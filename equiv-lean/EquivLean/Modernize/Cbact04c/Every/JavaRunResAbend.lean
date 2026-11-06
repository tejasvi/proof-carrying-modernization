import EquivLean.Modernize.Cbact04c.Every.JavaRunResInit2

/-!
# CBACT04C → Java, `run`: the abends (a missing account, cross-reference or `DEFAULT` group)
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-- The cross-reference array, from the inputs, in a state grown from the entry state. -/
theorem xrefArr_of {g : G} {args : List Value} {σ0 σ : State} (hpre : RunPreG g args σ0)
    (hg : Grows σ0 σ) : ∃ xs, XrefArr g σ xs := by
  obtain ⟨-, ⟨b1, b2, b3, b4, q1, c1, hargs, -, ⟨et2, xs2, h2, -, hp2⟩, -, -, -, -, -, -, hv2, -⟩,
    -⟩ := hpre
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨-, rfl, -⟩ := hargs
  exact ⟨xs2, ⟨et2, heap_of_grows hg h2⟩, forall2_mono (fun _ _ h => jrecAt_grows hg h) hp2, hv2⟩


/-- `findAcct` returns `-1` for an id that no account of the table has. -/
theorem acctIdx_missing {σ : State} {A : Addr} {axs : List Value} {accts : List (List FV)}
    (hA : σ.heap A = some (.array (.cls "Cbact04c$AccountRecord") axs))
    (h : Forall2 (JRecAt AccountRecord "Cbact04c$AccountRecord" σ) axs accts)
    (hv : ∀ a ∈ accts, AccountRecord.Valid a) {id : Int} (hid0 : 0 ≤ id)
    (hid1 : id < 100000000000) (hno : ¬ ∃ a ∈ accts, Model.aId a = id) :
    acctIdx σ A (BitVec.ofInt 64 id) = -1 := by
  have hn : accts.findIdx? (fun a => Model.aId a == id) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro a ha
    rw [beq_eq_false_iff_ne]
    exact fun e => hno ⟨a, ha, e⟩
  simp only [acctIdx, hA, findIdx_table hid0 hid1 h hv, hn]

theorem forall2_append_l {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β} {c : List α} {d : List β}, Forall2 R a b → Forall2 R c d →
      Forall2 R (a ++ c) (b ++ d)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h hs, h2 => .cons h (forall2_append_l hs h2)

/-- **The postcondition after an abend**: the abend lines added to the display list, `abended`
set; the other objects of the loop heap kept. -/
theorem runPost_abend {g : G} {σ0 σ σ' : State} {h : Hp} {s : Model.St} {M : List Addr}
    {dxs : List Value} {dm m' : Nat} {fsR : List (FieldKey × Value)} {vs : List Value}
    {lines : List (List Nat)}
    (hc : CoreHeap g σ0 σ h s M)
    (hld : σ.heap h.ld = some (.list .arrayList dxs dm))
    (hR : σ.heap h.res = some (.plain "Cbact04c$Result" fsR))
    (hag : Agree σ σ' [h.ld, h.res])
    (hld' : σ'.heap h.ld = some (.list .arrayList (dxs ++ vs) m'))
    (hR' : σ'.heap h.res = some (.plain "Cbact04c$Result"
      (Fields.set fsR ("Cbact04c$Result", "abended") (.int 1#32))))
    (hvs : Forall2 (JStrAt σ') vs (lines.map jline))
    (hout : g.out =
      { disp := s.disp ++ lines, writes := s.writes, rewrites := s.rewrites, abended := true }) :
    RunPostG g (some (.ref h.res)) σ' := by
  obtain ⟨-, -, hfr, ⟨fsR', hR0, hRd, hRw, hRr, -⟩, ⟨xs, m, hld0, hxs⟩, ⟨wxs, wm, hlw, hw, -⟩,
    ⟨rxs, rm, hlr, hr, -⟩, -⟩ := hc
  rw [hR] at hR0
  cases hR0
  rw [hld] at hld0
  simp only [Option.some.injEq, Obj.list.injEq, true_and] at hld0
  obtain ⟨rfl, rfl⟩ := hld0
  obtain ⟨-, -, -, -, -, -, hdw, hdl, -⟩ := hfr
  -- the objects that changed: no strings, no records
  have hns : NoStr σ [h.ld, h.res] := by
    intro a ha st hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · rw [hld] at hs; cases hs
    · rw [hR] at hs; cases hs
  have hnotrec : ∀ (cls : ClassName), cls ≠ "Cbact04c$Result" → ∀ (a : Addr) (fs : List (FieldKey × Value)),
      σ.heap a = some (.plain cls fs) → a ∉ [h.ld, h.res] := by
    intro cls hcls a fs ha hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · rw [hld] at ha; cases ha
    · rw [hR] at ha; simp only [Option.some.injEq, Obj.plain.injEq] at ha; exact hcls ha.1.symm
  have hlist : ∀ (a : Addr) (k : ListKind) (l : List Value) (n : Nat), σ.heap a = some (.list k l n) →
      a ≠ h.res := by
    intro a k l n ha e; rw [e, hR] at ha; cases ha
  have hlw' : σ'.heap h.lw = some (.list .arrayList wxs wm) := by
    rw [hag.2 h.lw (State.lt_next_of_heap hlw) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (e | e)
      · exact hdw e.symm
      · exact hlist _ _ _ _ hlw e), hlw]
  have hlr' : σ'.heap h.lr = some (.list .arrayList rxs rm) := by
    rw [hag.2 h.lr (State.lt_next_of_heap hlr) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (e | e)
      · exact hdl e.symm
      · exact hlist _ _ _ _ hlr e), hlr]
  have hrecs : ∀ {sch : Schema} {cls : ClassName}, cls ≠ "Cbact04c$Result" →
      ∀ {ys : List Value} {vals : List (List FV)}, Forall2 (JRecAt sch cls σ) ys vals →
        Forall2 (JRecAt sch cls σ') ys vals := by
    intro sch cls hcls ys vals hf
    refine forall2_jrecAt_agree hag hns hf (fun v hv a hva => ?_)
    obtain ⟨vals', hrel⟩ := forall2_mem_rel hf v hv
    obtain ⟨b, fsb, hb, hbh, -⟩ := jrec_obj hrel
    rw [hva] at hb
    cases hb
    exact hnotrec cls hcls a fsb hbh
  have hs : (if g.out.abended then (1 : I32) else 0) = 1#32 := by rw [hout]; rfl
  refine ⟨h.res, _, h.ld, .arrayList, dxs ++ vs, m', h.lw, .arrayList, wxs, wm, h.lr, .arrayList,
    rxs, rm, rfl, hR', ?_, hld', ?_, ?_, hlw', ?_, ?_, hlr', ?_, ?_⟩
  · simp only [fields_get_set]; simpa using hRd
  · rw [hout]
    simp only [List.map_append]
    exact forall2_append_l (forall2_jstrAt_agree hag hns hxs) hvs
  · simp only [fields_get_set]; simpa using hRw
  · rw [hout]; exact hrecs (by decide) hw
  · simp only [fields_get_set]; simpa using hRr
  · rw [hout]; exact hrecs (by decide) hr
  · rw [hs]; simp [fields_get_set]

/-! ## The model outputs of the abends -/

theorem findAcctO_none {l : List (List FV)} {id : Int} (h : ¬ ∃ a ∈ l, Model.aId a = id) :
    Model.findAcctO l id = none := by
  unfold Model.findAcctO
  rw [List.find?_eq_none]
  intro a ha he
  exact h ⟨a, ha, by simpa using he⟩

/-- **A missing account**: the outputs after the rewrite, the abend lines. -/
theorem out_acct_missing {g : G} {n : Nat} (hn : n < g.tcat.length) (hs : (g.stE n).stop = false)
    (hne : (g.st n).lastId ≠ some (Model.tAcct (g.trec n)))
    (hno : ¬ ∃ a ∈ (stRw (g.st n) (g.trec n)).accts, Model.aId a = Model.tAcct (g.trec n)) :
    g.out =
      { disp := (stRw (g.st n) (g.trec n)).disp ++
          [Model.txt "ACCOUNT NOT FOUND: " ++ zpad 11 (Model.tAcct (g.trec n)).natAbs,
            Model.txt "ERROR READING ACCOUNT FILE", Model.txt "FILE STATUS IS: NNNN0023",
            Model.txt "ABENDING PROGRAM"],
        writes := (stRw (g.st n) (g.trec n)).writes,
        rewrites := (stRw (g.st n) (g.trec n)).rewrites, abended := true } := by
  have e := G.stE_succ g hn
  rw [← trec_eq hn] at e
  have ha : Model.findAcctO (rwE (g.stE n) (g.trec n)).accts (Model.tAcct (g.trec n)) = none := by
    apply findAcctO_none
    have h2 : (rwE (g.stE n) (g.trec n)).accts = (stRw (g.st n) (g.trec n)).accts :=
      congrArg Model.St.accts (stOf_rwE (g.stE n) (g.trec n))
    rw [h2]
    exact hno
  rw [stepE_acct_missing g (g.stE n) (g.trec n) hs hne ha] at e
  have hs1 : (g.stE (n + 1)).stop = true := by rw [e]; rfl
  rw [G.out_stopped g hs1 (by omega)]
  have hst : g.st (n + 1) = stOf ((rwE (g.stE n) (g.trec n)).abend
      [Model.txt "ACCOUNT NOT FOUND: " ++ zpad 11 (Model.tAcct (g.trec n)).natAbs,
        Model.txt "ERROR READING ACCOUNT FILE"]) := by
    show stOf (g.stE (n + 1)) = _
    rw [e]
  rw [hst, stOf_abend, stOf_rwE]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rfl

set_option maxRecDepth 4000 in
theorem txt_accountNotFound : (Model.txt "ACCOUNT NOT FOUND: ").map (BitVec.ofNat 16) =
    [65#16, 67#16, 67#16, 79#16, 85#16, 78#16, 84#16, 32#16, 78#16, 79#16, 84#16, 32#16, 70#16, 79#16,
      85#16, 78#16, 68#16, 58#16, 32#16] := by decide

/-- **A missing cross-reference**: the outputs after the rewrite, the abend lines. -/
theorem out_xref_missing {g : G} {n : Nat} (hn : n < g.tcat.length) (hs : (g.stE n).stop = false)
    (hne : (g.st n).lastId ≠ some (Model.tAcct (g.trec n)))
    (hacc : (stAcct (g.st n) (g.trec n)).acct ≠ [])
    (hno : ¬ ∃ x ∈ g.xrefs, Model.xAcct x = Model.tAcct (g.trec n)) :
    g.out =
      { disp := (stRw (g.st n) (g.trec n)).disp ++
          [Model.txt "ACCOUNT NOT FOUND: " ++ zpad 11 (Model.tAcct (g.trec n)).natAbs,
            Model.txt "ERROR READING XREF FILE", Model.txt "FILE STATUS IS: NNNN0023",
            Model.txt "ABENDING PROGRAM"],
        writes := (stRw (g.st n) (g.trec n)).writes,
        rewrites := (stRw (g.st n) (g.trec n)).rewrites, abended := true } := by
  have e := G.stE_succ g hn
  rw [← trec_eq hn] at e
  have h2 : (rwE (g.stE n) (g.trec n)).accts = (stRw (g.st n) (g.trec n)).accts :=
    congrArg Model.St.accts (stOf_rwE (g.stE n) (g.trec n))
  have ha : Model.findAcctO (rwE (g.stE n) (g.trec n)).accts (Model.tAcct (g.trec n)) =
      some (Model.findAcct (stRw (g.st n) (g.trec n)).accts (Model.tAcct (g.trec n))) := by
    rw [h2]
    exact findAcctO_of_ne hacc
  have hx : Model.findXrefO g.xrefs (Model.tAcct (g.trec n)) = none := by
    unfold Model.findXrefO
    rw [List.find?_eq_none]
    intro x hx he
    exact hno ⟨x, hx, by simpa using he⟩
  rw [stepE_xref_missing g (g.stE n) (g.trec n) hs hne ha hx] at e
  have hs1 : (g.stE (n + 1)).stop = true := by rw [e]; rfl
  rw [G.out_stopped g hs1 (by omega)]
  have hst : g.st (n + 1) = stOf ((rwE (g.stE n) (g.trec n)).abend
      [Model.txt "ACCOUNT NOT FOUND: " ++ zpad 11 (Model.tAcct (g.trec n)).natAbs,
        Model.txt "ERROR READING XREF FILE"]) := by
    show stOf (g.stE (n + 1)) = _
    rw [e]
  rw [hst, stOf_abend, stOf_rwE]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rfl

/-- The search ran past the array: no cross-reference has the account id. -/
theorem xref_none_of_exit {g : G} {σ : State} {xs : List Value} (hx : XrefArr g σ xs) {id : Int}
    (hid0 : 0 ≤ id) (hid1 : id < 100000000000) {k : Nat} (hk : g.xrefs.length ≤ k)
    (hprev : ∀ x ∈ xs.take k, xrefIdOf σ x ≠ some (BitVec.ofInt 64 id)) :
    ¬ ∃ x ∈ g.xrefs, Model.xAcct x = id :=
  fun hex => xref_exit_absurd hx hid0 hid1 hex hk hprev

end EquivLean.Modernize.Cbact04c.Java
