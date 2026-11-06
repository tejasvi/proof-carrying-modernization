import EquivLean.Modernize.Cbact04c.JavaRunRes125

/-!
# CBACT04C → Java, `run`: the cross-reference search (statements 148–160)

The loop at 148 compares the `xrefAcctId` of the cross-reference objects with the record's
account id. `j148_next`: no match at `k`, the next iteration; `j172_of_found`: the first match at
`k`, copied into the current cross-reference object (the cut point 172); `xref_exit_absurd`: the
search does not run past the array (the domain has a cross-reference for every record).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

theorem xAcct_range {x : List FV} (hv : CardXrefRecord.Valid x) :
    0 ≤ Model.xAcct x ∧ Model.xAcct x < 100000000000 := by
  have r := holds_display rfl (valid_num hv (i := 2) (by decide) (fmt := {digits := 11})
    (by decide)).2
  simp only [Nat.reducePow] at r
  have a0 := Int.natAbs_eq (Model.numOf (x.getD 2 default))
  have q := r.2 trivial
  simp only [Model.xAcct]
  omega

/-- The account id field of a valid cross-reference record object. -/
theorem xrefIdOf_rec {σ : State} {v : Value} {x : List FV}
    (h : JRecAt CardXrefRecord "Cbact04c$CardXrefRecord" σ v x) (hv : CardXrefRecord.Valid x) :
    xrefIdOf σ v = some (BitVec.ofInt 64 (Model.xAcct x)) := by
  obtain ⟨y, fs, rfl, hy, hf⟩ := jrec_obj h
  have hk := jfield_num hf hv (i := 2) (by decide) (fmt := {digits := 11}) (by decide)
  simp only [xrefIdOf, hy]
  rw [show (CardXrefRecord.fields.getD 2 default).jname = "xrefAcctId" from rfl] at hk
  rw [hk]
  rfl

/-- The search's comparison is the model's. -/
theorem xrefIdOf_eq_iff {σ : State} {v : Value} {x : List FV}
    (h : JRecAt CardXrefRecord "Cbact04c$CardXrefRecord" σ v x) (hv : CardXrefRecord.Valid x)
    {id : Int} (hid0 : 0 ≤ id) (hid1 : id < 100000000000) :
    xrefIdOf σ v = some (BitVec.ofInt 64 id) ↔ Model.xAcct x = id := by
  rw [xrefIdOf_rec h hv]
  have hr := xAcct_range hv
  constructor
  · intro he
    exact ofInt64_inj (by omega) (by omega) (by omega) (by omega) (Option.some.inj he)
  · intro he
    rw [he]

/-- The cross-reference array in a state grown from the entry state. -/
def XrefArr (g : G) (σ : State) (xs : List Value) : Prop :=
  (∃ et, σ.heap g.a2 = some (.array et xs)) ∧
    Forall2 (JRecAt CardXrefRecord "Cbact04c$CardXrefRecord" σ) xs g.xrefs ∧
    ∀ x ∈ g.xrefs, CardXrefRecord.Valid x

/-- The first `k` cross-references do not match: the model's first match is at `k` or later. -/
theorem findXref_eq_of_first {g : G} {σ : State} {xs : List Value} (hx : XrefArr g σ xs)
    {id : Int} (hid0 : 0 ≤ id) (hid1 : id < 100000000000) {k : Nat} (hk : k < g.xrefs.length)
    (hm : Model.xAcct (g.xrefs[k]) = id)
    (hprev : ∀ x ∈ xs.take k, xrefIdOf σ x ≠ some (BitVec.ofInt 64 id)) :
    Model.findXref g.xrefs id = g.xrefs[k] := by
  obtain ⟨-, hf, hv⟩ := hx
  have hlen := Forall2.length_eq hf
  simp only [Model.findXref]
  rw [Model.find?_eq_getElem _ _ k hk (by simpa using hm) (fun j hj => ?_), Option.getD_some]
  have hjx : j < xs.length := by omega
  have hrel := forall2_getElem hf j hjx
  have hmem : xs[j] ∈ xs.take k := by
    rw [List.mem_iff_getElem]
    exact ⟨j, by simp; omega, by simp⟩
  have hne := mt (xrefIdOf_eq_iff hrel (hv _ (List.getElem_mem _)) hid0 hid1).2 (hprev _ hmem)
  simpa using hne

/-- **The search does not run past the array**: some cross-reference has the record's id. -/
theorem xref_exit_absurd {g : G} {σ : State} {xs : List Value} (hx : XrefArr g σ xs) {id : Int}
    (hid0 : 0 ≤ id) (hid1 : id < 100000000000) (hex : ∃ x ∈ g.xrefs, Model.xAcct x = id) {k : Nat}
    (hk : g.xrefs.length ≤ k) (hprev : ∀ x ∈ xs.take k, xrefIdOf σ x ≠ some (BitVec.ofInt 64 id)) :
    False := by
  obtain ⟨-, hf, hv⟩ := hx
  obtain ⟨x, hxm, hxid⟩ := hex
  obtain ⟨v, hvm, hrel⟩ := forall2_mem_right hf x hxm
  have hlen := Forall2.length_eq hf
  rw [List.take_of_length_le (by omega)] at hprev
  exact hprev v hvm ((xrefIdOf_eq_iff hrel (hv x hxm) hid0 hid1).2 hxid)

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

/-- **No match at `k`**: the next iteration of the search (the cut point 148 at `k + 1`). -/
theorem j148_next {g : G} {σ0 σ : State} {fr' : Frame} {i : I32} {hp : Hp} {y : Addr}
    {acctV lastV : Value} {k : I32} {xs : List Value}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some (.ref y))
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32)) (f12 : fr'.get 12 = some (.long 0#64))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some acctV)
    (f13 : fr'.get 13 = some (.long (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)))))
    (f18 : fr'.get 18 = some (.int (-1#32))) (f23 : fr'.get 23 = some (.int (k + 1#32)))
    (hk0 : 0 ≤ k.toInt) (hklt : k.toInt < g.xrefs.length) (hlen : g.xrefs.length < 2147483648)
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y)
      (g.trec i.toInt.toNat)))
    (hne : (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)))
    (hx : Hide (XrefArr g σ xs))
    (hid0 : 0 ≤ Model.tAcct (g.trec i.toInt.toNat))
    (hid1 : Model.tAcct (g.trec i.toInt.toNat) < 100000000000)
    (hprev : ∀ et xs', σ.heap g.a2 = some (.array et xs') → ∀ x ∈ xs'.take k.toInt.toNat,
      xrefIdOf σ x ≠ some (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat))))
    (hnm : Model.xAcct (g.xrefs[k.toInt.toNat]'(by omega)) ≠ Model.tAcct (g.trec i.toInt.toNat))
    (hcore : Hide (CoreHeap g σ0 σ hp (stAcct (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
      (addrOf acctV)))
    (hacct : Hide (JRecAt AccountRecord "Cbact04c$AccountRecord" σ acctV
      (stAcct (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).acct))
    (hlast : Hide (JStrAt σ lastV (lastText (some (Model.tAcct (g.trec i.toInt.toNat))))))
    (hfresh : ∀ a, acctV = .ref a → σ0.next ≤ a) :
    J148 g g.args σ0 fr' σ := by
  obtain ⟨⟨et0, hA⟩, hf, hv⟩ := Hide.elim hx
  have hxl := Forall2.length_eq hf
  have hk1 := i32_toInt_add_one k hk0 (by omega)
  refine ⟨i, hp, .ref y, acctV, lastV, k + 1#32, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb⟩, hne, f3,
    f12, f14, f25, f16, f13, f18, f23, by omega, by omega, ?_, hcore, hacct, hlast, hfresh⟩
  intro et xs' hxs' x hxm
  rw [hA] at hxs'
  simp only [Option.some.injEq, Obj.array.injEq] at hxs'
  obtain ⟨-, rfl⟩ := hxs'
  have hkx : k.toInt.toNat < xs.length := by omega
  have hkn : (k + 1#32).toInt.toNat = k.toInt.toNat + 1 := by omega
  rw [hkn] at hxm
  rcases mem_take_succ hkx hxm with hxm | rfl
  · exact hprev _ _ hA x hxm
  · have hrel := forall2_getElem hf _ hkx
    exact fun he => hnm ((xrefIdOf_eq_iff hrel (hv _ (List.getElem_mem _)) hid0 hid1).1 he)

/-- The heap invariant reads the outputs and the table of the model state only. -/
theorem coreHeap_congr {g : G} {σ0 σ : State} {h : Hp} {s s' : Model.St} {M : List Addr}
    (hc : CoreHeap g σ0 σ h s M) (h1 : s'.disp = s.disp) (h2 : s'.writes = s.writes)
    (h3 : s'.rewrites = s.rewrites) (h4 : s'.accts = s.accts) : CoreHeap g σ0 σ h s' M := by
  unfold CoreHeap at *
  rw [h1, h2, h3, h4]
  exact hc

theorem stRw_k (s : Model.St) (t : List FV) : (stRw s t).k = s.k := by
  unfold stRw disp1
  cases s.lastId <;> rfl

/-- **The first match at `k`**, copied into the current cross-reference object: the cut point
172. -/
theorem j172_of_found {g : G} {σ0 σ σ1 : State} {fr' : Frame} {i : I32} {hp : Hp} {y : Addr}
    {acctV lastV : Value} {k : Nat} {xs : List Value} {xk xc : Addr}
    {fsc : List (FieldKey × Value)}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some (.ref y))
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32)) (f12 : fr'.get 12 = some (.long 0#64))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some acctV)
    (f17 : fr'.get 17 = some (.ref xc))
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y)
      (g.trec i.toInt.toNat)))
    (hne : (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)))
    (hx : Hide (XrefArr g σ xs)) (hk : k < g.xrefs.length)
    (hid0 : 0 ≤ Model.tAcct (g.trec i.toInt.toNat))
    (hid1 : Model.tAcct (g.trec i.toInt.toNat) < 100000000000)
    (hm : Model.xAcct (g.xrefs[k]) = Model.tAcct (g.trec i.toInt.toNat))
    (hprev : ∀ x ∈ xs.take k, xrefIdOf σ x ≠
      some (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat))))
    (hcore : Hide (CoreHeap g σ0 σ hp (stAcct (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
      (addrOf acctV)))
    (hacct : Hide (JRecAt AccountRecord "Cbact04c$AccountRecord" σ acctV
      (stAcct (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).acct))
    (hlast : Hide (JStrAt σ lastV (lastText (some (Model.tAcct (g.trec i.toInt.toNat))))))
    (hfresh : ∀ a, acctV = .ref a → σ0.next ≤ a)
    (hxk : xs[k]? = some (.ref xk))
    (hxc : σ1.heap xc = some (.plain "Cbact04c$CardXrefRecord" fsc))
    (hkc : ∀ key ∈ keysXC, Fields.get fsc ("Cbact04c$CardXrefRecord", key) =
      Fields.get (fieldsOf σ xk) ("Cbact04c$CardXrefRecord", key))
    (hg : Grows σ σ1) (hi : σ1.inits = σ.inits) :
    J172 g g.args σ0 fr' σ1 := by
  have hxa := Hide.elim hx
  obtain ⟨-, hf, hv⟩ := id hxa
  have hxl := Forall2.length_eq hf
  have hkx : k < xs.length := by omega
  have hrel := forall2_getElem hf k hkx
  rw [List.getElem?_eq_getElem hkx] at hxk
  have hxk' : xs[k] = .ref xk := Option.some.inj hxk
  rw [hxk'] at hrel
  obtain ⟨x0, fsk, hx0, hxkh, -⟩ := id hrel
  cases hx0
  have hfind := findXref_eq_of_first hxa hid0 hid1 hk hm hprev
  have hsel : stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat) =
      { stAcct (g.st i.toInt.toNat) (g.trec i.toInt.toNat) with
        xref := Model.findXref g.xrefs (Model.tAcct (g.trec i.toInt.toNat)) } := by
    simp only [stSel, hne, ↓reduceIte]
  have hrc : JRecAt CardXrefRecord "Cbact04c$CardXrefRecord" σ1 (.ref xc)
      (Model.findXref g.xrefs (Model.tAcct (g.trec i.toInt.toNat))) := by
    rw [hfind]
    rw [fieldsOf_eq hxkh] at hkc
    exact jrecAt_copy hrel hxkh hxc (same_keys cardXrefRecord_jnames hkc) (strKeep_of_grows hg)
  refine ⟨i, hp, .ref y, acctV, .ref xc, lastV, ⟨hn, hi0, hlocs, f22, f6, f4, f5,
    Hide.intro (jrecAt_grows hg (Hide.elim htcb))⟩, f3, ?_, ?_, f25, f16, f17, ?_⟩
  · rw [hsel]; simpa [stAcct] using f12
  · rw [hsel]; simpa [stAcct, stRw_k] using f14
  · rw [hsel]
    refine Hide.intro ⟨?_, fun _ => jrecAt_grows hg (Hide.elim hacct), fun _ => hrc,
      jstrAt_grows hg (Hide.elim hlast), fun _ => hfresh⟩
    have hc := coreHeap_grows (Hide.elim hcore) hg hi
    have hM : curAcct { stAcct (g.st i.toInt.toNat) (g.trec i.toInt.toNat) with
        xref := Model.findXref g.xrefs (Model.tAcct (g.trec i.toInt.toNat)) } acctV = addrOf acctV := by
      simp [curAcct, stAcct]
    rw [hM]
    exact coreHeap_congr hc rfl rfl rfl rfl

end EquivLean.Modernize.Cbact04c.Java
