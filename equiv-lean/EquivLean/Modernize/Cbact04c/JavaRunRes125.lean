import EquivLean.Modernize.Cbact04c.JavaRunRes108

/-!
# CBACT04C → Java, `run`: statements 125–147 (the new account read)

* 125–128: the new account id's text (`fmtU`), the cut point 129 (`j129_of_fmt`);
* 129–147: `findAcct` finds the account in the table copy, `copyAcct` copies it into the current
  account object; the cross-reference search starts (the cut point 148, `j148_of_acct`).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-- **The new account id's text** (statements 125–128): the cut point 129. -/
theorem j129_of_fmt {g : G} {σ0 σ σ1 : State} {fr' : Frame} {i : I32} {hp : Hp} {y yl : Addr}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some (.ref y))
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32)) (f12 : fr'.get 12 = some (.long 0#64))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)))
    (f11 : fr'.get 11 = some (.long (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)))))
    (f25 : fr'.get 25 = some (.ref yl))
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y)
      (g.trec i.toInt.toNat)))
    (hne : (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)))
    (hcore : Hide (CoreHeap g σ0 σ hp (stRw (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) []))
    (hyl : σ1.heap yl = some (.str (zpadJ (Model.tAcct (g.trec i.toInt.toNat)).natAbs 11)))
    (hg : Grows σ σ1) (hi : σ1.inits = σ.inits) : J129 g g.args σ0 fr' σ1 :=
  ⟨i, hp, .ref y, .ref yl, ⟨hn, hi0, hlocs, f22, f6, f4, f5,
    Hide.intro (jrecAt_grows hg (Hide.elim htcb))⟩, hne, f3, f12, f14, f11, f25,
    Hide.intro ⟨yl, rfl, hyl⟩, Hide.intro (coreHeap_grows (Hide.elim hcore) hg hi)⟩

/-- A fresh object is in none of the lists of the heap invariant. -/
theorem coreHeap_add_fresh {g : G} {σ0 σ : State} {h : Hp} {s : Model.St} {y : Addr}
    (hc : CoreHeap g σ0 σ h s []) (hy : σ.next ≤ y) : CoreHeap g σ0 σ h s [y] := by
  obtain ⟨hg0, hin, hfr, hres, hdisp, hw, ⟨rxs, rm, hlr, hrr, -⟩, ⟨axs, hA, haa, -⟩, htr, hp, hcl⟩ := hc
  have hnot : ∀ (xs : List Value) (vals : List (List FV)),
      Forall2 (JRecAt AccountRecord "Cbact04c$AccountRecord" σ) xs vals →
      ∀ v ∈ xs, ∀ a, v = .ref a → a ∉ [y] := by
    intro xs vals hxs v hv a hva hm
    rw [List.mem_singleton] at hm
    subst hm
    obtain ⟨vals', hr⟩ := forall2_mem_rel hxs v hv
    rw [hva] at hr
    obtain ⟨x, fs, hx, hxh, -⟩ := hr
    cases hx
    have := State.lt_next_of_heap hxh
    jomega
  exact ⟨hg0, hin, hfr, hres, hdisp, hw, ⟨rxs, rm, hlr, hrr, hnot _ _ hrr⟩,
    ⟨axs, hA, haa, hnot _ _ haa⟩, htr, hp, hcl⟩

theorem stAcct_acct (s : Model.St) (t : List FV) :
    (stAcct s t).acct = Model.findAcct (stRw s t).accts (Model.tAcct t) := rfl

/-- **The new account copied into the current account object** (statements 129–147): the cut
point 148, nothing searched yet. -/
theorem j148_of_acct {g : G} {σ0 σ σ2 : State} {fr' : Frame} {i : I32} {hp : Hp} {y : Addr}
    {lastV : Value} {axs : List Value} {j : Nat} {e y3 : Addr} {fs3 : List (FieldKey × Value)}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some (.ref y))
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32)) (f12 : fr'.get 12 = some (.long 0#64))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some (.ref y3))
    (f13 : fr'.get 13 = some (.long (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)))))
    (f18 : fr'.get 18 = some (.int (-1#32))) (f23 : fr'.get 23 = some (.int 0#32))
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y)
      (g.trec i.toInt.toNat)))
    (hne : (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)))
    (hlast : Hide (JStrAt σ lastV (lastText (some (Model.tAcct (g.trec i.toInt.toNat))))))
    (hcore : Hide (CoreHeap g σ0 σ hp (stRw (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) []))
    (hA : σ.heap hp.A = some (.array (.cls "Cbact04c$AccountRecord") axs))
    (hj : (stRw (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).accts.findIdx?
      (fun a => Model.aId a == Model.tAcct (g.trec i.toInt.toNat)) = some j)
    (he : axs[j]? = some (.ref e))
    (hy3 : σ2.heap y3 = some (.plain "Cbact04c$AccountRecord" fs3))
    (hk3 : ∀ k ∈ keysAC, Fields.get fs3 ("Cbact04c$AccountRecord", k) =
      Fields.get (fieldsOf σ e) ("Cbact04c$AccountRecord", k))
    (hfr3 : σ.next ≤ y3) (hg : Grows σ σ2) (hi : σ2.inits = σ.inits) :
    J148 g g.args σ0 fr' σ2 := by
  have hc := Hide.elim hcore
  obtain ⟨hg0, -, -, -, -, -, -, ⟨axs', hA', haa, -⟩, -⟩ := id hc
  rw [hA] at hA'
  simp only [Option.some.injEq, Obj.array.injEq, true_and] at hA'
  subst hA'
  obtain ⟨hjl, hjp, hjprev⟩ := List.findIdx?_eq_some_iff_getElem.1 hj
  have hlen := Forall2.length_eq haa
  have hjx : j < axs.length := by omega
  have hej : axs[j] = .ref e := by
    rw [List.getElem?_eq_getElem hjx] at he
    exact Option.some.inj he
  have hre := forall2_getElem haa j hjx
  rw [hej] at hre
  have hfind : Model.findAcct (stRw (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).accts
      (Model.tAcct (g.trec i.toInt.toNat)) =
      (stRw (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).accts[j] := by
    simp only [Model.findAcct]
    rw [Model.find?_eq_getElem _ _ j hjl hjp (fun k hk => by simpa using hjprev k hk),
      Option.getD_some]
  obtain ⟨x, fse, hx, hxe, -⟩ := id hre
  cases hx
  have hr3 : JRecAt AccountRecord "Cbact04c$AccountRecord" σ2 (.ref y3)
      (stAcct (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).acct := by
    rw [stAcct_acct, hfind]
    rw [fieldsOf_eq hxe] at hk3
    exact jrecAt_copy hre hxe hy3 (same_keys accountRecord_jnames hk3) (strKeep_of_grows hg)
  have hc2 : CoreHeap g σ0 σ2 hp (stAcct (g.st i.toInt.toNat) (g.trec i.toInt.toNat)) [y3] :=
    coreHeap_grows (coreHeap_add_fresh hc hfr3) hg hi
  refine ⟨i, hp, .ref y, .ref y3, lastV, 0#32, ⟨hn, hi0, hlocs, f22, f6, f4, f5,
    Hide.intro (jrecAt_grows hg (Hide.elim htcb))⟩, hne, f3, f12, f14, f25, f16, f13, f18, f23,
    by decide, by simp, ?_, Hide.intro hc2, Hide.intro hr3,
    Hide.intro (jstrAt_grows hg (Hide.elim hlast)), ?_⟩
  · intro et xs _ x hx
    simp at hx
  · intro a ha
    cases ha
    exact Nat.le_trans hg0.1 hfr3

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

/-- The table after the rewrite of the previous account: the ids of the input table, valid
records. -/
theorem stRw_table {g : G} {s : Model.St} (h : StInv g s) (t : List FV) :
    (stRw s t).accts.map Model.aId = g.accts.map Model.aId ∧
      ∀ a ∈ (stRw s t).accts, AccountRecord.Valid a := by
  obtain ⟨hid, hgrp, hval, hcur, ht1, ht2, hk⟩ := h
  unfold stRw disp1
  cases hl : s.lastId with
  | none => exact ⟨hid, hval⟩
  | some id =>
    obtain ⟨hacc, -, hexg, -, -⟩ := hcur id hl
    have hex' := exists_aId_of_map hid hexg
    have hspec := Model.findAcct_spec s.accts id hex'
    have hacid : Model.aId s.acct = id := by rw [hacc]; exact hspec.2
    simp only [Option.isSome_some, ↓reduceIte, hacid]
    refine ⟨?_, ?_⟩
    · rw [map_replaceFirst_findAcct _ _ _ _ hex' (by rw [Model.aId_posted, hacc])]; exact hid
    · intro a ha
      rcases Model.mem_replaceFirst _ _ _ a ha with rfl | ha
      · exact valid_posted (hval _ (hacc ▸ hspec.1)) ht1 ht2
      · exact hval a ha

end EquivLean.Modernize.Cbact04c.Java
