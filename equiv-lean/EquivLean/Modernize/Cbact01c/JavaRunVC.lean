import EquivLean.Modernize.Cbact01c.JavaRunOther

/-!
# CBACT01C → Java: the verification conditions of `run`

`run_vc`: the entry segment, and at the loop head (statement 10) the three cases (`endOfFile`
set; a record left; all records read, `pastEnd` not set).
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

/-- The facts of a record of the input array that the read segment uses. -/
theorem acctAt_run {σ0 : Jimple.State} {c : Addr} {v : List EquivLean.Cobol.Rec.FVal}
    (h : AcctAt σ0 c v) : ∃ fsc x7 s7 dbt, σ0.heap c = some (.plain acctCls fsc) ∧
      Fields.get fsc (acctCls, "acctReissueDate") = some (.ref x7) ∧
      σ0.heap x7 = some (.str s7) ∧ s7.length < 2147483648 ∧
      Fields.get fsc (acctCls, "acctCurrCycDebit") = some (.long dbt) ∧ AcctOk σ0 c := by
  obtain ⟨n0, n2, n3, n4, n8, n9, b1, b5, b6, b7, b10, b11, b12, -, hok, -⟩ := acctAt_flat h
  have hok' := hok
  obtain ⟨fsc, hc, -, -, -, -, -, -, -, ⟨x7, s7, hf7, hx7, hs7⟩, -, ⟨dbt, hf9, -⟩, -, -, -⟩ := hok'
  exact ⟨fsc, x7, s7, dbt, hc, hf7, hx7, hs7, hf9, hok⟩

theorem forall2_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → ∀ {k : Nat} (hk : k < xs.length),
      ∃ x y, xs[k]? = some x ∧ ys[k]? = some y ∧ R x y
  | _, _, .nil, _, hk => by simp at hk
  | _, _, .cons h t, 0, _ => ⟨_, _, rfl, rfl, h⟩
  | _, _, .cons _ t, k + 1, hk => forall2_getElem? t (k := k) (by simpa using hk)

/-- From the loop head, in each case of the flags and the record count. -/
theorem run_loop (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal))
    (hfile : AcctfileFileAt σ0 a vals) (hvalid : ∀ v ∈ vals, AccountRecord.Valid v)
    (hI5 : Inits σ0) (fr : Frame) (σ : Jimple.State)
    (hI : runInv10 σ0 a vals [.ref a] σ0 fr σ) : RunWP σ0 a vals 10 fr σ := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := hI5
  obtain ⟨et, xs, i, z1, z0, cd, d, s, fs, ys1, ys2, ys3, ys4, m1, m2, m3, m4, ha, f0, f1, f7, f12,
    f11, f3, f9, hd, hR, hl1, hl2, hl3, hl4, hi0, hin, hz10, hz0, hzi, hdB1, hdB2, hdB3, hdB4, hR1,
    hR2, hR3, hR4, hR5, hD, hg, hinits, hstatics⟩ := hI
  obtain ⟨et', xs', ha', hlen, hrec⟩ := hfile
  rw [ha] at ha'
  simp only [Option.some.injEq, Obj.array.injEq] at ha'
  obtain ⟨rfl, rfl⟩ := ha'
  subst hz10
  have ha0 := State.lt_next_of_heap ha
  have hl40 : σ0.next + 4 < σ.next := State.lt_next_of_heap hl4
  rcases hz0 with rfl | rfl
  · rcases Int.lt_or_le i.toInt xs.length with hlt | hge
    · have hik : i.toNat = (BitVec.toInt i).toNat :=
        toNat_of_toInt_eq (Int.toNat_of_nonneg hi0).symm
      obtain ⟨w, v, hw, hv, hJ⟩ := forall2_getElem? hrec (k := i.toNat) (by omega)
      have hJ' := hJ
      obtain ⟨c, fsc', hwc, -⟩ := hJ'
      subst hwc
      have hA : AcctAt σ0 c v := ⟨hJ, hvalid v (List.mem_of_getElem? hv)⟩
      obtain ⟨fsc, x7, s7, dbt, hc, hf7, hx7, hs7, hf9, hok⟩ := acctAt_run hA
      have hk : (BitVec.toInt i).toNat < xs.length := by omega
      have hxk2 : xs[(BitVec.toInt i).toNat]'hk = .ref c := by
        have hw' : xs[(BitVec.toInt i).toNat]? = some (.ref c) := hik ▸ hw
        obtain ⟨_, hx⟩ := List.getElem?_eq_some_iff.mp hw'
        exact hx
      have hs20 : s.length = 20 := (Hide.elim hD).2.1
      exact run_seg10_read σ0 a vals fr σ et xs i cd d s fs ys1 ys2 ys3 ys4 m1 m2 m3 m4 c fsc x7 s7
        dbt ha ha0 hlen f0 f1 f7 f12 f11 f3 f9 hd hR hl1 hl2 hl3 hl4 hi0 hlt hdB1 hdB2 hdB3 hdB4
        hR1 hR2 hR3 hR4 hR5 hD hg.1 hg.2 hinits hstatics hw hk hxk2 hs20 (State.lt_next_of_heap hc) hc hf7
        (State.lt_next_of_heap hx7) hx7 hs7 hf9 (Hide.intro hok) v (Hide.intro hv) (Hide.intro hA)
        (State.lt_next_of_heap hd) hl40
        i1 i2 i3 i4 i5
    · exact run_seg10_eof σ0 a vals fr σ et xs i cd d s fs ys1 ys2 ys3 ys4 m1 m2 m3 m4 ha ha0 hlen
        f0 f1 f7 f12 f11 f3 f9 hd hR hl1 hl2 hl3 hl4 (by omega) hdB1 hdB2 hdB3 hdB4 hR1 hR2 hR3
        hR4 hR5 hD hg.1 hg.2 hinits hstatics i1
  · exact run_seg10_exit σ0 a vals fr σ et xs i cd d s fs ys1 ys2 ys3 ys4 m1 m2 m3 m4 ha f0 f11 hR
      hl1 hl2 hl3 hl4 (hzi (by decide)) (Forall2.length_eq hrec) hR1 hR2 hR3 hR4 hR5 hD hg.1 hl40

/- The verification conditions are applied as they are stated: `bodyWP` must not be unfolded. -/
attribute [local irreducible] bodyWP

abbrev runRefJ : MethodRef := Gen.Cbact01c.«run(Cbact01c$AccountRecord[])».ref

theorem run_isStatic : runRefJ.decl.mods.isStatic = true := rfl

theorem run_vc (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal)) :
    MethodVC Gen.prog (runEnv σ0) 1 runRefJ (runSpecG σ0 a vals) (runInv σ0 a vals) 200 := by
  refine ⟨runBody, rfl, ?_⟩
  intro args σ0' hpre
  obtain ⟨rfl, rfl, hfile, hvalid, hI5⟩ := hpre
  refine ⟨?_, ?_⟩
  · have hl : ((runInv σ0' a vals).inst [.ref a] σ0').lookup 0 = none := rfl
    have hfile' := hfile
    obtain ⟨et, xs, ha, hlen, -⟩ := hfile'
    obtain ⟨i1, i2, i3, i4, i5⟩ := hI5
    have h := run_entry σ0' a vals et xs ha hlen i1 i2 i3 i4 i5
    unfold RunWP at h
    simp only [hl, run_isStatic]
    exact h
  · intro p hp fr σ hJ
    simp only [runInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    subst hp
    have h := run_loop σ0' a vals hfile hvalid hI5 fr σ hJ
    unfold RunWP at h
    exact h

end EquivLean.Modernize.Cbact01c.Java
