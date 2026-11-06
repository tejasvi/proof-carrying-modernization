-- Termination package by JimpleLean's session: TermPk/Cbact01c/JavaTermLink.lean (sha256 d8aecd0a3852cd52...); only the module root renamed.
import EquivLean.Modernize.Cbact01c.JavaTermHelpers
import EquivLean.Modernize.Cbact01c.JavaTermOther
import EquivLean.Modernize.Cbact01c.JavaTermRead
import EquivLean.Modernize.Cbact01c.JavaTermDefs

/-!
# CBACT01C → Java: `run` terminates, and is totally correct

Each helper terminates (`*_term`: its `MethodVC` with its thin VC, `Jimple.TermVC.of_thin`); the
contracts `run` uses (`runCallees`, the `*SpecR` and `*SpecF` variants) terminate as the
helpers do, their preconditions being stronger (`ContractTerm.mono`). `run_thin` collects the
thin VCs of `run` as `run_vc` does; `run_term`, `run_total` as for the other programs.
-/

-- as in the originals (JimpleLean 2006Z took `ite_nat_ne` out of `jsimp`)
attribute [local jsimp high] Jimple.ite_nat_ne

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

/-! ## The helpers -/

theorem spaces_term : ∀ args σ, spacesSpec.pre args σ → MTerm Gen.prog spacesRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) spaces_vc spaces_thin)
theorem pad_term : ∀ args σ, padSpec.pre args σ → MTerm Gen.prog padRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) pad_vc pad_thin)
theorem zoned_term : ∀ args σ, zonedSpec.pre args σ → MTerm Gen.prog zonedRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) zoned_vc zoned_thin)
theorem cobdatft_term : ∀ args σ, cobdatftSpec.pre args σ → MTerm Gen.prog cobdatftRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) cobdatft_vc cobdatft_thin)

set_option maxHeartbeats 0 in
theorem spaces_cterm : ContractTerm Gen.prog spacesSig spacesSpec := by jcontract_term [spaces_term]
set_option maxHeartbeats 0 in
theorem pad_cterm : ContractTerm Gen.prog padSig padSpec := by jcontract_term [pad_term]
set_option maxHeartbeats 0 in
theorem zoned_cterm : ContractTerm Gen.prog zonedSig zonedSpec := by jcontract_term [zoned_term]
set_option maxHeartbeats 0 in
theorem cobdatft_cterm : ContractTerm Gen.prog cobdatftSig cobdatftSpec := by
  jcontract_term [cobdatft_term]

theorem spaces_ctermF : ContractTerm Gen.prog spacesSig spacesSpecF := ContractTerm.mono spaces_cterm fun _ _ h => h
theorem pad_ctermF : ContractTerm Gen.prog padSig padSpecF := ContractTerm.mono pad_cterm fun _ _ h => h

theorem textCallees_term :
    ∀ sig S, (textCallees.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [textCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact ⟨zoned_cterm, pad_cterm⟩) _ _

theorem accountRecordText_term :
    ∀ args σ, accountRecordTextSpec.pre args σ → MTerm Gen.prog accountRecordTextRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) textCallees_valid textCallees_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) accountRecordText_vc accountRecordText_thin)

theorem displayAcctRecord_term (L : Addr) :
    ∀ args σ, (displayAcctRecordSpec L).pre args σ → MTerm Gen.prog displayAcctRecordRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      simp only [dispCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact zoned_ok))
    (Contracts.term_of_ok (by
      simp only [dispCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact zoned_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (displayAcctRecord_vc L)
      (displayAcctRecord_thin L))

theorem writeOutRecord_term (L : Addr) :
    ∀ args σ, (writeOutRecordSpec L).pre args σ → MTerm Gen.prog writeOutRecordRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      simp only [outCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact pad_okF))
    (Contracts.term_of_ok (by
      simp only [outCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact pad_ctermF) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (writeOutRecord_vc L) (writeOutRecord_thin L))

theorem writeArrayRecord_term (L : Addr) :
    ∀ args σ, (writeArrayRecordSpec L).pre args σ → MTerm Gen.prog writeArrayRecordRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      simp only [arrCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact spaces_okF))
    (Contracts.term_of_ok (by
      simp only [arrCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact spaces_ctermF) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (writeArrayRecord_vc L)
      (writeArrayRecord_thin L))

theorem writeVbrcRecords_term (L1 L4 : Addr) :
    ∀ args σ, (writeVbrcRecordsSpec L1 L4).pre args σ → MTerm Gen.prog writeVbrcRecordsRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) textCallees_valid textCallees_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (writeVbrcRecords_vc L1 L4)
      (writeVbrcRecords_thin L1 L4))

set_option maxHeartbeats 0 in
theorem accountRecordText_cterm : ContractTerm Gen.prog accountRecordTextSig accountRecordTextSpec := by
  jcontract_term [accountRecordText_term]
set_option maxHeartbeats 0 in
theorem displayAcctRecord_cterm (L : Addr) :
    ContractTerm Gen.prog displayAcctRecordSig (displayAcctRecordSpec L) := by
  jcontract_term [displayAcctRecord_term L]
set_option maxHeartbeats 0 in
theorem writeOutRecord_cterm (L : Addr) :
    ContractTerm Gen.prog writeOutRecordSig (writeOutRecordSpec L) := by
  jcontract_term [writeOutRecord_term L]
set_option maxHeartbeats 0 in
theorem writeArrayRecord_cterm (L : Addr) :
    ContractTerm Gen.prog writeArrayRecordSig (writeArrayRecordSpec L) := by
  jcontract_term [writeArrayRecord_term L]
set_option maxHeartbeats 0 in
theorem writeVbrcRecords_cterm (L1 L4 : Addr) :
    ContractTerm Gen.prog writeVbrcRecordsSig (writeVbrcRecordsSpec L1 L4) := by
  jcontract_term [writeVbrcRecords_term L1 L4]

/-! ## The contracts `run` uses (preconditions as in `JavaRun`'s `*R_sat`) -/

theorem padR_cterm (σ0 : Jimple.State) : ContractTerm Gen.prog padSig (padSpecR σ0) :=
  ContractTerm.mono pad_cterm fun _ _ h => h.1

theorem cobdatftR_cterm (σ0 : Jimple.State) : ContractTerm Gen.prog cobdatftSig (cobdatftSpecR σ0) :=
  ContractTerm.mono cobdatft_cterm fun _ _ h => h.1

theorem accountRecordTextR_cterm (σ0 : Jimple.State) :
    ContractTerm Gen.prog accountRecordTextSig (accountRecordTextSpecR σ0) :=
  ContractTerm.mono accountRecordText_cterm (by
    rintro args σ ⟨c, hargs, hok, hg, -, hi⟩
    exact ⟨c, hargs, acctOk_of_grows hg (Hide.elim hok), hi⟩)

theorem displayAcctRecordR_cterm (σ0 : Jimple.State) (L : Addr) (hL : σ0.next < L) :
    ContractTerm Gen.prog displayAcctRecordSig (displayAcctRecordSpecR σ0 L) :=
  ContractTerm.mono (displayAcctRecord_cterm L) (by
    rintro args σ ⟨res, c, fs, ys, m, hargs, hres, hfs, hl, hrl, hok, hg, -, hi⟩
    exact ⟨res, c, fs, ys, m, hargs, hres, hfs, hl, hrl, State.lt_next_of_heap hl,
      acctOkB_of_grows hg (Hide.elim hok) (by jomega), hi⟩)

theorem writeOutRecordR_cterm (σ0 : Jimple.State) (L : Addr) (hL : σ0.next < L) :
    ContractTerm Gen.prog writeOutRecordSig (writeOutRecordSpecR σ0 L) :=
  ContractTerm.mono (writeOutRecord_cterm L) (by
    rintro args σ ⟨res, c, d, cd, fs, ys, m, sd, hargs, hres, hfs, hl, hrl, hok, hg, -, hd, hsd,
      hdL, hi1, hi2⟩
    exact ⟨res, c, d, cd, fs, ys, m, sd, hargs, hres, hfs, hl, hrl, State.lt_next_of_heap hl,
      acctOkB_of_grows hg (Hide.elim hok) (by jomega), hd, hsd, hdL, hi1, hi2⟩)

theorem writeArrayRecordR_cterm (σ0 : Jimple.State) (L : Addr) (hL : σ0.next < L) :
    ContractTerm Gen.prog writeArrayRecordSig (writeArrayRecordSpecR σ0 L) :=
  ContractTerm.mono (writeArrayRecord_cterm L) (by
    rintro args σ ⟨res, c, fs, ys, m, hargs, hres, hfs, hl, hrl, hok, hg, -, hi1, hi2⟩
    exact ⟨res, c, fs, ys, m, hargs, hres, hfs, hl, hrl, State.lt_next_of_heap hl,
      acctOkB_of_grows hg (Hide.elim hok) (by jomega), hi1, hi2⟩)

theorem writeVbrcRecordsR_cterm (σ0 : Jimple.State) (L1 L4 : Addr) (hL : σ0.next < L1)
    (h14 : L1 < L4) : ContractTerm Gen.prog writeVbrcRecordsSig (writeVbrcRecordsSpecR σ0 L1 L4) :=
  ContractTerm.mono (writeVbrcRecords_cterm L1 L4) (by
    rintro args σ ⟨res, c, fs, ys1, m1, ys4, m4, hargs, hres, hf1, hf4, hrl, hl1, hl4, hok, hg, -,
      hi⟩
    exact ⟨res, c, fs, ys1, m1, ys4, m4, hargs, hres, hf1, hf4, h14, hrl,
      State.lt_next_of_heap hl4, hl1, hl4, acctOkB_of_grows hg (Hide.elim hok) (by jomega), hi⟩)

set_option maxHeartbeats 0 in
theorem runCallees_term (σ0 : Jimple.State) : ∀ p ∈ runCallees σ0, ContractTerm Gen.prog p.1 p.2 := by
  simp only [runCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  have h1 : σ0.next < σ0.next + 1 := by jomega
  have h2 : σ0.next < σ0.next + 2 := by jomega
  have h3 : σ0.next < σ0.next + 3 := by jomega
  have h14 : σ0.next + 1 < σ0.next + 4 := by jomega
  exact ⟨spaces_ctermF, padR_cterm σ0, cobdatftR_cterm σ0, displayAcctRecordR_cterm σ0 _ h1,
    writeOutRecordR_cterm σ0 _ h2, writeArrayRecordR_cterm σ0 _ h3,
    writeVbrcRecordsR_cterm σ0 _ _ h1 h14, accountRecordTextR_cterm σ0⟩

theorem runEnv_term (σ0 : Jimple.State) :
    ∀ sig S, ((runEnv σ0).below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S := by
  intro sig S h
  rw [SpecEnv.below_const _ _ (by decide)] at h
  unfold runEnv at h
  by_cases hc : sig.cls = "Cbact01c"
  · simp only [hc, ↓reduceIte] at h
    exact Contracts.term_of_ok (runCallees_term σ0) (fun _ => 0) 1 sig S
      (by rw [SpecEnv.below_const _ _ (by decide)]; exact h)
  · simp only [hc, ↓reduceIte] at h
    cases h

/-! ## `run` -/

/-- From the loop head, in each case of the flags and the record count. -/
theorem run_tloop (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal))
    (hfile : AcctfileFileAt σ0 a vals) (hvalid : ∀ v ∈ vals, AccountRecord.Valid v)
    (hI5 : Inits σ0) (fr : Frame) (σ : Jimple.State)
    (hI : runInv10 σ0 a vals [.ref a] σ0 fr σ) : RunThinWP σ0 a vals 10 fr σ := by
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
      exact run_tseg10_read σ0 a vals fr σ et xs i cd d s fs ys1 ys2 ys3 ys4 m1 m2 m3 m4 c fsc x7 s7
        dbt ha ha0 hlen f0 f1 f7 f12 f11 f3 f9 hd hR hl1 hl2 hl3 hl4 hi0 hlt hdB1 hdB2 hdB3 hdB4
        hR1 hR2 hR3 hR4 hR5 hD hg.1 hg.2 hinits hstatics hw hk hxk2 hs20 (State.lt_next_of_heap hc) hc hf7
        (State.lt_next_of_heap hx7) hx7 hs7 hf9 (Hide.intro hok) v (Hide.intro hv) (Hide.intro hA)
        (State.lt_next_of_heap hd) hl40
        i1 i2 i3 i4 i5
    · exact run_tseg10_eof σ0 a vals fr σ et xs i cd d s fs ys1 ys2 ys3 ys4 m1 m2 m3 m4 ha ha0 hlen
        f0 f1 f7 f12 f11 f3 f9 hd hR hl1 hl2 hl3 hl4 (by omega) hdB1 hdB2 hdB3 hdB4 hR1 hR2 hR3
        hR4 hR5 hD hg.1 hg.2 hinits hstatics i1
  · exact run_tseg10_exit σ0 a vals fr σ et xs i cd d s fs ys1 ys2 ys3 ys4 m1 m2 m3 m4 ha f0 f11 hR
      hl1 hl2 hl3 hl4 (hzi (by decide)) (Forall2.length_eq hrec) hR1 hR2 hR3 hR4 hR5 hD hg.1 hl40

/- The verification conditions are applied as they are stated: `bodyWP` must not be unfolded. -/
attribute [local irreducible] bodyWP

theorem run_thin (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal)) :
    ThinVC Gen.prog (runEnv σ0) 1 runRefJ (runSpecG σ0 a vals) (runInv σ0 a vals) runVs 200 := by
  refine ⟨runBody, rfl, ?_⟩
  intro args σ0' hpre
  obtain ⟨rfl, rfl, hfile, hvalid, hI5⟩ := hpre
  refine ⟨?_, ?_⟩
  · have hl : ((runInv σ0' a vals).inst [.ref a] σ0').lookup 0 = none := rfl
    have hfile' := hfile
    obtain ⟨et, xs, ha, hlen, -⟩ := hfile'
    obtain ⟨i1, i2, i3, i4, i5⟩ := hI5
    have h := run_tentry σ0' a vals et xs ha hlen i1 i2 i3 i4 i5
    unfold RunThinWP0 at h
    simp only [hl, run_isStatic]
    exact h
  · intro p hp fr σ hJ
    simp only [runInv, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    have h := run_tloop σ0' a vals hfile hvalid hI5 fr σ hJ
    unfold RunThinWP at h
    exact h

/-- `run` terminates, for the contract with fixed ghost values. -/
theorem run_termG (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal)) :
    ∀ args σ, (runSpecG σ0 a vals).pre args σ → MTerm Gen.prog runRefJ args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (runEnv_valid (runCallees_valid σ0)) (runEnv_term σ0)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (run_vc σ0 a vals) (run_thin σ0 a vals))

/-- **`run` terminates** on every input of `runSpec`. -/
theorem run_term : ∀ args σ, runSpec.pre args σ → MTerm Gen.prog runRef args σ := by
  intro args σ hpre
  obtain ⟨vals, ⟨a, rfl, hfile, hvalid⟩, i1, i2, i3, i4, i5⟩ := hpre
  exact run_termG σ a vals _ σ ⟨rfl, rfl, hfile, hvalid, ⟨i1, i2, i3, i4, i5⟩⟩

/-- **CBACT01C → Java, total correctness**: on every input of `runSpec`, `run` has an outcome, and
    every outcome satisfies `runSpec`. -/
theorem run_total : ∀ args σ, runSpec.pre args σ →
    (∃ o, MExec Gen.prog runRef args σ o) ∧ ∀ o, MExec Gen.prog runRef args σ o → runSpec.post args σ o :=
  total_of_sat_mterm run_sat run_term

end EquivLean.Modernize.Cbact01c.Java

#print axioms EquivLean.Modernize.Cbact01c.Java.run_term
#print axioms EquivLean.Modernize.Cbact01c.Java.run_total
