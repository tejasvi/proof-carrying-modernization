import EquivLean.Modernize.Cbact04c.Every.JavaRunRes85

/-!
# CBACT04C → Java, `run`: the read loop's head (statement 85): record `i` read and copied
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_seg85_iter (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreG g g.args σ0) (h : J85 g g.args σ0 fr σ)
    (hc : ∀ i : I32, fr.get 22 = some (.int i) → i.toInt < (g.tcat.length : Int))
    (c86 : cuts.lookup 86 = none) (c87 : cuts.lookup 87 = none) (c88 : cuts.lookup 88 = none)
    (c89 : cuts.lookup 89 = none) (c90 : cuts.lookup 90 = some (J89 g g.args σ0)) :
    RunWPc g σ0 cuts 85 fr σ := by
  obtain ⟨i, hp, acctV, xrefV, lastV, hi0, hilen, hlocs, f22, f12, f3, f14, f25, f16, f17, f4, f5,
    hheap, hstop⟩ := h
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hpre.lens
  have hci := hc i f22
  clear hc
  obtain ⟨-, ⟨b1, b2, b3, b4, q1, c1, hargs, ⟨et1, xs1, h1, hb1, hp1⟩, -, -, -, -, -, -, hv1, -⟩, -⟩ :=
    hpre
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  have hlen1 := Forall2.length_eq hp1
  have hn' : i.toInt.toNat < g.tcat.length := by omega
  have hn : i.toInt.toNat < xs1.length := by omega
  have htr : g.trec i.toInt.toNat = g.tcat[i.toInt.toNat]'hn' := by
    simp [G.trec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn']
  have hrec := forall2_getElem hp1 _ hn
  have hrec2 : JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ0 xs1[i.toInt.toNat]
      (g.trec i.toInt.toNat) := by rw [htr]; exact hrec
  clear hrec hv1 hp1 htr
  obtain ⟨y, fs, hy, hyfs, hyf⟩ := jrec_obj hrec2
  have hpres : ∀ k ∈ keysTC, ∃ v, Fields.get fs ("Cbact04c$TranCatBalRecord", k) = some v :=
    present_keys tranCatBalRecord_jnames hyf
  clear hyf
  have hg0 : Grows σ0 σ := (Hide.elim hheap).1.1
  have hyh := heap_of_grows hg0 hyfs
  have h1' := heap_of_grows hg0 h1
  have hinit : Inits σ := (Hide.elim hheap).1.2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  rw [hy] at hrec2
  have hy' : xs1[i.toInt.toNat]'hn = .ref y := hy
  have hrec' := Hide.intro hrec2
  clear hy hrec2 hyfs h1 hg0
  unfold RunWPc
  jvc [runSpecG, runC, copyTcbSig, Grows]
  refine j89_of_copyF hn' hi0 hstop (Hide.elim hlocs') f12 f3 f14 f25 f16 f17 f4 f5 hheap hrec' hyh ‹_› ‹_›
    ⟨‹_›, ‹_›⟩ ‹_›

end EquivLean.Modernize.Cbact04c.Java
