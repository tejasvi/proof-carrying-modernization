-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermVt2.lean (sha256 fc6bd572e497a553...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVt2
import EquivLean.Modernize.Cbtrn02c.JavaTermDefsH

/-!
# CBTRN02C → Java, termination: thin twins of `JavaRunVt2`

The statements and preambles of the originals over the thin cut list (each cut assertion
a variant comparison, the entry's `True`), calls by `callWPThin` (`callWPT` without the
callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

attribute [local irreducible] VtD VtIn

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem vt_tseg11 (d xA aD wX wA : Addr) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hpre : validateTranSpec.pre [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0)
    (h : vt11 [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0 fr σ)
    (hc : ∀ k, 12 ≤ k → k ≤ 16 → cuts.lookup k = none)
    (c17 : cuts.lookup 17 = some (fun fr' σ' => vtVs 17 [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0 fr' σ' < vtVs 11 [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0 fr σ)) :
    VtThinWPc [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0 cuts 11 fr σ := by
  have hkeepP := Hide.intro hpre
  obtain ⟨d', xA', aD', wX', wA', t, vals2, accts, fsX, fsA, hargs, hD, hIn, hX, hXk, hA, hAk,
    i1⟩ := hpre
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨fsX', v, f2, f1, f0, f9, f5, rfl, hv, hkeepX⟩ := h d xA aD wX wA rfl
  have hkeepD := Hide.intro hD
  have hkeepI := Hide.intro hIn
  unfold VtD at hD
  unfold VtIn at hIn
  obtain ⟨fsd, sc, so, hdo, hdc, hsc, hda, hdt, hso, hol, hamt⟩ := hD
  obtain ⟨etX, xsX, etA, xsA, hxA, hlX, hshX, hfX, hvX, hnX, haD, hlA, hshA, hfA, hvA, hnA⟩ := hIn
  have hAS : AcctShapes σ0 xsA := acctShapes_of hshA
  have hAall : ∀ v ∈ xsA, ∃ y fs, v = .ref y ∧
      σ0.heap y = some (.plain "Cbtrn02c$AccountRecord" fs) ∧ AllSome acKeys fs := by
    intro v hv
    obtain ⟨x, -, hr⟩ := forall2_ex_mem hfA v hv
    obtain ⟨y, fs, rfl, hy, hf⟩ := hr
    exact ⟨y, fs, rfl, hy, by rw [← keysOf_acct2]; exact allSome_of_jrecT ⟨y, fs, rfl, hy, hf⟩ hy⟩
  have hwXA : wA ≠ wX := by
    intro he
    rw [he, hX] at hA
    simp at hA
  clear hshX hfX hvX hshA hfA hvA hda hdt hso hol hamt hdc hsc hdo
  have c12 := hc 12 (by omega) (by omega)
  have c13 := hc 13 (by omega) (by omega)
  have c14 := hc 14 (by omega) (by omega)
  have c15 := hc 15 (by omega) (by omega)
  have c16 := hc 16 (by omega) (by omega)
  clear hc
  unfold VtThinWPc
  jvc [vtCallees, findAccountSig, findAccountSpecF, findAccountSpec, assignAccountSig,
    assignAccountSpecF, Grows, narrow_long, narrow_cls, vtVs]

end EquivLean.Modernize.Cbtrn02c.Java
