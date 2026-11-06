-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermVt3.lean (sha256 e35f0c7892086f49...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVt3
import EquivLean.Modernize.Cbtrn02c.JavaTermDefsH

/-!
# CBTRN02C → Java, termination: thin twins of `JavaRunVt3`

The statements and preambles of the originals over the thin cut list (each cut assertion
a variant comparison, the entry's `True`), calls by `callWPThin` (`callWPT` without the
callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

attribute [local irreducible] VtD VtIn decJ cp037Tab cp037Str cp037Unit

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem vt_tseg17 (d xA aD wX wA : Addr) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hpre : validateTranSpec.pre [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0)
    (h : vt17 [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0 fr σ)
    (hc : ∀ k, 18 ≤ k → k ≤ 35 → cuts.lookup k = none) :
    VtThinWPc [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0 cuts 17 fr σ := by
  have hkeepP := Hide.intro hpre
  obtain ⟨d', xA', aD', wX', wA', t, vals2, accts, fsX, fsA, hargs, hD, hIn, hX, hXk, hA, hAk,
    i1⟩ := hpre
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨fsX', fsA', cc, cd, lim, es, exs, f2, f5, rfl, hcc, hcd, hlim, hes, hesS, hesX, hesA,
    hkeepA⟩ := h d xA aD wX wA rfl
  have hkeepD := Hide.intro hD
  have hkeepI := Hide.intro hIn
  unfold VtD at hD
  obtain ⟨fsd, sc, so, hdo, hdc, hsc, hda, hdt, hso, hol, hamt⟩ := hD
  have hsoL : (cp037Str (Model.tOrig t)).length = 26 := by rw [cp037Str_length]; exact hol
  have hdX : d ≠ wX := by
    intro he
    rw [he, hX] at hdo
    simp at hdo
  have hdA : d ≠ wA := by
    intro he
    rw [he, hA] at hdo
    simp at hdo
  have hsoX : so ≠ wX := by
    intro he
    rw [he, hX] at hso
    cases hso
  have hsoA : so ≠ wA := by
    intro he
    rw [he, hA] at hso
    cases hso
  clear hIn hdc hsc hamt
  generalize hO : cp037Str (Model.tOrig t) = origS at hso hsoL
  generalize hM : BitVec.ofInt 64 (Model.tAmt t) = amt at hda
  have hkeepO := Hide.intro (And.intro hO hM)
  clear hO hM hol
  have c18 := hc 18 (by omega) (by omega)
  have c19 := hc 19 (by omega) (by omega)
  have c20 := hc 20 (by omega) (by omega)
  have c21 := hc 21 (by omega) (by omega)
  have c22 := hc 22 (by omega) (by omega)
  have c23 := hc 23 (by omega) (by omega)
  have c24 := hc 24 (by omega) (by omega)
  have c25 := hc 25 (by omega) (by omega)
  have c26 := hc 26 (by omega) (by omega)
  have c27 := hc 27 (by omega) (by omega)
  have c28 := hc 28 (by omega) (by omega)
  have c29 := hc 29 (by omega) (by omega)
  have c30 := hc 30 (by omega) (by omega)
  have c31 := hc 31 (by omega) (by omega)
  have c32 := hc 32 (by omega) (by omega)
  have c33 := hc 33 (by omega) (by omega)
  have c34 := hc 34 (by omega) (by omega)
  have c35 := hc 35 (by omega) (by omega)
  clear hc
  unfold VtThinWPc
  jvc [vtCallees, compareEbcdicSig, compareEbcdicSpecF, compareEbcdicSpec, Grows, narrow_long,
    narrow_cls, vtVs]

end EquivLean.Modernize.Cbtrn02c.Java
