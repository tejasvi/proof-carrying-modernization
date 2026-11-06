import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunLoop
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunT3
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunModelX
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunWAb
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5d
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM0s
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM1
import EquivLean.Modernize.Cbtrn02c.Any.JavaSpec

/-!
# CBTRN02C → Java: `run` on any input, the definitions

`runSpecGX g`: `run`'s contract for fixed inputs `g` (`Model.runX`'s outputs); `RunWPcX`: the
symbolic execution of `run`'s body against the final callee contracts `runCX`; `L65X`/`L75X`: the
main loop's invariants with the any-input model state (`G.stx k = ⟨G.st k, false⟩`: no stop yet).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The precondition of `run` on any input, with fixed inputs. -/
def RunPreGX (g : G) (args : List Value) (σ : State) : Prop :=
  args = g.args ∧ Any.Java.RunIn g.args σ g.trans g.xrefs g.accts g.cats g.clk ∧ Inits σ

/-- The postcondition of `run` on any input, with fixed inputs (the outputs of `Model.runX`). -/
def RunPostGX (g : G) (r : Option Value) (σ' : State) : Prop :=
  ∃ res fs l k xs mods, r = some (.ref res) ∧
    σ'.heap res = some (.plain "Cbtrn02c$Result" fs) ∧
    Fields.get fs ("Cbtrn02c$Result", "displays") = some (.ref l) ∧
    σ'.heap l = some (.list k xs mods) ∧ Forall2 (JStrAt σ') xs (g.outX.disp.map jline) ∧
    ListOf σ' fs "transactFileWrites" TranRecord "Cbtrn02c$TranRecord" g.outX.tranW ∧
    ListOf σ' fs "dalyrejsFileWrites" RejectRecord "Cbtrn02c$RejectRecord" g.outX.rejW ∧
    ListOf σ' fs "tcatbalFileWrites" TranCatBalRecord "Cbtrn02c$TranCatBalRecord" g.outX.catW ∧
    ListOf σ' fs "accountFileRewrites" AccountRecord "Cbtrn02c$AccountRecord" g.outX.acctRW ∧
    ListOf σ' fs "tcatbalFileRewrites" TranCatBalRecord "Cbtrn02c$TranCatBalRecord" g.outX.catRW ∧
    Fields.get fs ("Cbtrn02c$Result", "returnCode") = some (.int (BitVec.ofInt 32 g.outX.rc)) ∧
    Fields.get fs ("Cbtrn02c$Result", "abended") = some (.int (if g.outX.abended then 1 else 0))

def runSpecGX (g : G) : Spec := Spec.of (RunPreGX g) (fun _ _ r σ' => RunPostGX g r σ')

/-- The callee contracts of `run`. -/
def runCX : Contracts :=
  [(copyAccountSigT, copyAccountSpecF), (copyTcatSigT, copyTcatSpecF), (spacesSigT, spacesSpec),
   (ctorXRSig, ctorXRSpec), (ctorACSig, ctorACSpec), (ctorTCSig, ctorTCSpec), (ctorTRSig, ctorTRSpec),
   (padNumSig, padNumSpec), (validateTranSig, validateTranSpec), (writeRejectSig, writeRejectSpec),
   (postTransactionSig, postTransactionSpec)]

/-- `run`'s postcondition on any input, folded. -/
def runPostX (g : G) (σ0 : State) : Outcome → Prop := (runSpecGX g).post g.args σ0

attribute [irreducible] runPostX

/-- Symbolic execution of `run`'s body from `pc` against the cut list `cuts`. -/
def RunWPcX (g : G) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog runCX.env 1) runBodyT cuts (runPostX g σ0) 60 pc fr σ

attribute [irreducible] RunWPcX

theorem RunWPcX_eq (g : G) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) :
    RunWPcX g σ0 cuts pc fr σ = bodyWP Gen.prog (callWP Gen.prog runCX.env 1) runBodyT cuts
      ((runSpecGX g).post g.args σ0) 60 pc fr σ := by
  unfold RunWPcX runPostX
  rfl

set_option maxRecDepth 4000 in
/-- **`W` at the first visit of the main loop**: the state holds `Model.init`. -/
theorem W_initX {g : G} {σ0 σ : State} {lC lK wX wA wC wT : Addr}
    (hin : Any.Java.RunIn g.args σ0 g.trans g.xrefs g.accts g.cats g.clk) (hP : PreL g σ0 σ lC lK)
    (hX : WSObj σ wX xrCls (keysOf CardXrefRecord xrCls))
    (hA : WSObj σ wA acCls (keysOf AccountRecord acCls))
    (hC : WSObj σ wC tcCls (keysOf TranCatBalRecord tcCls))
    (hT : WSObj σ wT trCls (keysOf TranRecord trCls))
    (hFC : WSFill σ wC tcCls (Model.sp 22)) (hFT : WSFill σ wT trCls (Model.sp 20))
    (h1 : lK < wX) (h2 : wX < wA) (h3 : wA < wC) (h4 : wC < wT) (hg : Grows σ0 σ) :
    W σ (A0 σ0 lC lK wX wA wC wT) (Model.init g.accts g.cats) ∧
      Inp σ g (A0 σ0 lC lK wX wA wC wT) ∧ MV (Model.init g.accts g.cats) := by
  obtain ⟨a1, a2, a3, a4, cs, hargs, hd, hx, ha, hc, hcs, -, hv1, hv2, hv3, hv4, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨hR, ⟨⟨mD, hD⟩, hS, ⟨mT, hT0⟩, ⟨mR, hR0⟩, ⟨mCW, hCW0⟩, ⟨mAR, hAR0⟩, ⟨mCR, hCR0⟩⟩,
    ⟨ys, hys, hysf, hysa⟩, ⟨xs, m, hxs, hxsf, hxsa⟩, ⟨mK, hK⟩, hlC, hlCK⟩ := hP
  obtain ⟨et3, xs3, -, hl3, hf3⟩ := ha
  obtain ⟨et4, xs4, -, hl4, hf4⟩ := hc
  have hlen3 := forall2_length hf3
  have hlen4 := forall2_length hf4
  have hlenys := forall2_length hysf
  have hlenxs := forall2_length hxsf
  have hws : ∀ w ∈ (A0 σ0 lC lK wX wA wC wT).ws, σ0.next ≤ w := by
    intro w hw
    simp only [Addrs.ws, A0, List.mem_cons, List.not_mem_nil, or_false] at hw
    jomega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hX, hA, hC, hT, hFC, hFT, ?_⟩,
    ⟨arec_input hd hg hws, arec_input hx hg hws, jstrAt_grows hcs hg⟩, hv3, hv4, ?_⟩
  · exact hR
  · exact ⟨[.ref (σ0.next + 7)], mD, hD, .cons ⟨σ0.next + 7, rfl, hS⟩ .nil, by simp⟩
  · exact ⟨[], mT, hT0, .nil, by simp, by decide⟩
  · exact ⟨[], mR, hR0, .nil, by simp, by decide⟩
  · exact ⟨[], mCW, hCW0, .nil, by simp, by decide⟩
  · exact ⟨[], mAR, hAR0, .nil, by simp, by decide⟩
  · exact ⟨[], mCR, hCR0, .nil, by simp, by decide⟩
  · exact ⟨_, ys, hys, hysf, fun v hv w hw => by
      intro hvw
      subst hvw
      exact not_ws (hysa _ hv w rfl).2 h1 h2 h3 h4 w hw rfl, by omega⟩
  · exact ⟨xs, m, hxs, hxsf, fun v hv w hw => by
      intro hvw
      subst hvw
      exact not_ws (hxsa _ hv w rfl).2 h1 h2 h3 h4 w hw rfl, by omega⟩
  · exact ⟨[], mK, hK, .nil, by decide⟩
  · simp only [A0, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    repeat' constructor
    all_goals jomega
  · simp [Model.init, Model.sp]


/-- **The main loop** (statement 65): `k` transactions processed, the counters, the state holds
the model state after them. -/
def L65X (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (A : Addrs) (k : Nat) (next z : I32) (tx rej : I64) (et : JType) (xsD : List Value),
    Locs65 g A fr ∧ fr.get 14 = some (.int next) ∧ fr.get 4 = some (.int z) ∧
    fr.get 9 = some (.long tx) ∧ fr.get 10 = some (.long rej) ∧
    σ.heap g.a1 = some (.array et xsD) ∧ xsD.length = g.trans.length ∧
    next.toInt = k ∧ k ≤ g.trans.length ∧ (z = 0#32 ∨ (z = 1#32 ∧ k = g.trans.length)) ∧
    tx = BitVec.ofNat 64 (k % 1000000000) ∧ rej = BitVec.ofNat 64 ((g.st k).rejects % 1000000000) ∧
    g.stx k = ⟨g.st k, false⟩ ∧ Hide (W σ A (g.st k) ∧ MV (g.st k) ∧ AdEt σ A.aD ∧ Fresh σ0 A) ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics

/-- After `validateTran` (statement 75): the transaction `k` is `d`, its reject reason `c`; when
it is valid, `xrefWs` and `acctWs` hold its cross-reference and account. -/
def L75X (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (A : Addrs) (k : Nat) (next c : I32) (tx rej : I64) (et : JType) (xsD : List Value) (d : Addr),
    Locs65 g A fr ∧ fr.get 14 = some (.int next) ∧ fr.get 9 = some (.long tx) ∧
    fr.get 10 = some (.long rej) ∧ fr.get 30 = some (.ref d) ∧ fr.get 15 = some (.int c) ∧
    fr.get 4 = some (.int 0#32) ∧
    σ.heap g.a1 = some (.array et xsD) ∧ xsD.length = g.trans.length ∧ xsD[k]? = some (.ref d) ∧
    k < g.trans.length ∧ next.toInt = k + 1 ∧
    tx = BitVec.ofNat 64 ((k + 1) % 1000000000) ∧ rej = BitVec.ofNat 64 ((g.st k).rejects % 1000000000) ∧
    c = BitVec.ofInt 32 (vreason g.xrefs (g.st k).accts (g.trec k)) ∧ g.stx k = ⟨g.st k, false⟩ ∧
    Hide (W σ A (g.st k) ∧ MV (g.st k) ∧ AdEt σ A.aD ∧ Fresh σ0 A ∧
      (vreason g.xrefs (g.st k).accts (g.trec k) = 0 → ∃ x a,
        Model.findXref g.xrefs (Model.tCard (g.trec k)) = some x ∧
        Model.findAcct (g.st k).accts (Model.xAcct x) = some a ∧
        JRecAt CardXrefRecord xrCls σ (.ref A.wX) x ∧
        JRecAt AccountRecord acCls σ (.ref A.wA) a)) ∧
    Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics

theorem l65x_init {g : G} {σ0 σ : State} {fr : Frame} {lC lK wX wA wC wT : Addr}
    (hin : Any.Java.RunIn g.args σ0 g.trans g.xrefs g.accts g.cats g.clk)
    (hloc : LocsP g σ0 fr lC lK) (f6 : fr.get 6 = some (.ref wX)) (f13 : fr.get 13 = some (.ref wA))
    (f29 : fr.get 29 = some (.ref wC)) (f28 : fr.get 28 = some (.ref wT))
    (f14 : fr.get 14 = some (.int 0#32)) (f4 : fr.get 4 = some (.int 0#32))
    (f9 : fr.get 9 = some (.long 0#64)) (f10 : fr.get 10 = some (.long 0#64))
    (hP : PreL g σ0 σ lC lK)
    (hX : WSObj σ wX xrCls (keysOf CardXrefRecord xrCls))
    (hA : WSObj σ wA acCls (keysOf AccountRecord acCls))
    (hC : WSObj σ wC tcCls (keysOf TranCatBalRecord tcCls))
    (hT : WSObj σ wT trCls (keysOf TranRecord trCls))
    (hFC : WSFill σ wC tcCls (Model.sp 22)) (hFT : WSFill σ wT trCls (Model.sp 20))
    (h1 : lK < wX) (h2 : wX < wA) (h3 : wA < wC) (h4 : wC < wT) (hS : StateP σ0 σ) :
    L65X g g.args σ0 fr σ := by
  obtain ⟨hg, hinits, hstat, -⟩ := hS
  have hW := W_initX hin hP hX hA hC hT hFC hFT h1 h2 h3 h4 hg
  have hAd : AdEt σ (A0 σ0 lC lK wX wA wC wT).aD := by
    obtain ⟨-, -, ⟨ys, hys, -, -⟩, -⟩ := hP
    exact ⟨ys, hys⟩
  have hFr : Fresh σ0 (A0 σ0 lC lK wX wA wC wT) := by
    obtain ⟨-, -, -, -, -, h9, hCK⟩ := hP
    intro a ha
    simp only [A0, List.mem_cons, List.not_mem_nil, or_false] at ha
    jomega
  obtain ⟨a1, a2, a3, a4, cs, hargs, ⟨et1, xs1, h1h, hl1, hf1⟩, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨f32, f0, f16, f31, f8, f11, f12⟩ := hloc
  refine ⟨A0 σ0 lC lK wX wA wC wT, 0, 0#32, 0#32, 0#64, 0#64, et1, xs1,
    ⟨f32, f0, f16, f31, f8, f11, f12, f6, f13, f29, f28⟩, f14, f4, f9, f10, heap_of_grows hg h1h,
    forall2_length hf1, by decide, Nat.zero_le _, Or.inl rfl, by decide, ?_, G.stx_zero g, ?_, hg, hinits,
    hstat⟩
  · rw [G.st_zero]; rfl
  · rw [G.st_zero]; exact Hide.intro ⟨hW.1, hW.2.2, hAd, hFr⟩

end EquivLean.Modernize.Cbtrn02c.Java
