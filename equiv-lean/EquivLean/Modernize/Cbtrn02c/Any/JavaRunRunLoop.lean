import EquivLean.Modernize.Cbtrn02c.Any.JavaRunPL4
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunML

/-!
# CBTRN02C → Java: the main loop of `run`

`L65`: the loop head after `k` daily transactions (the state holds `G.st k`); `L75`: after
`validateTran` on transaction `k` (its reject reason, the cross-reference and account it found).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The account table holds `AccountRecord`s (its element type). -/
def AdEt (σ : State) (aD : Addr) : Prop :=
  ∃ xs, σ.heap aD = some (.array (.cls "Cbtrn02c$AccountRecord") xs)

/-- `run`'s objects were allocated by `run`. -/
def Fresh (σ0 : State) (A : Addrs) : Prop :=
  ∀ a ∈ [A.r, A.lD, A.lT, A.lR, A.lCW, A.lAR, A.lCR, A.aD, A.lC, A.lK, A.wX, A.wA, A.wC, A.wT],
    σ0.next ≤ a

/-- **The main loop** (statement 65): `k` transactions processed, the counters, the state holds
the model state after them. -/
def L65 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (A : Addrs) (k : Nat) (next z : I32) (tx rej : I64) (et : JType) (xsD : List Value),
    Locs65 g A fr ∧ fr.get 14 = some (.int next) ∧ fr.get 4 = some (.int z) ∧
    fr.get 9 = some (.long tx) ∧ fr.get 10 = some (.long rej) ∧
    σ.heap g.a1 = some (.array et xsD) ∧ xsD.length = g.trans.length ∧
    next.toInt = k ∧ k ≤ g.trans.length ∧ (z = 0#32 ∨ (z = 1#32 ∧ k = g.trans.length)) ∧
    tx = BitVec.ofNat 64 (k % 1000000000) ∧ rej = BitVec.ofNat 64 ((g.st k).rejects % 1000000000) ∧
    Hide (W σ A (g.st k) ∧ MV (g.st k) ∧ AdEt σ A.aD ∧ Fresh σ0 A) ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics

/-- After `validateTran` (statement 75): the transaction `k` is `d`, its reject reason `c`; when
it is valid, `xrefWs` and `acctWs` hold its cross-reference and account. -/
def L75 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (A : Addrs) (k : Nat) (next c : I32) (tx rej : I64) (et : JType) (xsD : List Value) (d : Addr),
    Locs65 g A fr ∧ fr.get 14 = some (.int next) ∧ fr.get 9 = some (.long tx) ∧
    fr.get 10 = some (.long rej) ∧ fr.get 30 = some (.ref d) ∧ fr.get 15 = some (.int c) ∧
    σ.heap g.a1 = some (.array et xsD) ∧ xsD.length = g.trans.length ∧ xsD[k]? = some (.ref d) ∧
    k < g.trans.length ∧ next.toInt = k + 1 ∧
    tx = BitVec.ofNat 64 ((k + 1) % 1000000000) ∧ rej = BitVec.ofNat 64 ((g.st k).rejects % 1000000000) ∧
    c = BitVec.ofInt 32 (vreason g.xrefs (g.st k).accts (g.trec k)) ∧
    Hide (W σ A (g.st k) ∧ MV (g.st k) ∧ AdEt σ A.aD ∧ Fresh σ0 A ∧
      (vreason g.xrefs (g.st k).accts (g.trec k) = 0 → ∃ x a,
        Model.findXref g.xrefs (Model.tCard (g.trec k)) = some x ∧
        Model.findAcct (g.st k).accts (Model.xAcct x) = some a ∧
        JRecAt CardXrefRecord xrCls σ (.ref A.wX) x ∧
        JRecAt AccountRecord acCls σ (.ref A.wA) a)) ∧
    Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics

theorem l65_init {g : G} {σ0 σ : State} {fr : Frame} {lC lK wX wA wC wT : Addr}
    (hin : RunIn g.args σ0 g.trans g.xrefs g.accts g.cats g.clk)
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
    L65 g g.args σ0 fr σ := by
  obtain ⟨hg, hinits, hstat, -⟩ := hS
  have hW := W_init hin hP hX hA hC hT hFC hFT h1 h2 h3 h4 hg
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
    forall2_length hf1, by decide, Nat.zero_le _, Or.inl rfl, by decide, ?_, ?_, hg, hinits, hstat⟩
  · rw [G.st_zero]; rfl
  · rw [G.st_zero]; exact Hide.intro ⟨hW.1, hW.2.2, hAd, hFr⟩

end EquivLean.Modernize.Cbtrn02c.Java
