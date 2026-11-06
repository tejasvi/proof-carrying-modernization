/-
  Jimple/Interp.lean

  An executable interpreter for the semantics: the same `step` function, with fuel and
  every nondeterministic choice resolved to `0`. `runM_sound` shows that each outcome it
  computes is allowed by the relational semantics, so running it on real programs and
  comparing with the JVM tests the semantics itself.
-/
import Jimple.Semantics

namespace Jimple

mutual
def runM (P : Program) : Nat → MethodRef → List Value → State → Option Outcome
  | 0, _, _, _ => none
  | n + 1, m, args, σ =>
    match m.decl.body with
    | some b => runB P n b 0 (Frame.init m.decl.mods.isStatic args) σ
    | none => some (.wrong "abstract or native method")

def runV (P : Program) : Nat → MethodSig → ClassName → List Value → State → Option Outcome
  | 0, _, _, _, _ => none
  | n + 1, sig, c, args, σ =>
    match P.selectVirtual c sig.sub with
    | .jimple m => runM P n m args σ
    | .native lc =>
      match args with
      | .ref a :: rest =>
        match σ.heap a with
        | some (.plain c' fs) =>
          if c' = c then
            match Native.plainInst P sig lc a c fs rest σ with
            | some r => (runR P n r).map EvOut.toOutcome
            | none => some (.wrong "no model for library method")
          else none
        | _ => none
      | _ => none
    | .none why => if P.concrete c then some (.wrong why) else none

def runR (P : Program) {α : Type} : Nat → Res α → Option α
  | 0, _ => none
  | _ + 1, .ret a => some a
  | n + 1, .call _ (.method m) args σ k =>
    match runM P n m args σ with
    | some o => runR P n (k o)
    | none => none
  | n + 1, .call sig (.virtual c) args σ k =>
    match runV P n sig c args σ with
    | some o => runR P n (k o)
    | none => none
  | n + 1, .choose k => runR P n (k 0)

def runB (P : Program) : Nat → Body → Nat → Frame → State → Option Outcome
  | 0, _, _, _, _ => none
  | n + 1, b, pc, fr, σ =>
    match runR P n (step P b pc fr σ) with
    | some r =>
      match afterStep P b pc fr r with
      | .cont pc' fr' σ' => runB P n b pc' fr' σ'
      | .done o => some o
    | none => none
end

mutual
theorem runM_sound (P : Program) : ∀ n m args σ o, runM P n m args σ = some o → MExec P m args σ o
  | 0, _, _, _, _, h => by simp [runM] at h
  | n + 1, m, args, σ, o, h => by
    unfold runM at h
    split at h
    · next b hb => exact .body hb (runB_sound P n b 0 _ σ o h)
    · next hb => cases h; exact .noBody hb

theorem runV_sound (P : Program) : ∀ n sig c args σ o, runV P n sig c args σ = some o →
    VExec P sig c args σ o
  | 0, _, _, _, _, _, h => by simp [runV] at h
  | n + 1, sig, c, args, σ, o, h => by
    unfold runV at h
    split at h
    · next m hm => exact .jimple hm (runM_sound P n m args σ o h)
    · next lc hlc =>
      split at h
      · next a rest =>
        split at h
        · next c' fs hheap =>
          split at h
          · next hc =>
            subst hc
            split at h
            · next r hr =>
              cases hrun : runR P n r with
              | none => simp [hrun] at h
              | some ev =>
                simp [hrun] at h
                subst h
                exact .native hlc hheap hr (runR_sound P n r ev hrun)
            · next hr => cases h; exact .noModel hlc hheap hr
          · simp at h
        · simp at h
      · simp at h
    · next why hwhy =>
      split at h
      · next hc => cases h; exact .none hwhy hc
      · simp at h

theorem runR_sound (P : Program) {α : Type} : ∀ n (r : Res α) a, runR P n r = some a → RExec P r a
  | 0, _, _, h => by simp [runR] at h
  | _ + 1, .ret a', a, h => by simp [runR] at h; subst h; exact .ret
  | n + 1, .call _ (.method m) args σ k, a, h => by
    simp only [runR] at h
    split at h
    · next o ho => exact .callM (runM_sound P n m args σ o ho) (runR_sound P n (k o) a h)
    · simp at h
  | n + 1, .call sig (.virtual c) args σ k, a, h => by
    simp only [runR] at h
    split at h
    · next o ho => exact .callV (runV_sound P n sig c args σ o ho) (runR_sound P n (k o) a h)
    · simp at h
  | n + 1, .choose k, a, h => by
    simp only [runR] at h
    exact .choose 0 (runR_sound P n (k 0) a h)

theorem runB_sound (P : Program) : ∀ n b pc fr σ o, runB P n b pc fr σ = some o →
    BExec P b pc fr σ o
  | 0, _, _, _, _, _, h => by simp [runB] at h
  | n + 1, b, pc, fr, σ, o, h => by
    unfold runB at h
    split at h
    · next r hr =>
      split at h
      · next pc' fr' σ' hc => exact .cont (runR_sound P n _ r hr) hc (runB_sound P n b pc' fr' σ' o h)
      · next o' hd => cases h; exact .done (runR_sound P n _ r hr) hd
    · simp at h
end

/-! ### Running a program from `main` -/

def mainSig (cls : ClassName) : MethodSig :=
  ⟨cls, .void, "main", [.array (.cls "java.lang.String")]⟩

/-- Run `cls.main(new String[0])` from the empty state (after initializing `cls`). -/
def runMain (P : Program) (cls : ClassName) (fuel : Nat := 100000000) : Option Outcome :=
  match P.selectStatic (mainSig cls) with
  | .jimple m =>
    let (arr, σ) := State.empty.alloc (.array (.cls "java.lang.String") [])
    let prog : Res EvOut := initThen P m.cls σ fun σ => callM (mainSig cls) m [.ref arr] σ
    (runR P fuel prog).map EvOut.toOutcome
  | _ => some (.wrong "no main method")

/-- Text printed to `System.out`, or a description of how the run ended otherwise. -/
def runMainOutput (P : Program) (cls : ClassName) (fuel : Nat := 100000000) : String :=
  match runMain P cls fuel with
  | some (.normal _ σ) => JStr.toLean σ.out
  | some (.exc e σ) =>
    let cls := match σ.heap e with
      | some o => match o.ty with | .cls c => c | _ => "?"
      | none => "?"
    JStr.toLean σ.out ++ s!"<uncaught exception {cls}>"
  | some (.wrong m) => s!"<wrong: {m}>"
  | none => "<out of fuel>"

end Jimple
