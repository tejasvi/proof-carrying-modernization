import EquivLean.Modernize.Cbstm03a.Java.Cs.Step

/-!
# CBSTM03A → Java: `createStatement`, the paths through one call of `stmt`/`html`

From a cut point right before a call of `html` (literal or local argument) or `stmt` (local argument) to the cut
point right after it (`cut_html_lit`, `cut_html_loc`, `cut_stmt_loc`), and the last call with the return
(`cut_last`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans keeps_refl keeps_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

theorem wp_eq (g : G) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) :
    wp g args σ0 pc fr σ = bodyWP Gen.prog (callWP Gen.prog csCallees.env 1) body ((inv g).inst args σ0)
      ((specG g).post args σ0) (59 + 1) pc fr σ := by
  unfold wp; rfl

theorem cut_unfold {g : G} {ns nh : Nat} {L : G → List (Nat × JStr)} {bal : Bool} {args : List Value}
    {σ0 : State} {fr : Frame} {σ : State} :
    cut g ns nh L bal args σ0 fr σ ↔ CutI g ns nh (L g) bal σ0 fr σ := by
  unfold cut; exact Iff.rfl

set_option maxRecDepth 20000 in
theorem cut_html_lit {g : G} {args : List Value} {σ0 : State} {pc ns nh : Nat} {L L' : G → List (Nat × JStr)}
    {bal bal' : Bool} {lit : String}
    (hs : body.stmtAt pc = some (.invoke (.static htmlSig [.loc 22, .const (.str lit)])))
    (hnext : ((inv g).inst args σ0).lookup (pc + 1) = some (cut g ns (nh + 1) L' bal' args σ0))
    (hline : (jCreateStatement g.c g.a).2[nh]? = some (hl (JStr.ofString lit)))
    (hlen : (JStr.ofString lit).length < 2147483648)
    (hL : ∀ σ fr, LocsAt σ fr (L g) → LocsAt σ fr (L' g)) (hb : bal' = true → bal = true) :
    ∀ fr σ, cut g ns nh L bal args σ0 fr σ → wp g args σ0 pc fr σ := by
  intro fr σ hI
  rw [cut_unfold] at hI
  rw [wp_eq]
  have hI0 := hI
  have hres := hI.1.1
  have hR := hI.1.2.1
  have hini := hI.1.2.2.2.2.2
  apply wp_html_lit hs hres hR hini hlen
  intro σ' hR' hK' hi' hs'
  rw [hnext]
  show cut g ns (nh + 1) L' bal' args σ0 fr σ'
  rw [cut_unfold]
  obtain ⟨hA, hL2, hb2⟩ := cutI_ht hI0 (grows_alloc σ _) hR' hK' hi' hs' rfl rfl hline
  exact ⟨hA, hL _ _ hL2, fun h => hb2 (hb h)⟩

set_option maxRecDepth 20000 in
theorem cut_html_loc {g : G} {args : List Value} {σ0 : State} {pc ns nh k : Nat} {s : JStr}
    {L L' : G → List (Nat × JStr)} {rest : List (Nat × JStr)} {bal bal' : Bool}
    (hs : body.stmtAt pc = some (.invoke (.static htmlSig [.loc 22, .loc k])))
    (hLk : L g = (k, s) :: rest)
    (hnext : ((inv g).inst args σ0).lookup (pc + 1) = some (cut g ns (nh + 1) L' bal' args σ0))
    (hline : (jCreateStatement g.c g.a).2[nh]? = some (hl s))
    (hL : ∀ σ fr, LocsAt σ fr (L g) → LocsAt σ fr (L' g)) (hb : bal' = true → bal = true) :
    ∀ fr σ, cut g ns nh L bal args σ0 fr σ → wp g args σ0 pc fr σ := by
  intro fr σ hI
  rw [cut_unfold] at hI
  rw [wp_eq]
  have hI0 := hI
  have hres := hI.1.1
  have hR := hI.1.2.1
  have hini := hI.1.2.2.2.2.2
  have hLc := hI.2.1
  rw [hLk] at hLc
  obtain ⟨x, hx1, hx2, hx3⟩ := hLc.1
  apply wp_html_loc hs hres hx1 hx2 hR hini hx3
  intro σ' hR' hK' hi' hs'
  rw [hnext]
  show cut g ns (nh + 1) L' bal' args σ0 fr σ'
  rw [cut_unfold]
  obtain ⟨hA, hL2, hb2⟩ := cutI_ht hI0 (grows_refl σ) hR' hK' hi' hs' rfl rfl hline
  exact ⟨hA, hL _ _ hL2, fun h => hb2 (hb h)⟩

set_option maxRecDepth 20000 in
theorem cut_stmt_loc {g : G} {args : List Value} {σ0 : State} {pc ns nh k : Nat} {s : JStr}
    {L L' : G → List (Nat × JStr)} {rest : List (Nat × JStr)} {bal bal' : Bool}
    (hs : body.stmtAt pc = some (.invoke (.static stmtSig [.loc 22, .loc k])))
    (hLk : L g = (k, s) :: rest)
    (hnext : ((inv g).inst args σ0).lookup (pc + 1) = some (cut g (ns + 1) nh L' bal' args σ0))
    (hline : (jCreateStatement g.c g.a).1[ns]? = some (sl s))
    (hL : ∀ σ fr, LocsAt σ fr (L g) → LocsAt σ fr (L' g)) (hb : bal' = true → bal = true) :
    ∀ fr σ, cut g ns nh L bal args σ0 fr σ → wp g args σ0 pc fr σ := by
  intro fr σ hI
  rw [cut_unfold] at hI
  rw [wp_eq]
  have hI0 := hI
  have hres := hI.1.1
  have hR := hI.1.2.1
  have hini := hI.1.2.2.2.2.2
  have hLc := hI.2.1
  rw [hLk] at hLc
  obtain ⟨x, hx1, hx2, hx3⟩ := hLc.1
  apply wp_stmt_loc hs hres hx1 hx2 hR hini hx3
  intro σ' hR' hK' hi' hs'
  rw [hnext]
  show cut g (ns + 1) nh L' bal' args σ0 fr σ'
  rw [cut_unfold]
  obtain ⟨hA, hL2, hb2⟩ := cutI_st hI0 (grows_refl σ) hR' hK' hi' hs' rfl rfl hline
  exact ⟨hA, hL _ _ hL2, fun h => hb2 (hb h)⟩

-- The last call `stmt(res, dashes)` and the return: the postcondition.
set_option maxRecDepth 20000 in
theorem cut_last (g : G) : CutVC g 146 15 56 LK false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  rw [wp_eq]
  have hres := hI.1.1
  have hR := hI.1.2.1
  have hk0 := hI.1.2.2.1
  have hin0 := hI.1.2.2.2.1
  have hst0 := hI.1.2.2.2.2.1
  have hini := hI.1.2.2.2.2.2
  obtain ⟨x, hx1, hx2, hx3⟩ := hI.2.1.1
  apply wp_stmt_loc rfl hres hx1 hx2 hR hini hx3
  intro σ' hR' hK' hi' hs'
  have hnone : ((inv g).inst args σ0).lookup (146 + 1) = none := rfl
  rw [hnone]
  show bodyWP Gen.prog (callWP Gen.prog csCallees.env 1) body ((inv g).inst args σ0) ((specG g).post args σ0)
    (58 + 1) 147 fr σ'
  rw [bodyWP_succ]
  have hs147 : body.stmtAt 147 = some .returnVoid := rfl
  simp only [step, hs147, stepStmt, wpR, afterStep, specG, Spec.of]
  have e1 : (jCreateStatement g.c g.a).1.take 15 ++ [sl tDashes] = (jCreateStatement g.c g.a).1 := rfl
  have e2 : (jCreateStatement g.c g.a).2.take 56 = (jCreateStatement g.c g.a).2 := rfl
  rw [List.append_assoc, e1, e2] at hR'
  exact ⟨trivial, hR', keepsRes_trans hk0 hK', by rw [hi', hin0], by rw [hs', hst0]⟩

end EquivLean.Modernize.Cbstm03a.Java.Cs
