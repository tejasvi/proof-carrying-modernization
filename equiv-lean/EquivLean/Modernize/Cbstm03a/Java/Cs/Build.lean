import EquivLean.Modernize.Cbstm03a.Java.Cs.VCut

/-!
# CBSTM03A → Java: `createStatement`, the `StringBuilder` calls

A call `app(b, cap, src, delim)` at statement `pc` (`src` a local and `delim` a literal, or `src` a literal and
`delim` `null`), answered by `appSpec`: the paths from `pc` hold when the paths from `pc + 1` hold for every state
the contract allows (`wp_app_ll`, `wp_app_lit`). Between the calls, the virtual cut points `bcut`: a cut point's
facts (`CutI`) and the builder in local `k` holding `b` (`BuildI`); `app` changes only the builder, which is newer
than the entry state (`cutI_keepsD`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans keeps_refl keeps_trans fixStr_length heap_grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

theorem sel_app : Gen.prog.selectStatic appSig = .jimple appRef := by rfl
theorem env_app : csCallees.env appSig = some appSpec := by rfl

set_option maxHeartbeats 1000000 in
theorem wp_app_ll {I : Cuts} {Post : Outcome → Prop} {n pc k j : Nat} {cap capI : Int} {lit : String}
    {fr : Frame} {σ : State} {d x : Addr} {b s : JStr}
    (hs : body.stmtAt pc = some (.invoke (.static appSig [.loc k, .const (.int cap), .loc j, .const (.str lit)])))
    (hk : fr.get k = some (.ref d)) (hd : σ.heap d = some (.builder "java.lang.StringBuilder" b))
    (hbl : b.length < 2147483648) (hj : fr.get j = some (.ref x)) (hx : σ.heap x = some (.str s))
    (hsl : s.length < 2147483648) (hcap : (BitVec.ofInt 32 cap).toInt = capI) (hcap0 : 0 ≤ capI)
    (hlen : (JStr.ofString lit).length < 2147483648) (hini : σ.initOf "Cbstm03a" = .done)
    (hcont : ∀ σ', σ'.heap d = some (.builder "java.lang.StringBuilder" (appStr b capI s (some (JStr.ofString lit)))) →
      Keeps (fun y => y = d) (σ.alloc (.str (JStr.ofString lit))).2 σ' → σ'.inits = σ.inits →
      σ'.statics = σ.statics →
      match I.lookup (pc + 1) with
      | some A => A fr σ'
      | none => bodyWP Gen.prog csH body I Post n (pc + 1) fr σ') :
    bodyWP Gen.prog csH body I Post (n + 1) pc fr σ := by
  rw [bodyWP_succ]
  simp only [step, hs, stepStmt, evalInvoke, evalArgs, evalImm, hk, hj, Option.map_some, evalConst, allocStr,
    sel_app]
  have hcls : appRef.cls = "Cbstm03a" := rfl
  have hdl : d < σ.next := State.lt_next_of_heap hd
  have hxl : x < σ.next := State.lt_next_of_heap hx
  simp only [hcls, initThen, ensureInit, prog_cbstm, Bool.not_true, Bool.false_eq_true, ite_false,
    State.initOf_alloc, hini, Res.bind_ret, callM, Res.bind_call, wpR, callWP, env_app, State.alloc_fst]
  refine ⟨⟨Or.inl sel_app, rfl⟩, ⟨d, _, _, _, b, rfl, by rw [State.heap_alloc_of_lt hdl, hd], hbl,
    by rw [hcap]; exact hcap0, ⟨x, s, rfl, by rw [State.heap_alloc_of_lt hxl, hx], hsl⟩,
    Or.inr ⟨σ.next, _, rfl, by simp [State.heap_alloc], hlen⟩⟩, ?_⟩
  intro o ho
  cases o with
  | normal r σ' =>
    simp only [appSpec, Spec.of] at ho
    obtain ⟨-, hd', hK', hi', hs'⟩ := ho d _ _ _ b rfl (by rw [State.heap_alloc_of_lt hdl, hd])
    have e1 : argText (σ.alloc (.str (JStr.ofString lit))).2 (.ref x) = s := by
      simp [argText, strOf, State.heap_alloc_of_lt hxl, hx]
    have e2 : strOf (σ.alloc (.str (JStr.ofString lit))).2 (.ref σ.next) = some (JStr.ofString lit) := by
      simp [strOf, State.heap_alloc]
    rw [e1, e2, hcap] at hd'
    simp only [outToEv, afterEv, afterStep]
    exact hcont σ' hd' hK' (by rw [hi']; rfl) (by rw [hs']; rfl)
  | exc e σ' => simp only [appSpec, Spec.of] at ho
  | wrong m => simp only [appSpec, Spec.of] at ho

set_option maxHeartbeats 1000000 in
theorem wp_app_lit {I : Cuts} {Post : Outcome → Prop} {n pc k : Nat} {cap capI : Int} {lit : String}
    {fr : Frame} {σ : State} {d : Addr} {b : JStr}
    (hs : body.stmtAt pc = some (.invoke (.static appSig [.loc k, .const (.int cap), .const (.str lit), .const .null])))
    (hk : fr.get k = some (.ref d)) (hd : σ.heap d = some (.builder "java.lang.StringBuilder" b))
    (hbl : b.length < 2147483648) (hcap : (BitVec.ofInt 32 cap).toInt = capI) (hcap0 : 0 ≤ capI)
    (hlen : (JStr.ofString lit).length < 2147483648) (hini : σ.initOf "Cbstm03a" = .done)
    (hcont : ∀ σ', σ'.heap d = some (.builder "java.lang.StringBuilder" (appStr b capI (JStr.ofString lit) none)) →
      Keeps (fun y => y = d) (σ.alloc (.str (JStr.ofString lit))).2 σ' → σ'.inits = σ.inits →
      σ'.statics = σ.statics →
      match I.lookup (pc + 1) with
      | some A => A fr σ'
      | none => bodyWP Gen.prog csH body I Post n (pc + 1) fr σ') :
    bodyWP Gen.prog csH body I Post (n + 1) pc fr σ := by
  rw [bodyWP_succ]
  simp only [step, hs, stepStmt, evalInvoke, evalArgs, evalImm, hk, Option.map_some, evalConst, allocStr,
    sel_app]
  have hcls : appRef.cls = "Cbstm03a" := rfl
  have hdl : d < σ.next := State.lt_next_of_heap hd
  simp only [hcls, initThen, ensureInit, prog_cbstm, Bool.not_true, Bool.false_eq_true, ite_false,
    State.initOf_alloc, hini, Res.bind_ret, callM, Res.bind_call, wpR, callWP, env_app, State.alloc_fst]
  refine ⟨⟨Or.inl sel_app, rfl⟩, ⟨d, _, _, _, b, rfl, by rw [State.heap_alloc_of_lt hdl, hd], hbl,
    by rw [hcap]; exact hcap0, ⟨σ.next, _, rfl, by simp [State.heap_alloc], hlen⟩, Or.inl rfl⟩, ?_⟩
  intro o ho
  cases o with
  | normal r σ' =>
    simp only [appSpec, Spec.of] at ho
    obtain ⟨-, hd', hK', hi', hs'⟩ := ho d _ _ _ b rfl (by rw [State.heap_alloc_of_lt hdl, hd])
    have e1 : argText (σ.alloc (.str (JStr.ofString lit))).2 (.ref σ.next) = JStr.ofString lit := by
      simp [argText, strOf, State.heap_alloc]
    have e2 : strOf (σ.alloc (.str (JStr.ofString lit))).2 .null = none := rfl
    rw [e1, e2, hcap] at hd'
    simp only [outToEv, afterEv, afterStep]
    exact hcont σ' hd' hK' (by rw [hi']; rfl) (by rw [hs']; rfl)
  | exc e σ' => simp only [appSpec, Spec.of] at ho
  | wrong m => simp only [appSpec, Spec.of] at ho

/-! ## The builder between the calls -/

/-- A virtual cut point inside a builder segment: the cut point's facts and the builder in local `k` holding `b`
(newer than the entry state, at most 80 characters). -/
def BuildI (g : G) (ns nh : Nat) (L : List (Nat × JStr)) (bal : Bool) (k : Nat) (b : JStr) (σ0 : State)
    (fr : Frame) (σ : State) : Prop :=
  CutI g ns nh L bal σ0 fr σ ∧
    ∃ d, fr.get k = some (.ref d) ∧ σ.heap d = some (.builder "java.lang.StringBuilder" b) ∧ σ0.next ≤ d ∧
      b.length ≤ 80

@[irreducible] def bcut (g : G) (ns nh : Nat) (L : G → List (Nat × JStr)) (bal : Bool) (k : Nat) (b : JStr) :
    List Value → State → Frame → State → Prop :=
  fun _ σ0 fr σ => BuildI g ns nh (L g) bal k b σ0 fr σ

theorem bcut_unfold {g : G} {ns nh : Nat} {L : G → List (Nat × JStr)} {bal : Bool} {k : Nat} {b : JStr}
    {args : List Value} {σ0 : State} {fr : Frame} {σ : State} :
    bcut g ns nh L bal k b args σ0 fr σ ↔ BuildI g ns nh (L g) bal k b σ0 fr σ := by
  unfold bcut; exact Iff.rfl

theorem heap_keepsD {σ σ' : State} {d y : Addr} {o : Obj} (hk : Keeps (fun y => y = d) σ σ')
    (hy : σ.heap y = some o) (hne : y ≠ d) : σ'.heap y = some o := by
  rw [hk.2 y (State.lt_next_of_heap hy) hne, hy]

theorem ne_of_builder {σ : State} {d y : Addr} {o : Obj} {c : ClassName} {b : JStr}
    (hd : σ.heap d = some (.builder c b)) (hy : σ.heap y = some o) (ho : ∀ c b, o ≠ .builder c b) : y ≠ d := by
  intro e
  subst e
  rw [hd] at hy
  exact ho c b (Option.some.inj hy).symm

theorem strMono_keepsD {σ σ' : State} {d : Addr} {c : ClassName} {b : JStr}
    (hd : σ.heap d = some (.builder c b)) (hk : Keeps (fun y => y = d) σ σ') : StrMono σ σ' :=
  fun x s hx => heap_keepsD hk hx (ne_of_builder hd hx (fun _ _ h => by cases h))

theorem listAt_keepsD {σ σ' : State} {d l : Addr} {c : ClassName} {b : JStr} {ss : List JStr}
    (hd : σ.heap d = some (.builder c b)) (hk : Keeps (fun y => y = d) σ σ') (h : ListAt σ l ss) :
    ListAt σ' l ss := by
  obtain ⟨xs, m, h1, h2⟩ := h
  exact ⟨xs, m, heap_keepsD hk h1 (ne_of_builder hd h1 (fun _ _ h => by cases h)),
    forall2_jstr_mono (strMono_keepsD hd hk) h2⟩

theorem locsAt_strMono {σ σ' : State} {fr : Frame} (hm : StrMono σ σ') :
    ∀ {L : List (Nat × JStr)}, LocsAt σ fr L → LocsAt σ' fr L
  | [], _ => trivial
  | (_, _) :: _, ⟨⟨x, h1, h2, h3⟩, h4⟩ => ⟨⟨x, h1, hm x _ h2, h3⟩, locsAt_strMono hm h4⟩

/-- `app` changes only the builder, which is newer than the entry state. -/
theorem cutI_keepsD {g : G} {ns nh : Nat} {L : List (Nat × JStr)} {bal : Bool} {σ0 σ σ' : State} {fr : Frame}
    {d : Addr} {c : ClassName} {b : JStr} (hI : CutI g ns nh L bal σ0 fr σ) (hd : σ.heap d = some (.builder c b))
    (hd0 : σ0.next ≤ d) (hk : Keeps (fun y => y = d) σ σ') (hin : σ'.inits = σ.inits)
    (hst : σ'.statics = σ.statics) : CutI g ns nh L bal σ0 fr σ' := by
  have hres := hI.1.1
  have hR := hI.1.2.1
  have hk0 := hI.1.2.2.1
  have hin0 := hI.1.2.2.2.1
  have hst0 := hI.1.2.2.2.2.1
  have hini := hI.1.2.2.2.2.2
  obtain ⟨fs, hr, gd, gs, gh, gab, n1, n2, n3, Ld, Ls, Lh⟩ := hR
  refine ⟨⟨hres, ⟨fs, heap_keepsD hk hr (ne_of_builder hd hr (fun _ _ h => by cases h)), gd, gs, gh, gab, n1, n2,
    n3, listAt_keepsD hd hk Ld, listAt_keepsD hd hk Ls, listAt_keepsD hd hk Lh⟩, ⟨Nat.le_trans hk0.1 hk.1,
    fun y hy a1 a2 a3 a4 => by
      rw [hk.2 y (Nat.lt_of_lt_of_le hy hk0.1) (fun e => absurd (e ▸ hy) (Nat.not_lt.2 hd0)),
        hk0.2 y hy a1 a2 a3 a4]⟩, by rw [hin, hin0], by rw [hst, hst0], ?_⟩,
    locsAt_strMono (strMono_keepsD hd hk) hI.2.1, hI.2.2⟩
  unfold State.initOf at hini ⊢
  rw [hin]
  exact hini

theorem appStr_length_le (b : JStr) (cap : Int) (src : JStr) (dd : Option JStr) :
    (appStr b cap src dd).length ≤ max b.length cap.toNat := by
  unfold appStr
  split
  · omega
  · next h =>
    simp only [List.length_append, List.length_take]
    omega

set_option maxRecDepth 20000 in
-- The step through `app(b, cap, src, delim)`, `src` a local, `delim` a literal, between two virtual cut points.
theorem bcut_app_ll {g : G} {args : List Value} {σ0 : State} {pc ns nh k j : Nat} {L : G → List (Nat × JStr)}
    {bal : Bool} {cap capI : Int} {lit : String} {b s : JStr} {n : Nat}
    (hs : body.stmtAt pc = some (.invoke (.static appSig [.loc k, .const (.int cap), .loc j, .const (.str lit)])))
    (hjs : (j, s) ∈ L g) (hcap : (BitVec.ofInt 32 cap).toInt = capI) (hcap0 : 0 ≤ capI) (hcap1 : capI ≤ 80)
    (hlen : (JStr.ofString lit).length < 2147483648) :
    ∀ fr σ, bcut g ns nh L bal k b args σ0 fr σ →
      bodyWP Gen.prog csH body
        ((pc + 1, bcut g ns nh L bal k (appStr b capI s (some (JStr.ofString lit))) args σ0) :: (inv g).inst args σ0)
        ((specG g).post args σ0) (n + 1) pc fr σ := by
  intro fr σ hB
  rw [bcut_unfold] at hB
  obtain ⟨hI, d, hk, hd, hd0, hbl⟩ := hB
  obtain ⟨x, hx1, hx2, hx3⟩ := locsAt_mem hI.2.1 hjs
  have hini := hI.1.2.2.2.2.2
  refine wp_app_ll hs hk hd (by omega) hx1 hx2 hx3 hcap hcap0 hlen hini ?_
  intro σ' hd' hK' hi' hs'
  simp only [List.lookup_cons, beq_self_eq_true]
  show bcut g ns nh L bal k _ args σ0 fr σ'
  rw [bcut_unfold]
  have hdl : d < σ.next := State.lt_next_of_heap hd
  have hI1 : CutI g ns nh (L g) bal σ0 fr (σ.alloc (.str (JStr.ofString lit))).2 :=
    cutI_next hI (grows_alloc σ _) rfl rfl rfl (locsAt_frame (grows_alloc σ _) hI.2.1 (fun _ _ => rfl)) hI.2.2
  refine ⟨cutI_keepsD hI1 (by rw [State.heap_alloc_of_lt hdl]; exact hd) hd0 hK' (by rw [hi']; rfl)
    (by rw [hs']; rfl), d, hk, hd', hd0, ?_⟩
  have := appStr_length_le b capI s (some (JStr.ofString lit))
  omega

set_option maxRecDepth 20000 in
-- The step through `app(b, cap, lit, null)` between two virtual cut points.
theorem bcut_app_lit {g : G} {args : List Value} {σ0 : State} {pc ns nh k : Nat} {L : G → List (Nat × JStr)}
    {bal : Bool} {cap capI : Int} {lit : String} {b : JStr} {n : Nat}
    (hs : body.stmtAt pc = some (.invoke (.static appSig [.loc k, .const (.int cap), .const (.str lit), .const .null])))
    (hcap : (BitVec.ofInt 32 cap).toInt = capI) (hcap0 : 0 ≤ capI) (hcap1 : capI ≤ 80)
    (hlen : (JStr.ofString lit).length < 2147483648) :
    ∀ fr σ, bcut g ns nh L bal k b args σ0 fr σ →
      bodyWP Gen.prog csH body
        ((pc + 1, bcut g ns nh L bal k (appStr b capI (JStr.ofString lit) none) args σ0) :: (inv g).inst args σ0)
        ((specG g).post args σ0) (n + 1) pc fr σ := by
  intro fr σ hB
  rw [bcut_unfold] at hB
  obtain ⟨hI, d, hk, hd, hd0, hbl⟩ := hB
  have hini := hI.1.2.2.2.2.2
  refine wp_app_lit hs hk hd (by omega) hcap hcap0 hlen hini ?_
  intro σ' hd' hK' hi' hs'
  simp only [List.lookup_cons, beq_self_eq_true]
  show bcut g ns nh L bal k _ args σ0 fr σ'
  rw [bcut_unfold]
  have hdl : d < σ.next := State.lt_next_of_heap hd
  have hI1 : CutI g ns nh (L g) bal σ0 fr (σ.alloc (.str (JStr.ofString lit))).2 :=
    cutI_next hI (grows_alloc σ _) rfl rfl rfl (locsAt_frame (grows_alloc σ _) hI.2.1 (fun _ _ => rfl)) hI.2.2
  refine ⟨cutI_keepsD hI1 (by rw [State.heap_alloc_of_lt hdl]; exact hd) hd0 hK' (by rw [hi']; rfl)
    (by rw [hs']; rfl), d, hk, hd', hd0, ?_⟩
  have := appStr_length_le b capI (JStr.ofString lit) none
  omega

end EquivLean.Modernize.Cbstm03a.Java.Cs
