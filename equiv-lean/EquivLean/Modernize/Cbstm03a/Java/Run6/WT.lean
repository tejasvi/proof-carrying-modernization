import EquivLean.Modernize.Cbstm03a.Java.Run6.BodyDefs

/-!
# CBSTM03A → Java `run`, statement 179: `writeTrans`' contract restated for the symbolic run

`writeTransSpec` quantifies over the `Result` object's lists and outputs (`ld … ab`) in its precondition and its
postcondition; under these binders the symbolic executor cannot carry the `Result` relation over the substring's
allocation. The relation is functional in them (`resAtL_unique`), so the contract equals `writeTransSpecR`, which
names them by the `Result` object (`resTup`, `ResOk`, `WTPost`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space GrowsK grows_split
  growsK_elim forall2_imp)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg6

/-! ## The `Result` relation is functional -/

theorem jstrAt_unique {σ : State} {v : Value} {s s' : JStr} (h : JStrAt σ v s) (h' : JStrAt σ v s') : s = s' := by
  obtain ⟨x, rfl, hx⟩ := h
  obtain ⟨x', hxx, hx'⟩ := h'
  cases hxx
  rw [hx] at hx'
  cases hx'
  rfl

theorem forall2_jstr_unique {σ : State} :
    ∀ {xs : List Value} {ss ss' : List JStr}, Forall2 (JStrAt σ) xs ss → Forall2 (JStrAt σ) xs ss' → ss = ss'
  | [], [], [], .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons h hs, .cons h' hs' => by
    rw [jstrAt_unique h h', forall2_jstr_unique hs hs']

theorem listAt_unique {σ : State} {l : Addr} {ss ss' : List JStr} (h : ListAt σ l ss) (h' : ListAt σ l ss') :
    ss = ss' := by
  obtain ⟨xs, m, h1, h2⟩ := h
  obtain ⟨xs', m', h1', h2'⟩ := h'
  rw [h1] at h1'
  cases h1'
  exact forall2_jstr_unique h2 h2'

theorem resAtL_unique {σ : State} {res ld ls lh ld' ls' lh' : Addr} {d s t d' s' t' : List JStr} {ab ab' : Bool}
    (h : ResAtL σ res ld ls lh d s t ab) (h' : ResAtL σ res ld' ls' lh' d' s' t' ab') :
    ld = ld' ∧ ls = ls' ∧ lh = lh' ∧ d = d' ∧ s = s' ∧ t = t' ∧ ab = ab' := by
  obtain ⟨fs, hr, f1, f2, f3, f4, -, -, -, l1, l2, l3⟩ := h
  obtain ⟨fs', hr', f1', f2', f3', f4', -, -, -, l1', l2', l3'⟩ := h'
  rw [hr] at hr'
  cases hr'
  rw [f1] at f1'; rw [f2] at f2'; rw [f3] at f3'; rw [f4] at f4'
  cases f1'; cases f2'; cases f3'
  refine ⟨rfl, rfl, rfl, listAt_unique l1 l1', listAt_unique l2 l2', listAt_unique l3 l3', ?_⟩
  cases ab <;> cases ab' <;> first | rfl | (simp at f4')

/-! ## The `Result` object's lists and outputs, named by the object -/

abbrev RTup := Addr × Addr × Addr × List JStr × List JStr × List JStr × Bool

def ResAtT (σ : State) (res : Addr) (u : RTup) : Prop :=
  ResAtL σ res u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2.1 u.2.2.2.2.2.1 u.2.2.2.2.2.2

open Classical in
noncomputable def resTup (σ : State) (res : Addr) : RTup :=
  if h : ∃ u, ResAtT σ res u then Classical.choose h else default

theorem resTup_eq {σ : State} {res : Addr} {u : RTup} (h : ResAtT σ res u) : resTup σ res = u := by
  have hex : ∃ u, ResAtT σ res u := ⟨u, h⟩
  have hc := Classical.choose_spec hex
  unfold resTup
  rw [dif_pos hex]
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := resAtL_unique hc h
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := u
  generalize Classical.choose hex = c at e1 e2 e3 e4 e5 e6 e7 ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := c
  simp only at e1 e2 e3 e4 e5 e6 e7
  subst e1 e2 e3 e4 e5 e6 e7
  rfl

/-- The `Result` object at `res` holds some outputs. -/
@[irreducible] def ResOk (σ : State) (res : Addr) : Prop := ∃ u, ResAtT σ res u

theorem resOk_intro {σ : State} {res ld ls lh : Addr} {d s t : List JStr} {ab : Bool}
    (h : ResAtL σ res ld ls lh d s t ab) : ResOk σ res := by
  unfold ResOk; exact ⟨(ld, ls, lh, d, s, t, ab), h⟩

theorem resOk_tup {σ : State} {res : Addr} (h : ResOk σ res) : ResAtT σ res (resTup σ res) := by
  unfold ResOk at h
  obtain ⟨u, hu⟩ := h
  rw [resTup_eq hu]; exact hu

theorem resOk_alloc {σ : State} {res : Addr} (o : Obj) (h : ResOk σ res) : ResOk (σ.alloc o).2 res := by
  have hu := resOk_tup h
  unfold ResOk; exact ⟨_, resAtL_grows hu (grows_alloc σ o)⟩

theorem resOk_growsK {σ σ' : State} {res : Addr} (h : ResOk σ res) (hg : GrowsK σ σ') : ResOk σ' res := by
  have hu := resOk_tup h
  unfold ResOk; exact ⟨_, resAtL_grows hu (growsK_elim hg)⟩

/-- `writeTrans`' frame and outputs for the `Result` object at `res`. -/
@[irreducible] def WTPost (σ σ' : State) (res : Addr) (tid trest : JStr) (amt : I64) : Prop :=
  ResAtL σ' res (resTup σ res).1 (resTup σ res).2.1 (resTup σ res).2.2.1 (resTup σ res).2.2.2.1
      ((resTup σ res).2.2.2.2.1 ++ (jWriteTrans tid trest amt.toInt).1)
      ((resTup σ res).2.2.2.2.2.1 ++ (jWriteTrans tid trest amt.toInt).2) (resTup σ res).2.2.2.2.2.2 ∧
    KeepsRes res (resTup σ res).1 (resTup σ res).2.1 (resTup σ res).2.2.1 σ σ'

theorem wtPost_elim {σ σ' : State} {res ld ls lh : Addr} {d s t : List JStr} {ab : Bool} {tid trest : JStr}
    {amt : I64} (h : WTPost σ σ' res tid trest amt) (hR : ResAtL σ res ld ls lh d s t ab) :
    ResAtL σ' res ld ls lh d (s ++ (jWriteTrans tid trest amt.toInt).1) (t ++ (jWriteTrans tid trest amt.toInt).2)
        ab ∧ KeepsRes res ld ls lh σ σ' := by
  have hu : resTup σ res = (ld, ls, lh, d, s, t, ab) := resTup_eq hR
  unfold WTPost at h
  rw [hu] at h
  exact h

/-- A list of four values, by its elements. -/
theorem list4_getD {args : List Value} (h : args.length = 4) :
    args = [args.getD 0 .null, args.getD 1 .null, args.getD 2 .null, args.getD 3 .null] := by
  match args, h with
  | [a, b, c, d], _ => rfl

/-- `writeTrans`' contract with the `Result` object's lists and outputs named by the object (each argument of the
postcondition right after its binder). -/
def writeTransSpecR : Spec := Spec.of
  (fun args σ => ∃ (res : Addr) (tv rv : Value) (amt : I64) (t tr : JStr),
     args = [.ref res, tv, rv, .long amt] ∧ ResOk σ res ∧ JStrAt σ tv t ∧
     JStrAt σ rv tr ∧ 65 ≤ tr.length ∧ tr.length < 2147483648 ∧ t.length < 1000000 ∧
     -9223372036854775808 < amt.toInt ∧ σ.initOf "Cbstm03a" = .done)
  (fun args σ r σ' => ∀ res : Addr, args.getD 0 .null = .ref res → ∀ amt : I64, args.getD 3 .null = .long amt →
     args.length = 4 → ResOk σ res →
     r = none ∧ WTPost σ σ' res (argText σ (args.getD 1 .null)) (argText σ (args.getD 2 .null)) amt ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

theorem writeTransSpec_eq : writeTransSpec = writeTransSpecR := by
  unfold writeTransSpec writeTransSpecR Spec.of
  congr 1
  · funext args σ
    apply propext
    constructor
    · rintro ⟨res, ld, ls, lh, disp, st, ht, ab, tv, rv, amt, t, tr, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      exact ⟨res, tv, rv, amt, t, tr, h1, resOk_intro h2, h3, h4, h5, h6, h7, h8, h9⟩
    · rintro ⟨res, tv, rv, amt, t, tr, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      have hu := resOk_tup h2
      exact ⟨res, _, _, _, _, _, _, _, tv, rv, amt, t, tr, h1, hu, h3, h4, h5, h6, h7, h8, h9⟩
  · funext args σ o
    cases o with
    | normal r σ' =>
      apply propext
      constructor
      · intro H res h0 amt h3 hl h2
        have hu := resOk_tup h2
        have ha : args = [.ref res, args.getD 1 .null, args.getD 2 .null, .long amt] := by
          rw [← h0, ← h3]; exact list4_getD hl
        obtain ⟨e1, e2, e3, e4, e5⟩ := H res _ _ _ _ _ _ _ _ _ amt ha hu
        refine ⟨e1, ?_, e4, e5⟩
        unfold WTPost
        exact ⟨e2, e3⟩
      · intro H res ld ls lh disp st ht ab tv rv amt h1 h2
        subst h1
        obtain ⟨e1, e2, e4, e5⟩ := H res rfl amt rfl rfl (resOk_intro h2)
        obtain ⟨e2a, e2b⟩ := wtPost_elim e2 h2
        exact ⟨e1, e2a, e2b, e4, e5⟩
    | exc e σ' => rfl
    | wrong m => rfl

end EquivLean.Modernize.Cbstm03a.Java.Seg6
