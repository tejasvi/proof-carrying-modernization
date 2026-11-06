import EquivLean.Modernize.Cbtrn03c.JavaW.W
import EquivLean.Modernize.Cbtrn03c.JavaTop.WsRel

/-!
# CBTRN03C → Java: from the writers' Java contracts to the shared model contracts

What `Frame3` keeps (the working state and its lists are the only objects a writer changes):
the strings, the records, every object `KeepsNonWs` asks for.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

section
variable {σ σ' : State} {w ld lr : Addr} {fs : List (FieldKey × Value)}
  {k1 k2 : ListKind} {y1 y2 : List Value} {m1 m2 : Nat}

theorem ne_of_heap_str {x a : Addr} {s : JStr} {o : Obj} (hx : σ.heap x = some (.str s))
    (ha : σ.heap a = some o) (ho : ∀ s', o ≠ .str s') : x ≠ a := by
  intro e; subst e; rw [hx] at ha; cases ha; exact ho s rfl

theorem frame3_keeps (hf : Frame3 σ σ' w ld lr) (hw : σ.heap w = some (.plain wsC fs))
    (hld : σ.heap ld = some (.list k1 y1 m1)) (hlr : σ.heap lr = some (.list k2 y2 m2))
    {x : Addr} {o : Obj} (hx : σ.heap x = some o) (hnw : o ≠ .plain wsC fs)
    (hnl1 : ∀ k y m, o ≠ .list k y m) : σ'.heap x = some o := by
  have hlt := State.lt_next_of_heap hx
  have h1 : x ≠ w := by intro e; subst e; rw [hw] at hx; cases hx; exact hnw rfl
  have h2 : x ≠ ld := by intro e; subst e; rw [hld] at hx; cases hx; exact hnl1 _ _ _ rfl
  have h3 : x ≠ lr := by intro e; subst e; rw [hlr] at hx; cases hx; exact hnl1 _ _ _ rfl
  rw [hf.2 x hlt h1 h2 h3, hx]

theorem strMono_of_frame3 (hf : Frame3 σ σ' w ld lr) (hw : σ.heap w = some (.plain wsC fs))
    (hld : σ.heap ld = some (.list k1 y1 m1)) (hlr : σ.heap lr = some (.list k2 y2 m2)) :
    StrMono σ σ' :=
  fun _ _ hx => frame3_keeps hf hw hld hlr hx (by simp) (by simp)

theorem keepsNonWs_of_frame3 (hf : Frame3 σ σ' w ld lr) (hw : σ.heap w = some (.plain wsC fs))
    (hld : σ.heap ld = some (.list k1 y1 m1)) (hlr : σ.heap lr = some (.list k2 y2 m2)) :
    Top.KeepsNonWs σ σ' := by
  refine ⟨hf.1, strMono_of_frame3 hf hw hld hlr, ?_, ?_⟩
  · intro x c fs' hx hc
    refine frame3_keeps hf hw hld hlr hx ?_ (by simp)
    intro e; cases e; exact hc rfl
  · intro x et xs hx
    exact frame3_keeps hf hw hld hlr hx (by simp) (by simp)

theorem top_recText_mono (hm : Top.KeepsNonWs σ σ') {v : Value} {s : JStr}
    (h : Top.recText σ v = some s) : Top.recText σ' v = some s := by
  cases v with
  | ref x =>
    simp only [Top.recText] at h ⊢
    cases hx : σ.heap x with
    | none => rw [hx] at h; simp at h
    | some o =>
      rw [hx] at h
      cases o with
      | plain c fs =>
        by_cases hc : c = Top.fdC
        · subst hc
          rw [hm.2.2.1 x Top.fdC fs hx (by decide)]
          simp only [ite_true] at h ⊢
          cases hf : Fields.get fs (Top.fdC, "fdReptfileRec") with
          | none => rw [hf] at h; simp at h
          | some sv =>
            rw [hf] at h
            simp only at h ⊢
            obtain ⟨y, rfl, hy⟩ := strOf_eq_some_iff.1 h
            exact strOf_eq_some_iff.2 ⟨y, rfl, hm.2.1 y s hy⟩
        · simp [hc] at h
      | _ => simp at h
  | _ => simp [Top.recText] at h

theorem top_recsAt_mono (hm : Top.KeepsNonWs σ σ') {ys : List Value} {ss : List JStr}
    (h : Top.RecsAt σ ys ss) : Top.RecsAt σ' ys ss := by
  unfold Top.RecsAt at *
  induction ys generalizing ss with
  | nil => exact h
  | cons y ys ih =>
    cases ss with
    | nil => simp at h
    | cons s ss =>
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      exact ⟨top_recText_mono hm h.1, ih h.2⟩

theorem top_recsAt_snoc (σ : State) (ys : List Value) (y : Value) (ss : List JStr) (s : JStr) :
    Top.RecsAt σ (ys ++ [y]) (ss ++ [s]) ↔ Top.RecsAt σ ys ss ∧ Top.recText σ y = some s := by
  unfold Top.RecsAt
  simp only [List.map_append, List.map_cons, List.map_nil]
  constructor
  · intro h
    have hl : ys.length = ss.length := by
      have := congrArg List.length h
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at this
      omega
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp [hl])
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

theorem top_recText_of_heap {r z : Addr} {fsR : List (FieldKey × Value)} {s : JStr}
    (hr : σ.heap r = some (.plain fdC fsR)) (hf : Fields.get fsR (fdC, "fdReptfileRec") = some (.ref z))
    (hz : σ.heap z = some (.str s)) : Top.recText σ (.ref r) = some s := by
  have hf' : Fields.get fsR ("Cbtrn03c$FdReptfileRec", "fdReptfileRec") = some (.ref z) := hf
  simp [Top.recText, hr, Top.fdC, fdC, hf', strOf, hz]

end

end EquivLean.Modernize.Cbtrn03c.Java
