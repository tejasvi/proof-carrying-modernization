import EquivLean.Modernize.Cbtrn03c.JavaTop.WsRel

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java, top layer: lemmas for the segments

Frame lemmas (`jframe`) for the representation predicates of `shared/WsRel.lean`, the rule of
consequence and the ghost rule for contracts, machine arithmetic of the totals.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

/-! ## Contracts -/

/-- The rule of consequence. -/
theorem Sat.conseq {P : Program} {m : MethodRef} {S S' : Spec} (h : Sat P m S)
    (hpre : ∀ args σ, S'.pre args σ → S.pre args σ)
    (hpost : ∀ args σ o, S'.pre args σ → S.post args σ o → S'.post args σ o) : Sat P m S' :=
  fun args σ o hp hx => hpost args σ o hp (h args σ o (hpre args σ hp) hx)

/-! ## Frames -/

theorem KeepsNonWs.trans {σ1 σ2 σ3 : State} (h1 : KeepsNonWs σ1 σ2) (h2 : KeepsNonWs σ2 σ3) :
    KeepsNonWs σ1 σ3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun x s h => h2.2.1 x s (h1.2.1 x s h),
   fun x c fs h hc => h2.2.2.1 x c fs (h1.2.2.1 x c fs h hc) hc,
   fun x et xs h => h2.2.2.2 x et xs (h1.2.2.2 x et xs h)⟩

theorem KeepsNonWs.refl (σ : State) : KeepsNonWs σ σ :=
  ⟨Nat.le_refl _, fun _ _ h => h, fun _ _ _ h _ => h, fun _ _ _ h => h⟩

attribute [jframe] KeepsNonWs.trans

theorem heap_agree {σ σ' : State} (h : Agree σ σ') {x : Addr} {o : Obj} (hx : σ.heap x = some o) :
    σ'.heap x = some o := by
  rw [h x (State.lt_next_of_heap hx), hx]

theorem strOf_agree {σ σ' : State} (h : Agree σ σ') {v : Value} {s : JStr}
    (hv : strOf σ v = some s) : strOf σ' v = some s := by
  obtain ⟨y, rfl, hy⟩ := strOf_eq_some_iff.1 hv
  exact strOf_eq_some_iff.2 ⟨y, rfl, heap_agree h hy⟩

theorem StrsAt.agree {σ σ' : State} {ys : List Value} {ss : List JStr} (h : StrsAt σ ys ss)
    (ha : Agree σ σ') : StrsAt σ' ys ss :=
  StrsAt.mono h (fun x s hx => heap_agree ha hx)

theorem recText_agree {σ σ' : State} (h : Agree σ σ') {v : Value} {s : JStr}
    (hv : recText σ v = some s) : recText σ' v = some s := by
  cases v with
  | ref x =>
    simp only [recText] at hv ⊢
    cases hx : σ.heap x with
    | none => rw [hx] at hv; simp at hv
    | some o =>
      rw [hx] at hv
      rw [heap_agree h hx]
      cases o with
      | plain c fs =>
        simp only at hv ⊢
        split at hv
        · split at hv
          · rename_i sv hsv
            simp only [*, ite_true]
            exact strOf_agree h hv
          · simp at hv
        · simp at hv
      | _ => simp at hv
  | _ => simp [recText] at hv

theorem RecsAt.agree {σ σ' : State} {ys : List Value} {ss : List JStr} (h : RecsAt σ ys ss)
    (ha : Agree σ σ') : RecsAt σ' ys ss := by
  unfold RecsAt at *
  induction ys generalizing ss with
  | nil => exact h
  | cons y ys ih =>
    cases ss with
    | nil => simp at h
    | cons s ss =>
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      exact ⟨recText_agree ha h.1, ih h.2⟩

/-- Strings and report records stay. -/
def RecMono (σ σ' : State) : Prop :=
  StrMono σ σ' ∧ ∀ x fs, σ.heap x = some (.plain fdC fs) → σ'.heap x = some (.plain fdC fs)

theorem recText_mono {σ σ' : State} (hm : RecMono σ σ') {v : Value} {s : JStr}
    (hv : recText σ v = some s) : recText σ' v = some s := by
  cases v with
  | ref x =>
    simp only [recText] at hv ⊢
    cases hx : σ.heap x with
    | none => rw [hx] at hv; simp at hv
    | some o =>
      rw [hx] at hv
      cases o with
      | plain c fs =>
        by_cases hc : c = fdC
        · subst hc
          rw [hm.2 x fs hx]
          simp only [ite_true] at hv ⊢
          cases hf : Fields.get fs (fdC, "fdReptfileRec") with
          | none => rw [hf] at hv; simp at hv
          | some sv =>
            rw [hf] at hv
            simp only at hv ⊢
            obtain ⟨y, rfl, hy⟩ := strOf_eq_some_iff.1 hv
            exact strOf_eq_some_iff.2 ⟨y, rfl, hm.1 y s hy⟩
        · simp [hc] at hv
      | _ => simp at hv
  | _ => simp [recText] at hv

theorem RecsAt.mono {σ σ' : State} {ys : List Value} {ss : List JStr} (h : RecsAt σ ys ss)
    (hm : RecMono σ σ') : RecsAt σ' ys ss := by
  unfold RecsAt at *
  induction ys generalizing ss with
  | nil => exact h
  | cons y ys ih =>
    cases ss with
    | nil => simp at h
    | cons s ss =>
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      exact ⟨recText_mono hm h.1, ih h.2⟩

attribute [jframe] RecsAt.mono

theorem RecsAt_snoc (σ : State) (ys : List Value) (y : Value) (ss : List JStr) (s : JStr) :
    RecsAt σ (ys ++ [y]) (ss ++ [s]) ↔ RecsAt σ ys ss ∧ recText σ y = some s := by
  unfold RecsAt
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

theorem WsRel.agree {σ σ' : State} {w ld lr : Addr} {d : List EquivLean.Cobol.Rec.FVal}
    {s : Model.St} (h : WsRel σ w ld lr d s) (ha : Agree σ σ') : WsRel σ' w ld lr d s := by
  obtain ⟨fs, dsp, wrs, dm, wm, c, rx, ex, hw, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, hld, hlr, n1, n2, n3, hd, hr, hc, hrx, hex, hfirst, hok⟩ := h
  exact ⟨fs, dsp, wrs, dm, wm, c, rx, ex, heap_agree ha hw, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, heap_agree ha hld, heap_agree ha hlr, n1, n2, n3, StrsAt.agree hd ha,
    RecsAt.agree hr ha, heap_agree ha hc, heap_agree ha hrx, heap_agree ha hex, hfirst, hok⟩

attribute [jframe] WsRel.agree

theorem TranFields.of_keep {σ σ' : State} {c : Addr} {t : List EquivLean.Cobol.Rec.FVal}
    (h : TranFields σ c t) (hs : StrMono σ σ')
    (hp : ∀ x c fs, σ.heap x = some (.plain c fs) → c ≠ wsC → σ'.heap x = some (.plain c fs)) :
    TranFields σ' c t := by
  obtain ⟨fs, hc, ⟨y0, e0, h0⟩, ⟨y1, e1, h1⟩, l2, ⟨y3, e3, h3⟩, ⟨y4, e4, h4⟩, l5, l6,
    ⟨y7, e7, h7⟩, ⟨y8, e8, h8⟩, ⟨y9, e9, h9⟩, ⟨y10, e10, h10⟩, ⟨y11, e11, h11⟩,
    ⟨y12, e12, h12⟩, ⟨y13, e13, h13⟩⟩ := h
  exact ⟨fs, hp c tranC fs hc (by decide), ⟨y0, e0, hs _ _ h0⟩, ⟨y1, e1, hs _ _ h1⟩, l2,
    ⟨y3, e3, hs _ _ h3⟩, ⟨y4, e4, hs _ _ h4⟩, l5, l6, ⟨y7, e7, hs _ _ h7⟩, ⟨y8, e8, hs _ _ h8⟩,
    ⟨y9, e9, hs _ _ h9⟩, ⟨y10, e10, hs _ _ h10⟩, ⟨y11, e11, hs _ _ h11⟩, ⟨y12, e12, hs _ _ h12⟩,
    ⟨y13, e13, hs _ _ h13⟩⟩

theorem TranFields.keeps {σ σ' : State} {c : Addr} {t : List EquivLean.Cobol.Rec.FVal}
    (h : TranFields σ c t) (hk : KeepsNonWs σ σ') : TranFields σ' c t :=
  TranFields.of_keep h hk.2.1 hk.2.2.1

theorem TranFields.agree {σ σ' : State} {c : Addr} {t : List EquivLean.Cobol.Rec.FVal}
    (h : TranFields σ c t) (ha : Agree σ σ') : TranFields σ' c t :=
  TranFields.of_keep h (fun _ _ hx => heap_agree ha hx) (fun _ _ _ hx _ => heap_agree ha hx)

attribute [jframe] TranFields.keeps TranFields.agree

/-! ## Machine arithmetic of the totals -/

theorem natAbs_trunc11_lt (x : Int) : (Model.trunc11 x).natAbs < 100000000000 := by
  unfold Model.trunc11
  have l1 := Int.tmod_lt_of_pos x (show (0 : Int) < 100000000000 by decide)
  have l2 := Int.lt_tmod_of_pos x (show (0 : Int) < 100000000000 by decide)
  omega

theorem toInt_ofInt64_small {x : Int} (h : x.natAbs < 200000000000) :
    (BitVec.ofInt 64 x).toInt = x := by
  rw [BitVec.toInt_ofInt, Int.bmod_def]
  have h2 : ((2 : Nat) ^ 64 : Nat) = 18446744073709551616 := by decide
  simp only [h2]
  split <;> omega

/-- `add11` on the totals: the model's `trunc11` of the sum. -/
theorem add11_ofInt (a b : Int) (ha : a.natAbs < 100000000000) (hb : b.natAbs < 100000000000) :
    (BitVec.ofInt 64 a + BitVec.ofInt 64 b).srem 100000000000#64 =
      BitVec.ofInt 64 (Model.trunc11 (a + b)) := by
  unfold Model.trunc11
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_srem]
  have h2 : ((2 : Nat) ^ 64 : Nat) = 18446744073709551616 := by decide
  have hab : (BitVec.ofInt 64 a + BitVec.ofInt 64 b).toInt = a + b := by
    rw [BitVec.toInt_add, toInt_ofInt64_small (by omega), toInt_ofInt64_small (by omega),
      Int.bmod_def]
    simp only [h2]
    split <;> omega
  have hc : (100000000000#64 : BitVec 64).toInt = 100000000000 := by decide
  have l1 := Int.tmod_lt_of_pos (a + b) (show (0 : Int) < 100000000000 by decide)
  have l2 := Int.lt_tmod_of_pos (a + b) (show (0 : Int) < 100000000000 by decide)
  rw [hab, hc, toInt_ofInt64_small (by omega)]

end EquivLean.Modernize.Cbtrn03c.Java.Top

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

open Lean Meta in
/-- `Model.txt "…"` on a literal as its explicit list of code points (the model's display lines
against the Java string constants, spelled out by `jconcat`). -/
dsimproc txtLit (EquivLean.Modernize.Cbtrn03c.Model.txt _) := fun e => do
  let_expr EquivLean.Modernize.Cbtrn03c.Model.txt s := e | return .continue
  let .lit (.strVal str) := s.consumeMData | return .continue
  let elems := str.toList.map fun c => mkNatLit c.toNat
  return .done (← mkListLit (mkConst ``Nat) elems)

end EquivLean.Modernize.Cbtrn03c.Java.Top

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

/-- `add11` on the totals, for the modulus as simp writes it. -/
theorem add11_ofInt' (a b : Int) (c : BitVec 64) (hc : c.toInt = 100000000000)
    (ha : a.natAbs < 100000000000) (hb : b.natAbs < 100000000000) :
    (BitVec.ofInt 64 a + BitVec.ofInt 64 b).srem c = BitVec.ofInt 64 (Model.trunc11 (a + b)) := by
  have : c = 100000000000#64 := by
    apply BitVec.eq_of_toInt_eq; rw [hc]; decide
  subst this
  exact add11_ofInt a b ha hb

/-- Two and three strings added to a list (simp writes `(ys ++ [a]) ++ [b]` as `ys ++ [a, b]`). -/
theorem StrsAt_append2 (σ : State) (ys : List Value) (a b : Value) (ss : List JStr) (s1 s2 : JStr) :
    StrsAt σ (ys ++ [a, b]) (ss ++ [s1, s2]) ↔
      StrsAt σ ys ss ∧ strOf σ a = some s1 ∧ strOf σ b = some s2 := by
  rw [show ys ++ [a, b] = (ys ++ [a]) ++ [b] by simp, show ss ++ [s1, s2] = (ss ++ [s1]) ++ [s2] by simp,
    StrsAt_snoc, StrsAt_snoc, and_assoc]

theorem StrsAt_append3 (σ : State) (ys : List Value) (a b c : Value) (ss : List JStr)
    (s1 s2 s3 : JStr) :
    StrsAt σ (ys ++ [a, b, c]) (ss ++ [s1, s2, s3]) ↔
      StrsAt σ ys ss ∧ strOf σ a = some s1 ∧ strOf σ b = some s2 ∧ strOf σ c = some s3 := by
  rw [show ys ++ [a, b, c] = ((ys ++ [a]) ++ [b]) ++ [c] by simp,
    show ss ++ [s1, s2, s3] = ((ss ++ [s1]) ++ [s2]) ++ [s3] by simp,
    StrsAt_snoc, StrsAt_snoc, StrsAt_snoc, and_assoc, and_assoc]

end EquivLean.Modernize.Cbtrn03c.Java.Top
