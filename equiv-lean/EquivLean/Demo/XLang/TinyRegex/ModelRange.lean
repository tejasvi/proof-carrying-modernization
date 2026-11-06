import EquivLean.Demo.XLang.TinyRegex.Model

/-!
# tiny-regex-c model: the range of its results

Two facts about the model alone, used to state the Rust ↔ C equivalence on exact `int` values:
* `reMatch_ret_range`: the return value is `-1` or a text index;
* `reMatch_ml_range`: without undefined behaviour (`ub = 0`) the final `*matchlength` is an
  `int` (every value it takes is either `0` or an increment/decrement whose overflow sets the
  `ubOverflow` bit, and the mask only grows).
-/

namespace EquivLean.Demo.XLang.TinyRegex

/-- An `int` value. -/
def InR (v : Int) : Prop := INT_MIN ≤ v ∧ v ≤ INT_MAX

/-- No `int` overflow recorded in a UB mask. -/
def NoOv (ub : Nat) : Prop := ub.testBit 4 = false

theorem noOv_or (a b : Nat) : NoOv (a ||| b) ↔ NoOv a ∧ NoOv b := by
  simp [NoOv, Nat.testBit_or]

theorem noOv_chk (v : Int) : NoOv (chk v) ↔ InR v := by
  unfold chk NoOv InR
  by_cases h : INT_MIN ≤ v ∧ v ≤ INT_MAX
  · simp [h]
  · have h16 : Nat.testBit ubOverflow 4 = true := by unfold ubOverflow; decide
    simp [h, h16]

theorem noOv_zero : NoOv 0 := by unfold NoOv; decide
theorem noOv_ubRead : NoOv ubRead := by unfold NoOv ubRead; decide
theorem noOv_ubStar : NoOv ubStar := by unfold NoOv ubStar; decide
theorem noOv_ubPtr : NoOv ubPtr := by unfold NoOv ubPtr; decide

theorem inR_zero : InR 0 := by unfold InR INT_MIN INT_MAX; omega

/-- The first loop of `matchstar`/`matchplus`: the mask only grows, and `*matchlength` stays an
`int` unless the overflow bit is set. -/
theorem advance_range (C : Ctx) (p : Tok) :
    ∀ (n ti : Nat) (ml : Int) (ub : Nat), C.T.size - ti = n →
      (NoOv (advance C p ti ml ub).2.2 → NoOv ub) ∧
        (InR ml → NoOv (advance C p ti ml ub).2.2 → InR (advance C p ti ml ub).2.1) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro ti ml ub hn
  rw [advance.eq_1]
  by_cases h1 : ti < C.T.size
  · rw [dite_eq_left h1]
    simp only []
    by_cases h2 : (C.T[ti] != 0) = true
    · rw [ite_eq_left h2]
      by_cases h3 : (matchone C p C.T[ti]).1 = true
      · rw [ite_eq_left h3]
        have IH' := IH _ (by omega) (ti + 1) (ml + 1)
          (ub ||| (matchone C p C.T[ti]).2 ||| chk (ml + 1)) rfl
        refine ⟨fun hno => ?_, fun hml hno => ?_⟩
        · have := IH'.1 hno
          simp only [noOv_or] at this
          exact this.1.1
        · have hA := IH'.1 hno
          simp only [noOv_or, noOv_chk] at hA
          exact IH'.2 hA.2 hno
      · rw [ite_eq_right h3]
        refine ⟨fun hno => ?_, fun hml _ => hml⟩
        simp only [noOv_or] at hno
        exact hno.1
    · rw [ite_eq_right h2]
      exact ⟨id, fun hml _ => hml⟩
  · rw [dite_eq_right h1]
    split
    · exact ⟨id, fun hml _ => hml⟩
    · refine ⟨fun hno => ?_, fun hml _ => hml⟩
      simp only [noOv_or] at hno
      exact hno.1

/-! ## The recursion group -/

/-- For each function of the group at pattern index `pi`: the mask only grows, and the result's
`*matchlength` is an `int` (if the inputs are) unless the overflow bit is set. -/
def RMP (C : Ctx) (pi : Nat) : Prop := ∀ pre ti ml ub,
  (NoOv (mpLoop C pre pi ti ml ub).ub → NoOv ub) ∧
    (InR ml → InR pre → NoOv (mpLoop C pre pi ti ml ub).ub → InR (mpLoop C pre pi ti ml ub).ml)
def RMQ (C : Ctx) (pi : Nat) : Prop := ∀ p ti ml ub,
  (NoOv (matchquestion C p pi ti ml ub).ub → NoOv ub) ∧
    (InR ml → NoOv (matchquestion C p pi ti ml ub).ub → InR (matchquestion C p pi ti ml ub).ml)
def RSB (C : Ctx) (pi : Nat) : Prop := ∀ prelen pre ti ml ub,
  (NoOv (starBack C pi prelen pre ti ml ub).ub → NoOv ub) ∧
    (InR prelen → InR ml → NoOv (starBack C pi prelen pre ti ml ub).ub →
      InR (starBack C pi prelen pre ti ml ub).ml)
def RMS (C : Ctx) (pi : Nat) : Prop := ∀ p ti ml ub,
  (NoOv (matchstar C p pi ti ml ub).ub → NoOv ub) ∧
    (InR ml → NoOv (matchstar C p pi ti ml ub).ub → InR (matchstar C p pi ti ml ub).ml)
def RPB (C : Ctx) (pi : Nat) : Prop := ∀ pre ti ml ub,
  (NoOv (plusBack C pi pre ti ml ub).ub → NoOv ub) ∧
    (InR ml → NoOv (plusBack C pi pre ti ml ub).ub → InR (plusBack C pi pre ti ml ub).ml)
def RMPl (C : Ctx) (pi : Nat) : Prop := ∀ p ti ml ub,
  (NoOv (matchplus C p pi ti ml ub).ub → NoOv ub) ∧
    (InR ml → NoOv (matchplus C p pi ti ml ub).ub → InR (matchplus C p pi ti ml ub).ml)

theorem matchquestion_unused_eq (C : Ctx) (p : Tok) (pi ti : Nat) (ml : Int) (ub : Nat)
    (hu : (p.type == UNUSED) = true) : matchquestion C p pi ti ml ub = ⟨true, ml, ub⟩ := by
  rw [matchquestion.eq_1, ite_eq_left hu]

theorem rmp_step (C : Ctx) (pi : Nat)
    (IH : ∀ pi', C.P.size - pi' < C.P.size - pi → RMP C pi' ∧ RMQ C pi' ∧ RMS C pi' ∧ RMPl C pi') :
    RMP C pi := by
  intro pre ti ml ub
  rw [mpLoop.eq_1]
  by_cases hpi : pi < C.P.size
  · rw [dite_eq_left hpi]
    simp only []
    by_cases hu : (C.P[pi].type == UNUSED) = true
    · rw [ite_eq_left hu, matchquestion_unused_eq _ _ _ _ _ _ hu]
      refine ⟨fun hno => ?_, fun hml _ _ => hml⟩
      split at hno
      · exact hno
      · exact ((noOv_or _ _).1 hno).1
    rw [ite_eq_right hu]
    by_cases hp1 : pi + 1 < C.P.size
    · rw [dite_eq_left hp1]
      have hQ := (IH (pi + 2) (by omega)).2.1 C.P[pi] ti ml ub
      have hS := (IH (pi + 2) (by omega)).2.2.1 C.P[pi] ti ml ub
      have hPl := (IH (pi + 2) (by omega)).2.2.2 C.P[pi] ti ml ub
      have hM := (IH (pi + 1) (by omega)).1 pre (ti + 1) (ml + 1)
        (ub ||| chk (ml + 1) ||| (rd C.T ti).snd ||| (matchone C C.P[pi] (rd C.T ti).fst).snd)
      clear IH
      (repeat' split) <;> constructor <;> intros <;> simp_all [noOv_or, noOv_chk]
    · rw [dite_eq_right hp1]
      refine ⟨fun hno => ((noOv_or _ _).1 hno).1, fun hml _ _ => hml⟩
  · rw [dite_eq_right hpi]
    refine ⟨fun hno => ((noOv_or _ _).1 hno).1, fun hml _ _ => hml⟩

theorem rmq_step (C : Ctx) (pi : Nat) (hmp : RMP C pi) : RMQ C pi := by
  intro p ti ml ub
  rw [matchquestion.eq_1]
  simp only []
  have h1 := hmp ml ti ml ub
  have h2 := hmp (mpLoop C ml pi ti ml ub).ml (ti + 1) (mpLoop C ml pi ti ml ub).ml
    ((mpLoop C ml pi ti ml ub).ub ||| (rd C.T ti).snd ||| (matchone C p (rd C.T ti).fst).snd)
  (repeat' split) <;> constructor <;> intros <;> simp_all [noOv_or, noOv_chk]

theorem rsb_step (C : Ctx) (pi : Nat) (hmp : RMP C pi) : RSB C pi := by
  suffices H : ∀ (n : Nat) (prelen : Int) (pre ti : Nat) (ml : Int) (ub : Nat), ti = n →
      (NoOv (starBack C pi prelen pre ti ml ub).ub → NoOv ub) ∧
        (InR prelen → InR ml → NoOv (starBack C pi prelen pre ti ml ub).ub →
          InR (starBack C pi prelen pre ti ml ub).ml) by
    intro prelen pre ti ml ub
    exact H ti prelen pre ti ml ub rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro prelen pre ti ml ub hn
  rw [starBack.eq_1]
  simp only []
  have h1 := hmp ml ti ml (if ti = 0 then ub ||| ubStar else ub)
  have h2 : ti ≠ 0 → _ := fun hti => IH (ti - 1) (by omega) prelen pre (ti - 1)
    ((mpLoop C ml pi ti ml (if ti = 0 then ub ||| ubStar else ub)).ml - 1)
    ((mpLoop C ml pi ti ml (if ti = 0 then ub ||| ubStar else ub)).ub |||
      chk ((mpLoop C ml pi ti ml (if ti = 0 then ub ||| ubStar else ub)).ml - 1)) rfl
  clear IH
  (repeat' split) <;> constructor <;> intros <;> simp_all [noOv_or, noOv_chk]

theorem rms_step (C : Ctx) (pi : Nat) (hsb : RSB C pi) : RMS C pi := by
  intro p ti ml ub
  rw [matchstar.eq_1]
  simp only []
  have ha := advance_range C p _ ti ml ub rfl
  have hb := hsb ml ti (advance C p ti ml ub).1 (advance C p ti ml ub).2.1 (advance C p ti ml ub).2.2
  constructor <;> intros <;> simp_all

theorem rpb_step (C : Ctx) (pi : Nat) (hmp : RMP C pi) : RPB C pi := by
  suffices H : ∀ (n pre ti : Nat) (ml : Int) (ub : Nat), ti = n →
      (NoOv (plusBack C pi pre ti ml ub).ub → NoOv ub) ∧
        (InR ml → NoOv (plusBack C pi pre ti ml ub).ub → InR (plusBack C pi pre ti ml ub).ml) by
    intro pre ti ml ub
    exact H ti pre ti ml ub rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro pre ti ml ub hn
  rw [plusBack.eq_1]
  simp only []
  have h1 := hmp ml ti ml ub
  have h2 : pre < ti → _ := fun hlt => IH (ti - 1) (by omega) pre (ti - 1)
    ((mpLoop C ml pi ti ml ub).ml - 1)
    ((mpLoop C ml pi ti ml ub).ub ||| chk ((mpLoop C ml pi ti ml ub).ml - 1)) rfl
  clear IH
  (repeat' split) <;> constructor <;> intros <;> simp_all [noOv_or, noOv_chk]

theorem rmpl_step (C : Ctx) (pi : Nat) (hpb : RPB C pi) : RMPl C pi := by
  intro p ti ml ub
  rw [matchplus.eq_1]
  simp only []
  have ha := advance_range C p _ ti ml ub rfl
  have hb := hpb ti (advance C p ti ml ub).1 (advance C p ti ml ub).2.1 (advance C p ti ml ub).2.2
  constructor <;> intros <;> simp_all

/-- The whole group, at every pattern index. -/
theorem group_range (C : Ctx) :
    ∀ (n pi : Nat), C.P.size - pi = n →
      RMP C pi ∧ RMQ C pi ∧ RSB C pi ∧ RMS C pi ∧ RPB C pi ∧ RMPl C pi := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro pi hn
  have hmp := rmp_step C pi (fun pi' h =>
    let r := IH _ (by omega) pi' rfl
    ⟨r.1, r.2.1, r.2.2.2.1, r.2.2.2.2.2⟩)
  have hsb := rsb_step C pi hmp
  have hpb := rpb_step C pi hmp
  exact ⟨hmp, rmq_step C pi hmp, hsb, rms_step C pi hsb, hpb, rmpl_step C pi hpb⟩

/-! ## `re_matchp`, `re_match` -/

theorem searchLoop_range (C : Ctx) :
    ∀ (n ti : Nat) (ml : Int) (ub : Nat), C.T.size - ti = n →
      (NoOv (searchLoop C ti ml ub).2.2 → NoOv ub) ∧
        (InR ml → NoOv (searchLoop C ti ml ub).2.2 → InR (searchLoop C ti ml ub).2.1) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro ti ml ub hn
  rw [searchLoop.eq_1]
  simp only []
  have h1 := (group_range C _ 0 rfl).1 ml ti ml (ub ||| chk ti)
  have h2 : ti < C.T.size → _ := fun hlt => IH _ (by omega) (ti + 1)
    (mpLoop C ml 0 ti ml (ub ||| chk ti)).ml (mpLoop C ml 0 ti ml (ub ||| chk ti)).ub rfl
  clear IH
  (repeat' split) <;> constructor <;> intros <;> simp_all [noOv_or, noOv_chk]

theorem searchLoop_ret (C : Ctx) :
    ∀ (n ti : Nat) (ml : Int) (ub : Nat), C.T.size - ti = n →
      (searchLoop C ti ml ub).1 = -1 ∨
        (0 ≤ (searchLoop C ti ml ub).1 ∧ (searchLoop C ti ml ub).1 < C.T.size) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro ti ml ub hn
  rw [searchLoop.eq_1]
  simp only []
  have h2 : ti < C.T.size → _ := fun hlt => IH _ (by omega) (ti + 1)
    (mpLoop C ml 0 ti ml (ub ||| chk ti)).ml (mpLoop C ml 0 ti ml (ub ||| chk ti)).ub rfl
  clear IH
  (repeat' split) <;> simp_all <;> omega

/-- Without undefined behaviour, the final `*matchlength` of `re_match` is an `int`. -/
theorem reMatch_ml_range (p t : List Nat) (h : (reMatch p t).2.2 = 0) :
    INT_MIN ≤ (reMatch p t).2.1 ∧ (reMatch p t).2.1 ≤ INT_MAX := by
  revert h
  simp only [reMatch]
  rcases hc : (compile p.toArray).1 with _ | ⟨P, B⟩
  · intro _; exact inR_zero
  · simp only [reMatchp]
    split
    · intro h
      simp only at h
      exact ((group_range ⟨P, B, t.toArray⟩ _ 1 rfl).1 0 0 0 _).2 inR_zero inR_zero
        (by rw [h]; exact noOv_zero)
    · intro h
      exact (searchLoop_range ⟨P, B, t.toArray⟩ _ 0 0 _ rfl).2 inR_zero (by rw [h]; exact noOv_zero)

/-- The return value of `re_match` is `-1` or a text index (`0` also for `^` on the empty text). -/
theorem reMatch_ret_range (p t : List Nat) :
    (reMatch p t).1 = -1 ∨ (0 ≤ (reMatch p t).1 ∧ (reMatch p t).1 ≤ t.length) := by
  simp only [reMatch]
  rcases hc : (compile p.toArray).1 with _ | ⟨P, B⟩
  · simp [reMatchp]
  · simp only [reMatchp]
    split
    · split <;> simp
    · have := searchLoop_ret ⟨P, B, t.toArray⟩ _ 0 0 (compile p.toArray).2 rfl
      simp only [List.size_toArray] at this
      omega

end EquivLean.Demo.XLang.TinyRegex

#print axioms EquivLean.Demo.XLang.TinyRegex.reMatch_ml_range
#print axioms EquivLean.Demo.XLang.TinyRegex.reMatch_ret_range
