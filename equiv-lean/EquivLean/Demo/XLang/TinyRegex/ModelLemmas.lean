import EquivLean.Demo.XLang.TinyRegex.ModelRange

/-!
# tiny-regex-c model: lemmas for the C-side proofs

Facts about the model alone (core Lean), for the CIR proofs of `re_compile` and of the matcher.
* UB masks only grow: every function keeps the bits of its input mask in its result's
  (`*_mono`), so a mask that is `0` at the end was `0` at every call on the way, and a mask that
  is not `0` stays so (`*_ub_eq_zero`).
* `re_compile` has no undefined behaviour in the model, for every pattern (`compile_ub_eq_zero`):
  its reads stop at the NUL; one-step equations of its loop (`compLoop_exit`, `compLoop_step`) and
  of the `[..]` copy (`cclCopy_stop`, `cclCopy_esc*`, `cclCopy_full`, `cclCopy_char`,
  `cclCopy_last`).
* The invariant of `re_compile`'s loop (`CompInv`: sizes, zero entries ahead, `ccl_bufidx` in
  `1..40`, class tokens inside `ccl_buf`) holds at the start and is kept by `compStep`; every
  compiled regex satisfies `CompRes` (`compile_some`).  With a C-string pattern, also bytes
  everywhere and NUL-terminated classes (`CompWF`, `compile_wf`).
-/

namespace EquivLean.Demo.XLang.TinyRegex

/-! ## Masks -/

/-- The bits of `a` are bits of `b`. -/
def Bits (a b : Nat) : Prop := ∀ i, a.testBit i = true → b.testBit i = true

theorem bits_refl (a : Nat) : Bits a a := fun _ h => h

theorem bits_or_left (a b : Nat) : Bits a (a ||| b) := fun i h => by
  simp [Nat.testBit_or, h]

theorem bits_or {a b : Nat} (c : Nat) (h : Bits a b) : Bits a (b ||| c) := fun i hi => by
  simp [Nat.testBit_or, h i hi]

theorem bits_trans {a b c : Nat} (h1 : Bits a b) (h2 : Bits b c) : Bits a c :=
  fun i h => h2 i (h1 i h)

theorem eq_zero_of_bits {a b : Nat} (h : Bits a b) (hb : b = 0) : a = 0 := by
  subst hb
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.zero_testBit]
  cases hc : a.testBit i
  · rfl
  · have := h i hc
    simp at this

theorem ne_zero_of_bits {a b : Nat} (h : Bits a b) (ha : a ≠ 0) : b ≠ 0 :=
  fun hb => ha (eq_zero_of_bits h hb)

/-! ## The first loop of `matchstar`/`matchplus` -/

theorem advance_mono (C : Ctx) (p : Tok) :
    ∀ (n ti : Nat) (ml : Int) (ub : Nat), C.T.size - ti = n →
      Bits ub (advance C p ti ml ub).2.2 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro ti ml ub hn
  rw [advance.eq_1]
  simp only []
  have h2 : ∀ h : ti < C.T.size, _ := fun hlt => IH _ (by omega) (ti + 1) (ml + 1)
    (ub ||| (matchone C p C.T[ti]).2 ||| chk (ml + 1)) rfl
  clear IH
  (repeat' split) <;> simp_all [Bits, Nat.testBit_or]

/-! ## The recursion group -/

def MMP (C : Ctx) (pi : Nat) : Prop := ∀ pre ti ml ub, Bits ub (mpLoop C pre pi ti ml ub).ub
def MMQ (C : Ctx) (pi : Nat) : Prop := ∀ p ti ml ub, Bits ub (matchquestion C p pi ti ml ub).ub
def MSB (C : Ctx) (pi : Nat) : Prop :=
  ∀ prelen pre ti ml ub, Bits ub (starBack C pi prelen pre ti ml ub).ub
def MMS (C : Ctx) (pi : Nat) : Prop := ∀ p ti ml ub, Bits ub (matchstar C p pi ti ml ub).ub
def MPB (C : Ctx) (pi : Nat) : Prop := ∀ pre ti ml ub, Bits ub (plusBack C pi pre ti ml ub).ub
def MMPl (C : Ctx) (pi : Nat) : Prop := ∀ p ti ml ub, Bits ub (matchplus C p pi ti ml ub).ub

theorem mmp_step (C : Ctx) (pi : Nat)
    (IH : ∀ pi', C.P.size - pi' < C.P.size - pi → MMP C pi' ∧ MMQ C pi' ∧ MMS C pi' ∧ MMPl C pi') :
    MMP C pi := by
  intro pre ti ml ub
  rw [mpLoop.eq_1]
  by_cases hpi : pi < C.P.size
  · rw [dite_eq_left hpi]
    simp only []
    by_cases hu : (C.P[pi].type == UNUSED) = true
    · rw [ite_eq_left hu, matchquestion_unused_eq _ _ _ _ _ _ hu]
      split <;> (intro i hi; simp [Nat.testBit_or, hi])
    rw [ite_eq_right hu]
    by_cases hp1 : pi + 1 < C.P.size
    · rw [dite_eq_left hp1]
      have hQ := (IH (pi + 2) (by omega)).2.1 C.P[pi] ti ml ub
      have hS := (IH (pi + 2) (by omega)).2.2.1 C.P[pi] ti ml ub
      have hPl := (IH (pi + 2) (by omega)).2.2.2 C.P[pi] ti ml ub
      have hM := (IH (pi + 1) (by omega)).1 pre (ti + 1) (ml + 1)
        (ub ||| chk (ml + 1) ||| (rd C.T ti).snd ||| (matchone C C.P[pi] (rd C.T ti).fst).snd)
      clear IH
      (repeat' split) <;> simp_all [Bits, Nat.testBit_or]
    · rw [dite_eq_right hp1]
      exact bits_or_left _ _
  · rw [dite_eq_right hpi]
    exact bits_or_left _ _

theorem mmq_step (C : Ctx) (pi : Nat) (hmp : MMP C pi) : MMQ C pi := by
  intro p ti ml ub
  rw [matchquestion.eq_1]
  simp only []
  have h1 := hmp ml ti ml ub
  have h2 := hmp (mpLoop C ml pi ti ml ub).ml (ti + 1) (mpLoop C ml pi ti ml ub).ml
    ((mpLoop C ml pi ti ml ub).ub ||| (rd C.T ti).snd ||| (matchone C p (rd C.T ti).fst).snd)
  (repeat' split) <;> simp_all [Bits, Nat.testBit_or]

theorem msb_step (C : Ctx) (pi : Nat) (hmp : MMP C pi) : MSB C pi := by
  suffices H : ∀ (n : Nat) (prelen : Int) (pre ti : Nat) (ml : Int) (ub : Nat), ti = n →
      Bits ub (starBack C pi prelen pre ti ml ub).ub by
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
  (repeat' split) <;> simp_all [Bits, Nat.testBit_or]

theorem mms_step (C : Ctx) (pi : Nat) (hsb : MSB C pi) : MMS C pi := by
  intro p ti ml ub
  rw [matchstar.eq_1]
  simp only []
  exact bits_trans (advance_mono C p _ ti ml ub rfl) (hsb _ _ _ _ _)

theorem mpb_step (C : Ctx) (pi : Nat) (hmp : MMP C pi) : MPB C pi := by
  suffices H : ∀ (n pre ti : Nat) (ml : Int) (ub : Nat), ti = n →
      Bits ub (plusBack C pi pre ti ml ub).ub by
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
  (repeat' split) <;> simp_all [Bits, Nat.testBit_or]

theorem mmpl_step (C : Ctx) (pi : Nat) (hpb : MPB C pi) : MMPl C pi := by
  intro p ti ml ub
  rw [matchplus.eq_1]
  simp only []
  exact bits_trans (advance_mono C p _ ti ml ub rfl) (hpb _ _ _ _)

/-- Every function of the group keeps the bits of its input mask. -/
theorem group_mono (C : Ctx) :
    ∀ (n pi : Nat), C.P.size - pi = n →
      MMP C pi ∧ MMQ C pi ∧ MSB C pi ∧ MMS C pi ∧ MPB C pi ∧ MMPl C pi := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro pi hn
  have hmp := mmp_step C pi (fun pi' h =>
    let r := IH _ (by omega) pi' rfl
    ⟨r.1, r.2.1, r.2.2.2.1, r.2.2.2.2.2⟩)
  have hsb := msb_step C pi hmp
  have hpb := mpb_step C pi hmp
  exact ⟨hmp, mmq_step C pi hmp, hsb, mms_step C pi hsb, hpb, mmpl_step C pi hpb⟩

theorem mpLoop_mono (C : Ctx) (pre : Int) (pi ti : Nat) (ml : Int) (ub : Nat) :
    Bits ub (mpLoop C pre pi ti ml ub).ub := (group_mono C _ pi rfl).1 pre ti ml ub
theorem matchquestion_mono (C : Ctx) (p : Tok) (pi ti : Nat) (ml : Int) (ub : Nat) :
    Bits ub (matchquestion C p pi ti ml ub).ub := (group_mono C _ pi rfl).2.1 p ti ml ub
theorem starBack_mono (C : Ctx) (pi : Nat) (prelen : Int) (pre ti : Nat) (ml : Int) (ub : Nat) :
    Bits ub (starBack C pi prelen pre ti ml ub).ub := (group_mono C _ pi rfl).2.2.1 prelen pre ti ml ub
theorem matchstar_mono (C : Ctx) (p : Tok) (pi ti : Nat) (ml : Int) (ub : Nat) :
    Bits ub (matchstar C p pi ti ml ub).ub := (group_mono C _ pi rfl).2.2.2.1 p ti ml ub
theorem plusBack_mono (C : Ctx) (pi pre ti : Nat) (ml : Int) (ub : Nat) :
    Bits ub (plusBack C pi pre ti ml ub).ub := (group_mono C _ pi rfl).2.2.2.2.1 pre ti ml ub
theorem matchplus_mono (C : Ctx) (p : Tok) (pi ti : Nat) (ml : Int) (ub : Nat) :
    Bits ub (matchplus C p pi ti ml ub).ub := (group_mono C _ pi rfl).2.2.2.2.2 p ti ml ub

/-! ## The search loop, `reMatchp`, the class loop, `compLoop` -/

theorem searchLoop_mono (C : Ctx) :
    ∀ (n ti : Nat) (ml : Int) (ub : Nat), C.T.size - ti = n →
      Bits ub (searchLoop C ti ml ub).2.2 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro ti ml ub hn
  rw [searchLoop.eq_1]
  simp only []
  have h1 := mpLoop_mono C ml 0 ti ml (ub ||| chk ti)
  have h2 : ti < C.T.size → _ := fun hlt => IH _ (by omega) (ti + 1)
    (mpLoop C ml 0 ti ml (ub ||| chk ti)).ml (mpLoop C ml 0 ti ml (ub ||| chk ti)).ub rfl
  clear IH
  (repeat' split) <;> simp_all [Bits, Nat.testBit_or]

theorem reMatchp_mono (cp : Option (_root_.Array Tok × _root_.Array Nat)) (T : _root_.Array Nat)
    (ub : Nat) : Bits ub (reMatchp cp T ub).2.2 := by
  unfold reMatchp
  split
  · exact bits_refl _
  · split
    · exact mpLoop_mono _ _ _ _ _ _
    · exact searchLoop_mono _ _ 0 0 _ rfl

theorem matchcharclass_mono (B : _root_.Array Nat) (c : Nat) :
    ∀ (n k ub : Nat), B.size - k = n → Bits ub (matchcharclass B c k ub).2 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro k ub hn
  rw [matchcharclass.eq_1]
  simp only []
  have h1 : k + 1 < B.size → ∀ u, Bits u (matchcharclass B c (k + 2) u).2 :=
    fun hlt u => IH _ (by omega) (k + 2) u rfl
  have h2 : k < B.size → ∀ u, Bits u (matchcharclass B c (k + 1) u).2 :=
    fun hlt u => IH _ (by omega) (k + 1) u rfl
  clear IH
  (repeat' split) <;> simp_all [Bits, Nat.testBit_or]

theorem compLoop_mono (p : _root_.Array Nat) :
    ∀ (n i j bidx : Nat) (re : _root_.Array Tok) (buf : _root_.Array Nat) (ub : Nat), MAXOBJ - j = n →
      Bits ub (compLoop p i j bidx re buf ub).2 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro i j bidx re buf ub hn
  rw [compLoop.eq_1]
  simp only []
  have h1 : j + 1 < MAXOBJ → ∀ i' bidx' re' buf' u, Bits u (compLoop p i' (j + 1) bidx' re' buf' u).2 :=
    fun hlt i' bidx' re' buf' u => IH _ (by omega) i' (j + 1) bidx' re' buf' u rfl
  clear IH
  (repeat' split) <;> simp_all [Bits, Nat.testBit_or]

/-! ## A mask that is `0` at the end was `0` on entry -/

theorem mpLoop_ub_eq_zero {C : Ctx} {pre : Int} {pi ti : Nat} {ml : Int} {ub : Nat}
    (h : (mpLoop C pre pi ti ml ub).ub = 0) : ub = 0 := eq_zero_of_bits (mpLoop_mono C pre pi ti ml ub) h
theorem matchquestion_ub_eq_zero {C : Ctx} {p : Tok} {pi ti : Nat} {ml : Int} {ub : Nat}
    (h : (matchquestion C p pi ti ml ub).ub = 0) : ub = 0 :=
  eq_zero_of_bits (matchquestion_mono C p pi ti ml ub) h
theorem starBack_ub_eq_zero {C : Ctx} {pi : Nat} {prelen : Int} {pre ti : Nat} {ml : Int} {ub : Nat}
    (h : (starBack C pi prelen pre ti ml ub).ub = 0) : ub = 0 := eq_zero_of_bits (starBack_mono C pi prelen pre ti ml ub) h
theorem matchstar_ub_eq_zero {C : Ctx} {p : Tok} {pi ti : Nat} {ml : Int} {ub : Nat}
    (h : (matchstar C p pi ti ml ub).ub = 0) : ub = 0 := eq_zero_of_bits (matchstar_mono C p pi ti ml ub) h
theorem plusBack_ub_eq_zero {C : Ctx} {pi pre ti : Nat} {ml : Int} {ub : Nat}
    (h : (plusBack C pi pre ti ml ub).ub = 0) : ub = 0 := eq_zero_of_bits (plusBack_mono C pi pre ti ml ub) h
theorem matchplus_ub_eq_zero {C : Ctx} {p : Tok} {pi ti : Nat} {ml : Int} {ub : Nat}
    (h : (matchplus C p pi ti ml ub).ub = 0) : ub = 0 := eq_zero_of_bits (matchplus_mono C p pi ti ml ub) h
theorem advance_ub_eq_zero {C : Ctx} {p : Tok} {ti : Nat} {ml : Int} {ub : Nat}
    (h : (advance C p ti ml ub).2.2 = 0) : ub = 0 := eq_zero_of_bits (advance_mono C p _ ti ml ub rfl) h
theorem searchLoop_ub_eq_zero {C : Ctx} {ti : Nat} {ml : Int} {ub : Nat}
    (h : (searchLoop C ti ml ub).2.2 = 0) : ub = 0 := eq_zero_of_bits (searchLoop_mono C _ ti ml ub rfl) h
theorem reMatchp_ub_eq_zero {cp : Option (_root_.Array Tok × _root_.Array Nat)} {T : _root_.Array Nat}
    {ub : Nat} (h : (reMatchp cp T ub).2.2 = 0) : ub = 0 := eq_zero_of_bits (reMatchp_mono cp T ub) h
theorem matchcharclass_ub_eq_zero {B : _root_.Array Nat} {c k ub : Nat}
    (h : (matchcharclass B c k ub).2 = 0) : ub = 0 :=
  eq_zero_of_bits (matchcharclass_mono B c _ k ub rfl) h
theorem compLoop_ub_eq_zero {p : _root_.Array Nat} {i j bidx : Nat} {re : _root_.Array Tok}
    {buf : _root_.Array Nat} {ub : Nat} (h : (compLoop p i j bidx re buf ub).2 = 0) : ub = 0 :=
  eq_zero_of_bits (compLoop_mono p _ i j bidx re buf ub rfl) h

/-- `re_match` without UB: `compile` had no UB either. -/
theorem compile_ub_eq_zero_of_reMatch {p t : List Nat} (h : (reMatch p t).2.2 = 0) :
    (compile p.toArray).2 = 0 := by
  simp only [reMatch] at h
  exact reMatchp_ub_eq_zero h

/-! ## `re_compile` reads nothing past the NUL: `(compile p).2 = 0` -/

theorem rd_of_lt {p : _root_.Array Nat} {i : Nat} (h : i < p.size) : rd p i = (p[i], 0) := by
  unfold rd
  rw [dite_eq_left h]

theorem rd_size (p : _root_.Array Nat) : rd p p.size = (0, 0) := by
  unfold rd
  rw [dite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl]

theorem rd_snd_of_le {p : _root_.Array Nat} {i : Nat} (h : i ≤ p.size) : (rd p i).2 = 0 := by
  unfold rd
  split
  · rfl
  · rw [ite_eq_left (by omega)]

theorem lt_size_of_rd_ne_zero {p : _root_.Array Nat} {i : Nat} (h : (rd p i).1 ≠ 0) :
    i < p.size := by
  unfold rd at h
  split at h
  · assumption
  · split at h <;> simp at h

/-- The `[..]` copy, started inside the pattern, reads nothing past its end. -/
theorem cclCopy_snd (p : _root_.Array Nat) :
    ∀ (n i bidx : Nat) (buf : _root_.Array Nat), p.size - i = n → i < p.size →
      (cclCopy p i bidx buf).2 = 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro i bidx buf hn hi
  rw [cclCopy.eq_1]
  by_cases h1 : i + 1 < p.size
  · rw [dite_eq_left h1]
    simp only []
    split
    · rfl
    · split
      · split
        · rfl
        · by_cases h2 : i + 2 < p.size
          · rw [dite_eq_left h2]
            split
            · rfl
            · exact IH _ (by omega) _ _ _ rfl (by omega)
          · rw [dite_eq_right h2, ite_eq_left (by omega)]
      · split
        · rfl
        · exact IH _ (by omega) _ _ _ rfl (by omega)
  · rw [dite_eq_right h1, ite_eq_left (by omega)]

/-- Where the `[..]` copy stops: after its start, inside the pattern (at the `]` or NUL, or at
the end), with `ccl_bufidx` only growing and staying within the buffer, `ccl_buf` keeping its size. -/
theorem cclCopy_some (p : _root_.Array Nat) :
    ∀ (n i bidx : Nat) (buf : _root_.Array Nat) (i' b' : Nat) (buf' : _root_.Array Nat),
      p.size - i = n → (cclCopy p i bidx buf).1 = some (i', b', buf') →
      i < i' ∧ i' ≤ p.size ∧ bidx ≤ b' ∧ (bidx ≤ MAXCCL → b' ≤ MAXCCL) ∧ buf'.size = buf.size := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro i bidx buf i' b' buf' hn h
  rw [cclCopy.eq_1] at h
  by_cases h1 : i + 1 < p.size
  · rw [dite_eq_left h1] at h
    simp only [] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      omega
    · split at h
      · split at h
        · simp at h
        · by_cases h2 : i + 2 < p.size
          · rw [dite_eq_left h2] at h
            split at h
            · simp at h
            · have := IH _ (by omega) _ _ _ _ _ _ rfl h
              simp only [_root_.Array.size_set!] at this
              unfold MAXCCL at *
              omega
          · rw [dite_eq_right h2] at h
            split at h <;> simp at h
      · split at h
        · simp at h
        · have := IH _ (by omega) _ _ _ _ _ _ rfl h
          simp only [_root_.Array.size_set!] at this
          unfold MAXCCL at *
          omega
  · rw [dite_eq_right h1] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      omega
    · simp at h

theorem compStep_snd {p : _root_.Array Nat} {i j bidx : Nat} {re : _root_.Array Tok}
    {buf : _root_.Array Nat} {c : Nat} (hi : i < p.size) : (compStep p i j bidx re buf c).2 = 0 := by
  have h1 : (rd p (i + 1)).2 = 0 := rd_snd_of_le (by omega)
  have h4 : (cclCopy p i bidx buf).2 = 0 := cclCopy_snd p _ _ _ _ rfl hi
  unfold compStep
  dsimp only
  by_cases c1 : (c == 94) = true; · rw [ite_eq_left c1]
  rw [ite_eq_right c1]
  by_cases c2 : (c == 36) = true; · rw [ite_eq_left c2]
  rw [ite_eq_right c2]
  by_cases c3 : (c == 46) = true; · rw [ite_eq_left c3]
  rw [ite_eq_right c3]
  by_cases c4 : (c == 42) = true; · rw [ite_eq_left c4]
  rw [ite_eq_right c4]
  by_cases c5 : (c == 43) = true; · rw [ite_eq_left c5]
  rw [ite_eq_right c5]
  by_cases c6 : (c == 63) = true; · rw [ite_eq_left c6]
  rw [ite_eq_right c6]
  by_cases c7 : (c == 92) = true
  · rw [ite_eq_left c7]
    by_cases c8 : ((rd p (i + 1)).fst != 0) = true
    · rw [ite_eq_left c8]; exact h1
    · rw [ite_eq_right c8]; exact h1
  rw [ite_eq_right c7]
  by_cases c9 : (c == 91) = true
  · rw [ite_eq_left c9]
    by_cases c10 : ((rd p (i + 1)).fst == 94) = true
    · rw [ite_eq_left c10]
      have h94' : (rd p (i + 1)).1 = 94 := by simpa using c10
      have hlt : i + 1 < p.size := lt_size_of_rd_ne_zero (by rw [h94']; decide)
      have h2 : (rd p (i + 2)).2 = 0 := rd_snd_of_le (by omega)
      have h3 : (cclCopy p (i + 1) bidx buf).2 = 0 := cclCopy_snd p _ _ _ _ rfl hlt
      by_cases c11 : ((rd p (i + 2)).fst == 0) = true
      · rw [ite_eq_left c11]
        show (rd p (i + 1)).snd ||| (rd p (i + 2)).snd = 0
        simp only [h1, h2, Nat.or_zero]
      · rw [ite_eq_right c11]
        rcases hcc : cclCopy p (i + 1) bidx buf with ⟨_ | ⟨i'', b'', buf''⟩, u3⟩
        · rw [hcc] at h3
          dsimp only at h3 ⊢
          simp only [h1, h2, h3, Nat.or_zero]
        · rw [hcc] at h3
          dsimp only at h3 ⊢
          by_cases c12 : b'' ≥ MAXCCL
          · rw [ite_eq_left c12]; dsimp only; simp only [h1, h2, h3, Nat.or_zero]
          · rw [ite_eq_right c12]; dsimp only; simp only [h1, h2, h3, Nat.or_zero]
    · rw [ite_eq_right c10]
      rcases hcc : cclCopy p i bidx buf with ⟨_ | ⟨i'', b'', buf''⟩, u3⟩
      · rw [hcc] at h4
        dsimp only at h4 ⊢
        simp only [h1, h4, Nat.or_zero]
      · rw [hcc] at h4
        dsimp only at h4 ⊢
        by_cases c12 : b'' ≥ MAXCCL
        · rw [ite_eq_left c12]; dsimp only; simp only [h1, h4, Nat.or_zero]
        · rw [ite_eq_right c12]; dsimp only; simp only [h1, h4, Nat.or_zero]
  · rw [ite_eq_right c9]

theorem fst_eq_of_some {α : Type} {a a' : Nat} {r r' : α} (h : some (a, r) = some (a', r')) :
    a = a' :=
  congrArg Prod.fst (Option.some.inj h)

theorem compStep_fst_le {p : _root_.Array Nat} {i j bidx : Nat} {re : _root_.Array Tok}
    {buf : _root_.Array Nat} {c i' b' : Nat} {re' : _root_.Array Tok} {buf' : _root_.Array Nat}
    (hi : i < p.size) (h : (compStep p i j bidx re buf c).1 = some (i', b', re', buf')) :
    i' ≤ p.size := by
  unfold compStep at h
  dsimp only at h
  by_cases c1 : (c == 94) = true
  · rw [ite_eq_left c1] at h; have := fst_eq_of_some h; omega
  rw [ite_eq_right c1] at h
  by_cases c2 : (c == 36) = true
  · rw [ite_eq_left c2] at h; have := fst_eq_of_some h; omega
  rw [ite_eq_right c2] at h
  by_cases c3 : (c == 46) = true
  · rw [ite_eq_left c3] at h; have := fst_eq_of_some h; omega
  rw [ite_eq_right c3] at h
  by_cases c4 : (c == 42) = true
  · rw [ite_eq_left c4] at h; have := fst_eq_of_some h; omega
  rw [ite_eq_right c4] at h
  by_cases c5 : (c == 43) = true
  · rw [ite_eq_left c5] at h; have := fst_eq_of_some h; omega
  rw [ite_eq_right c5] at h
  by_cases c6 : (c == 63) = true
  · rw [ite_eq_left c6] at h; have := fst_eq_of_some h; omega
  rw [ite_eq_right c6] at h
  by_cases c7 : (c == 92) = true
  · rw [ite_eq_left c7] at h
    by_cases c8 : ((rd p (i + 1)).fst != 0) = true
    · rw [ite_eq_left c8] at h; have := fst_eq_of_some h; omega
    · rw [ite_eq_right c8] at h; have := fst_eq_of_some h; omega
  rw [ite_eq_right c7] at h
  by_cases c9 : (c == 91) = true
  · rw [ite_eq_left c9] at h
    by_cases c10 : ((rd p (i + 1)).fst == 94) = true
    · rw [ite_eq_left c10] at h
      by_cases c11 : ((rd p (i + 2)).fst == 0) = true
      · rw [ite_eq_left c11] at h; cases h
      · rw [ite_eq_right c11] at h
        rcases hcc : cclCopy p (i + 1) bidx buf with ⟨_ | ⟨i'', b'', buf''⟩, u3⟩
        · rw [hcc] at h; cases h
        · rw [hcc] at h
          dsimp only at h
          have hs := (cclCopy_some p _ _ _ _ _ _ _ rfl (by rw [hcc])).2.1
          by_cases c12 : b'' ≥ MAXCCL
          · rw [ite_eq_left c12] at h; cases h
          · rw [ite_eq_right c12] at h; have := fst_eq_of_some h; omega
    · rw [ite_eq_right c10] at h
      rcases hcc : cclCopy p i bidx buf with ⟨_ | ⟨i'', b'', buf''⟩, u3⟩
      · rw [hcc] at h; cases h
      · rw [hcc] at h
        dsimp only at h
        have hs := (cclCopy_some p _ _ _ _ _ _ _ rfl (by rw [hcc])).2.1
        by_cases c12 : b'' ≥ MAXCCL
        · rw [ite_eq_left c12] at h; cases h
        · rw [ite_eq_right c12] at h; have := fst_eq_of_some h; omega
  · rw [ite_eq_right c9] at h; have := fst_eq_of_some h; omega

/-- `re_compile`'s loop, from any position inside the pattern, adds nothing to the mask. -/
theorem compLoop_snd (p : _root_.Array Nat) :
    ∀ (n i j bidx : Nat) (re : _root_.Array Tok) (buf : _root_.Array Nat) (ub : Nat),
      MAXOBJ - j = n → i ≤ p.size → (compLoop p i j bidx re buf ub).2 = ub := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro i j bidx re buf ub hn hi
  rw [compLoop.eq_1]
  simp only [rd_snd_of_le hi, Nat.or_zero]
  split
  · rename_i hc
    have hi' := lt_size_of_rd_ne_zero hc.1
    have hs : ∀ x, compStep p i j bidx re buf (rd p i).1 = x → x.2 = 0 := fun x hx =>
      hx ▸ compStep_snd hi'
    split
    · rename_i u' heq
      have := hs _ heq
      simp only at this
      simp [this]
    · rename_i i' b' re' buf' u' heq
      have hu := hs _ heq
      simp only at hu
      have hle : i' ≤ p.size := compStep_fst_le hi' (by rw [heq])
      simp only [rd_snd_of_le hle, hu, Nat.or_zero]
      split
      · rfl
      · rename_i hci
        exact IH _ (by unfold MAXOBJ at *; omega) _ _ _ _ _ _ rfl
          (by have := lt_size_of_rd_ne_zero (p := p) (i := i') (by simpa using hci); omega)
  · rfl

/-- **`re_compile` has no undefined behaviour in the model**, for every pattern: its reads stop at
the NUL. -/
theorem compile_ub_eq_zero (p : _root_.Array Nat) : (compile p).2 = 0 := by
  unfold compile
  exact compLoop_snd p _ 0 0 1 _ _ 0 rfl (Nat.zero_le _)

/-- The same, in the form asked for (the hypothesis is not needed). -/
theorem compile_ub_eq_zero' (p : _root_.Array Nat) (_hp : ∀ b ∈ p.toList, b ≠ 0) :
    (compile p).2 = 0 := compile_ub_eq_zero p

/-! ## One-step equations of `compLoop` (mask `0`) -/

theorem compLoop_exit {p : _root_.Array Nat} {i j bidx : Nat} {re : _root_.Array Tok}
    {buf : _root_.Array Nat} (hi : i ≤ p.size) (h : (rd p i).1 = 0 ∨ MAXOBJ ≤ j + 1) :
    compLoop p i j bidx re buf 0 = (some (re.set! j { re[j]! with type := UNUSED }, buf), 0) := by
  rw [compLoop.eq_1]
  simp only [rd_snd_of_le hi, Nat.or_zero]
  rw [dite_eq_right (by rintro ⟨h1, h2⟩; rcases h with h | h; exact h1 h; omega)]

theorem compLoop_step {p : _root_.Array Nat} {i j bidx : Nat} {re : _root_.Array Tok}
    {buf : _root_.Array Nat} (hi : i < p.size) (h0 : p[i] ≠ 0) (hj : j + 1 < MAXOBJ) :
    compLoop p i j bidx re buf 0 =
      match compStep p i j bidx re buf p[i] with
      | (none, u) => (none, u)
      | (some (i', b', re', buf'), u) =>
        if (rd p i').1 = 0 then (none, u ||| (rd p i').2)
        else compLoop p (i' + 1) (j + 1) b' re' buf' (u ||| (rd p i').2) := by
  rw [compLoop.eq_1]
  simp only [rd_of_lt hi, Nat.or_zero, Nat.zero_or]
  rw [dite_eq_left ⟨h0, hj⟩]
  rcases compStep p i j bidx re buf p[i] with ⟨_ | ⟨i', b', re', buf'⟩, u⟩
  · rfl
  · simp only [Bool.beq_eq_decide_eq, decide_eq_true_eq]

/-! ## One-step equations of the `[..]` copy `cclCopy` (by the next character `p[i + 1]`) -/

theorem cclCopy_unfold {p : _root_.Array Nat} {i bidx : Nat} {buf : _root_.Array Nat}
    (h : i + 1 < p.size) :
    cclCopy p i bidx buf =
      if (p[i + 1] == 93 || p[i + 1] == 0) = true then (some (i + 1, bidx, buf), 0)
      else if (p[i + 1] == 92) = true then
        if bidx ≥ MAXCCL - 1 then (none, 0)
        else if h2 : i + 2 < p.size then
          if (p[i + 2] == 0) = true then (none, 0)
          else cclCopy p (i + 2) (bidx + 2) ((buf.set! bidx p[i + 1]).set! (bidx + 1) p[i + 2])
        else if i + 2 = p.size then (none, 0) else (none, ubRead)
      else if bidx ≥ MAXCCL then (none, 0)
      else cclCopy p (i + 1) (bidx + 1) (buf.set! bidx p[i + 1]) := by
  rw [cclCopy.eq_1, dite_eq_left h]

/-- `]` or NUL: the copy ends there. -/
theorem cclCopy_stop {p : _root_.Array Nat} {i bidx : Nat} {buf : _root_.Array Nat}
    (h : i + 1 < p.size) (hc : p[i + 1] = 93 ∨ p[i + 1] = 0) :
    cclCopy p i bidx buf = (some (i + 1, bidx, buf), 0) := by
  rw [cclCopy_unfold h, ite_eq_left (by rcases hc with hc | hc <;> simp [hc])]

/-- `\` with no room for two more bytes: `return 0`. -/
theorem cclCopy_esc_full {p : _root_.Array Nat} {i bidx : Nat} {buf : _root_.Array Nat}
    (h : i + 1 < p.size) (hc : p[i + 1] = 92) (hb : MAXCCL - 1 ≤ bidx) :
    cclCopy p i bidx buf = (none, 0) := by
  rw [cclCopy_unfold h, ite_eq_right (by simp [hc]), ite_eq_left (by simp [hc]),
    ite_eq_left hb]

/-- `\` followed by NUL: `return 0`. -/
theorem cclCopy_esc_nul {p : _root_.Array Nat} {i bidx : Nat} {buf : _root_.Array Nat}
    (h2 : i + 2 < p.size) (hc : p[i + 1] = 92) (hb : bidx < MAXCCL - 1) (h0 : p[i + 2] = 0) :
    cclCopy p i bidx buf = (none, 0) := by
  rw [cclCopy_unfold (by omega), ite_eq_right (by simp [hc]), ite_eq_left (by simp [hc]),
    ite_eq_right (by omega), dite_eq_left h2, ite_eq_left (by simp [h0])]

/-- `\` as the last byte of the pattern (its NUL follows): `return 0`. -/
theorem cclCopy_esc_end {p : _root_.Array Nat} {i bidx : Nat} {buf : _root_.Array Nat}
    (h : i + 1 < p.size) (hc : p[i + 1] = 92) (hb : bidx < MAXCCL - 1) (he : i + 2 = p.size) :
    cclCopy p i bidx buf = (none, 0) := by
  rw [cclCopy_unfold h, ite_eq_right (by simp [hc]), ite_eq_left (by simp [hc]),
    ite_eq_right (by omega), dite_eq_right (by omega), ite_eq_left he]

/-- `\x`: both bytes are copied, and the copy goes on after them. -/
theorem cclCopy_esc {p : _root_.Array Nat} {i bidx : Nat} {buf : _root_.Array Nat}
    (h2 : i + 2 < p.size) (hc : p[i + 1] = 92) (hb : bidx < MAXCCL - 1) (h0 : p[i + 2] ≠ 0) :
    cclCopy p i bidx buf =
      cclCopy p (i + 2) (bidx + 2) ((buf.set! bidx 92).set! (bidx + 1) p[i + 2]) := by
  rw [cclCopy_unfold (by omega), ite_eq_right (by simp [hc]), ite_eq_left (by simp [hc]),
    ite_eq_right (by omega), dite_eq_left h2, ite_eq_right (by simp [h0]), hc]

/-- Another byte with the buffer full: `return 0`. -/
theorem cclCopy_full {p : _root_.Array Nat} {i bidx : Nat} {buf : _root_.Array Nat}
    (h : i + 1 < p.size) (hc0 : p[i + 1] ≠ 0) (hc92 : p[i + 1] ≠ 92) (hc93 : p[i + 1] ≠ 93)
    (hb : MAXCCL ≤ bidx) : cclCopy p i bidx buf = (none, 0) := by
  rw [cclCopy_unfold h, ite_eq_right (by simp [hc0, hc93]), ite_eq_right (by simp [hc92]),
    ite_eq_left hb]

/-- Another byte: copied, and the copy goes on. -/
theorem cclCopy_char {p : _root_.Array Nat} {i bidx : Nat} {buf : _root_.Array Nat}
    (h : i + 1 < p.size) (hc0 : p[i + 1] ≠ 0) (hc92 : p[i + 1] ≠ 92) (hc93 : p[i + 1] ≠ 93)
    (hb : bidx < MAXCCL) :
    cclCopy p i bidx buf = cclCopy p (i + 1) (bidx + 1) (buf.set! bidx p[i + 1]) := by
  rw [cclCopy_unfold h, ite_eq_right (by simp [hc0, hc93]), ite_eq_right (by simp [hc92]),
    ite_eq_right (by omega)]

/-- At the last byte of the pattern (its NUL follows): the copy ends at the NUL. -/
theorem cclCopy_last {p : _root_.Array Nat} {i bidx : Nat} {buf : _root_.Array Nat}
    (h : i + 1 = p.size) : cclCopy p i bidx buf = (some (i + 1, bidx, buf), 0) := by
  rw [cclCopy.eq_1, dite_eq_right (by omega), ite_eq_left h]

/-! ## Invariants of `re_compile`'s loop -/

/-- The state of `re_compile`'s loop before entry `j`: the two arrays keep their sizes, the
entries from `j` on are still zero, `ccl_bufidx` is in `1..40`, and every class token so far
points into `ccl_buf`. -/
def CompInv (j bidx : Nat) (re : _root_.Array Tok) (buf : _root_.Array Nat) : Prop :=
  re.size = MAXOBJ ∧ buf.size = MAXCCL ∧ (∀ k, j ≤ k → k < MAXOBJ → re[k]! = {}) ∧
    1 ≤ bidx ∧ bidx ≤ MAXCCL ∧
    (∀ k, k < j → (re[k]!.type = CHAR_CLASS ∨ re[k]!.type = INV_CHAR_CLASS) → re[k]!.ccl < MAXCCL)

theorem compInv_start : CompInv 0 1 (_root_.Array.replicate MAXOBJ {}) (_root_.Array.replicate MAXCCL 0) := by
  refine ⟨by simp, by simp, fun k _ hk => ?_, by decide, by decide, fun k hk => absurd hk (by omega)⟩
  simp [getElem!_pos, hk]

theorem some4_inj {α β γ δ : Type} {a a' : α} {b b' : β} {c c' : γ} {d d' : δ}
    (h : some (a, b, c, d) = some (a', b', c', d')) : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  injection h with h
  injection h with h1 h2
  injection h2 with h2 h3
  injection h3 with h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- One entry written: the invariant moves to `j + 1`. -/
theorem compInv_next {j bidx b' : Nat} {re re' : _root_.Array Tok} {buf buf' : _root_.Array Nat}
    (hinv : CompInv j bidx re buf) (hj : j + 1 < MAXOBJ)
    (hsize : re'.size = re.size) (hother : ∀ k, k ≠ j → re'[k]! = re[k]!)
    (hcls : (re'[j]!.type = CHAR_CLASS ∨ re'[j]!.type = INV_CHAR_CLASS) → re'[j]!.ccl < MAXCCL)
    (hb1 : 1 ≤ b') (hb2 : b' ≤ MAXCCL) (hbuf : buf'.size = MAXCCL) :
    CompInv (j + 1) b' re' buf' := by
  obtain ⟨h1, _, h3, _, _, h6⟩ := hinv
  refine ⟨by rw [hsize, h1], hbuf, fun k hk1 hk2 => ?_, hb1, hb2, fun k hk => ?_⟩
  · rw [hother k (by omega)]; exact h3 k (by omega) hk2
  · by_cases hkj : k = j
    · subst hkj; exact hcls
    · rw [hother k hkj]; exact h6 k (by omega)

theorem set_other {re : _root_.Array Tok} {j : Nat} {x : Tok} :
    ∀ k, k ≠ j → (re.set! j x)[k]! = re[k]! :=
  fun k hk => _root_.Array.getElem!_set!_ne re j k x (fun h => hk h.symm)

/-- `compStep` keeps the invariant (moving it to `j + 1`). -/
theorem compInv_step {p : _root_.Array Nat} {i j bidx : Nat} {re : _root_.Array Tok}
    {buf : _root_.Array Nat} {c i' b' : Nat} {re' : _root_.Array Tok} {buf' : _root_.Array Nat}
    (hinv : CompInv j bidx re buf) (hj : j + 1 < MAXOBJ)
    (h : (compStep p i j bidx re buf c).1 = some (i', b', re', buf')) :
    CompInv (j + 1) b' re' buf' := by
  have hj30 : j < re.size := by rw [hinv.1]; omega
  have hb := hinv.2.2.2
  -- an entry `j` of a non-class kind, written with `set!`
  have hset : ∀ (t : Nat) (x : Tok), x.type = t → t ≠ CHAR_CLASS → t ≠ INV_CHAR_CLASS →
      CompInv (j + 1) bidx (re.set! j x) buf := fun t x hx h8 h9 =>
    compInv_next hinv hj (by simp) set_other
      (by rw [_root_.Array.getElem!_set!_self _ _ _ hj30, hx]; intro hc; rcases hc with hc | hc <;>
        contradiction)
      hb.1 hb.2.1 hinv.2.1
  unfold compStep at h
  dsimp only at h
  by_cases c1 : (c == 94) = true
  · rw [ite_eq_left c1] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
    exact hset BEGIN _ rfl (by decide) (by decide)
  rw [ite_eq_right c1] at h
  by_cases c2 : (c == 36) = true
  · rw [ite_eq_left c2] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
    exact hset END _ rfl (by decide) (by decide)
  rw [ite_eq_right c2] at h
  by_cases c3 : (c == 46) = true
  · rw [ite_eq_left c3] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
    exact hset DOT _ rfl (by decide) (by decide)
  rw [ite_eq_right c3] at h
  by_cases c4 : (c == 42) = true
  · rw [ite_eq_left c4] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
    exact hset STAR _ rfl (by decide) (by decide)
  rw [ite_eq_right c4] at h
  by_cases c5 : (c == 43) = true
  · rw [ite_eq_left c5] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
    exact hset PLUS _ rfl (by decide) (by decide)
  rw [ite_eq_right c5] at h
  by_cases c6 : (c == 63) = true
  · rw [ite_eq_left c6] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
    exact hset QUESTIONMARK _ rfl (by decide) (by decide)
  rw [ite_eq_right c6] at h
  by_cases c7 : (c == 92) = true
  · rw [ite_eq_left c7] at h
    by_cases c8 : ((rd p (i + 1)).fst != 0) = true
    · rw [ite_eq_left c8] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
      split
      · exact hset DIGIT _ rfl (by decide) (by decide)
      split
      · exact hset NOT_DIGIT _ rfl (by decide) (by decide)
      split
      · exact hset ALPHA _ rfl (by decide) (by decide)
      split
      · exact hset NOT_ALPHA _ rfl (by decide) (by decide)
      split
      · exact hset WHITESPACE _ rfl (by decide) (by decide)
      split
      · exact hset NOT_WHITESPACE _ rfl (by decide) (by decide)
      · exact hset CHAR _ rfl (by decide) (by decide)
    · rw [ite_eq_right c8] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
      -- `\` at the end of the pattern: entry `j` stays zero
      exact compInv_next hinv hj rfl (fun _ _ => rfl)
        (by rw [hinv.2.2.1 j (Nat.le_refl _) (by omega)]; intro hc; rcases hc with hc | hc <;>
          cases hc)
        hb.1 hb.2.1 hinv.2.1
  rw [ite_eq_right c7] at h
  by_cases c9 : (c == 91) = true
  · rw [ite_eq_left c9] at h
    by_cases c10 : ((rd p (i + 1)).fst == 94) = true
    · rw [ite_eq_left c10] at h
      by_cases c11 : ((rd p (i + 2)).fst == 0) = true
      · rw [ite_eq_left c11] at h; cases h
      · rw [ite_eq_right c11] at h
        rcases hcc : cclCopy p (i + 1) bidx buf with ⟨_ | ⟨i'', b'', buf''⟩, u3⟩
        · rw [hcc] at h; cases h
        · rw [hcc] at h
          dsimp only at h
          have hs := cclCopy_some p _ _ _ _ _ _ _ rfl (by rw [hcc])
          by_cases c12 : b'' ≥ MAXCCL
          · rw [ite_eq_left c12] at h; cases h
          · rw [ite_eq_right c12] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
            refine compInv_next hinv hj (by simp) (fun k hk => by rw [set_other k hk, set_other k hk])
              ?_ (by omega) (by omega) (by simp [hs.2.2.2.2, hinv.2.1])
            rw [_root_.Array.getElem!_set!_self _ _ _ (by simpa using hj30)]
            intro _
            simp only
            omega
    · rw [ite_eq_right c10] at h
      rcases hcc : cclCopy p i bidx buf with ⟨_ | ⟨i'', b'', buf''⟩, u3⟩
      · rw [hcc] at h; cases h
      · rw [hcc] at h
        dsimp only at h
        have hs := cclCopy_some p _ _ _ _ _ _ _ rfl (by rw [hcc])
        by_cases c12 : b'' ≥ MAXCCL
        · rw [ite_eq_left c12] at h; cases h
        · rw [ite_eq_right c12] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
          refine compInv_next hinv hj (by simp) (fun k hk => by rw [set_other k hk, set_other k hk])
            ?_ (by omega) (by omega) (by simp [hs.2.2.2.2, hinv.2.1])
          rw [_root_.Array.getElem!_set!_self _ _ _ (by simpa using hj30)]
          intro _
          simp only
          omega
  · rw [ite_eq_right c9] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
    exact hset CHAR _ rfl (by decide) (by decide)

/-- What a compiled regex looks like: 30 objects, 40 class bytes, the last object `UNUSED`, and
every class token pointing into `ccl_buf`. -/
def CompRes (P : _root_.Array Tok) (B : _root_.Array Nat) : Prop :=
  P.size = MAXOBJ ∧ B.size = MAXCCL ∧ P[MAXOBJ - 1]!.type = UNUSED ∧
    ∀ k, k < MAXOBJ → (P[k]!.type = CHAR_CLASS ∨ P[k]!.type = INV_CHAR_CLASS) → P[k]!.ccl < MAXCCL

theorem compLoop_some (p : _root_.Array Nat) :
    ∀ (n i j bidx : Nat) (re : _root_.Array Tok) (buf : _root_.Array Nat) (ub : Nat)
      (P : _root_.Array Tok) (B : _root_.Array Nat), MAXOBJ - j = n → j < MAXOBJ →
      CompInv j bidx re buf → (compLoop p i j bidx re buf ub).1 = some (P, B) → CompRes P B := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro i j bidx re buf ub P B hn hj hinv h
  have hj30 : j < re.size := by rw [hinv.1]; exact hj
  rw [compLoop.eq_1] at h
  dsimp only at h
  split at h
  · rename_i hc
    rcases hcs : compStep p i j bidx re buf (rd p i).1 with ⟨_ | ⟨i', b', re', buf'⟩, u'⟩
    · rw [hcs] at h; cases h
    · rw [hcs] at h
      dsimp only at h
      have hinv' := compInv_step hinv hc.2 (by rw [hcs])
      split at h
      · cases h
      · exact IH _ (by omega) _ _ _ _ _ _ _ _ rfl hc.2 hinv' h
  · obtain ⟨rfl, rfl⟩ : re.set! j { re[j]! with type := UNUSED } = P ∧ buf = B := by
      injection h with h; injection h with h1 h2; exact ⟨h1, h2⟩
    obtain ⟨h1, h2, h3, _, _, h6⟩ := hinv
    refine ⟨by simp [h1], h2, ?_, fun k hk => ?_⟩
    · by_cases h29 : j = MAXOBJ - 1
      · rw [← h29, _root_.Array.getElem!_set!_self _ _ _ hj30]
      · rw [set_other _ (Ne.symm h29), h3 _ (by unfold MAXOBJ at *; omega) (by unfold MAXOBJ; omega)]
        rfl
    · by_cases hkj : k = j
      · subst hkj
        rw [_root_.Array.getElem!_set!_self _ _ _ hj30]
        intro hc; rcases hc with hc | hc <;> cases hc
      · rw [set_other _ hkj]
        by_cases hlt : k < j
        · exact h6 k hlt
        · rw [h3 k (by omega) hk]
          intro hc; rcases hc with hc | hc <;> cases hc

/-- **Every compiled regex has 30 objects, 40 class bytes, an `UNUSED` last object, and class
tokens pointing into `ccl_buf`.** -/
theorem compile_some {p : _root_.Array Nat} {P : _root_.Array Tok} {B : _root_.Array Nat}
    (h : (compile p).1 = some (P, B)) : CompRes P B :=
  compLoop_some p _ 0 0 1 _ _ 0 P B rfl (by decide) compInv_start h

/-! ## Well-formed compile output (bytes, tokens, NUL-terminated classes) -/

theorem some3_inj {α β γ : Type} {a a' : α} {b b' : β} {c c' : γ}
    (h : some (a, b, c) = some (a', b', c')) : a = a' ∧ b = b' ∧ c = c' := by
  injection h with h
  injection h with h1 h2
  injection h2 with h2 h3
  exact ⟨h1, h2, h3⟩

theorem getElem!_set!_out {α : Type} [Inhabited α] (xs : _root_.Array α) (i k : Nat) (x : α)
    (h : ¬ i < xs.size) : (xs.set! i x)[k]! = xs[k]! := by
  simp only [_root_.Array.set!_eq_setIfInBounds, _root_.Array.setIfInBounds, h, dite_false]

/-- The `[..]` copy writes only from `ccl_bufidx` on, and only pattern bytes. -/
theorem cclCopy_buf (p : _root_.Array Nat) (hp : ∀ x ∈ p.toList, x < 256) :
    ∀ (n i bidx : Nat) (buf : _root_.Array Nat) (i' b' : Nat) (buf' : _root_.Array Nat),
      p.size - i = n → (cclCopy p i bidx buf).1 = some (i', b', buf') →
      (∀ k : Nat, k < bidx → buf'[k]! = buf[k]!) ∧
        ((∀ k : Nat, buf[k]! < 256) → ∀ k : Nat, buf'[k]! < 256) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro i bidx buf i' b' buf' hn h
  have hpb : ∀ (m : Nat) (hm : m < p.size), p[m] < 256 := fun m hm => hp _ (by simp)
  rw [cclCopy.eq_1] at h
  by_cases h1 : i + 1 < p.size
  · rw [dite_eq_left h1] at h
    dsimp only at h
    split at h
    · obtain ⟨-, -, rfl⟩ := some3_inj h
      exact ⟨fun _ _ => rfl, fun hb => hb⟩
    · split at h
      · split at h
        · cases h
        · by_cases h2 : i + 2 < p.size
          · rw [dite_eq_left h2] at h
            split at h
            · cases h
            · obtain ⟨hk, hv⟩ := IH _ (by omega) _ _ _ _ _ _ rfl h
              refine ⟨fun k hkb => ?_, fun hb => hv (fun k => ?_)⟩
              · rw [hk k (by omega), _root_.Array.getElem!_set!_ne _ _ _ _ (by omega),
                  _root_.Array.getElem!_set!_ne _ _ _ _ (by omega)]
              · by_cases hk1 : k = bidx + 1
                · rw [hk1]
                  by_cases hin : bidx + 1 < (buf.set! bidx p[i + 1]).size
                  · rw [_root_.Array.getElem!_set!_self _ _ _ hin]; exact hpb _ h2
                  · rw [getElem!_set!_out _ _ _ _ hin]
                    by_cases hin2 : bidx < buf.size
                    · rw [_root_.Array.getElem!_set!_ne _ _ _ _ (by omega)]; exact hb _
                    · rw [getElem!_set!_out _ _ _ _ hin2]; exact hb _
                · rw [_root_.Array.getElem!_set!_ne _ _ _ _ (Ne.symm hk1)]
                  by_cases hk0 : k = bidx
                  · rw [hk0]
                    by_cases hin : bidx < buf.size
                    · rw [_root_.Array.getElem!_set!_self _ _ _ hin]; exact hpb _ h1
                    · rw [getElem!_set!_out _ _ _ _ hin]; exact hb _
                  · rw [_root_.Array.getElem!_set!_ne _ _ _ _ (Ne.symm hk0)]; exact hb _
          · rw [dite_eq_right h2] at h
            split at h <;> cases h
      · split at h
        · cases h
        · obtain ⟨hk, hv⟩ := IH _ (by omega) _ _ _ _ _ _ rfl h
          refine ⟨fun k hkb => ?_, fun hb => hv (fun k => ?_)⟩
          · rw [hk k (by omega), _root_.Array.getElem!_set!_ne _ _ _ _ (by omega)]
          · by_cases hk0 : k = bidx
            · rw [hk0]
              by_cases hin : bidx < buf.size
              · rw [_root_.Array.getElem!_set!_self _ _ _ hin]; exact hpb _ h1
              · rw [getElem!_set!_out _ _ _ _ hin]; exact hb _
            · rw [_root_.Array.getElem!_set!_ne _ _ _ _ (Ne.symm hk0)]; exact hb _
  · rw [dite_eq_right h1] at h
    split at h
    · obtain ⟨-, -, rfl⟩ := some3_inj h
      exact ⟨fun _ _ => rfl, fun hb => hb⟩
    · cases h

theorem rd_fst_lt {p : _root_.Array Nat} (hp : ∀ x ∈ p.toList, x < 256) (i : Nat) :
    (rd p i).1 < 256 := by
  unfold rd
  split
  · exact hp _ (by simp)
  · split <;> decide

/-- `CompInv` plus: `ccl_buf` holds bytes, every token's type and `ch` are bytes, and every class
token so far starts at an index `≥ 1` and has its NUL below `ccl_bufidx`. -/
def CompWF (j bidx : Nat) (re : _root_.Array Tok) (buf : _root_.Array Nat) : Prop :=
  CompInv j bidx re buf ∧ (∀ k : Nat, buf[k]! < 256) ∧
    (∀ k : Nat, re[k]!.type < 256 ∧ re[k]!.ch < 256) ∧
    (∀ k, k < j → (re[k]!.type = CHAR_CLASS ∨ re[k]!.type = INV_CHAR_CLASS) →
      1 ≤ re[k]!.ccl ∧ ∃ e, re[k]!.ccl ≤ e ∧ e < bidx ∧ buf[e]! = 0)

theorem compWF_start :
    CompWF 0 1 (_root_.Array.replicate MAXOBJ {}) (_root_.Array.replicate MAXCCL 0) := by
  refine ⟨compInv_start, fun k => ?_, fun k => ?_, fun k hk => absurd hk (by omega)⟩
  · by_cases hk : k < MAXCCL
    · simp [getElem!_pos, hk]
    · rw [getElem!_neg _ _ (by simpa using hk)]; decide
  · by_cases hk : k < MAXOBJ
    · simp [getElem!_pos, hk]
    · rw [getElem!_neg _ _ (by simpa using hk)]; decide

theorem compWF_next {j bidx b' : Nat} {re re' : _root_.Array Tok} {buf buf' : _root_.Array Nat}
    (hwf : CompWF j bidx re buf) (hj : j + 1 < MAXOBJ)
    (hsize : re'.size = re.size) (hother : ∀ k, k ≠ j → re'[k]! = re[k]!)
    (hcls : (re'[j]!.type = CHAR_CLASS ∨ re'[j]!.type = INV_CHAR_CLASS) →
      re'[j]!.ccl < MAXCCL ∧ 1 ≤ re'[j]!.ccl ∧ ∃ e, re'[j]!.ccl ≤ e ∧ e < b' ∧ buf'[e]! = 0)
    (htc : re'[j]!.type < 256 ∧ re'[j]!.ch < 256)
    (hb1 : 1 ≤ b') (hb2 : b' ≤ MAXCCL) (hbb : bidx ≤ b') (hbuf : buf'.size = MAXCCL)
    (hbytes : ∀ k : Nat, buf'[k]! < 256) (hkeep : ∀ k, k < bidx → buf'[k]! = buf[k]!) :
    CompWF (j + 1) b' re' buf' := by
  obtain ⟨hinv, _, htc0, hcl0⟩ := hwf
  refine ⟨compInv_next hinv hj hsize hother (fun h => (hcls h).1) hb1 hb2 hbuf, hbytes,
    fun k => ?_, fun k hk hc => ?_⟩
  · by_cases hkj : k = j
    · subst hkj; exact htc
    · rw [hother k hkj]; exact htc0 k
  · by_cases hkj : k = j
    · subst hkj; exact (hcls hc).2
    · rw [hother k hkj] at hc ⊢
      obtain ⟨h1, e, he1, he2, he3⟩ := hcl0 k (by omega) hc
      exact ⟨h1, e, he1, by omega, by rw [hkeep e he2]; exact he3⟩

/-- `compStep` keeps `CompWF` (moving it to `j + 1`), for a pattern of bytes and a byte `c`. -/
theorem compWF_step {p : _root_.Array Nat} (hp : ∀ x ∈ p.toList, x < 256) {i j bidx : Nat}
    {re : _root_.Array Tok} {buf : _root_.Array Nat} {c i' b' : Nat} {re' : _root_.Array Tok}
    {buf' : _root_.Array Nat} (hc : c < 256)
    (hwf : CompWF j bidx re buf) (hj : j + 1 < MAXOBJ)
    (h : (compStep p i j bidx re buf c).1 = some (i', b', re', buf')) :
    CompWF (j + 1) b' re' buf' := by
  have hinv := hwf.1
  have hj30 : j < re.size := by rw [hinv.1]; omega
  have hb := hinv.2.2.2
  have hch : re[j]!.ch < 256 := (hwf.2.2.1 j).2
  -- an entry `j` of a non-class kind with a byte `ch`, written with `set!`
  have hset : ∀ (t : Nat) (x : Tok), x.type = t → t < 256 → x.ch < 256 → t ≠ CHAR_CLASS →
      t ≠ INV_CHAR_CLASS → CompWF (j + 1) bidx (re.set! j x) buf := fun t x hx ht hxc h8 h9 =>
    compWF_next hwf hj (by simp) set_other
      (by rw [_root_.Array.getElem!_set!_self _ _ _ hj30, hx]; intro hc; rcases hc with hc | hc <;>
        contradiction)
      (by rw [_root_.Array.getElem!_set!_self _ _ _ hj30, hx]; exact ⟨ht, hxc⟩)
      hb.1 hb.2.1 (Nat.le_refl _) hinv.2.1 hwf.2.1 (fun _ _ => rfl)
  unfold compStep at h
  dsimp only at h
  by_cases c1 : (c == 94) = true
  · rw [ite_eq_left c1] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
    exact hset BEGIN _ rfl (by decide) hch (by decide) (by decide)
  rw [ite_eq_right c1] at h
  by_cases c2 : (c == 36) = true
  · rw [ite_eq_left c2] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
    exact hset END _ rfl (by decide) hch (by decide) (by decide)
  rw [ite_eq_right c2] at h
  by_cases c3 : (c == 46) = true
  · rw [ite_eq_left c3] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
    exact hset DOT _ rfl (by decide) hch (by decide) (by decide)
  rw [ite_eq_right c3] at h
  by_cases c4 : (c == 42) = true
  · rw [ite_eq_left c4] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
    exact hset STAR _ rfl (by decide) hch (by decide) (by decide)
  rw [ite_eq_right c4] at h
  by_cases c5 : (c == 43) = true
  · rw [ite_eq_left c5] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
    exact hset PLUS _ rfl (by decide) hch (by decide) (by decide)
  rw [ite_eq_right c5] at h
  by_cases c6 : (c == 63) = true
  · rw [ite_eq_left c6] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
    exact hset QUESTIONMARK _ rfl (by decide) hch (by decide) (by decide)
  rw [ite_eq_right c6] at h
  by_cases c7 : (c == 92) = true
  · rw [ite_eq_left c7] at h
    have hc1 := rd_fst_lt hp (i + 1)
    by_cases c8 : ((rd p (i + 1)).fst != 0) = true
    · rw [ite_eq_left c8] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
      split
      · exact hset DIGIT _ rfl (by decide) hch (by decide) (by decide)
      split
      · exact hset NOT_DIGIT _ rfl (by decide) hch (by decide) (by decide)
      split
      · exact hset ALPHA _ rfl (by decide) hch (by decide) (by decide)
      split
      · exact hset NOT_ALPHA _ rfl (by decide) hch (by decide) (by decide)
      split
      · exact hset WHITESPACE _ rfl (by decide) hch (by decide) (by decide)
      split
      · exact hset NOT_WHITESPACE _ rfl (by decide) hch (by decide) (by decide)
      · exact hset CHAR _ rfl (by decide) hc1 (by decide) (by decide)
    · rw [ite_eq_right c8] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
      exact compWF_next hwf hj rfl (fun _ _ => rfl)
        (by rw [hinv.2.2.1 j (Nat.le_refl _) (by omega)]; intro hc; rcases hc with hc | hc <;>
          cases hc)
        (hwf.2.2.1 j) hb.1 hb.2.1 (Nat.le_refl _) hinv.2.1 hwf.2.1 (fun _ _ => rfl)
  rw [ite_eq_right c7] at h
  by_cases c9 : (c == 91) = true
  · rw [ite_eq_left c9] at h
    by_cases c10 : ((rd p (i + 1)).fst == 94) = true
    · rw [ite_eq_left c10] at h
      by_cases c11 : ((rd p (i + 2)).fst == 0) = true
      · rw [ite_eq_left c11] at h; cases h
      · rw [ite_eq_right c11] at h
        rcases hcc : cclCopy p (i + 1) bidx buf with ⟨_ | ⟨i'', b'', buf''⟩, u3⟩
        · rw [hcc] at h; cases h
        · rw [hcc] at h
          dsimp only at h
          have hs := cclCopy_some p _ _ _ _ _ _ _ rfl (by rw [hcc])
          have hbuf := cclCopy_buf p hp _ _ _ _ _ _ _ rfl (by rw [hcc])
          by_cases c12 : b'' ≥ MAXCCL
          · rw [ite_eq_left c12] at h; cases h
          · rw [ite_eq_right c12] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
            have hb'' : b'' < buf''.size := by rw [hs.2.2.2.2, hinv.2.1]; omega
            refine compWF_next hwf hj (by simp) (fun k hk => by rw [set_other k hk, set_other k hk])
              ?_ ?_ (by omega) (by omega) (by omega) (by simp [hs.2.2.2.2, hinv.2.1])
              (fun k => ?_) (fun k hk => ?_)
            · rw [_root_.Array.getElem!_set!_self _ _ _ (by simpa using hj30)]
              intro _
              simp only
              refine ⟨by omega, hb.1, b'', hs.2.2.1, by omega, ?_⟩
              rw [_root_.Array.getElem!_set!_self _ _ _ hb'']
            · rw [_root_.Array.getElem!_set!_self _ _ _ (by simpa using hj30)]
              simp only
              rw [_root_.Array.getElem!_set!_self _ _ _ hj30]
              exact ⟨by simp [INV_CHAR_CLASS], hch⟩
            · by_cases hkb : k = b''
              · rw [hkb, _root_.Array.getElem!_set!_self _ _ _ hb'']; decide
              · rw [_root_.Array.getElem!_set!_ne _ _ _ _ (Ne.symm hkb)]
                exact hbuf.2 hwf.2.1 k
            · rw [_root_.Array.getElem!_set!_ne _ _ _ _ (by omega)]
              exact hbuf.1 k hk
    · rw [ite_eq_right c10] at h
      rcases hcc : cclCopy p i bidx buf with ⟨_ | ⟨i'', b'', buf''⟩, u3⟩
      · rw [hcc] at h; cases h
      · rw [hcc] at h
        dsimp only at h
        have hs := cclCopy_some p _ _ _ _ _ _ _ rfl (by rw [hcc])
        have hbuf := cclCopy_buf p hp _ _ _ _ _ _ _ rfl (by rw [hcc])
        by_cases c12 : b'' ≥ MAXCCL
        · rw [ite_eq_left c12] at h; cases h
        · rw [ite_eq_right c12] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
          have hb'' : b'' < buf''.size := by rw [hs.2.2.2.2, hinv.2.1]; omega
          refine compWF_next hwf hj (by simp) (fun k hk => by rw [set_other k hk, set_other k hk])
            ?_ ?_ (by omega) (by omega) (by omega) (by simp [hs.2.2.2.2, hinv.2.1])
            (fun k => ?_) (fun k hk => ?_)
          · rw [_root_.Array.getElem!_set!_self _ _ _ (by simpa using hj30)]
            intro _
            simp only
            refine ⟨by omega, hb.1, b'', hs.2.2.1, by omega, ?_⟩
            rw [_root_.Array.getElem!_set!_self _ _ _ hb'']
          · rw [_root_.Array.getElem!_set!_self _ _ _ (by simpa using hj30)]
            simp only
            rw [_root_.Array.getElem!_set!_self _ _ _ hj30]
            exact ⟨by simp [CHAR_CLASS], hch⟩
          · by_cases hkb : k = b''
            · rw [hkb, _root_.Array.getElem!_set!_self _ _ _ hb'']; decide
            · rw [_root_.Array.getElem!_set!_ne _ _ _ _ (Ne.symm hkb)]
              exact hbuf.2 hwf.2.1 k
          · rw [_root_.Array.getElem!_set!_ne _ _ _ _ (by omega)]
            exact hbuf.1 k hk
  · rw [ite_eq_right c9] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := some4_inj h
    exact hset CHAR _ rfl (by decide) hc (by decide) (by decide)

theorem compLoop_wf (p : _root_.Array Nat) (hp : ∀ x ∈ p.toList, x < 256) :
    ∀ (n i j bidx : Nat) (re : _root_.Array Tok) (buf : _root_.Array Nat) (ub : Nat)
      (P : _root_.Array Tok) (B : _root_.Array Nat), MAXOBJ - j = n → j < MAXOBJ →
      CompWF j bidx re buf → (compLoop p i j bidx re buf ub).1 = some (P, B) →
      P.size = MAXOBJ ∧ B.size = MAXCCL ∧ (∀ k : Nat, B[k]! < 256) ∧
        (∀ k : Nat, k < MAXOBJ → P[k]!.type < 256 ∧ P[k]!.ch < 256 ∧
          ((P[k]!.type = CHAR_CLASS ∨ P[k]!.type = INV_CHAR_CLASS) →
            1 ≤ P[k]!.ccl ∧ ∃ e, P[k]!.ccl ≤ e ∧ e < MAXCCL ∧ B[e]! = 0)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro i j bidx re buf ub P B hn hj hwf h
  have hj30 : j < re.size := by rw [hwf.1.1]; exact hj
  rw [compLoop.eq_1] at h
  dsimp only at h
  split at h
  · rename_i hc
    rcases hcs : compStep p i j bidx re buf (rd p i).1 with ⟨_ | ⟨i', b', re', buf'⟩, u'⟩
    · rw [hcs] at h; cases h
    · rw [hcs] at h
      dsimp only at h
      have hwf' := compWF_step hp (rd_fst_lt hp i) hwf hc.2 (by rw [hcs])
      split at h
      · cases h
      · exact IH _ (by omega) _ _ _ _ _ _ _ _ rfl hc.2 hwf' h
  · obtain ⟨rfl, rfl⟩ : re.set! j { re[j]! with type := UNUSED } = P ∧ buf = B := by
      injection h with h; injection h with h1 h2; exact ⟨h1, h2⟩
    obtain ⟨⟨h1, h2, h3, hb1, hb2, _⟩, hby, htc, hcl⟩ := hwf
    refine ⟨by simp [h1], h2, hby, fun k hk => ?_⟩
    by_cases hkj : k = j
    · subst hkj
      rw [_root_.Array.getElem!_set!_self _ _ _ hj30]
      refine ⟨by simp [UNUSED], (htc k).2, fun hc => ?_⟩
      simp [UNUSED, CHAR_CLASS, INV_CHAR_CLASS] at hc
    · rw [set_other _ hkj]
      refine ⟨(htc k).1, (htc k).2, fun hc => ?_⟩
      by_cases hlt : k < j
      · obtain ⟨hc1, e, he1, he2, he3⟩ := hcl k hlt hc
        exact ⟨hc1, e, he1, by omega, he3⟩
      · rw [h3 k (by omega) hk] at hc
        rcases hc with hc | hc <;> cases hc

/-- **Every compiled regex of a C-string pattern is well formed**: 30 tokens, 40 class bytes, all
bytes; every token's type and `ch` are bytes; a class token starts at an index `≥ 1` of
`ccl_buf` and is NUL-terminated inside it. -/
theorem compile_wf (p : List Nat) (hp : ∀ b ∈ p, 0 < b ∧ b < 256) (P : _root_.Array Tok)
    (B : _root_.Array Nat) (h : (compile p.toArray).1 = some (P, B)) :
    P.size = 30 ∧ B.size = 40 ∧ (∀ x ∈ B.toList, x < 256) ∧
      (∀ (i : Nat) (_hi : i < 30), P[i]!.type < 256 ∧ P[i]!.ch < 256 ∧
        ((P[i]!.type = 8 ∨ P[i]!.type = 9) →
          1 ≤ P[i]!.ccl ∧ ∃ e, P[i]!.ccl ≤ e ∧ e < 40 ∧ B[e]! = 0)) := by
  have hp' : ∀ x ∈ p.toArray.toList, x < 256 := fun x hx => (hp x (by simpa using hx)).2
  obtain ⟨h1, h2, h3, h4⟩ :=
    compLoop_wf p.toArray hp' _ 0 0 1 _ _ 0 P B rfl (by decide) compWF_start h
  refine ⟨h1, h2, fun x hx => ?_, fun i hi => h4 i hi⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have := h3 k
  rw [getElem!_pos B k (by simpa using hk)] at this
  simpa using this

end EquivLean.Demo.XLang.TinyRegex

#print axioms EquivLean.Demo.XLang.TinyRegex.compile_ub_eq_zero
#print axioms EquivLean.Demo.XLang.TinyRegex.compLoop_step
#print axioms EquivLean.Demo.XLang.TinyRegex.group_mono
#print axioms EquivLean.Demo.XLang.TinyRegex.compInv_step
#print axioms EquivLean.Demo.XLang.TinyRegex.compile_some
#print axioms EquivLean.Demo.XLang.TinyRegex.cclCopy_esc
#print axioms EquivLean.Demo.XLang.TinyRegex.compile_wf
