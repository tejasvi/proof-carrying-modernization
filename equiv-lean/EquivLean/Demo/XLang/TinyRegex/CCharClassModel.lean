import EquivLean.Demo.XLang.TinyRegex.CCharClass

/-!
# tiny-regex-c → model: the model's class walk is the C walk `cclC`

`matchcharclass_cclC`: on a class string NUL-terminated inside `ccl_buf` (at index `e`), from a
start `k ≥ 1`, the model's `matchcharclass` reads nothing past the NUL (it adds no UB bit) and its
result is the C algorithm `cclC` on the bytes, for a byte `b ≠ 0` read as the `char` `sc b`.
Every read stays at or below `e`: `matchrange` reads `k + 1` only past a non-NUL `B[k]`, and
`k + 2` only past `B[k + 1] = '-'`; the escape reads `k + 1` past `'\\'`; the dash case reads
`k - 1` (`k ≥ 1`) and `k + 1` past `B[k] = '-'`.
-/

namespace EquivLean.Demo.XLang.TinyRegex.C

open EquivLean.Demo.XLang.TinyRegex (sc matchcharclass matchrange matchmetachar bget ismetachar
  isdigitC isalphaC isspaceC matchalphanum ubRead)

/-! ## Bytes -/

theorem bget_lt {B : Array Nat} {k : Nat} (h : k < B.size) : bget B k = (B[k], 0) := by
  unfold bget
  rw [dite_eq_left h]

theorem bget_fst_lt {B : Array Nat} (hB : ∀ x ∈ B.toList, x < 256) (k : Nat) :
    (bget B k).1 < 256 := by
  unfold bget
  split
  · rename_i h
    exact hB _ (by simp)
  · decide

theorem xs_getD (B : Array Nat) (j : Nat) :
    (B.toList.map fun x : Nat => (x : Int)).getD j 0 = ((bget B j).1 : Int) := by
  unfold bget
  split
  · rename_i h
    simp [List.getD_eq_getElem?_getD, h]
  · rename_i h
    have hn : B[j]? = none := Array.getElem?_eq_none (by omega)
    simp [List.getD_eq_getElem?_getD, hn]

theorem s8_sc {x : Nat} (h : x < 256) : s8 (x : Int) = sc x := by
  unfold s8 sc
  split <;> split <;> omega

theorem sc_inj {a c : Nat} (ha : a < 256) (hc : c < 256) : sc a = sc c ↔ a = c := by
  unfold sc
  constructor
  · intro h
    split at h <;> split at h <;> omega
  · intro h
    rw [h]

theorem isdigitC_digitP {b : Nat} (h : b < 256) : isdigitC b = true ↔ digitP (sc b) := by
  rw [isdigitC_iff h]; rfl

theorem isspaceC_spaceP {b : Nat} (h : b < 256) : isspaceC b = true ↔ spaceP (sc b) := by
  rw [isspaceC_iff h]; rfl

theorem matchalphanum_alnumP {b : Nat} (h : b < 256) : matchalphanum b = true ↔ alnumP (sc b) := by
  rw [matchalphanum_iff h]
  unfold alnumP alphaP digitP
  simp only [or_assoc]

theorem ismetachar_metacharP {b : Nat} (h : b < 256) : ismetachar b = true ↔ metacharP (sc b) := by
  rw [ismetachar_iff h]
  unfold metacharP
  rfl

/-! ## `matchrange`, `matchmetachar` -/

theorem bget_snd_lt {B : Array Nat} {k : Nat} (h : k < B.size) : (bget B k).2 = 0 := by
  rw [bget_lt h]

/-- A byte before the NUL at `e` is not the last one. -/
theorem lt_of_bget_ne {B : Array Nat} {k e : Nat} (hke : k ≤ e) (he : e < B.size) (he0 : B[e] = 0)
    (h : (bget B k).1 ≠ 0) : k < e := by
  rcases Nat.lt_or_ge k e with h' | h'
  · exact h'
  · exfalso
    have hk : k = e := by omega
    subst hk
    rw [bget_lt he, he0] at h
    exact h rfl

theorem matchrange_fst_iff {B : Array Nat} (hB : ∀ x ∈ B.toList, x < 256) {b : Nat} (hb : b < 256)
    (k : Nat) :
    (matchrange B b k).1 = true ↔ rangeP (sc b) (B.toList.map fun x : Nat => (x : Int)) k := by
  have h0 := bget_fst_lt hB k
  have h1 := bget_fst_lt hB (k + 1)
  have h2 := bget_fst_lt hB (k + 2)
  unfold matchrange rangeP
  simp only [xs_getD]
  rw [s8_sc h0, s8_sc h2]
  by_cases h45 : b = 45
  · subst h45
    simp [sc]
  · have hsc : sc b ≠ 45 := fun h => h45 ((sc_inj hb (by decide)).1 h)
    rw [ite_eq_right (by simp [h45])]
    by_cases hs : ((bget B k).1 == 0 || (bget B k).1 == 45) = true
    · rw [ite_eq_left hs]
      simp only [Bool.or_eq_true, beq_iff_eq] at hs
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro _ hA hB'
      rcases hs with hs | hs
      · exact absurd (by rw [hs]; rfl) hA
      · exact absurd (by rw [hs]; rfl) hB'
    · rw [ite_eq_right hs]
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hs
      by_cases hm : ((bget B (k + 1)).1 != 45) = true
      · rw [ite_eq_left hm]
        simp only [bne_iff_ne, ne_eq] at hm
        simp only [Bool.false_eq_true, false_iff, not_and]
        intro _ _ _ h3
        exact (hm (by exact_mod_cast h3)).elim
      · rw [ite_eq_right hm]
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hm
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨⟨h4, h5⟩, h6⟩
          refine ⟨hsc, by exact_mod_cast hs.1, by exact_mod_cast hs.2, by exact_mod_cast hm,
            by exact_mod_cast h4, h5, h6⟩
        · rintro ⟨_, _, _, _, h4, h5, h6⟩
          exact ⟨⟨by exact_mod_cast h4, h5⟩, h6⟩

theorem matchrange_snd {B : Array Nat} {b k e : Nat} (hke : k ≤ e) (he : e < B.size)
    (he0 : B[e] = 0) : (matchrange B b k).2 = 0 := by
  have hk : k < B.size := by omega
  unfold matchrange
  split
  · rfl
  · rw [bget_lt hk]
    dsimp only
    split
    · rfl
    · rename_i hs
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hs
      have hk1 : k < e := lt_of_bget_ne hke he he0 (by rw [bget_lt hk]; exact hs.1)
      rw [bget_lt (by omega : k + 1 < B.size)]
      dsimp only
      split
      · rfl
      · rename_i hm
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hm
        have hk2 : k + 1 < e := lt_of_bget_ne (by omega) he he0
          (by rw [bget_lt (by omega : k + 1 < B.size), hm]; decide)
        rw [bget_lt (by omega : k + 2 < B.size)]
        simp

theorem matchmetachar_fst_iff {B : Array Nat} (hB : ∀ x ∈ B.toList, x < 256) {b : Nat}
    (hb : b < 256) (k : Nat) :
    (matchmetachar B b k).1 = true ↔
      metaP (sc b) ((B.toList.map fun x : Nat => (x : Int)).getD k 0) := by
  have h0 := bget_fst_lt hB k
  unfold matchmetachar metaP
  rw [xs_getD]
  dsimp only
  generalize (bget B k).1 = s at h0 ⊢
  by_cases c1 : s = 100
  · subst c1; simp [isdigitC_digitP hb]
  by_cases c2 : s = 68
  · subst c2; simp; rw [← isdigitC_digitP hb]; cases isdigitC b <;> simp
  by_cases c3 : s = 119
  · subst c3; simp [matchalphanum_alnumP hb]
  by_cases c4 : s = 87
  · subst c4; simp; rw [← matchalphanum_alnumP hb]; cases matchalphanum b <;> simp
  by_cases c5 : s = 115
  · subst c5; simp [isspaceC_spaceP hb]
  by_cases c6 : s = 83
  · subst c6; simp; rw [← isspaceC_spaceP hb]; cases isspaceC b <;> simp
  have e1 : (s : Int) ≠ 100 := by omega
  have e2 : (s : Int) ≠ 68 := by omega
  have e3 : (s : Int) ≠ 119 := by omega
  have e4 : (s : Int) ≠ 87 := by omega
  have e5 : (s : Int) ≠ 115 := by omega
  have e6 : (s : Int) ≠ 83 := by omega
  simp only [c1, c2, c3, c4, c5, c6, e1, e2, e3, e4, e5, e6, beq_iff_eq, _root_.ite_false,
    s8_sc h0, sc_inj hb h0]

theorem matchmetachar_snd {B : Array Nat} {b k : Nat} (hk : k < B.size) :
    (matchmetachar B b k).2 = 0 := by
  unfold matchmetachar
  dsimp only
  rw [bget_snd_lt hk]

/-! ## The class walk -/

theorem esc_iff {b s : Nat} (hb : b < 256) (hs : s < 256) :
    (b == s && !ismetachar b) = true ↔ (sc b = s8 (s : Int) ∧ ¬ metacharP (sc b)) := by
  rw [s8_sc hs, sc_inj hb hs, ← ismetachar_metacharP hb]
  simp

theorem xs_length (B : Array Nat) : (B.toList.map fun x : Nat => (x : Int)).length = B.size := by
  simp

/-- **The model's class walk is the C walk**: on a class string NUL-terminated at `e` inside
`ccl_buf` (bytes `< 256`), from `k ≥ 1`, for a byte `b ≠ 0`, `matchcharclass` returns `cclC` on
the `char` `sc b` and adds no UB bit. -/
theorem matchcharclass_cclC (B : Array Nat) (hB : ∀ x ∈ B.toList, x < 256) (b : Nat) (hb0 : 0 < b)
    (hb : b < 256) (k e : Nat) (hk1 : 1 ≤ k) (hke : k ≤ e) (he : e < B.size) (he0 : B[e] = 0)
    (ub : Nat) :
    matchcharclass B b k ub = (cclC (B.toList.map fun x : Nat => (x : Int)) (sc b) k, ub) := by
  suffices H : ∀ n k ub, e - k = n → 1 ≤ k → k ≤ e →
      matchcharclass B b k ub = (cclC (B.toList.map fun x : Nat => (x : Int)) (sc b) k, ub) from
    H _ k ub rfl hk1 hke
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro k ub hn hk1 hke
  have hk : k < B.size := by omega
  have hxk : (B.toList.map fun x : Nat => (x : Int)).getD k 0 = (B[k] : Int) := by
    rw [xs_getD, bget_lt hk]
  have hBk : B[k] < 256 := hB _ (by simp)
  rw [matchcharclass.eq_1]
  rw [show matchrange B b k = ((matchrange B b k).1, 0) from
    Prod.ext rfl (matchrange_snd hke he he0)]
  dsimp only
  by_cases hr : rangeP (sc b) (B.toList.map fun x : Nat => (x : Int)) k
  · rw [ite_eq_left ((matchrange_fst_iff hB hb k).2 hr), cclC_range hr]
    simp
  rw [ite_eq_right (fun h => hr ((matchrange_fst_iff hB hb k).1 h)), bget_lt hk]
  dsimp only
  by_cases h92 : B[k] = 92
  · -- an escape `\x`
    have hke' : k < e := lt_of_bget_ne hke he he0 (by rw [bget_lt hk, h92]; decide)
    have hk1s : k + 1 < B.size := by omega
    have hBk1 : B[k + 1] < 256 := hB _ (by simp)
    have hx92 : (B.toList.map fun x : Nat => (x : Int)).getD k 0 = 92 := by rw [hxk, h92]; rfl
    have hxk1 : (B.toList.map fun x : Nat => (x : Int)).getD (k + 1) 0 = (B[k + 1] : Int) := by
      rw [xs_getD, bget_lt hk1s]
    rw [ite_eq_left (by simp [h92])]
    rw [show matchmetachar B b (k + 1) = ((matchmetachar B b (k + 1)).1, 0) from
      Prod.ext rfl (matchmetachar_snd hk1s)]
    dsimp only
    by_cases hm : metaP (sc b) ((B.toList.map fun x : Nat => (x : Int)).getD (k + 1) 0)
    · rw [ite_eq_left ((matchmetachar_fst_iff hB hb (k + 1)).2 hm), cclC_meta hr hx92 hm]
      simp
    rw [ite_eq_right (fun h => hm ((matchmetachar_fst_iff hB hb (k + 1)).1 h)), bget_lt hk1s]
    dsimp only
    by_cases hce : sc b = s8 ((B.toList.map fun x : Nat => (x : Int)).getD (k + 1) 0) ∧
        ¬ metacharP (sc b)
    · rw [cclC_esc hr hx92 hm hce.1 hce.2, ite_eq_left ((esc_iff hb hBk1).2 (by rw [← hxk1]; exact hce))]
      simp
    rw [ite_eq_right (fun h => hce (by rw [hxk1]; exact (esc_iff hb hBk1).1 h)), dite_eq_left hk1s]
    by_cases hz : B[k + 1] = 0
    · rw [ite_eq_right (by simp [hz]), cclC_esc_end hr hx92 hm hce (by rw [hxk1, hz]; rfl)]
      simp
    · have hk2 : k + 1 < e := lt_of_bget_ne (by omega) he he0 (by rw [bget_lt hk1s]; exact hz)
      rw [ite_eq_left (by simp [hz]),
        cclC_esc_next hr hx92 hm hce (by rw [xs_length]; omega) (by rw [hxk1]; exact_mod_cast hz)]
      exact (IH _ (by omega) (k + 2) _ rfl (by omega) (by omega)).trans (by simp)
  rw [ite_eq_right (by simp [h92])]
  have hx92 : (B.toList.map fun x : Nat => (x : Int)).getD k 0 ≠ 92 := by
    rw [hxk]; exact_mod_cast h92
  by_cases hcs : b = B[k]
  · -- the character itself
    have hcs' : sc b = s8 ((B.toList.map fun x : Nat => (x : Int)).getD k 0) := by
      rw [hxk, s8_sc hBk, hcs]
    rw [ite_eq_left (by simp [hcs])]
    by_cases h45 : b = 45
    · have hke' : k < e := lt_of_bget_ne hke he he0 (by rw [bget_lt hk, ← hcs]; omega)
      rw [ite_eq_left (by simp [h45]), ite_eq_right (by omega : ¬ k = 0),
        bget_lt (by omega : k - 1 < B.size)]
      dsimp only
      rw [cclC_dash hr hx92 hcs' (by rw [h45]; rfl)]
      have hxm : (B.toList.map fun x : Nat => (x : Int)).getD (k - 1) 0 = (B[k - 1] : Int) := by
        rw [xs_getD, bget_lt (by omega : k - 1 < B.size)]
      have hxk1 : (B.toList.map fun x : Nat => (x : Int)).getD (k + 1) 0 = (B[k + 1] : Int) := by
        rw [xs_getD, bget_lt (by omega : k + 1 < B.size)]
      rw [hxm, hxk1]
      by_cases hsm : B[k - 1] = 0
      · rw [ite_eq_left (by simp [hsm])]
        simp [hsm]
      · rw [ite_eq_right (by simp [hsm]), bget_lt (by omega : k + 1 < B.size)]
        simp [hsm, Bool.beq_eq_decide_eq]
    · rw [ite_eq_right (by simp [h45]), cclC_char hr hx92 hcs' (by
        intro h; exact h45 ((sc_inj hb (by decide)).1 (by rw [h]; rfl)))]
      simp
  · rw [ite_eq_right (by simp [hcs])]
    have hcs' : sc b ≠ s8 ((B.toList.map fun x : Nat => (x : Int)).getD k 0) := by
      rw [hxk, s8_sc hBk]; intro h; exact hcs ((sc_inj hb hBk).1 h)
    rw [dite_eq_left hk]
    by_cases hz : B[k] = 0
    · rw [ite_eq_right (by simp [hz]), cclC_end hr hx92 hcs' (by rw [hxk, hz]; rfl)]
      simp
    · have hke' : k < e := lt_of_bget_ne hke he he0 (by rw [bget_lt hk]; exact hz)
      rw [ite_eq_left (by simp [hz]),
        cclC_next hr hx92 hcs' (by rw [xs_length]; omega) (by rw [hxk]; exact_mod_cast hz)]
      exact (IH _ (by omega) (k + 1) _ rfl (by omega) (by omega)).trans (by simp)

end EquivLean.Demo.XLang.TinyRegex.C

#print axioms EquivLean.Demo.XLang.TinyRegex.C.matchcharclass_cclC
