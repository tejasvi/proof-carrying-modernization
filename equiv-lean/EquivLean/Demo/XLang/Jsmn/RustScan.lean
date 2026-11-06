import EquivLean.Demo.XLang.Jsmn.RustBase

/-!
# jsmn → model, Rust side: the token allocation and the backward searches

`alloc_token` (the next free token, or none when the array is full) and the two backward searches
`find_open` / `find_open_container` (from index `k - 1` down: the model's `lastOpen` /
`lastOpenCont` below `k`, `-1` for none).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas jsmn_rs

namespace EquivLean.Demo.XLang.Jsmn.Rust

/-! ## Casts -/

theorem hcast_usize_val {x : I32} (h0 : 0 ≤ x.val) : (IScalar.hcast .Usize x).val = x.val.toNat := by
  rw [IScalar.hcast_val_eq]
  have h1 := IScalar.hmax x
  simp only [IScalarTy.I32_numBits_eq] at h1
  simp only [UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> rw [Int.emod_eq_of_lt h0 (by omega)]

theorem hcast_i32_val {x : Usize} (h : x.val < 2 ^ 31) : (UScalar.hcast .I32 x).val = x.val := by
  rw [UScalar.hcast_val_eq]
  simp only [IScalarTy.I32_numBits_eq]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-! ## `alloc_token` -/

theorem alloc_token_none {p : JsmnParser} {ts : Slice JsmnTok} (h : ts.val.length ≤ p.toknext.val) :
    alloc_token p ts = .ok (none, p, ts) := by
  apply eq_ok_of_wp
  unfold alloc_token
  aeneas_wp
  simp [h]

/-- The token `alloc_token` leaves at the free index: the old type, `start = end = -1`, size 0. -/
def allocd (t : JsmnTok) : JsmnTok := ⟨t.typ, (-1)#i32, (-1)#i32, 0#i32⟩

theorem alloc_token_some {p : JsmnParser} {ts : Slice JsmnTok} (h : p.toknext.val < ts.val.length) :
    ∃ v, alloc_token p ts = .ok v ∧ v.1 = some p.toknext ∧ v.2.1.pos = p.pos ∧
      v.2.1.toknext.val = p.toknext.val + 1 ∧ v.2.1.toksuper = p.toksuper ∧
      v.2.2 = ts.set p.toknext (allocd (ts.val[p.toknext.val]'h)) := by
  have hmax := ts.property
  have h1 : p.toknext.val + 1 ≤ Usize.max := by omega
  apply exists_ok_of_wp
  unfold alloc_token
  aeneas_wp [slice_index_mut_usize_eq]
  simp only [Slice.set_val_eq, List.length_set, Nat.not_le.mpr h, h, h1, _root_.ite_false,
    _root_.dite_true]
  refine ⟨_, rfl, rfl, rfl, by simp, rfl, ?_⟩
  apply Slice.ext
  simp [Slice.set_val_eq, allocd, List.set_set]

/-! ## The backward searches -/

/-- An open token (`start != -1 && end == -1`). -/
theorem isOpen_toTok (t : JsmnTok) : isOpen (toTok t) = (t.start.val != -1 && t.end.val == -1) := rfl

/-- The model's search result as an `Int` (-1 for none). -/
def optIdx : Option Nat → Int
  | some j => j
  | none => -1

/-! ## Loops one turn at a time -/

theorem loop_cont {α β : Type} {body : α → Result (ControlFlow α β)} {x y : α}
    (h : body x = .ok (.cont y)) : loop body x = loop body y := by
  rw [loop_unfold, h]
  simp

theorem loop_done {α β : Type} {body : α → Result (ControlFlow α β)} {x : α} {b : β}
    (h : body x = .ok (.done b)) : loop body x = .ok b := by
  rw [loop_unfold, h]
  simp

/-- `i - 1` for `0 ≤ i` (no overflow). -/
def predI (i : I32) (h : 0 ≤ i.val) : I32 :=
  IScalar.ofIntCore (i.val - 1) ((IScalar.inBounds_iff _).2 (by
    have := IScalar.hmax i
    simp only [IScalarTy.I32_numBits_eq, IScalar.min_IScalarTy_I32_eq, IScalar.max_IScalarTy_I32_eq,
      I32.min_eq, I32.max_eq] at *
    omega))

theorem predI_val (i : I32) (h : 0 ≤ i.val) : (predI i h).val = i.val - 1 := by
  simp [predI]

theorem find_open_body_found (ts : Slice JsmnTok) (i : I32) :
    find_open_loop.body ts i true = .ok (.done i) := rfl

theorem find_open_body_neg (ts : Slice JsmnTok) {i : I32} (h : i.val < 0) :
    find_open_loop.body ts i false = .ok (.done i) := by
  apply eq_ok_of_wp
  unfold find_open_loop.body
  aeneas_wp
  rust_split
  all_goals try (exfalso; omega)
  all_goals simp

theorem find_open_body_nonneg (ts : Slice JsmnTok) {i : I32} (h0 : 0 ≤ i.val)
    (hl : i.val.toNat < ts.val.length) :
    find_open_loop.body ts i false =
      .ok (if isOpen (toTok (ts.val[i.val.toNat]'hl)) then .cont (i, true) else .cont (predI i h0, false)) := by
  have hcast : (IScalar.hcast .Usize i).val = i.val.toNat := hcast_usize_val h0
  have himax := IScalar.hmax i
  simp only [IScalarTy.I32_numBits_eq] at himax
  apply eq_ok_of_wp
  unfold find_open_loop.body
  aeneas_wp [hcast]
  rust_split
  all_goals try (exfalso; omega)
  all_goals simp_all [isOpen_toTok, predI]

theorem find_open_loop_eq (ts : Slice JsmnTok) (K : Nat) (hK : K ≤ ts.val.length) :
    ∀ (k : Nat) (i : I32), k ≤ K → i.val = (k : Int) - 1 →
      ∃ r, find_open_loop ts i false = .ok r ∧ r.val = optIdx (lastOpen (mtoks ts K) k) := by
  intro k
  induction k with
  | zero =>
    intro i _ hi
    refine ⟨i, ?_, by simp [hi, lastOpen, optIdx]⟩
    unfold find_open_loop
    exact loop_done (find_open_body_neg ts (by omega))
  | succ k IH =>
    intro i hk hi
    have hkl : k < ts.val.length := by omega
    have hi0 : 0 ≤ i.val := by omega
    have hkk : i.val.toNat = k := by omega
    have hl : i.val.toNat < ts.val.length := by omega
    have hget : (mtoks ts K).getD k dflt = toTok (ts.val[k]'hkl) := mtoks_getD (by omega) hK dflt
    have hb := find_open_body_nonneg ts hi0 hl
    have hgetk : ts.val[i.val.toNat]'hl = ts.val[k]'hkl := by simp [hkk]
    rw [hgetk] at hb
    by_cases ho : isOpen (toTok (ts.val[k]'hkl)) = true
    · rw [if_pos ho] at hb
      refine ⟨i, ?_, ?_⟩
      · unfold find_open_loop
        rw [loop_cont hb]
        exact loop_done (find_open_body_found ts i)
      · simp only [lastOpen, hget, ho, _root_.ite_true, optIdx]
        omega
    · rw [if_neg ho] at hb
      obtain ⟨r, hr, hrv⟩ := IH (predI i hi0) (by omega) (by rw [predI_val]; omega)
      refine ⟨r, ?_, ?_⟩
      · unfold find_open_loop at hr ⊢
        rw [loop_cont hb]
        exact hr
      · rw [hrv]
        simp only [lastOpen, hget, ho, Bool.false_eq_true, _root_.ite_false]


theorem find_open_container_body_found (ts : Slice JsmnTok) (i : I32) :
    find_open_container_loop.body ts i true = .ok (.done i) := rfl

theorem find_open_container_body_neg (ts : Slice JsmnTok) {i : I32} (h : i.val < 0) :
    find_open_container_loop.body ts i false = .ok (.done i) := by
  apply eq_ok_of_wp
  unfold find_open_container_loop.body
  aeneas_wp
  rust_split
  all_goals try (exfalso; omega)
  all_goals simp

theorem find_open_container_body_nonneg (ts : Slice JsmnTok) {i : I32} (h0 : 0 ≤ i.val)
    (hl : i.val.toNat < ts.val.length) :
    find_open_container_loop.body ts i false =
      .ok (if isCont (ts.val[i.val.toNat]'hl).typ = true ∧ isOpen (toTok (ts.val[i.val.toNat]'hl)) = true
        then .cont (i, true) else .cont (predI i h0, false)) := by
  have hcast : (IScalar.hcast .Usize i).val = i.val.toNat := hcast_usize_val h0
  have himax := IScalar.hmax i
  simp only [IScalarTy.I32_numBits_eq] at himax
  apply eq_ok_of_wp
  unfold find_open_container_loop.body
  aeneas_wp [hcast, is_container_eq]
  rust_split
  all_goals try (exfalso; omega)
  all_goals simp_all [isOpen_toTok, predI]

theorem find_open_container_loop_eq (ts : Slice JsmnTok) (K : Nat) (hK : K ≤ ts.val.length) :
    ∀ (k : Nat) (i : I32), k ≤ K → i.val = (k : Int) - 1 →
      ∃ r, find_open_container_loop ts i false = .ok r ∧
        r.val = optIdx (lastOpenCont (mtoks ts K) k) := by
  intro k
  induction k with
  | zero =>
    intro i _ hi
    refine ⟨i, ?_, by simp [hi, lastOpenCont, optIdx]⟩
    unfold find_open_container_loop
    exact loop_done (find_open_container_body_neg ts (by omega))
  | succ k IH =>
    intro i hk hi
    have hkl : k < ts.val.length := by omega
    have hi0 : 0 ≤ i.val := by omega
    have hkk : i.val.toNat = k := by omega
    have hl : i.val.toNat < ts.val.length := by omega
    have hget : (mtoks ts K).getD k dflt = toTok (ts.val[k]'hkl) := mtoks_getD (by omega) hK dflt
    have hb := find_open_container_body_nonneg ts hi0 hl
    have hgetk : ts.val[i.val.toNat]'hl = ts.val[k]'hkl := by simp [hkk]
    rw [hgetk] at hb
    have hc : (isCont (ts.val[k]'hkl).typ = true ∧ isOpen (toTok (ts.val[k]'hkl)) = true) ↔
        (((toTok (ts.val[k]'hkl)).type = ARRAY ∨ (toTok (ts.val[k]'hkl)).type = OBJECT) ∧
          isOpen (toTok (ts.val[k]'hkl)) = true) := by
      rw [isCont_iff]; rfl
    by_cases ho : isCont (ts.val[k]'hkl).typ = true ∧ isOpen (toTok (ts.val[k]'hkl)) = true
    · rw [if_pos ho] at hb
      refine ⟨i, ?_, ?_⟩
      · unfold find_open_container_loop
        rw [loop_cont hb]
        exact loop_done (find_open_container_body_found ts i)
      · simp only [lastOpenCont, hget]
        rw [if_pos (hc.1 ho)]
        simp only [optIdx]
        omega
    · rw [if_neg ho] at hb
      obtain ⟨r, hr, hrv⟩ := IH (predI i hi0) (by omega) (by rw [predI_val]; omega)
      refine ⟨r, ?_, ?_⟩
      · unfold find_open_container_loop at hr ⊢
        rw [loop_cont hb]
        exact hr
      · rw [hrv]
        simp only [lastOpenCont, hget]
        rw [if_neg (fun h => ho (hc.2 h))]

end EquivLean.Demo.XLang.Jsmn.Rust
