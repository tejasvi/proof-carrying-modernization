import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Demo.XLang.TinyRegex.RustDefs

/-!
# tiny-regex-c → model, Rust side: the representation and the byte-level functions

The Rust crate (veriforch's c2rust translation, extracted by Charon + Aeneas into
`EquivLean.Demo.Gen.Aeneas.TinyRegex`) runs on a `Regex` (`objs : [RegexObj; 30]`,
`ccl_buf : [u8; 40]`) and a text slice; the model runs on a `Ctx` of `Nat` arrays.  `ctx re text`
is the model's view of them; `toI32` wraps the model's unbounded `int` (Rust's `wrapping_add`).
This file defines the representation and proves the byte-level functions equal the model's: the
accessors `at`, `obj`, `cb`, the byte classes, `matchmetachar` and `matchrange`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.XLang.TinyRegex.Rust

/-! ## The representation -/

/-- The object `obj` returns past the end of `objs`. -/
def objPast : tiny_regex.RegexObj := ⟨0#u8, 0#u8, 0#usize⟩

/-- `ccl_buf` as the model's byte array (`(ctx re text).B`). -/
def cclArr (re : tiny_regex.Regex) : _root_.Array Nat := (re.ccl_buf.val.map (fun b => b.val)).toArray

theorem ctx_B (re : tiny_regex.Regex) (text : Slice U8) : (ctx re text).B = cclArr re := rfl

/-- `objs[i]`, and `objPast` past the end (Rust's `obj`). -/
def objAt (re : tiny_regex.Regex) (i : Nat) : tiny_regex.RegexObj := re.objs.val.getD i objPast

/-- `ccl_buf[k]`, and 0 past the end (Rust's `cb`). -/
def cbyte (re : tiny_regex.Regex) (k : Nat) : U8 := re.ccl_buf.val.getD k 0#u8

/-- `text[i]`, and 0 past the end (Rust's `at`). -/
def tbyte (text : Slice U8) (i : Nat) : U8 := text.val.getD i 0#u8

theorem WF_iff (re : tiny_regex.Regex) : WF re ↔ (objAt re 29).kind.val = 0 := Iff.rfl

/-! ## Basic facts -/

theorem i32_ext {x y : I32} (h : x.bv = y.bv) : x = y := by
  cases x; cases y; cases h; rfl

theorem toI32_val (x : I32) : toI32 x.val = x := by
  apply i32_ext
  simp only [toI32, IScalar.val]
  exact BitVec.ofInt_toInt

theorem toI32_val_eq {v : Int} (h1 : INT_MIN ≤ v) (h2 : v ≤ INT_MAX) : (toI32 v).val = v := by
  simp only [toI32, IScalar.val]
  simp only [INT_MIN, INT_MAX] at h1 h2
  have := bmod_pow_numBits_eq_of_lt IScalarTy.I32 v (by simp; omega) (by simp; omega)
  simpa using this

theorem toI32_add_one (v : Int) : core.num.I32.wrapping_add (toI32 v) 1#i32 = toI32 (v + 1) := by
  apply i32_ext
  rw [core.num.I32.wrapping_add_bv_eq]
  simp only [toI32, BitVec.ofInt_add]
  rfl

theorem toI32_sub_one (v : Int) : core.num.I32.wrapping_sub (toI32 v) 1#i32 = toI32 (v - 1) := by
  apply i32_ext
  rw [core.num.I32.wrapping_sub_bv_eq]
  simp only [toI32, show v - 1 = v + -1 by omega, BitVec.ofInt_add, BitVec.ofInt_neg,
    ← BitVec.sub_eq_add_neg]
  rfl

theorem objs_length (re : tiny_regex.Regex) : re.objs.val.length = 30 := by
  simp

theorem ccl_length (re : tiny_regex.Regex) : re.ccl_buf.val.length = 40 := by
  simp

theorem cclArr_size (re : tiny_regex.Regex) : (cclArr re).size = 40 := by
  simp [cclArr]

theorem ctx_P_size (re : tiny_regex.Regex) (text : Slice U8) : (ctx re text).P.size = 30 := by
  simp [ctx]

theorem ctx_T_size (re : tiny_regex.Regex) (text : Slice U8) :
    (ctx re text).T.size = text.val.length := by
  simp [ctx]

theorem usize_max_ge : 4294967295 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max_eq, U64.max_eq]

theorem getElem_eq_getD {α : Type} (l : List α) (d : α) (n : Nat) (h : n < l.length) :
    l[n]'h = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem index_objs (re : tiny_regex.Regex) (i : Nat) (h : i < re.objs.val.length) :
    re.objs.val[i]'h = objAt re i :=
  getElem_eq_getD _ _ _ h

theorem index_ccl (re : tiny_regex.Regex) (k : Nat) (h : k < re.ccl_buf.val.length) :
    re.ccl_buf.val[k]'h = cbyte re k :=
  getElem_eq_getD _ _ _ h

theorem index_text (text : Slice U8) (i : Nat) (h : i < text.val.length) :
    text.val[i]'h = tbyte text i :=
  getElem_eq_getD _ _ _ h

theorem objAt_ge (re : tiny_regex.Regex) {i : Nat} (h : 30 ≤ i) : objAt re i = objPast :=
  List.getD_eq_default _ _ (by rw [objs_length]; exact h)

theorem cbyte_ge (re : tiny_regex.Regex) {k : Nat} (h : 40 ≤ k) : cbyte re k = 0#u8 :=
  List.getD_eq_default _ _ (by rw [ccl_length]; exact h)

theorem tbyte_ge (text : Slice U8) {i : Nat} (h : text.val.length ≤ i) : tbyte text i = 0#u8 :=
  List.getD_eq_default _ _ h

theorem ctx_P_get (re : tiny_regex.Regex) (text : Slice U8) (n : Nat)
    (h : n < (ctx re text).P.size) : (ctx re text).P[n] = tok (objAt re n) := by
  have h' : n < re.objs.val.length := by rw [ctx_P_size] at h; rw [objs_length]; exact h
  simp only [ctx, List.getElem_toArray, List.getElem_map]
  rw [index_objs re n h']

theorem cclArr_get (re : tiny_regex.Regex) (i : Nat) (h : i < (cclArr re).size) :
    (cclArr re)[i] = (cbyte re i).val := by
  have h' : i < re.ccl_buf.val.length := by rw [cclArr_size] at h; rw [ccl_length]; exact h
  simp only [cclArr, List.getElem_toArray, List.getElem_map]
  rw [index_ccl re i h']

theorem ctx_T_get (re : tiny_regex.Regex) (text : Slice U8) (i : Nat)
    (h : i < (ctx re text).T.size) : (ctx re text).T[i] = (tbyte text i).val := by
  have h' : i < text.val.length := by rw [ctx_T_size] at h; exact h
  simp only [ctx, List.getElem_toArray, List.getElem_map]
  rw [index_text text i h']

theorem bget_cclArr (re : tiny_regex.Regex) (k : Nat) :
    bget (cclArr re) k = ((cbyte re k).val, if k < 40 then 0 else ubRead) := by
  unfold bget
  by_cases h : k < 40
  · rw [dite_eq_left (by rw [cclArr_size]; exact h), cclArr_get, ite_eq_left h]
  · rw [dite_eq_right (by rw [cclArr_size]; exact h), cbyte_ge re (by omega), ite_eq_right h]
    rfl

theorem rd_eq (re : tiny_regex.Regex) (text : Slice U8) (i : Nat) :
    rd (ctx re text).T i = ((tbyte text i).val, if i ≤ text.val.length then 0 else ubRead) := by
  unfold rd
  by_cases h : i < text.val.length
  · rw [dite_eq_left (by rw [ctx_T_size]; exact h), ctx_T_get, ite_eq_left (by omega)]
  · rw [dite_eq_right (by rw [ctx_T_size]; exact h), tbyte_ge text (by omega), ctx_T_size]
    by_cases h2 : i = text.val.length
    · rw [ite_eq_left h2, ite_eq_left (by omega)]; rfl
    · rw [ite_eq_right h2, ite_eq_right (by omega)]; rfl

/-! ## The accessors -/

theorem eq_ok_of_wp {α : Type} {c : Result α} {v : α} (h : wp c (· = .ok v)) : c = Result.ok v := by
  rcases (wp_iff _ _).1 h with ⟨a, rfl, ha⟩ | ⟨e, rfl, he⟩
  · cases ha; rfl
  · cases he

theorem ex_of_forall {α : Type} {x : Result α} {g : Nat → α} (h : ∀ u, x = Result.ok (g u)) :
    ∃ R, x = Result.ok R ∧ ∀ u, g u = R :=
  ⟨g 0, h 0, fun u => by
    have h1 := (h u).symm.trans (h 0)
    have h2 : (Except.ok (g u) : Except Error α) = Except.ok (g 0) :=
      ofExcept_injective (by rw [ofExcept_ok, ofExcept_ok]; exact h1)
    injection h2⟩

/-- `Array.index_usize` in `wp` form. -/
theorem wp_Array_index_usize {α : Type} {n : Usize} (v : Std.Array α n) (i : Usize)
    (Q : Except Error α → Prop) :
    wp (Std.Array.index_usize v i) Q ↔
      if h : i.val < v.val.length then Q (.ok (v.val[i.val]'h)) else Q (.error .arrayOutOfBounds) := by
  unfold Std.Array.index_usize
  rw [Std.Array.getElem?_Usize_eq]
  by_cases h : i.val < v.val.length
  · rw [List.getElem?_eq_getElem h, dite_eq_left h]; exact wp_ok _ Q
  · rw [List.getElem?_eq_none (by omega), dite_eq_right h]; exact wp_fail _ Q

theorem at_eq (text : Slice U8) (ti : Usize) :
    tiny_regex.«at» text ti = Result.ok (tbyte text ti.val) := by
  unfold tiny_regex.«at»
  by_cases h : ti.val < text.val.length
  · have h' : ti < Slice.len text := by simpa using h
    rw [ite_eq_left h']
    apply eq_ok_of_wp
    rw [wp_Slice_index_usize, dite_eq_left h, index_text text _ h]
  · have h' : ¬ ti < Slice.len text := by simpa using h
    rw [ite_eq_right h', tbyte_ge text (by omega)]

theorem obj_eq (re : tiny_regex.Regex) (i : Usize) :
    tiny_regex.obj re i = Result.ok (objAt re i.val) := by
  unfold tiny_regex.obj
  by_cases h : i.val < 30
  · have h' : i < tiny_regex.MAX_REGEXP_OBJECTS := by
      simp only [tiny_regex.MAX_REGEXP_OBJECTS, UScalar.lt_equiv]; simpa using h
    rw [ite_eq_left h']
    apply eq_ok_of_wp
    rw [wp_Array_index_usize, dite_eq_left (by rw [objs_length]; exact h), index_objs]
  · have h' : ¬ i < tiny_regex.MAX_REGEXP_OBJECTS := by
      simp only [tiny_regex.MAX_REGEXP_OBJECTS, UScalar.lt_equiv]; simpa using h
    rw [ite_eq_right h', objAt_ge re (by omega)]
    simp only [objPast, tiny_regex.UNUSED]

theorem cb_eq (re : tiny_regex.Regex) (k : Usize) :
    tiny_regex.cb re k = Result.ok (cbyte re k.val) := by
  unfold tiny_regex.cb
  by_cases h : k.val < 40
  · have h' : k < tiny_regex.MAX_CHAR_CLASS_LEN := by
      simp only [tiny_regex.MAX_CHAR_CLASS_LEN, UScalar.lt_equiv]; simpa using h
    rw [ite_eq_left h']
    apply eq_ok_of_wp
    rw [wp_Array_index_usize, dite_eq_left (by rw [ccl_length]; exact h), index_ccl]
  · have h' : ¬ k < tiny_regex.MAX_CHAR_CLASS_LEN := by
      simp only [tiny_regex.MAX_CHAR_CLASS_LEN, UScalar.lt_equiv]; simpa using h
    rw [ite_eq_right h', cbyte_ge re (by omega)]

theorem hcast_i8_val (c : U8) : (UScalar.hcast .I8 c).val = sc c.val := by
  rw [UScalar.hcast_val_eq]
  have hc : c.val < 256 := by have h := c.hBounds; simp only [UScalarTy.U8_numBits_eq] at h; omega
  simp only [IScalarTy.I8_numBits_eq, sc, Int.bmod]
  split <;> split <;> omega

/-! ## Byte classes -/

theorem isdigit_eq (c : U8) : tiny_regex.isdigit c = Result.ok (isdigitC c.val) := by
  apply eq_ok_of_wp
  unfold tiny_regex.isdigit isdigitC
  aeneas_wp
  by_cases h1 : 48 ≤ c.val <;> simp [h1]

theorem isalpha_eq (c : U8) : tiny_regex.isalpha c = Result.ok (isalphaC c.val) := by
  apply eq_ok_of_wp
  unfold tiny_regex.isalpha isalphaC
  aeneas_wp
  by_cases h1 : 97 ≤ c.val <;> by_cases h2 : c.val ≤ 122 <;> by_cases h3 : 65 ≤ c.val <;>
    by_cases h4 : c.val ≤ 90 <;> simp [h1, h2, h3, h4]

theorem isspace_eq (c : U8) : tiny_regex.isspace c = Result.ok (isspaceC c.val) := by
  apply eq_ok_of_wp
  unfold tiny_regex.isspace isspaceC
  aeneas_wp
  by_cases h0 : c.val = 32 <;> by_cases h1 : 9 ≤ c.val <;> simp [h0, h1]

theorem matchalphanum_eq (c : U8) :
    tiny_regex.matchalphanum c = Result.ok (matchalphanum c.val) := by
  apply eq_ok_of_wp
  unfold tiny_regex.matchalphanum matchalphanum
  aeneas_wp [isalpha_eq, isdigit_eq]
  by_cases h0 : c.val = 95 <;> simp [h0]
  by_cases h1 : isalphaC c.val = true <;> simp [h1]

theorem ismetachar_eq (c : U8) : tiny_regex.ismetachar c = Result.ok (ismetachar c.val) := by
  apply eq_ok_of_wp
  unfold tiny_regex.ismetachar ismetachar
  aeneas_wp
  split_ifs <;> simp_all [Bool.beq_eq_decide_eq]

/-- The first component of the model's `matchmetachar`, on the class byte `s`. -/
def mmeta (c s : Nat) : Bool :=
  if s == 100 then isdigitC c else if s == 68 then !isdigitC c
  else if s == 119 then matchalphanum c else if s == 87 then !matchalphanum c
  else if s == 115 then isspaceC c else if s == 83 then !isspaceC c else c == s

theorem matchmetachar_pair (B : _root_.Array Nat) (c k : Nat) :
    matchmetachar B c k = (mmeta c (bget B k).1, (bget B k).2) := by
  unfold matchmetachar
  rcases bget B k with ⟨s, u⟩
  rfl

theorem u8_zero_val : (0#u8 : U8).val = 0 := rfl

theorem u8_mk_val (n : Nat) : (UScalar.mk (BitVec.ofNat 8 n) : U8).val = n % 256 := rfl

theorem matchmetachar_eq (c s : U8) :
    tiny_regex.matchmetachar c s = Result.ok (mmeta c.val s.val) := by
  unfold tiny_regex.matchmetachar
  split
  · simp [mmeta, isdigit_eq, u8_mk_val]
  · simp [mmeta, isdigit_eq, u8_mk_val]
  · simp [mmeta, matchalphanum_eq, u8_mk_val]
  · simp [mmeta, matchalphanum_eq, u8_mk_val]
  · simp [mmeta, isspace_eq, u8_mk_val]
  · simp [mmeta, isspace_eq, u8_mk_val]
  · rename_i h1 h2 h3 h4 h5 h6
    have e1 : s.val ≠ 100 := fun h => h1 (UScalar.eq_of_val_eq (by rw [h]; rfl))
    have e2 : s.val ≠ 68 := fun h => h2 (UScalar.eq_of_val_eq (by rw [h]; rfl))
    have e3 : s.val ≠ 119 := fun h => h3 (UScalar.eq_of_val_eq (by rw [h]; rfl))
    have e4 : s.val ≠ 87 := fun h => h4 (UScalar.eq_of_val_eq (by rw [h]; rfl))
    have e5 : s.val ≠ 115 := fun h => h5 (UScalar.eq_of_val_eq (by rw [h]; rfl))
    have e6 : s.val ≠ 83 := fun h => h6 (UScalar.eq_of_val_eq (by rw [h]; rfl))
    simp [mmeta, e1, e2, e3, e4, e5, e6, UScalar.eq_equiv, Bool.beq_eq_decide_eq]

/-! ## Character classes -/

theorem matchrange_eq (re : tiny_regex.Regex) (c : U8) (k : Usize) :
    tiny_regex.matchrange re c k = Result.ok (matchrange (cclArr re) c.val k.val).1 := by
  apply eq_ok_of_wp
  unfold tiny_regex.matchrange matchrange
  simp only [bget_cclArr]
  have hmax := usize_max_ge
  aeneas_wp [wp_Array_index_usize, cb_eq, tiny_regex.MAX_CHAR_CLASS_LEN, hcast_i8_val, index_ccl]
  by_cases h45 : c.val = 45
  · simp [h45]
  by_cases hk : 40 ≤ k.val
  · simp [h45, hk, cbyte_ge re hk]
  have hk' : k.val < re.ccl_buf.val.length := by rw [ccl_length]; omega
  have hk1 : k.val + 1 ≤ Usize.max := by omega
  have hk2 : k.val + 2 ≤ Usize.max := by omega
  simp only [h45, hk, hk', hk1, hk2, _root_.dite_true, _root_.ite_false, Bool.beq_eq_decide_eq,
    decide_false, Bool.false_eq_true]
  by_cases h0 : (cbyte re k.val).val = 0
  · simp [h0]
  by_cases h0' : (cbyte re k.val).val = 45
  · simp [h0']
  by_cases h1 : (cbyte re (k.val + 1)).val = 45
  · by_cases h2 : (cbyte re (k.val + 2)).val = 0
    · simp [h0, h0', h1, h2]
    · by_cases h3 : sc (cbyte re k.val).val ≤ sc c.val
      · simp [h0, h0', h1, h2, h3]
      · simp [h0, h0', h1, h2, h3]
  · simp [h0, h0', h1]

theorem matchrange_fst_ge (re : tiny_regex.Regex) (c k : Nat) (h : 40 ≤ k) :
    (matchrange (cclArr re) c k).1 = false := by
  unfold matchrange
  simp only [bget_cclArr, cbyte_ge re h]
  split <;> rfl

end EquivLean.Demo.XLang.TinyRegex.Rust
