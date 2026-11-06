import EquivLean.Bridge.Cobol.Records

/-!
# Lemmas shared by the COBOL-side glues of the modernization proofs

A glue relates a translation's field-value model (`Modernize/<Prog>/Model.lean`) to coblean's
theorem about the COBOL run.  The pieces every glue needs:

* the outputs of a run, from its events: the lines displayed (`dispL`), the records written
  (`wrL`) and rewritten (`rwL`) per file, oldest first, and how they split over appended events;
* keyed lookups: coblean's keyed `READ` (`Sem.findKey`) finds the record the translations'
  first-match search (`List.find?`) finds (`findKey_some`, `findKey_none`);
* field values: the value a valid field holds is a number or bytes (`num_of_valid`,
  `str_of_valid`), and the numbers a zoned or packed picture holds (`holds_display`,
  `holds_dec`);
* arithmetic: COBOL's high-order truncation is `Int.tmod` (`fitDec_eq`, `fitNum_signed`).
-/

open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.GlueKit

/-! ## Outputs of a run -/

/-- The lines displayed by the events `l` (oldest first). -/
def dispL (l : List Event) : List (List UInt8) :=
  l.filterMap fun | .display bs => some bs | _ => none

/-- The records written to file `f` by the events `l`. -/
def wrL (f : Nat) (l : List Event) : List (List UInt8) :=
  l.filterMap fun | .write g bs => if g = f then some bs else none | _ => none

/-- The records rewritten in file `f` by the events `l`. -/
def rwL (f : Nat) (l : List Event) : List (List UInt8) :=
  l.filterMap fun | .rewrite g bs => if g = f then some bs else none | _ => none

theorem displays_eq (st : State) : displays st = dispL st.out.reverse := rfl
theorem writes_eq (f : Nat) (st : State) : writes f st = wrL f st.out.reverse := rfl
theorem rewrites_eq (f : Nat) (st : State) : rewrites f st = rwL f st.out.reverse := rfl

theorem dispL_append (l l' : List Event) : dispL (l ++ l') = dispL l ++ dispL l' := by
  simp [dispL, List.filterMap_append]
theorem wrL_append (f : Nat) (l l' : List Event) : wrL f (l ++ l') = wrL f l ++ wrL f l' := by
  simp [wrL, List.filterMap_append]
theorem rwL_append (f : Nat) (l l' : List Event) : rwL f (l ++ l') = rwL f l ++ rwL f l' := by
  simp [rwL, List.filterMap_append]

theorem dispL_nil : dispL [] = [] := rfl
theorem wrL_nil (f : Nat) : wrL f [] = [] := rfl
theorem rwL_nil (f : Nat) : rwL f [] = [] := rfl

theorem dispL_display (bs : List UInt8) (l : List Event) :
    dispL (.display bs :: l) = bs :: dispL l := rfl
theorem dispL_write (g : Nat) (bs : List UInt8) (l : List Event) :
    dispL (.write g bs :: l) = dispL l := rfl
theorem dispL_rewrite (g : Nat) (bs : List UInt8) (l : List Event) :
    dispL (.rewrite g bs :: l) = dispL l := rfl
theorem dispL_call (p : String) (l : List Event) : dispL (.call p :: l) = dispL l := rfl

theorem wrL_display (f : Nat) (bs : List UInt8) (l : List Event) :
    wrL f (.display bs :: l) = wrL f l := rfl
theorem wrL_rewrite (f g : Nat) (bs : List UInt8) (l : List Event) :
    wrL f (.rewrite g bs :: l) = wrL f l := rfl
theorem wrL_call (f : Nat) (p : String) (l : List Event) : wrL f (.call p :: l) = wrL f l := rfl
theorem wrL_write (f g : Nat) (bs : List UInt8) (l : List Event) :
    wrL f (.write g bs :: l) = if g = f then bs :: wrL f l else wrL f l := by
  by_cases h : g = f <;> simp [wrL, h]

theorem rwL_display (f : Nat) (bs : List UInt8) (l : List Event) :
    rwL f (.display bs :: l) = rwL f l := rfl
theorem rwL_write (f g : Nat) (bs : List UInt8) (l : List Event) :
    rwL f (.write g bs :: l) = rwL f l := rfl
theorem rwL_call (f : Nat) (p : String) (l : List Event) : rwL f (.call p :: l) = rwL f l := rfl
theorem rwL_rewrite (f g : Nat) (bs : List UInt8) (l : List Event) :
    rwL f (.rewrite g bs :: l) = if g = f then bs :: rwL f l else rwL f l := by
  by_cases h : g = f <;> simp [rwL, h]

/-! ## Keyed lookups -/

/-- A keyed lookup finds nothing when the translations' search finds nothing. -/
theorem findKey_none {α : Type} [Inhabited α] {k : KeyDecl} {v : List UInt8} {g : α → List UInt8}
    {p : α → Bool} {l : List α} (hp : ∀ x ∈ l, (Sem.keyOf k (g x) == v) = p x)
    (h : l.find? p = none) : Sem.findKey k v (l.map g) = none := by
  have := findKey_map k v g p l hp
  rw [h] at this
  cases hf : Sem.findKey k v (l.map g) with
  | none => rfl
  | some i => rw [hf] at this; cases this

/-- A keyed lookup finds the record the translations' search finds. -/
theorem findKey_some {α : Type} [Inhabited α] {k : KeyDecl} {v : List UInt8} {g : α → List UInt8}
    {p : α → Bool} {l : List α} (hp : ∀ x ∈ l, (Sem.keyOf k (g x) == v) = p x) {x : α}
    (h : l.find? p = some x) :
    ∃ i, Sem.findKey k v (l.map g) = some i ∧ i < l.length ∧ l.getD i default = x := by
  have := findKey_map k v g p l hp
  rw [h] at this
  cases hf : Sem.findKey k v (l.map g) with
  | none => rw [hf] at this; cases this
  | some i =>
    rw [hf] at this
    have hi : i < l.length := by simpa using findKey_lt' hf
    exact ⟨i, rfl, hi, Option.some.inj this⟩

theorem find?_congr {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.find?_cons, h x (List.mem_cons_self ..),
      find?_congr (fun z hz => h z (List.mem_cons_of_mem _ hz))]

theorem getD_map_lt {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) {l : List α} {i : Nat}
    (h : i < l.length) : (l.map f).getD i default = f (l.getD i default) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-! ## Field values -/

theorem num_of_valid {f : Field} {fmt : NumFmt} (hk : f.desc.kind = .num fmt) {v : FVal}
    (h : f.Valid v) : ∃ n, v = .num n ∧ f.Valid (.num n) := by
  cases v with
  | num n => exact ⟨n, rfl, h⟩
  | str bs => obtain ⟨⟨j, hj⟩, -⟩ := h; rw [hk] at hj; cases hj

theorem str_of_valid {f : Field} {j : Bool} (hk : f.desc.kind = .alnum j) {v : FVal}
    (h : f.Valid v) : ∃ bs, v = .str bs ∧ bs.length = f.desc.len := by
  cases v with
  | num n => obtain ⟨fmt, hf, -⟩ := h; rw [hk] at hf; cases hf
  | str bs => exact ⟨bs, rfl, h.2⟩

/-- A value a picture that is not full binary holds (DISPLAY, packed). -/
theorem holds_dec {f : NumFmt} (hf : f.fullBinary {} = false) {v : Int} :
    f.Holds {} v ↔ v.natAbs < 10 ^ f.digits ∧ (f.signed = false → 0 ≤ v) := by
  unfold NumFmt.Holds
  simp [hf]

/-- A DISPLAY numeric value that a picture holds. -/
theorem holds_display {f : NumFmt} (hu : f.usage = .display) {v : Int} :
    f.Holds {} v ↔ v.natAbs < 10 ^ f.digits ∧ (f.signed = false → 0 ≤ v) :=
  holds_dec (by simp [NumFmt.fullBinary, hu])

/-! ## Arithmetic: COBOL's high-order truncation -/

theorem tmod_neg_of_neg {v m : Int} (_h : v < 0) : Int.tmod v m = -Int.tmod (-v) m := by
  have := Int.neg_tmod (-v) m
  simp at this
  simp

/-- Decimal high-order truncation keeps the sign: `Int.tmod` by `10 ^ n`. -/
theorem fitDec_eq (n : Nat) (v : Int) : (Sem.fitDec n v).2 = Int.tmod v (10 ^ n) := by
  unfold Sem.fitDec truncDigits
  have e : (((10 ^ n : Nat) : Int)) = (10 : Int) ^ n := by simp
  rw [← e]
  generalize 10 ^ n = M
  split
  · rename_i h
    by_cases h0 : 0 ≤ v
    · rw [Int.tmod_eq_of_lt h0 (by omega)]
    · rw [tmod_neg_of_neg (by omega), Int.tmod_eq_of_lt (by omega) (by omega)]
      omega
  · by_cases h0 : 0 ≤ v
    · simp only [h0, ↓reduceIte, Int.tmod_eq_emod_of_nonneg h0]
    · simp only [h0, ↓reduceIte, tmod_neg_of_neg (show v < 0 by omega),
        Int.tmod_eq_emod_of_nonneg (show 0 ≤ -v by omega)]

/-- `fitNum` of a signed DISPLAY item. -/
theorem fitNum_signed {f : NumFmt} (hu : f.usage = .display) (hs : f.signed = true) (v : Int) :
    (Sem.fitNum {} f v).2 = Int.tmod v (10 ^ f.digits) := by
  have hb : f.fullBinary {} = false := by simp [NumFmt.fullBinary, hu]
  simp only [Sem.fitNum, hs, ↓reduceIte, hb, Bool.false_eq_true]
  exact fitDec_eq _ _

end EquivLean.Modernize.GlueKit
