/-
StrictTS: rewriting lemmas for proofs about TypeScript code that builds strings.

Concrete instances evaluate by `decide` (e.g. `toJSString (F64.ofNat 42) = "42"`); for string
methods applied to longer literals `decide +kernel` avoids elaborator timeouts.
-/
import StrictTS.Str.JSStr
import StrictTS.Num.Format

namespace StrictTS
namespace JSStr

/-! ## Structure -/

theorem ext_units {a b : JSStr} (h : a.units = b.units) : a = b := by
  cases a; cases b; cases h; rfl

@[simp] theorem units_mk (l : List UInt16) : (JSStr.mk l).units = l := rfl

@[simp] theorem units_comp_mk : units ∘ JSStr.mk = id := rfl

@[simp] theorem mk_append_mk (a b : List UInt16) : JSStr.mk a ++ JSStr.mk b = JSStr.mk (a ++ b) :=
  rfl

@[simp] theorem length_mk (l : List UInt16) : (JSStr.mk l).length = l.length := rfl

@[simp] theorem length_append (a b : JSStr) : (a ++ b).length = a.length + b.length := by
  simp [length]

theorem append_assoc (a b c : JSStr) : a ++ b ++ c = a ++ (b ++ c) :=
  ext_units (by simp)

@[simp] theorem empty_append (a : JSStr) : empty ++ a = a := ext_units (by simp [empty])

@[simp] theorem append_empty (a : JSStr) : a ++ empty = a := ext_units (by simp [empty])

/-! ## `ofString` -/

@[simp] theorem units_ofString (s : String) : (ofString s).units = s.toList.flatMap encodeChar :=
  rfl

@[simp] theorem ofString_append (a b : String) : ofString (a ++ b) = ofString a ++ ofString b :=
  ext_units (by simp [String.toList_append])

@[simp] theorem ofString_empty : ofString "" = empty := ext_units (by simp [empty])

theorem length_encodeChar_of_lt {c : Char} (h : c.toNat < 0x10000) : (encodeChar c).length = 1 := by
  simp [encodeChar, h]

theorem length_flatMap_encodeChar (l : List Char) (h : ∀ c ∈ l, c.toNat < 0x10000) :
    (l.flatMap encodeChar).length = l.length := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [length_encodeChar_of_lt (h c (List.mem_cons_self ..)),
      ih fun d hd => h d (List.mem_cons_of_mem _ hd)]
    omega

/-- A string of BMP characters has one code unit per character. -/
theorem ofString_length_bmp (s : String) (h : ∀ c ∈ s.toList, c.toNat < 0x10000) :
    (ofString s).length = s.length := by
  rw [length, units_ofString, length_flatMap_encodeChar _ h, String.length_toList]

/-- For ASCII strings the JavaScript length is `String.length`. -/
theorem ofString_length_ascii (s : String) (h : ∀ c ∈ s.toList, c.toNat < 128) :
    (ofString s).length = s.length :=
  ofString_length_bmp s fun c hc => Nat.lt_trans (h c hc) (by decide)

/-! ## `slice`, `substring` on in-range indices -/

@[simp] theorem units_sub (s : JSStr) (a b : Nat) :
    (s.sub a b).units = (s.units.drop a).take (b - a) :=
  rfl

theorem relIndex_natCast {len a : Nat} (h : a ≤ len) : relIndex len a = a := by
  simp only [relIndex]
  split <;> omega

theorem relIndex_neg {len k : Nat} (h0 : 0 < k) (h : k ≤ len) :
    relIndex len (-(k : Int)) = len - k := by
  simp only [relIndex]
  split <;> omega

/-- `s.slice(a, b)` for `0 ≤ a, b ≤ s.length` is `drop a` then `take (b - a)`. -/
theorem slice_natCast (s : JSStr) {a b : Nat} (ha : a ≤ s.length) (hb : b ≤ s.length) :
    s.slice a b = ⟨(s.units.drop a).take (b - a)⟩ := by
  simp [slice, sub, relIndex_natCast ha, relIndex_natCast hb]

/-- `s.slice(-k)` for `0 < k ≤ s.length` is the suffix of length `k` (`s.slice(-0)` is `s`). -/
theorem slice_neg_length (s : JSStr) {k : Nat} (h0 : 0 < k) (hk : k ≤ s.length) :
    s.slice (-(k : Int)) s.length = ⟨s.units.drop (s.length - k)⟩ := by
  simp only [slice, sub, relIndex_neg h0 hk, relIndex_natCast (Nat.le_refl _)]
  apply ext_units
  rw [units_mk, List.take_of_length_le]
  simp [length]

/-- `s.substring(a, b)` for `a ≤ b ≤ s.length` is `drop a` then `take (b - a)`. -/
theorem substring_natCast (s : JSStr) {a b : Nat} (hab : a ≤ b) (hb : b ≤ s.length) :
    s.substring a b = ⟨(s.units.drop a).take (b - a)⟩ := by
  simp only [substring, sub, Int.toNat_natCast]
  rw [Nat.min_eq_left (Nat.le_trans hab hb), Nat.min_eq_left hb, Nat.min_eq_left hab,
    Nat.max_eq_right hab]

/-- `substring` does not depend on the order of its arguments. -/
theorem substring_comm (s : JSStr) (a b : Int) : s.substring a b = s.substring b a := by
  simp only [substring, Nat.min_comm (min a.toNat _), Nat.max_comm (min a.toNat _)]

/-- Splitting at an index and concatenating gives back the string. -/
theorem sub_append_sub (s : JSStr) (k : Nat) : s.sub 0 k ++ s.sub k s.length = s := by
  apply ext_units
  simp only [units_append, units_sub, List.drop_zero, Nat.sub_zero]
  rw [List.take_of_length_le (l := s.units.drop k) (by simp [length])]
  exact List.take_append_drop k s.units

/-! ## Searching -/

theorem findFrom_of_isPrefixOf {pat rest : List UInt16} (i : Nat)
    (h : pat.isPrefixOf rest = true) : findFrom pat rest i = some i := by
  cases rest <;> simp [findFrom, h]

/-- A string starts with each of its prefixes. -/
theorem startsWith_append (p t : JSStr) : (p ++ t).startsWith p 0 = true := by
  simp [startsWith]

/-- `(p + t).indexOf(p) = 0`. -/
theorem indexOf_append_self (p t : JSStr) : (p ++ t).indexOf p 0 = 0 := by
  simp [indexOf, indexOfNat?, findFrom_of_isPrefixOf]

theorem indexOf_self (s : JSStr) : s.indexOf s 0 = 0 := by
  simpa using indexOf_append_self s empty

theorem includes_append_self (p t : JSStr) : (p ++ t).includes p 0 = true := by
  simp [includes, indexOfNat?, findFrom_of_isPrefixOf]

/-- A string ends with each of its suffixes. -/
theorem endsWith_append (t p : JSStr) : (t ++ p).endsWith p (t ++ p).length = true := by
  simp only [endsWith, length_append, Nat.min_self, units_append]
  simp only [length, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
  rw [List.take_of_length_le (by simp), List.drop_left]
  simp

/-! ## `split` and `join` -/

theorem splitParts_ne_nil (sep : List UInt16) :
    ∀ fuel rest cur, splitParts sep fuel rest cur ≠ []
  | 0, _, _ => by simp [splitParts]
  | fuel + 1, rest, cur => by
    cases rest with
    | nil => simp [splitParts]
    | cons c t =>
      simp only [splitParts]
      split
      · simp
      · exact splitParts_ne_nil sep fuel t (cur ++ [c])

/-- Joining the parts with the separator restores the scanned text (for any fuel). -/
theorem intercalate_splitParts (sep : List UInt16) :
    ∀ fuel rest cur, List.intercalate sep (splitParts sep fuel rest cur) = cur ++ rest
  | 0, rest, cur => by simp [splitParts]
  | fuel + 1, rest, cur => by
    cases rest with
    | nil => simp [splitParts]
    | cons c t =>
      simp only [splitParts]
      split
      · rename_i h
        rw [List.intercalate_cons_of_ne_nil
            (splitParts_ne_nil sep fuel ((c :: t).drop sep.length) []),
          intercalate_splitParts sep fuel, List.nil_append, List.append_assoc]
        have hp := List.prefix_iff_eq_take.1 (List.isPrefixOf_iff_prefix.1 h)
        conv => rhs; rw [← List.take_append_drop sep.length (c :: t)]
        rw [← hp]
      · rw [intercalate_splitParts sep fuel]
        simp

theorem length_splitParts_le (sep : List UInt16) :
    ∀ fuel rest cur, (splitParts sep fuel rest cur).length ≤ fuel + 1
  | 0, _, _ => by simp [splitParts]
  | fuel + 1, rest, cur => by
    cases rest with
    | nil => simp [splitParts]
    | cons c t =>
      simp only [splitParts]
      split
      · simp only [List.length_cons]
        have := length_splitParts_le sep fuel ((c :: t).drop sep.length) []
        omega
      · have := length_splitParts_le sep fuel t (cur ++ [c])
        omega

theorem intercalate_nil_singletons (l : List UInt16) :
    List.intercalate [] (l.map fun u => [u]) = l := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    cases l with
    | nil => rfl
    | cons v l' =>
      simp only [List.map_cons] at ih ⊢
      rw [List.intercalate_cons_cons, ih]
      rfl

/-- `s.split(sep).join(sep) === s` for every separator (strings shorter than 2³² − 2). -/
theorem join_split (s sep : JSStr) (hs : s.length + 2 ≤ 2 ^ 32 - 1) :
    join sep (s.split sep none) = s := by
  apply ext_units
  unfold split
  simp only [Option.getD_none]
  rw [ite_eq_right (by decide)]
  by_cases hsep : sep.units = []
  · rw [ite_eq_left hsep]
    show List.intercalate sep.units
      (((s.units.take (2 ^ 32 - 1)).map fun u => JSStr.mk [u]).map units) = s.units
    rw [hsep, List.take_of_length_le (by simp only [length] at hs; omega), List.map_map]
    exact intercalate_nil_singletons s.units
  · rw [ite_eq_right hsep]
    by_cases hs0 : s.units = []
    · rw [ite_eq_left hs0]; simp [join]
    · rw [ite_eq_right hs0]
      have hlen := length_splitParts_le sep.units (s.length + 1) s.units []
      show List.intercalate sep.units
        ((((splitParts sep.units (s.length + 1) s.units []).take (2 ^ 32 - 1)).map
          JSStr.mk).map units) = s.units
      rw [List.take_of_length_le (by omega), List.map_map, units_comp_mk, List.map_id,
        intercalate_splitParts, List.nil_append]

theorem splitParts_of_findFrom_none (sep : List UInt16) :
    ∀ fuel rest cur i, findFrom sep rest i = none → splitParts sep fuel rest cur = [cur ++ rest]
  | 0, _, _, _, _ => by simp [splitParts]
  | fuel + 1, rest, cur, i, h => by
    cases rest with
    | nil => simp [splitParts]
    | cons c t =>
      simp only [findFrom] at h
      split at h
      · simp at h
      · rename_i hp
        simp only [splitParts, hp]
        rw [splitParts_of_findFrom_none sep fuel t (cur ++ [c]) (i + 1) h]
        simp

/-- If the non-empty `sep` does not occur in `s`, `s.split(sep)` is `[s]`. -/
theorem split_of_indexOf_eq_neg_one (s sep : JSStr) (hsep : sep.units ≠ [])
    (h : s.indexOf sep 0 = -1) : s.split sep none = [s] := by
  have hn : findFrom sep.units s.units 0 = none := by
    simp only [indexOf, indexOfNat?, Nat.min_eq_left (Nat.zero_le _), List.drop_zero] at h
    split at h
    · omega
    · assumption
  unfold split
  simp only [Option.getD_none]
  rw [ite_eq_right (by decide), ite_eq_right hsep]
  split
  · rfl
  · rw [splitParts_of_findFrom_none _ _ _ _ 0 hn]
    simp

/-! ## `split` of `join` -/

theorem isPrefixOf_append_of_le {sep X : List UInt16} (Y : List UInt16) (h : sep.length ≤ X.length) :
    sep.isPrefixOf (X ++ Y) = sep.isPrefixOf X := by
  induction sep generalizing X with
  | nil => simp
  | cons a s ih =>
    cases X with
    | nil => simp at h
    | cons b X' =>
      simp only [List.cons_append, List.isPrefixOf_cons_cons]
      rw [ih (by simp at h; omega)]

/-- More fuel than the text length does not change `splitParts` (non-empty separator). -/
theorem splitParts_fuel_succ (sep : List UInt16) (hsep : sep ≠ []) :
    ∀ fuel rest cur, rest.length < fuel →
      splitParts sep (fuel + 1) rest cur = splitParts sep fuel rest cur
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, rest, cur, h => by
    cases rest with
    | nil => rw [splitParts.eq_2, splitParts.eq_2]
    | cons c t =>
      rw [splitParts.eq_3, splitParts.eq_3]
      by_cases hp : sep.isPrefixOf (c :: t) = true
      · have hk : 0 < sep.length := List.length_pos_iff.2 hsep
        have hd : (List.drop sep.length (c :: t)).length = t.length + 1 - sep.length := by simp
        rw [ite_eq_left hp, ite_eq_left hp,
          splitParts_fuel_succ sep hsep fuel _ _ (by simp only [List.length_cons] at h; omega)]
      · rw [ite_eq_right hp, ite_eq_right hp,
          splitParts_fuel_succ sep hsep fuel _ _ (by simp only [List.length_cons] at h; omega)]

theorem splitParts_fuel_ge (sep : List UInt16) (hsep : sep ≠ []) (rest cur : List UInt16) :
    ∀ fuel, rest.length < fuel →
      splitParts sep fuel rest cur = splitParts sep (rest.length + 1) rest cur
  | 0, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, h => by
    by_cases he : rest.length = fuel
    · rw [he]
    · rw [splitParts_fuel_succ sep hsep fuel rest cur (by omega),
        splitParts_fuel_ge sep hsep rest cur fuel (by omega)]

/-- `sep` does not start inside `p` when scanning `p ++ sep`. -/
def NoEarlyMatch (sep p : List UInt16) : Prop :=
  ∀ j < p.length, sep.isPrefixOf ((p ++ sep).drop j) = false

theorem splitParts_part (sep : List UInt16) (hsep : sep ≠ []) (rest : List UInt16) :
    ∀ (p cur : List UInt16) (fuel : Nat), NoEarlyMatch sep p →
      (p ++ sep ++ rest).length < fuel →
      splitParts sep fuel (p ++ sep ++ rest) cur =
        (cur ++ p) :: splitParts sep (rest.length + 1) rest []
  | [], cur, fuel, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨a, s, rfl⟩ : ∃ a s, sep = a :: s := by
      cases sep with
      | nil => exact absurd rfl hsep
      | cons a s => exact ⟨a, s, rfl⟩
    simp only [List.nil_append, List.cons_append]
    rw [splitParts.eq_3, ite_eq_left (by simp), List.append_nil]
    congr 1
    have : List.drop (a :: s).length (a :: (s ++ rest)) = rest := by
      simp
    rw [this, splitParts_fuel_ge _ hsep _ _ f (by simp at hf; omega)]
  | c :: p', cur, fuel, hp, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have h0 := hp 0 (by simp)
    simp only [List.drop_zero] at h0
    have hle : sep.length ≤ (c :: p' ++ sep).length := by simp; omega
    rw [List.cons_append, List.cons_append, splitParts.eq_3]
    rw [show c :: (p' ++ sep ++ rest) = (c :: p' ++ sep) ++ rest by simp,
      isPrefixOf_append_of_le rest hle, h0]
    simp only [Bool.false_eq_true, ite_false]
    have hp' : NoEarlyMatch sep p' := fun j hj => by
      have := hp (j + 1) (by simp; omega)
      simpa using this
    rw [splitParts_part sep hsep rest p' (cur ++ [c]) f hp' (by simp at hf ⊢; omega)]
    simp

theorem splitParts_intercalate (sep : List UInt16) (hsep : sep ≠ []) :
    ∀ (parts : List (List UInt16)) (hne : parts ≠ []),
      (∀ p ∈ parts.dropLast, NoEarlyMatch sep p) →
      findFrom sep (parts.getLast hne) 0 = none →
      splitParts sep ((List.intercalate sep parts).length + 1) (List.intercalate sep parts) [] =
        parts
  | [p], _, _, hlast => by
    simp only [List.intercalate_singleton]
    rw [splitParts_of_findFrom_none sep _ p [] 0 hlast]
    simp
  | p :: q :: rest, _, hmid, hlast => by
    rw [List.intercalate_cons_cons,
      splitParts_part sep hsep _ p [] _ (hmid p (by simp)) (by simp), List.nil_append]
    congr 1
    exact splitParts_intercalate sep hsep (q :: rest) (by simp)
      (fun x hx => hmid x (by rw [List.dropLast_cons_cons]; exact List.mem_cons_of_mem _ hx))
      (by simpa [List.getLast_cons_cons] using hlast)

/-- `parts.join(sep).split(sep)` gives back `parts` when the non-empty `sep` starts nowhere inside
`p + sep` for each part `p` but the last, and does not occur in the last part. -/
theorem split_join (parts : List JSStr) (sep : JSStr) (hsep : sep.units ≠ []) (hne : parts ≠ [])
    (hmid : ∀ p ∈ parts.dropLast, NoEarlyMatch sep.units p.units)
    (hlast : findFrom sep.units (parts.getLast hne).units 0 = none)
    (hlen : (join sep parts).length + 2 ≤ 2 ^ 32 - 1) :
    (join sep parts).split sep none = parts := by
  have hne' : parts.map units ≠ [] := by simpa using hne
  have hmid' : ∀ p ∈ (parts.map units).dropLast, NoEarlyMatch sep.units p := by
    intro p hp
    rw [← List.map_dropLast] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact hmid q hq
  have hlast' : findFrom sep.units ((parts.map units).getLast hne') 0 = none := by
    rw [List.getLast_map]; exact hlast
  have key := splitParts_intercalate sep.units hsep _ hne' hmid' hlast'
  have hu : (join sep parts).units = List.intercalate sep.units (parts.map units) := rfl
  unfold split
  simp only [Option.getD_none]
  rw [ite_eq_right (by decide), ite_eq_right hsep]
  split
  · rename_i h0
    -- the joined text is empty only for `parts = [""]`
    match parts, hne, h0 with
    | [p], _, h0 =>
      have : p.units = [] := by simpa [hu] using h0
      exact congrArg (fun q => [q]) (ext_units (by rw [this]; exact h0))
    | p :: q :: r, _, h0 =>
      exfalso
      have : (join sep (p :: q :: r)).units =
          p.units ++ sep.units ++ List.intercalate sep.units (q.units :: r.map units) := by
        rw [hu]; simp only [List.map_cons, List.intercalate_cons_cons]
      rw [this] at h0
      simp at h0
      exact hsep h0.2.1
  · have hl := length_splitParts_le sep.units ((join sep parts).length + 1) (join sep parts).units []
    rw [List.take_of_length_le (by omega)]
    have hlen' : (join sep parts).length = (List.intercalate sep.units (parts.map units)).length := rfl
    rw [hu, ← hlen'] at *
    rw [show (join sep parts).length = (List.intercalate sep.units (parts.map units)).length from rfl,
      key, List.map_map, show (JSStr.mk ∘ units) = id from rfl, List.map_id]

theorem noEarlyMatch_single {c : UInt16} {p : List UInt16} (h : c ∉ p) : NoEarlyMatch [c] p := by
  intro j hj
  rw [List.drop_append_of_le_length (Nat.le_of_lt hj)]
  obtain ⟨x, rest, hx⟩ : ∃ x rest, p.drop j = x :: rest := by
    cases hd : p.drop j with
    | nil => simp at hd; omega
    | cons x rest => exact ⟨x, rest, rfl⟩
  have hxm : x ∈ p := List.mem_of_mem_drop (i := j) (l := p) (by rw [hx]; exact List.mem_cons_self ..)
  rw [hx, List.cons_append, List.isPrefixOf_cons_cons]
  have : (c == x) = false := by
    rw [beq_eq_false_iff_ne]; intro hcx; exact h (hcx ▸ hxm)
  simp [this]

theorem findFrom_single_none {c : UInt16} {p : List UInt16} (h : c ∉ p) (i : Nat) :
    findFrom [c] p i = none := by
  induction p generalizing i with
  | nil => simp [findFrom]
  | cons d t ih =>
    have hcd : (c == d) = false := by
      rw [beq_eq_false_iff_ne]; intro hcd; exact h (hcd ▸ List.mem_cons_self ..)
    simp only [findFrom, List.isPrefixOf_cons_cons, hcd, Bool.false_and, Bool.false_eq_true,
      ite_false]
    exact ih (fun hm => h (List.mem_cons_of_mem _ hm)) _

/-- Splitting at a one-code-unit separator that occurs in none of the parts inverts `join`. -/
theorem split_join_single (parts : List JSStr) (c : UInt16) (hne : parts ≠ [])
    (hc : ∀ p ∈ parts, c ∉ p.units) (hlen : (join ⟨[c]⟩ parts).length + 2 ≤ 2 ^ 32 - 1) :
    (join ⟨[c]⟩ parts).split ⟨[c]⟩ none = parts :=
  split_join parts ⟨[c]⟩ (by simp) hne
    (fun p hp => noEarlyMatch_single (hc p (List.dropLast_subset _ hp)))
    (findFrom_single_none (hc _ (List.getLast_mem hne)) 0) hlen

/-! ## Comparison -/

theorem compare_go_eq_lt (as bs : List UInt16) : compare.go as bs = .lt ↔ lt.go as bs = true := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [compare.go, lt.go]
  | cons a as ih =>
    cases bs with
    | nil => simp [compare.go, lt.go]
    | cons b bs =>
      simp only [compare.go, lt.go]
      split
      · simp
      · split
        · simp
        · exact ih bs

theorem compare_go_swap (as bs : List UInt16) : compare.go as bs = (compare.go bs as).swap := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [compare.go, Ordering.swap]
  | cons a as ih =>
    cases bs with
    | nil => simp [compare.go, Ordering.swap]
    | cons b bs =>
      simp only [compare.go]
      by_cases h1 : a < b
      · have h2 : ¬ b < a := fun h => absurd (UInt16.lt_trans h1 h) (UInt16.lt_irrefl _)
        simp [h1, h2, Ordering.swap]
      · by_cases h2 : b < a
        · simp [h1, h2, Ordering.swap]
        · simp only [h1, h2, ite_false]
          exact ih bs

theorem compare_go_eq_eq (as bs : List UInt16) : compare.go as bs = .eq ↔ as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [compare.go]
  | cons a as ih =>
    cases bs with
    | nil => simp [compare.go]
    | cons b bs =>
      simp only [compare.go, List.cons.injEq]
      by_cases h1 : a < b
      · simp only [h1, ite_true, reduceCtorEq, false_iff, not_and]
        intro hab; subst hab; exact absurd h1 (UInt16.lt_irrefl _)
      · by_cases h2 : b < a
        · simp only [h1, h2, ite_true, ite_false, reduceCtorEq, false_iff, not_and]
          intro hab; subst hab; exact absurd h2 (UInt16.lt_irrefl _)
        · simp only [h1, h2, ite_false]
          have hab : a = b := Decidable.byContradiction fun hne => by
            rcases UInt16.lt_or_lt_of_ne hne with h | h <;> contradiction
          subst hab
          simp [ih]

/-- `compare` agrees with `lt` (and hence with `le`, `gt`, `ge`). -/
theorem compare_eq_lt_iff (a b : JSStr) : compare a b = .lt ↔ lt a b = true :=
  compare_go_eq_lt a.units b.units

theorem compare_eq_gt_iff (a b : JSStr) : compare a b = .gt ↔ lt b a = true := by
  rw [← compare_eq_lt_iff, compare, compare, compare_go_swap]
  cases compare.go b.units a.units <;> simp [Ordering.swap]

theorem compare_eq_eq_iff (a b : JSStr) : compare a b = .eq ↔ a = b := by
  rw [compare, compare_go_eq_eq]
  exact ⟨fun h => ext_units h, fun h => h ▸ rfl⟩

/-! ## Repetition and concatenation -/

@[simp] theorem length_repeat (s : JSStr) (n : Nat) : (s.repeat n).length = n * s.length := by
  simp [JSStr.repeat, length, List.length_flatten, List.map_replicate, List.sum_replicate_nat]

theorem length_concat (s : JSStr) (args : List JSStr) :
    (s.concat args).length = s.length + (args.map length).sum := by
  induction args generalizing s with
  | nil => simp [concat]
  | cons a l ih =>
    simp only [concat, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [Nat.add_assoc]

end JSStr

namespace NumFormat

open JSStr

/-! ## Decimal digits agree with `toString` on `Nat` -/

theorem encodeChar_digitChar {d : Nat} (h : d < 10) :
    encodeChar (Nat.digitChar d) = [digitUnit d] := by
  match d, h with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide
  | 8, _ => decide
  | 9, _ => decide

theorem digitsCore_ten (fuel n : Nat) (acc : List Char) :
    digitsCore 10 fuel n (acc.flatMap encodeChar) =
      (Nat.toDigitsCore 10 fuel n acc).flatMap encodeChar := by
  induction fuel generalizing n acc with
  | zero => rfl
  | succ fuel ih =>
    have hc : (Nat.digitChar (n % 10) :: acc).flatMap encodeChar =
        digitUnit (n % 10) :: acc.flatMap encodeChar := by
      rw [List.flatMap_cons, encodeChar_digitChar (Nat.mod_lt _ (by decide))]
      rfl
    simp only [digitsCore, Nat.toDigitsCore]
    split
    · exact hc.symm
    · rw [← hc, ih]

theorem natDigits_ten (n : Nat) : natDigits 10 n = (Nat.toDigits 10 n).flatMap encodeChar := by
  simpa [natDigits, Nat.toDigits] using digitsCore_ten (n + 1) n []

/-- `String(n)` for a natural number, as code units. -/
theorem ofString_toString_nat (n : Nat) : ofString (toString n) = ⟨natDigits 10 n⟩ := by
  apply ext_units
  show (String.ofList (Nat.toDigits 10 n)).toList.flatMap encodeChar = natDigits 10 n
  rw [String.toList_ofList, natDigits_ten]

theorem ofString_minus : ofString "-" = ⟨[45]⟩ := by decide

/-- `String(i)` for an integer, as code units. -/
theorem ofString_toString_int (i : Int) :
    ofString (toString i) = ⟨(if i < 0 then [45] else []) ++ natDigits 10 i.natAbs⟩ := by
  cases i with
  | ofNat m =>
    show ofString (Nat.repr m) = _
    rw [ite_eq_right (by simp only [Int.ofNat_eq_natCast]; omega)]
    exact ofString_toString_nat m
  | negSucc m =>
    show ofString ("-" ++ Nat.repr (m + 1)) = _
    rw [ite_eq_left (Int.negSucc_lt_zero m), ofString_append, ofString_minus]
    exact congrArg (JSStr.mk [45] ++ ·) (ofString_toString_nat (m + 1))

/-- BigInt `toString` is `toString` on `Int`. -/
theorem bigintToJSString_eq (i : Int) : bigintToJSString i = ofString (toString i) := by
  rw [ofString_toString_int]
  rfl

@[simp] theorem boolToJSString_true : boolToJSString true = "true" := rfl

@[simp] theorem boolToJSString_false : boolToJSString false = "false" := rfl

/-! ## `String(n)` for safe integers -/

theorem mkFin_valid {neg : Bool} {man : Nat} {exp : Int}
    (h : (2 ^ 52 ≤ man ∧ man < 2 ^ 53 ∧ -1074 ≤ exp ∧ exp ≤ 971) ∨ (man < 2 ^ 52 ∧ exp = -1074)) :
    F64.mkFin neg man exp = .fin ⟨neg, man, exp, h⟩ := by
  unfold F64.mkFin
  rw [dite_eq_left h]

/-- Rounding a natural number `0 < n < 2^53` is exact: significand `n * 2^(52 - log₂ n)`. -/
theorem round_nat_exact (neg : Bool) {n : Nat} (h0 : n ≠ 0) (h : n < 2 ^ 53) :
    F64.round neg n 0 = F64.mkFin neg (n * 2 ^ (52 - n.log2)) ((n.log2 : Int) - 52) := by
  have hL : n.log2 < 53 := (Nat.log2_lt h0).2 h
  have hb : F64.bitLen n = n.log2 + 1 := by simp [F64.bitLen, h0]
  have hq : max ((0 : Int) + ((n.log2 + 1 : Nat) : Int) - 1 - 52) (-1074) =
      (n.log2 : Int) - 52 := by
    omega
  have he : (0 - ((n.log2 : Int) - 52)).toNat = 52 - n.log2 := by omega
  unfold F64.round
  simp only [h0, false_and, ite_false, hb, hq]
  rw [ite_eq_left (by omega), ite_eq_right (by omega), he]

theorem intValue_exact {n : Nat} (hL : n.log2 < 53) :
    intValue? (n * 2 ^ (52 - n.log2)) ((n.log2 : Int) - 52) = some n := by
  unfold intValue?
  by_cases h52 : n.log2 = 52
  · rw [ite_eq_left (by omega)]
    have : ((n.log2 : Int) - 52).toNat = 0 := by omega
    rw [this, h52]; simp
  · rw [ite_eq_right (by omega)]
    have : (-((n.log2 : Int) - 52)).toNat = 52 - n.log2 := by omega
    rw [this, Nat.mul_mod_left, ite_eq_left rfl, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- `toJSString` of a rounded natural number below `2^53` prints its exact digits. -/
theorem toJSString_round_nat (neg : Bool) {n : Nat} (h : n < 2 ^ 53) :
    toJSString (F64.round neg n 0) = ⟨(if neg && n != 0 then [45] else []) ++ natDigits 10 n⟩ := by
  by_cases h0 : n = 0
  · subst h0
    have hz : F64.round neg 0 0 = F64.mkFin neg 0 (-1074) := by simp [F64.round]
    rw [hz, mkFin_valid (Or.inr ⟨by decide, rfl⟩)]
    simp only [toJSString, ite_true]
    cases neg <;> decide
  · have hL : n.log2 < 53 := (Nat.log2_lt h0).2 h
    have hlo : 2 ^ n.log2 ≤ n := Nat.log2_self_le h0
    have hhi : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
    have hman_lo : 2 ^ 52 ≤ n * 2 ^ (52 - n.log2) :=
      calc 2 ^ 52 = 2 ^ n.log2 * 2 ^ (52 - n.log2) := by rw [← Nat.pow_add]; congr 1; omega
        _ ≤ n * 2 ^ (52 - n.log2) := Nat.mul_le_mul_right _ hlo
    have hman_hi : n * 2 ^ (52 - n.log2) < 2 ^ 53 :=
      calc n * 2 ^ (52 - n.log2) < 2 ^ (n.log2 + 1) * 2 ^ (52 - n.log2) :=
            Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
        _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega
    have hne : n * 2 ^ (52 - n.log2) ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hman_lo)
    rw [round_nat_exact neg h0 h, mkFin_valid (Or.inl ⟨hman_lo, hman_hi, by omega, by omega⟩)]
    simp only [toJSString, magString, intValue_exact hL, hne, ite_false, h, ite_true]
    simp [h0]

/-- `String(n)` for a natural number below `2^53` (`Number.isSafeInteger`). The bound is needed:
`F64.ofNat (2^53 + 1)` rounds to `2^53`, and `String(2**60)` is `"1152921504606847000"`. -/
@[simp] theorem toJSString_ofNat (n : Nat) (h : n < 2 ^ 53) :
    toJSString (F64.ofNat n) = ofString (toString n) := by
  rw [ofString_toString_nat]
  show toJSString (F64.round false n 0) = _
  rw [toJSString_round_nat false h]
  simp

/-- `String(i)` for an integer with `|i| < 2^53` (negative integers print with `-`). -/
@[simp] theorem toJSString_ofInt (i : Int) (h : i.natAbs < 2 ^ 53) :
    toJSString (F64.ofInt i) = ofString (toString i) := by
  rw [ofString_toString_int]
  show toJSString (F64.round (decide (i < 0)) i.natAbs 0) = _
  rw [toJSString_round_nat _ h]
  by_cases hi : i < 0
  · have hn : i.natAbs ≠ 0 := by omega
    simp [hi, hn]
  · simp [hi]

/-- The negative-integer case: `String(-n)` is `"-" + String(n)` for `0 < n < 2^53`. -/
theorem toJSString_ofInt_neg (n : Nat) (h0 : 0 < n) (h : n < 2 ^ 53) :
    toJSString (F64.ofInt (-(n : Int))) = ofString ("-" ++ toString n) := by
  rw [toJSString_ofInt _ (by omega), ofString_toString_int, ofString_append, ofString_minus,
    ofString_toString_nat, ite_eq_left (by omega)]
  simp

example : toJSString (F64.ofNat 42) = "42" := by decide
example : toJSString (F64.ofInt (-7)) = "-7" := by decide
example : toJSString (F64.ofNat 0) = "0" := by decide
example : toJSString (F64.ofNat 1000000) = "1000000" := by decide

end NumFormat
end StrictTS
