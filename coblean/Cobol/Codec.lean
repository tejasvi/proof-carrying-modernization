/-
# Storage encodings of numeric items

Zoned decimal (`DISPLAY`), packed decimal (`COMP-3`) and binary (`COMP`, `COMP-5`)
encoders and decoders, with the round-trip theorems

* `decodeNum c f (encodeNum c f v) = some v` whenever `f.Holds c v`,
* `decodeNum c f bs = some v → f.Holds c v` (decoded values are in range),
* `(encodeNum c f v).length = f.byteLen c`.

Decoders are strict: any byte pattern that is not a valid encoding (bad digit, bad sign,
non-zero pad nibble, binary value beyond the `PICTURE` under `TRUNC(STD)`) decodes to
`none`.  The semantics turns `none` into `unsupported`: the IR does not claim to know what
IBM hardware does with invalid data (S0C7 or garbage, depending on the generated code).
-/
import Cobol.Data
import Cobol.Digits
import Cobol.Round

namespace Cobol
open Digits

/-! ## Helpers -/

/-- Split off the last element. -/
def splitLast {α : Type _} : List α → Option (List α × α)
  | [] => none
  | [a] => some ([], a)
  | a :: b :: rest => (splitLast (b :: rest)).map (fun p => (a :: p.1, p.2))

theorem splitLast_append_singleton {α : Type _} (l : List α) (x : α) :
    splitLast (l ++ [x]) = some (l, x) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => simp only [List.cons_append] at ih ⊢; simp [splitLast, ih]

theorem splitLast_eq_some {α : Type _} {l : List α} {init : List α} {x : α}
    (h : splitLast l = some (init, x)) : l = init ++ [x] := by
  induction l generalizing init with
  | nil => simp [splitLast] at h
  | cons a l ih =>
    cases l with
    | nil => simp [splitLast] at h; obtain ⟨rfl, rfl⟩ := h; rfl
    | cons b l =>
      simp only [splitLast, Option.map_eq_some_iff] at h
      obtain ⟨⟨i, y⟩, h1, h2⟩ := h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      rw [ih h1]; rfl

/-- Attach a sign to a magnitude. -/
def applySign (neg : Bool) (v : Nat) : Int := if neg then -(v : Int) else (v : Int)

@[simp] theorem applySign_false (v : Nat) : applySign false v = v := rfl

theorem applySign_natAbs (v : Int) : applySign (decide (v < 0)) v.natAbs = v := by
  unfold applySign; split <;> rename_i h <;> simp at h <;> omega

theorem mapM_some_of_forall {α β : Type _} (f : α → Option β) (g : β → α) (l : List β)
    (h : ∀ x ∈ l, f (g x) = some x) : (l.map g).mapM f = some l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.mapM_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    rfl

theorem mapM_forall {α β : Type _} (f : α → Option β) (P : β → Prop)
    (hf : ∀ a b, f a = some b → P b) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → ∀ x ∈ r, P x := by
  intro l
  induction l with
  | nil => intro r h; simp at h; subst h; simp
  | cons a l ih =>
    intro r h
    simp only [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hm : l.mapM f with
      | none => simp [hfa, hm] at h
      | some r' =>
        simp [hfa, hm] at h; subst h
        intro x hx
        simp at hx
        rcases hx with rfl | hx
        · exact hf _ _ hfa
        · exact ih r' hm x hx

theorem mapM_length {α β : Type _} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → r.length = l.length := by
  intro l
  induction l with
  | nil => intro r h; simp at h; subst h; rfl
  | cons a l ih =>
    intro r h
    simp only [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hm : l.mapM f with
      | none => simp [hfa, hm] at h
      | some r' => simp [hfa, hm] at h; subst h; simp [ih r' hm]

/-! ## Byte-level facts about the zoned-decimal character functions -/

namespace Config

theorem decDigit_digitByte (c : Config) {d : Nat} (hd : d < 10) :
    c.decDigit (c.digitByte d) = some d := by
  unfold decDigit digitByte
  cases c.charset <;> simp [UInt8.toNat_ofNat'] <;> omega

theorem decDigit_lt (c : Config) {b : UInt8} {d : Nat} (h : c.decDigit b = some d) : d < 10 := by
  unfold decDigit at h
  cases hc : c.charset <;> simp only [hc] at h <;> split at h <;> simp at h <;> omega

theorem decSign_signByte (c : Config) (neg : Bool) {d : Nat} (hd : d < 10) :
    c.decSign (c.signByte neg d) = some (neg, d) := by
  unfold decSign signByte
  cases c.zonedSign <;> cases neg <;> simp [UInt8.toNat_ofNat']
  all_goals (first | omega | (split <;> simp_all <;> omega) | skip)
  all_goals (repeat' split) <;> simp_all <;> omega

theorem decSign_lt (c : Config) {b : UInt8} {neg : Bool} {d : Nat}
    (h : c.decSign b = some (neg, d)) : d < 10 := by
  unfold decSign at h
  have := b.toNat_lt
  cases c.zonedSign <;> simp only at h <;> (repeat' split at h) <;> simp_all <;> omega

theorem decUnsLast_digitByte (c : Config) {d : Nat} (hd : d < 10) :
    c.decUnsLast (c.digitByte d) = some d := by
  simp [decUnsLast, c.decDigit_digitByte hd]

theorem decUnsLast_lt (c : Config) {b : UInt8} {d : Nat} (h : c.decUnsLast b = some d) :
    d < 10 := by
  unfold decUnsLast at h
  cases hd : c.decDigit b with
  | some d' => simp [hd] at h; subst h; exact c.decDigit_lt hd
  | none => simp only [hd] at h; split at h <;> simp at h; omega

theorem plusChar_ne_minusChar (c : Config) : c.plusChar ≠ c.minusChar := by
  unfold plusChar minusChar chr; cases c.charset <;> decide

theorem decSepSign_sepSignByte (c : Config) (neg : Bool) :
    c.decSepSign (c.sepSignByte neg) = some neg := by
  unfold decSepSign sepSignByte
  have := c.plusChar_ne_minusChar
  cases neg <;> simp [Ne.symm this]

theorem decPackedSign_nibble (c : Config) (signed neg : Bool) :
    c.decPackedSign signed (packedSignNibble signed neg) = some (signed && neg) := by
  unfold decPackedSign packedSignNibble
  cases signed <;> cases neg <;> simp

end Config

/-! ## Zoned decimal (`DISPLAY`) -/

/-- Value of a list of digit bytes (non-sign positions). -/
def digitsVal (c : Config) (ds : List UInt8) : Option Nat :=
  (ds.mapM c.decDigit).map (ofDigits 10)

/-- Encode `v` (assumed `|v| < 10^digits`) as a zoned-decimal item. -/
def encZoned (c : Config) (f : NumFmt) (v : Int) : List UInt8 :=
  let a := v.natAbs
  let neg := decide (v < 0)
  if f.signed then
    if f.signSep then
      if f.signLead then c.sepSignByte neg :: (toDigits 10 f.digits a).map c.digitByte
      else (toDigits 10 f.digits a).map c.digitByte ++ [c.sepSignByte neg]
    else if f.signLead then
      c.signByte neg (a / 10 ^ (f.digits - 1) % 10) :: (toDigits 10 (f.digits - 1) a).map c.digitByte
    else
      (toDigits 10 (f.digits - 1) (a / 10)).map c.digitByte ++ [c.signByte neg (a % 10)]
  else
    (toDigits 10 (f.digits - 1) (a / 10)).map c.digitByte ++ [c.digitByte (a % 10)]

/-- Sign and magnitude of a zoned-decimal item, before the range check. -/
def zonedParts (c : Config) (f : NumFmt) (bs : List UInt8) : Option (Bool × Nat) :=
  if f.signed then
    if f.signSep then
      if f.signLead then
        match bs with
        | s :: ds =>
          if ds.length = f.digits then
            match c.decSepSign s, digitsVal c ds with
            | some neg, some w => some (neg, w)
            | _, _ => none
          else none
        | [] => none
      else
        match splitLast bs with
        | some (ds, s) =>
          if ds.length = f.digits then
            match c.decSepSign s, digitsVal c ds with
            | some neg, some w => some (neg, w)
            | _, _ => none
          else none
        | none => none
    else if f.signLead then
      match bs with
      | s :: ds =>
        if ds.length + 1 = f.digits then
          match c.decSign s, digitsVal c ds with
          | some (neg, d), some w => some (neg, d * 10 ^ (f.digits - 1) + w)
          | _, _ => none
        else none
      | [] => none
    else
      match splitLast bs with
      | some (ds, s) =>
        if ds.length + 1 = f.digits then
          match c.decSign s, digitsVal c ds with
          | some (neg, d), some w => some (neg, w * 10 + d)
          | _, _ => none
        else none
      | none => none
  else
    match splitLast bs with
    | some (ds, s) =>
      if ds.length + 1 = f.digits then
        match c.decUnsLast s, digitsVal c ds with
        | some d, some w => some (false, w * 10 + d)
        | _, _ => none
      else none
    | none => none

/-- Decode a zoned-decimal item; `none` on invalid data or wrong length.  The final range
check is redundant for well-formed input but makes the bound lemma immediate. -/
def decZoned (c : Config) (f : NumFmt) (bs : List UInt8) : Option Int :=
  match zonedParts c f bs with
  | some (neg, w) => if w < 10 ^ f.digits ∧ (f.signed || !neg) then some (applySign neg w) else none
  | none => none

theorem digitsVal_toDigits (c : Config) (n a : Nat) :
    digitsVal c ((toDigits 10 n a).map c.digitByte) = some (a % 10 ^ n) := by
  unfold digitsVal
  rw [mapM_some_of_forall c.decDigit c.digitByte _
    (fun x hx => c.decDigit_digitByte (toDigits_lt (by decide) n a x hx))]
  simp [ofDigits_toDigits]

theorem digitsVal_lt (c : Config) {ds : List UInt8} {v : Nat} (h : digitsVal c ds = some v) :
    v < 10 ^ ds.length := by
  unfold digitsVal at h
  cases hm : ds.mapM c.decDigit with
  | none => simp [hm] at h
  | some r =>
    simp [hm] at h; subst h
    have hl := mapM_length _ _ _ hm
    rw [← hl]
    exact ofDigits_lt (by decide) r (mapM_forall _ (· < 10) (fun _ _ h => c.decDigit_lt h) _ _ hm)

theorem length_encZoned (c : Config) (f : NumFmt) (v : Int) (hd : 0 < f.digits) :
    (encZoned c f v).length = f.digits + (if f.signed && f.signSep then 1 else 0) := by
  unfold encZoned
  cases f.signed <;> cases f.signSep <;> cases f.signLead <;> simp <;> omega

theorem zonedParts_encZoned (c : Config) (f : NumFmt) (v : Int) (hd : 0 < f.digits)
    (hv : v.natAbs < 10 ^ f.digits) :
    zonedParts c f (encZoned c f v) = some (f.signed && decide (v < 0), v.natAbs) := by
  have hpow : 10 ^ f.digits = 10 * 10 ^ (f.digits - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hdiv : v.natAbs / 10 < 10 ^ (f.digits - 1) := Nat.div_lt_of_lt_mul (by omega)
  have hlt : v.natAbs / 10 ^ (f.digits - 1) < 10 := Nat.div_lt_of_lt_mul (by
    rw [Nat.mul_comm]; omega)
  have h10 : v.natAbs % 10 < 10 := Nat.mod_lt _ (by decide)
  have e1 : v.natAbs / 10 * 10 + v.natAbs % 10 = v.natAbs := by omega
  have e2 : v.natAbs / 10 ^ (f.digits - 1) * 10 ^ (f.digits - 1) +
      v.natAbs % 10 ^ (f.digits - 1) = v.natAbs := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  unfold encZoned zonedParts
  cases hsg : f.signed <;> cases hsep : f.signSep <;> cases hld : f.signLead <;>
    simp only [Bool.false_eq_true, ↓reduceIte, splitLast_append_singleton, List.length_map,
      length_toDigits, digitsVal_toDigits, c.decSepSign_sepSignByte,
      c.decSign_signByte _ h10, c.decSign_signByte _ hlt, c.decUnsLast_digitByte h10,
      Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hlt,
      show f.digits - 1 + 1 = f.digits by omega, e1, e2, Bool.true_and, Bool.false_and]

theorem decZoned_encZoned (c : Config) (f : NumFmt) (v : Int) (hd : 0 < f.digits)
    (hv : v.natAbs < 10 ^ f.digits) (hs : f.signed = false → 0 ≤ v) :
    decZoned c f (encZoned c f v) = some v := by
  unfold decZoned
  rw [zonedParts_encZoned c f v hd hv]
  cases hsg : f.signed
  · have := hs hsg
    simp [hv]; omega
  · simp [hv, applySign_natAbs]

theorem decZoned_bound (c : Config) (f : NumFmt) {bs : List UInt8} {v : Int}
    (h : decZoned c f bs = some v) :
    v.natAbs < 10 ^ f.digits ∧ (f.signed = false → 0 ≤ v) := by
  unfold decZoned at h
  split at h
  · rename_i neg w _
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      unfold applySign
      cases neg <;> cases hs : f.signed <;> simp_all <;> omega
    · simp at h
  · simp at h

/-! ## Packed decimal (`COMP-3`) -/

/-- Pack a list of nibbles (even length) into bytes, high nibble first. -/
def packNibbles : List Nat → List UInt8
  | a :: b :: rest => UInt8.ofNat (a * 16 + b) :: packNibbles rest
  | _ => []

/-- Unpack bytes into nibbles, high nibble first. -/
def unpackNibbles (bs : List UInt8) : List Nat :=
  bs.flatMap (fun b => [b.toNat / 16, b.toNat % 16])

theorem unpack_pack : ∀ (ns : List Nat), (∀ n ∈ ns, n < 16) → ns.length % 2 = 0 →
    unpackNibbles (packNibbles ns) = ns
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | a :: b :: rest, hn, hl => by
    have ha := hn a (by simp)
    have hb := hn b (by simp)
    have ih := unpack_pack rest (fun n h => hn n (by simp [h])) (by simp at hl; omega)
    simp only [packNibbles, unpackNibbles, List.flatMap_cons] at ih ⊢
    rw [ih]
    simp [UInt8.toNat_ofNat']
    omega

theorem length_packNibbles : ∀ (ns : List Nat), (packNibbles ns).length = ns.length / 2
  | [] => by simp [packNibbles]
  | [_] => by simp [packNibbles]
  | a :: b :: rest => by simp [packNibbles, length_packNibbles rest]; omega

/-- Number of digit nibbles of a packed item (odd: a pad nibble when `digits` is even). -/
def packedDigitNibbles (f : NumFmt) : Nat := f.digits / 2 * 2 + 1

/-- Encode `v` (assumed `|v| < 10^digits`) as a packed-decimal item. -/
def encPacked (f : NumFmt) (v : Int) : List UInt8 :=
  packNibbles (toDigits 10 (packedDigitNibbles f) (v.natAbs % 10 ^ f.digits) ++
    [Config.packedSignNibble f.signed (decide (v < 0))])

/-- Decode a packed-decimal item; `none` on invalid data or wrong length. -/
def decPacked (c : Config) (f : NumFmt) (bs : List UInt8) : Option Int :=
  if bs.length = f.digits / 2 + 1 then
    match splitLast (unpackNibbles bs) with
    | some (ds, s) =>
      match c.decPackedSign f.signed s with
      | some neg =>
        if ds.all (· < 10) ∧ ofDigits 10 ds < 10 ^ f.digits ∧ (f.signed || !neg) then
          some (applySign neg (ofDigits 10 ds))
        else none
      | none => none
    | none => none
  else none

theorem length_encPacked (f : NumFmt) (v : Int) : (encPacked f v).length = f.digits / 2 + 1 := by
  unfold encPacked packedDigitNibbles
  rw [length_packNibbles]; simp; omega

theorem decPacked_encPacked (c : Config) (f : NumFmt) (v : Int)
    (hv : v.natAbs < 10 ^ f.digits) (hs : f.signed = false → 0 ≤ v) :
    decPacked c f (encPacked f v) = some v := by
  have hnd : f.digits ≤ packedDigitNibbles f := by unfold packedDigitNibbles; omega
  have hle : 10 ^ f.digits ≤ 10 ^ packedDigitNibbles f := Nat.pow_le_pow_right (by decide) hnd
  have hm : v.natAbs % 10 ^ f.digits = v.natAbs := Nat.mod_eq_of_lt hv
  have hds := toDigits_lt (b := 10) (by decide) (packedDigitNibbles f) (v.natAbs % 10 ^ f.digits)
  have hsign : Config.packedSignNibble f.signed (decide (v < 0)) < 16 := by
    unfold Config.packedSignNibble; split <;> (try split) <;> decide
  unfold decPacked
  rw [length_encPacked]
  simp only [↓reduceIte, encPacked]
  rw [unpack_pack _ (by
      intro n hn
      simp only [List.mem_append, List.mem_singleton] at hn
      rcases hn with hn | rfl
      · have := hds n hn; omega
      · exact hsign) (by simp [packedDigitNibbles]; omega),
    splitLast_append_singleton]
  simp only [ofDigits_toDigits, hm, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hv hle),
    c.decPackedSign_nibble]
  have hall : (toDigits 10 (packedDigitNibbles f) v.natAbs).all (· < 10) = true := by
    rw [List.all_eq_true]; intro x hx; have := hds x (by rw [hm]; exact hx); simpa using this
  cases hsg : f.signed
  · have := hs hsg; simp [hall, hv]; omega
  · simp [hall, hv, applySign_natAbs]

theorem decPacked_bound (c : Config) (f : NumFmt) {bs : List UInt8} {v : Int}
    (h : decPacked c f bs = some v) :
    v.natAbs < 10 ^ f.digits ∧ (f.signed = false → 0 ≤ v) := by
  unfold decPacked at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i ds s _
  split at h <;> try contradiction
  rename_i neg _
  split at h <;> try contradiction
  rename_i hc
  cases h
  unfold applySign
  cases neg <;> cases hs : f.signed <;> simp_all <;> omega

/-! ## Binary (`COMP`, `COMP-4`, `BINARY`, `COMP-5`) -/

/-- Two's-complement encoding of `v` in `n` bytes (big-endian unless `le`). -/
def encBinary (le : Bool) (n : Nat) (v : Int) : List UInt8 :=
  let u := (v % (binMod n : Int)).toNat
  let bs := (toDigits 256 n u).map UInt8.ofNat
  if le then bs.reverse else bs

/-- Decode an `n`-byte binary item, two's complement if `signed`. -/
def decBinary (le : Bool) (n : Nat) (signed : Bool) (bs : List UInt8) : Int :=
  let u := ofDigits 256 ((if le then bs.reverse else bs).map UInt8.toNat)
  if signed ∧ binHalf n ≤ u then (u : Int) - (binMod n : Int) else (u : Int)

theorem length_encBinary (le : Bool) (n : Nat) (v : Int) : (encBinary le n v).length = n := by
  unfold encBinary; cases le <;> simp

theorem pow256 (n : Nat) : (256 : Nat) ^ n = binMod n := by
  unfold binMod; rw [Nat.pow_mul]

theorem binMod_pos (n : Nat) : 0 < binMod n := Nat.pow_pos_iff.mpr (Or.inl (by decide))

/-- Range precondition of the binary codec. -/
def BinRange (n : Nat) (signed : Bool) (v : Int) : Prop :=
  if signed then -(binHalf n : Int) ≤ v ∧ v < binHalf n else 0 ≤ v ∧ v < binMod n

theorem decBinary_encBinary (le : Bool) (n : Nat) (signed : Bool) (v : Int) (hn : 0 < n)
    (h : BinRange n signed v) :
    decBinary le n signed (encBinary le n v) = v := by
  unfold BinRange at h
  have h2 := binMod_eq_two_mul hn
  have hM := binMod_pos n
  have hmod0 := Int.emod_nonneg v (b := (binMod n : Int)) (by omega)
  have hmod1 := Int.emod_lt_of_pos v (b := (binMod n : Int)) (by omega)
  have hrt : ((toDigits 256 n (v % (binMod n : Int)).toNat).map UInt8.ofNat).map UInt8.toNat
      = toDigits 256 n (v % (binMod n : Int)).toNat := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id (toDigits 256 n _)]
    apply List.map_congr_left
    intro x hx
    have := toDigits_lt (by decide) n _ x hx
    simp [UInt8.toNat_ofNat']; omega
  have hval : ofDigits 256 (toDigits 256 n (v % (binMod n : Int)).toNat)
      = (v % (binMod n : Int)).toNat := by
    rw [ofDigits_toDigits, pow256]
    apply Nat.mod_eq_of_lt
    omega
  -- `v % M` is `v` or `v + M`
  have hcase : (0 ≤ v ∧ v < binMod n → v % (binMod n : Int) = v) ∧
      (v < 0 ∧ -(binMod n : Int) ≤ v → v % (binMod n : Int) = v + binMod n) := by
    refine ⟨fun hv => Int.emod_eq_of_lt hv.1 hv.2, fun hv => ?_⟩
    have := Int.add_mul_emod_self_right v 1 (binMod n : Int)
    rw [Int.one_mul] at this
    rw [← this]; exact Int.emod_eq_of_lt (by omega) (by omega)
  unfold decBinary encBinary
  cases le <;> simp only [Bool.false_eq_true, ↓reduceIte, List.reverse_reverse, hrt, hval,
    ]
  all_goals
    cases signed <;> simp only [Bool.false_eq_true, ↓reduceIte, false_and, true_and] at h ⊢
    · rw [hcase.1 h]; omega
    · by_cases hv : 0 ≤ v
      · rw [hcase.1 ⟨hv, by omega⟩]
        split <;> omega
      · rw [hcase.2 ⟨by omega, by omega⟩]
        split <;> omega

theorem decBinary_range (le : Bool) (n : Nat) (signed : Bool) (bs : List UInt8)
    (hl : bs.length = n) (hn : 0 < n) :
    BinRange n signed (decBinary le n signed bs) := by
  have h2 := binMod_eq_two_mul hn
  have hall : ∀ l : List UInt8, l.length = n → ofDigits 256 (l.map UInt8.toNat) < binMod n := by
    intro l hl'
    rw [← pow256]
    have := ofDigits_lt (b := 256) (by decide) (l.map UInt8.toNat)
      (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨b, _, rfl⟩ := hx; exact b.toNat_lt)
    simpa [hl'] using this
  have hu : ofDigits 256 ((if le then bs.reverse else bs).map UInt8.toNat) < binMod n := by
    cases le
    · exact hall bs hl
    · exact hall bs.reverse (by simp [hl])
  simp only [BinRange, decBinary]
  generalize ofDigits 256 ((if le then bs.reverse else bs).map UInt8.toNat) = u at hu ⊢
  cases signed <;> simp only [Bool.false_eq_true, false_and, ↓reduceIte, true_and] <;>
    first | omega | (split <;> omega)

/-! ## Dispatch on `USAGE` -/

/-- Decode the value of a numeric item from its storage bytes. -/
def decodeNum (c : Config) (f : NumFmt) (bs : List UInt8) : Option Int :=
  match f.usage with
  | .display => if f.digits = 0 then none else decZoned c f bs
  | .packed => decPacked c f bs
  | .binary =>
    if bs.length = c.binBytes f.digits then
      let v := decBinary c.binaryLE (c.binBytes f.digits) f.signed bs
      if c.trunc = .bin ∨ v.natAbs < 10 ^ f.digits then some v else none
    else none
  | .comp5 =>
    if bs.length = c.binBytes f.digits then
      some (decBinary c.comp5LE (c.binBytes f.digits) f.signed bs)
    else none

/-- Encode a value into the storage bytes of a numeric item.  The value must already be
normalised for the item (`NumFmt.Holds`); the semantics guarantees this. -/
def encodeNum (c : Config) (f : NumFmt) (v : Int) : List UInt8 :=
  match f.usage with
  | .display => encZoned c f v
  | .packed => encPacked f v
  | .binary => encBinary c.binaryLE (c.binBytes f.digits) v
  | .comp5 => encBinary c.comp5LE (c.binBytes f.digits) v

theorem binBytes_pos (c : Config) (d : Nat) : 0 < c.binBytes d := by
  unfold Config.binBytes; split <;> (try split) <;> (try split) <;> omega

theorem length_encodeNum (c : Config) (f : NumFmt) (v : Int) (hd : 0 < f.digits) :
    (encodeNum c f v).length = f.byteLen c := by
  unfold encodeNum NumFmt.byteLen
  cases f.usage <;> simp [length_encZoned c f v hd, length_encPacked, length_encBinary]

/-- The decimal capacity of a binary item fits its signed binary range. -/
theorem pow10_le_binHalf (c : Config) (d : Nat) (hd : d ≤ 18) :
    10 ^ d ≤ binHalf (c.binBytes d) := by
  unfold Config.binBytes binHalf
  split
  · rename_i h; simp at h
    have : 10 ^ d ≤ 10 ^ 2 := Nat.pow_le_pow_right (by decide) h.2
    simp; omega
  · split
    · have : 10 ^ d ≤ 10 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
      simp; omega
    · split
      · have : 10 ^ d ≤ 10 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
        simp; omega
      · have : 10 ^ d ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) hd
        simp; omega

theorem decodeNum_encodeNum (c : Config) (f : NumFmt) (v : Int) (hd : 0 < f.digits)
    (hd18 : f.digits ≤ 18) (h : f.Holds c v) :
    decodeNum c f (encodeNum c f v) = some v := by
  unfold NumFmt.Holds NumFmt.fullBinary at h
  unfold decodeNum encodeNum
  have hpw := pow10_le_binHalf c f.digits hd18
  have hpos := binBytes_pos c f.digits
  have h2 := binMod_eq_two_mul hpos
  cases hu : f.usage <;> simp only [hu] at h ⊢
  · simp only [Nat.ne_of_gt hd, ↓reduceIte]
    exact decZoned_encZoned c f v hd h.1 h.2
  · exact decPacked_encPacked c f v h.1 h.2
  · simp only [length_encBinary, ↓reduceIte]
    cases ht : c.trunc <;> simp only [ht] at h ⊢ <;>
      simp only [reduceCtorEq, false_or, beq_self_eq_true, ↓reduceIte,
        true_or] at h ⊢
    · rw [decBinary_encBinary _ _ _ _ hpos (by
        unfold BinRange; cases hs : f.signed <;> simp [hs] at h ⊢ <;> omega)]
      simp only [h.1, ↓reduceIte]
    · rw [decBinary_encBinary _ _ _ _ hpos (by
        unfold BinRange; cases hs : f.signed <;> simp [hs] at h ⊢ <;> omega)]
      simp only [h.1, ↓reduceIte]
    · rw [decBinary_encBinary _ _ _ _ hpos (by unfold BinRange; exact h)]
  · simp only [length_encBinary, ↓reduceIte, Option.some.injEq]
    exact decBinary_encBinary _ _ _ _ hpos (by unfold BinRange; exact h)

theorem decodeNum_holds (c : Config) (f : NumFmt) {bs : List UInt8} {v : Int}
    (h : decodeNum c f bs = some v) : f.Holds c v := by
  unfold decodeNum at h
  unfold NumFmt.Holds NumFmt.fullBinary
  have hpos := binBytes_pos c f.digits
  cases hu : f.usage <;> simp only [hu] at h ⊢
  · split at h; · simp at h
    exact decZoned_bound c f h
  · exact decPacked_bound c f h
  · split at h <;> try contradiction
    rename_i hl
    have hb := decBinary_range c.binaryLE (c.binBytes f.digits) f.signed bs hl hpos
    split at h <;> try contradiction
    rename_i hc
    cases h
    unfold BinRange at hb
    cases ht : c.trunc <;> simp only [ht] at * <;>
      simp only [reduceCtorEq, false_or, beq_self_eq_true, ↓reduceIte,
        true_or] at *
    · refine ⟨hc, fun hs => ?_⟩
      rw [hs] at hb ⊢; simp at hb; omega
    · refine ⟨hc, fun hs => ?_⟩
      rw [hs] at hb ⊢; simp at hb; omega
    · exact hb
  · split at h <;> try contradiction
    rename_i hl
    cases h
    have := decBinary_range c.comp5LE (c.binBytes f.digits) f.signed bs hl hpos
    exact this

end Cobol
