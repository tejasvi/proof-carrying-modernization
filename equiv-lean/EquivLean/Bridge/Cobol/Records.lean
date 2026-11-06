import Cobol
import Cobol.Frontend.Load
import Cobol.Target.Codepage

/-!
# COBOL records as schemas, derived mechanically from coblean's IR

A translation of a COBOL program into Java or Rust represents each 01-level record as a class or
struct whose fields are the record's elementary items, named by a fixed rule (the style guide of
the translations): the record `ACCOUNT-RECORD` is the class/struct `AccountRecord`; the field
`ACCT-CURR-BAL` is `acctCurrBal` (Java) and `acct_curr_bal` (Rust); the `k`-th `FILLER` of a record
is `filler<k>`; group items are flattened to their elementary items, in copybook order; only the
first item of a `REDEFINES` contributes fields.

`cobol_schema S from "p.ir.json" record "ACCOUNT-RECORD"` reads the IR with coblean's own parser and
layout (`surfaceOfJson`, `layout`: the offsets and formats are exactly those the COBOL semantics
uses) and defines `S : Schema`: the record's length and, per elementary field, its COBOL name, its
Java and Rust names by the rule, its descriptor and its offset in the record.  Nothing in a schema
is written by hand or by a model.

A record's bytes decode field by field (`Schema.decode`): a numeric field to the integer
`decodeNum` gives (the value scaled by `10^scale`, the representation of the translations'
`long`/`i64`), an alphanumeric field to its bytes.
-/

open Cobol Cobol.Digits Lean

namespace EquivLean.Cobol.Rec

/-! ## Names by the rule -/

/-- `ACCT-CURR-BAL` ↦ `["ACCT", "CURR", "BAL"]`. -/
def words (n : String) : List String := (n.splitOn "-").filter (· ≠ "")

def capitalize (w : String) : String :=
  match w.toList with
  | [] => ""
  | c :: cs => String.ofList (c.toUpper :: cs.map Char.toLower)

/-- `ACCT-CURR-BAL` ↦ `acctCurrBal`. -/
def javaName (n : String) : String :=
  match words n with
  | [] => ""
  | w :: ws => String.join (w.toLower :: ws.map capitalize)

/-- `ACCT-CURR-BAL` ↦ `acct_curr_bal`. -/
def rustName (n : String) : String := "_".intercalate ((words n).map String.toLower)

/-- `ACCOUNT-RECORD` ↦ `AccountRecord`. -/
def typeName (n : String) : String := String.join ((words n).map capitalize)

/-! ## Schemas -/

/-- An elementary field of a record. -/
structure Field where
  /-- COBOL name (`FILLER` for a filler). -/
  cname : String
  /-- Field name in the Java and in the Rust translation. -/
  jname : String
  rname : String
  /-- coblean's descriptor (offset in program storage, length, format). -/
  desc : FieldDesc
  /-- Offset in the record. -/
  roff : Nat
  /-- The occurrence of an item under `OCCURS` (indices from 0, outermost first; `[]` when the
  item is not under `OCCURS`): the translations hold such an item in an array. -/
  idx : List Nat := []
  deriving Repr, Inhabited

/-- A 01-level record: its COBOL name, the translations' type name, its length, its fields. -/
structure Schema where
  cname : String
  tname : String
  len : Nat
  fields : List Field
  deriving Repr, Inhabited

/-- The value of a field: an integer (numeric fields, scaled), or bytes (alphanumeric fields). -/
inductive FVal where
  | num (v : Int)
  | str (bs : List UInt8)
  deriving DecidableEq, Repr, Inhabited

def Field.bytes (f : Field) (rec : List UInt8) : List UInt8 := (rec.drop f.roff).take f.desc.len

def Field.decode (f : Field) (rec : List UInt8) : Option FVal :=
  match f.desc.kind with
  | .num fmt => (decodeNum {} fmt (f.bytes rec)).map .num
  | .alnum _ => some (.str (f.bytes rec))
  | _ => none

/-- The fields of a record, decoded. -/
def Schema.decode (s : Schema) (rec : List UInt8) : Option (List FVal) :=
  s.fields.mapM (·.decode rec)

/-! ## Encoding, and decoding an encoding -/

/-- `R` holds elementwise between two lists of the same length. -/
inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Forall2 R [] []
  | cons {a b as bs} : R a b → Forall2 R as bs → Forall2 R (a :: as) (b :: bs)

/-- The bytes of a field value (`encodeNum` for numeric fields). -/
def Field.encode (f : Field) : FVal → List UInt8
  | .num v => match f.desc.kind with
    | .num fmt => encodeNum {} fmt v
    | _ => []
  | .str bs => bs

/-- A value the field can hold: a number its picture holds (coblean's `NumFmt.Holds`), or as many
bytes as the field is long. -/
def Field.Valid (f : Field) : FVal → Prop
  | .num v => ∃ fmt, f.desc.kind = .num fmt ∧ 0 < fmt.digits ∧ fmt.digits ≤ 18 ∧
      fmt.Holds {} v ∧ fmt.byteLen {} = f.desc.len
  | .str bs => (∃ j, f.desc.kind = .alnum j) ∧ bs.length = f.desc.len

/-- The record with the given field values. -/
def Schema.encode (s : Schema) (vals : List FVal) : List UInt8 :=
  (s.fields.zip vals).flatMap fun p => p.1.encode p.2

def Schema.Valid (s : Schema) (vals : List FVal) : Prop := Forall2 Field.Valid s.fields vals

/-- The fields tile `[o, o + n)`, in order. -/
def tiles : List Field → Nat → Nat → Bool
  | [], o, n => o == n
  | f :: fs, o, n => f.roff == o && tiles fs (o + f.desc.len) n

/-- The fields tile the record (true of every schema `cobol_schema` builds; checked by `decide`). -/
def Schema.Contig (s : Schema) : Prop := tiles s.fields 0 s.len = true

instance (s : Schema) : Decidable s.Contig := inferInstanceAs (Decidable (_ = true))

theorem Field.length_encode {f : Field} {v : FVal} (h : f.Valid v) :
    (f.encode v).length = f.desc.len := by
  cases v with
  | num v =>
    obtain ⟨fmt, hk, hd, -, -, hl⟩ := h
    simp only [Field.encode, hk]
    rw [length_encodeNum _ _ _ hd, hl]
  | str bs => exact h.2

theorem Field.decode_encode {f : Field} {v : FVal} (h : f.Valid v) (pre post : List UInt8)
    (hpre : pre.length = f.roff) :
    f.decode (pre ++ f.encode v ++ post) = some v := by
  have hb : f.bytes (pre ++ f.encode v ++ post) = f.encode v := by
    unfold Field.bytes
    rw [List.append_assoc, List.drop_left' hpre, ← Field.length_encode h, List.take_left]
  unfold Field.decode
  rw [hb]
  cases v with
  | num v =>
    obtain ⟨fmt, hk, hd, hd18, hh, -⟩ := h
    simp only [hk, Field.encode, decodeNum_encodeNum _ _ _ hd hd18 hh, Option.map_some]
  | str bs =>
    obtain ⟨⟨j, hk⟩, -⟩ := h
    simp only [hk, Field.encode]

theorem length_flatMap_encode : ∀ {fs : List Field} {vals : List FVal},
    Forall2 Field.Valid fs vals →
      ((fs.zip vals).flatMap fun p => p.1.encode p.2).length = (fs.map (·.desc.len)).sum
  | [], [], .nil => rfl
  | f :: fs, v :: vals, .cons h hs => by
    simp only [List.zip_cons_cons, List.flatMap_cons, List.length_append, List.map_cons,
      List.sum_cons, Field.length_encode h, length_flatMap_encode hs]

theorem decode_flatMap_encode : ∀ {fs : List Field} {vals : List FVal} {o n : Nat}
    (pre post : List UInt8), Forall2 Field.Valid fs vals → tiles fs o n = true →
      pre.length = o →
      fs.mapM (·.decode (pre ++ ((fs.zip vals).flatMap fun p => p.1.encode p.2) ++ post)) =
        some vals
  | [], [], _, _, _, _, .nil, _, _ => rfl
  | f :: fs, v :: vals, o, n, pre, post, .cons h hs, ht, hpre => by
    simp only [tiles, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨hro, ht⟩ := ht
    have e1 : f.decode (pre ++ (f.encode v ++
        (((fs.zip vals).flatMap fun p => p.1.encode p.2) ++ post))) = some v := by
      have := Field.decode_encode h pre (((fs.zip vals).flatMap fun p => p.1.encode p.2) ++ post)
        (by rw [hpre, hro])
      simpa only [List.append_assoc] using this
    have e2 := decode_flatMap_encode (pre ++ f.encode v) post hs ht
      (by rw [List.length_append, hpre, Field.length_encode h])
    simp only [List.append_assoc] at e2
    simp only [List.mapM_cons, List.zip_cons_cons, List.flatMap_cons, List.append_assoc, e1, e2]
    rfl

/-- **Decoding a record built from valid field values gives them back.** -/
theorem Schema.decode_encode {s : Schema} (hc : s.Contig) {vals : List FVal} (hv : s.Valid vals) :
    s.decode (s.encode vals) = some vals := by
  have h := decode_flatMap_encode (vals := vals) (o := 0) [] [] hv hc rfl
  simpa [Schema.decode, Schema.encode] using h

theorem tiles_sum : ∀ {fs : List Field} {o n : Nat}, tiles fs o n = true →
    o + (fs.map (·.desc.len)).sum = n
  | [], o, n, h => by simpa [tiles] using h
  | f :: fs, o, n, h => by
    simp only [tiles, Bool.and_eq_true, beq_iff_eq] at h
    have := tiles_sum h.2
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A record built from valid field values has the record's length. -/
theorem Schema.length_encode {s : Schema} (hc : s.Contig) {vals : List FVal} (hv : s.Valid vals) :
    (s.encode vals).length = s.len := by
  have := tiles_sum hc
  rw [Schema.encode, length_flatMap_encode hv]
  omega

theorem bytes_flatMap_encode : ∀ {fs : List Field} {vals : List FVal} {o n : Nat}
    (pre post : List UInt8), Forall2 Field.Valid fs vals → tiles fs o n = true →
      pre.length = o → ∀ p ∈ fs.zip vals,
        p.1.bytes (pre ++ ((fs.zip vals).flatMap fun p => p.1.encode p.2) ++ post) = p.1.encode p.2
  | [], [], _, _, _, _, .nil, _, _ => by simp
  | f :: fs, v :: vals, o, n, pre, post, .cons h hs, ht, hpre => by
    simp only [tiles, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨hro, ht⟩ := ht
    intro p hp
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · unfold Field.bytes
      simp only [List.zip_cons_cons, List.flatMap_cons, List.append_assoc]
      rw [List.drop_left' (by rw [hpre, hro]), ← Field.length_encode h, List.take_left]
    · have e2 := bytes_flatMap_encode (pre ++ f.encode v) post hs ht
        (by rw [List.length_append, hpre, Field.length_encode h]) p hp
      simp only [List.append_assoc] at e2
      simpa only [List.zip_cons_cons, List.flatMap_cons, List.append_assoc] using e2

/-- **The bytes of a field of a record built from valid values are the value's encoding.** -/
theorem Schema.bytes_encode {s : Schema} (hc : s.Contig) {vals : List FVal} (hv : s.Valid vals) :
    ∀ p ∈ s.fields.zip vals, p.1.bytes (s.encode vals) = p.1.encode p.2 := by
  intro p hp
  have h := bytes_flatMap_encode (vals := vals) (o := 0) [] [] hv hc rfl p hp
  simpa [Schema.encode] using h

theorem Forall2.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → xs.length = ys.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [h.length_eq]

theorem Forall2.getD {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → ∀ i, i < xs.length →
      R (xs.getD i default) (ys.getD i default)
  | [], [], .nil, _, hi => absurd hi (by simp)
  | _ :: _, _ :: _, .cons h _, 0, _ => by simpa using h
  | _ :: _, _ :: _, .cons _ hs, i + 1, hi => by
    simpa using hs.getD i (by simpa using hi)

theorem mem_zip_getD {α β : Type} [Inhabited α] [Inhabited β] :
    ∀ {xs : List α} {ys : List β}, xs.length = ys.length → ∀ i, i < xs.length →
      (xs.getD i default, ys.getD i default) ∈ xs.zip ys
  | [], [], _, _, hi => absurd hi (by simp)
  | _ :: _, _ :: _, _, 0, _ => by simp
  | _ :: xs, _ :: ys, h, i + 1, hi => by
    have := mem_zip_getD (xs := xs) (ys := ys) (by simpa using h) i (by simpa using hi)
    simp only [List.getD_cons_succ, List.zip_cons_cons, List.mem_cons]
    exact Or.inr this

/-- The bytes of field `i` of a record built from valid values. -/
theorem Schema.bytes_encode_getD {s : Schema} (hc : s.Contig) {vals : List FVal}
    (hv : s.Valid vals) (i : Nat) (hi : i < s.fields.length) :
    (s.fields.getD i default).bytes (s.encode vals) =
      (s.fields.getD i default).encode (vals.getD i default) :=
  Schema.bytes_encode hc hv _ (mem_zip_getD hv.length_eq i hi)

/-- `encodeNum` is one-to-one on the values a picture holds. -/
theorem encodeNum_beq {f : NumFmt} (hd : 0 < f.digits) (hd18 : f.digits ≤ 18) {v w : Int}
    (hv : f.Holds {} v) (hw : f.Holds {} w) :
    (encodeNum {} f v == encodeNum {} f w) = (v == w) := by
  by_cases h : v = w
  · subst h; rw [beq_self_eq_true, beq_self_eq_true]
  · have : encodeNum {} f v ≠ encodeNum {} f w := fun e => h (by
      have h1 := decodeNum_encodeNum {} f v hd hd18 hv
      rw [e, decodeNum_encodeNum {} f w hd hd18 hw] at h1
      exact (Option.some.inj h1).symm)
    have h1 : (v == w) = false := beq_eq_false_iff_ne.2 h
    have h2 : (encodeNum {} f v == encodeNum {} f w) = false := beq_eq_false_iff_ne.2 this
    rw [h1, h2]

/-! ## Keyed lookups

coblean's keyed `READ` finds the first record with the key (`Sem.findKey`); the translations
search the records in order for the first one whose key field holds the value. -/

/-- A keyed lookup in the records `l.map g` finds the record `l.find? p` gives, when `p` says
"the key of `g x` is `v`". -/
theorem findKey_map {α : Type} [Inhabited α] (k : KeyDecl) (v : List UInt8) (g : α → List UInt8)
    (p : α → Bool) : ∀ (l : List α), (∀ x ∈ l, (Sem.keyOf k (g x) == v) = p x) →
      (Sem.findKey k v (l.map g)).map (fun i => l.getD i default) = l.find? p
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, Sem.findKey, List.find?_cons]
    rw [h x (List.mem_cons_self ..)]
    cases p x
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_map]
      rw [← findKey_map k v g p xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      rfl
    · rfl

theorem findKey_lt' {k : KeyDecl} {v : List UInt8} :
    ∀ {l : List (List UInt8)} {i : Nat}, Sem.findKey k v l = some i → i < l.length
  | [], _, h => by simp [Sem.findKey] at h
  | r :: rs, i, h => by
    simp only [Sem.findKey] at h
    split at h
    · simp at h; subst h; simp
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      have := findKey_lt' hj
      simp; omega

/-! ## The characters of a record (CP037)

Both translations see the text of a record: the code points of its CP037-decoded bytes (UTF-16
units in Java, Latin-1 bytes in Rust; CP037 maps the bytes onto `0 ..= 255`).  A numeric DISPLAY
field shows its digits: `PIC 9(n)` the `n` decimal digits of the value, zero-padded
(`text_unsigned`). -/

/-- The code point of an EBCDIC byte (CP037). -/
def cp037Code (b : UInt8) : Nat := (_root_.Cobol.Codepage.cp037Char b).toNat

set_option maxRecDepth 4000 in
theorem cp037Code_digitByte : ∀ d, d < 10 → cp037Code (({} : Config).digitByte d) = 48 + d := by
  decide

/-- The `n` decimal digits of `v`, zero-padded, as code points (`'0'` = 48). -/
def zpad (n v : Nat) : List Nat := (toDigits 10 n v).map (48 + ·)

theorem toDigits_succ (n v : Nat) : toDigits 10 (n + 1) v = toDigits 10 n (v / 10) ++ [v % 10] := rfl

/-- **The text of an unsigned DISPLAY numeric field** is its value's digits, zero-padded. -/
theorem text_unsigned {fmt : NumFmt} (hu : fmt.usage = .display) (hs : fmt.signed = false)
    (hd : 0 < fmt.digits) (v : Int) :
    (encodeNum {} fmt v).map cp037Code = zpad fmt.digits v.natAbs := by
  unfold encodeNum encZoned zpad
  rw [hu]
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨k, hk⟩ : ∃ k, fmt.digits = k + 1 := ⟨fmt.digits - 1, by omega⟩
  rw [hk, toDigits_succ, Nat.add_sub_cancel, List.map_append, List.map_append, List.map_map,
    List.map_singleton, List.map_singleton]
  have h1 : List.map (cp037Code ∘ ({} : Config).digitByte) (toDigits 10 k (v.natAbs / 10)) =
      List.map (fun x => 48 + x) (toDigits 10 k (v.natAbs / 10)) := by
    apply List.map_congr_left
    intro d hd'
    exact cp037Code_digitByte d (toDigits_lt (by decide) k _ d hd')
  have h2 : cp037Code (({} : Config).digitByte (v.natAbs % 10)) = 48 + v.natAbs % 10 :=
    cp037Code_digitByte _ (Nat.mod_lt _ (by decide))
  rw [h1, h2]

/-- The code point of the last character of a signed DISPLAY field with an embedded (overpunch)
sign: `{`, `A` … `I` for `+0` … `+9`; `}`, `J` … `R` for `-0` … `-9`. -/
def overpunch (neg : Bool) (d : Nat) : Nat :=
  if neg then (if d = 0 then 125 else 73 + d) else (if d = 0 then 123 else 64 + d)

set_option maxRecDepth 4000 in
theorem cp037Code_signByte : ∀ (neg : Bool) (d : Nat), d < 10 →
    cp037Code (({} : Config).signByte neg d) = overpunch neg d := by
  decide

/-- **The text of a signed DISPLAY numeric field** (trailing embedded sign): the leading digits,
zero-padded, then the overpunched last digit. -/
theorem text_signed {fmt : NumFmt} (hu : fmt.usage = .display) (hs : fmt.signed = true)
    (hsep : fmt.signSep = false) (hlead : fmt.signLead = false) (v : Int) :
    (encodeNum {} fmt v).map cp037Code =
      zpad (fmt.digits - 1) (v.natAbs / 10) ++ [overpunch (decide (v < 0)) (v.natAbs % 10)] := by
  unfold encodeNum encZoned zpad
  rw [hu]
  simp only [hs, hsep, hlead, Bool.false_eq_true, ↓reduceIte]
  rw [List.map_append, List.map_map, List.map_singleton]
  have h1 : List.map (cp037Code ∘ ({} : Config).digitByte) (toDigits 10 (fmt.digits - 1)
      (v.natAbs / 10)) = List.map (fun x => 48 + x) (toDigits 10 (fmt.digits - 1) (v.natAbs / 10)) := by
    apply List.map_congr_left
    intro d hd'
    exact cp037Code_digitByte d (toDigits_lt (by decide) _ _ d hd')
  rw [h1, cp037Code_signByte _ _ (Nat.mod_lt _ (by decide))]

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-! ## The text of a record, field by field -/

/-- The text a field value shows, as code points: an alphanumeric field's CP037 text, a numeric
field's value zero-padded to the field's length. -/
def fieldText (f : Field) : FVal → List Nat
  | .str bs => bs.map cp037Code
  | .num v => zpad f.desc.len v.natAbs

/-- A record's text: its fields' texts, in order. -/
def Schema.text (s : Schema) (vals : List FVal) : List Nat :=
  ((s.fields.zip vals).map fun p => fieldText p.1 p.2).flatten

/-- Every numeric field is an unsigned DISPLAY item (`PIC 9(n)`). -/
def UnsignedDisplay (f : Field) : Prop :=
  ∀ fmt, f.desc.kind = .num fmt → fmt.usage = .display ∧ fmt.signed = false

instance (f : Field) : Decidable (UnsignedDisplay f) := by
  unfold UnsignedDisplay
  cases h : f.desc.kind with
  | num fmt =>
    exact decidable_of_iff (fmt.usage = .display ∧ fmt.signed = false)
      ⟨fun h' g hg => by cases hg; exact h', fun h' => h' fmt rfl⟩
  | group => exact isTrue (fun _ h => by cases h)
  | alnum j => exact isTrue (fun _ h => by cases h)
  | numEdited p b => exact isTrue (fun _ h => by cases h)

theorem fieldText_eq {f : Field} (hu : UnsignedDisplay f) {v : FVal} (hv : f.Valid v) :
    fieldText f v = (f.encode v).map cp037Code := by
  cases v with
  | num n =>
    obtain ⟨fmt, hk, hd, -, -, hl⟩ := hv
    obtain ⟨hdisp, hs⟩ := hu fmt hk
    have hbl : fmt.byteLen {} = fmt.digits := by
      unfold NumFmt.byteLen; rw [hdisp]; simp [hs]
    simp only [fieldText, Field.encode, hk]
    rw [text_unsigned hdisp hs hd, ← hl, hbl]
  | str bs => rfl

theorem text_flatten : ∀ {fs : List Field} {vals : List FVal},
    (∀ f ∈ fs, UnsignedDisplay f) → Forall2 Field.Valid fs vals →
      ((fs.zip vals).map fun p => fieldText p.1 p.2).flatten =
        ((fs.zip vals).flatMap fun p => p.1.encode p.2).map cp037Code
  | [], [], _, .nil => rfl
  | f :: fs, v :: vals, hu, .cons h hs => by
    simp only [List.zip_cons_cons, List.map_cons, List.flatten_cons, List.flatMap_cons,
      List.map_append]
    rw [fieldText_eq (hu f (List.mem_cons_self ..)) h,
      text_flatten (fun g hg => hu g (List.mem_cons_of_mem _ hg)) hs]

/-- **A record's text is the CP037 text of the record's bytes** (records whose numeric fields are
all unsigned DISPLAY items). -/
theorem Schema.text_eq {s : Schema} (hu : ∀ f ∈ s.fields, UnsignedDisplay f) {vals : List FVal}
    (hv : s.Valid vals) : s.text vals = (s.encode vals).map cp037Code :=
  text_flatten hu hv

/-! ## Records with signed DISPLAY fields

`Schema.text` covers records whose numeric fields are unsigned (`PIC 9(n)`).  `Schema.textS` also
shows a signed DISPLAY field with a trailing embedded sign (`PIC S9(n)`, the default sign
position): its leading digits, zero-padded, then the overpunched last digit (`text_signed`). -/

/-- The text a field value shows (unsigned, or signed with a trailing embedded sign). -/
def fieldTextS (f : Field) : FVal → List Nat
  | .str bs => bs.map cp037Code
  | .num v =>
    match f.desc.kind with
    | .num fmt =>
      if fmt.signed then zpad (f.desc.len - 1) (v.natAbs / 10) ++ [overpunch (decide (v < 0)) (v.natAbs % 10)]
      else zpad f.desc.len v.natAbs
    | _ => []

/-- A record's text (signed DISPLAY fields included). -/
def Schema.textS (s : Schema) (vals : List FVal) : List Nat :=
  ((s.fields.zip vals).map fun p => fieldTextS p.1 p.2).flatten

/-- Every numeric field is a DISPLAY item, unsigned or with a trailing embedded sign. -/
def DisplayNumeric (f : Field) : Prop :=
  ∀ fmt, f.desc.kind = .num fmt →
    fmt.usage = .display ∧ fmt.signSep = false ∧ fmt.signLead = false

instance (f : Field) : Decidable (DisplayNumeric f) := by
  unfold DisplayNumeric
  cases h : f.desc.kind with
  | num fmt =>
    exact decidable_of_iff (fmt.usage = .display ∧ fmt.signSep = false ∧ fmt.signLead = false)
      ⟨fun h' g hg => by cases hg; exact h', fun h' => h' fmt rfl⟩
  | group => exact isTrue (fun _ h => by cases h)
  | alnum j => exact isTrue (fun _ h => by cases h)
  | numEdited p b => exact isTrue (fun _ h => by cases h)

theorem fieldTextS_eq {f : Field} (hu : DisplayNumeric f) {v : FVal} (hv : f.Valid v) :
    fieldTextS f v = (f.encode v).map cp037Code := by
  cases v with
  | num n =>
    obtain ⟨fmt, hk, hd, -, -, hl⟩ := hv
    obtain ⟨hdisp, hsep, hlead⟩ := hu fmt hk
    have hbl : fmt.byteLen {} = fmt.digits := by
      unfold NumFmt.byteLen; rw [hdisp]; simp [hsep]
    simp only [fieldTextS, Field.encode, hk]
    cases hs : fmt.signed
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [text_unsigned hdisp hs hd, ← hl, hbl]
    · simp only [↓reduceIte]
      rw [text_signed hdisp hs hsep hlead, ← hl, hbl]
  | str bs => rfl

theorem textS_flatten : ∀ {fs : List Field} {vals : List FVal},
    (∀ f ∈ fs, DisplayNumeric f) → Forall2 Field.Valid fs vals →
      ((fs.zip vals).map fun p => fieldTextS p.1 p.2).flatten =
        ((fs.zip vals).flatMap fun p => p.1.encode p.2).map cp037Code
  | [], [], _, .nil => rfl
  | f :: fs, v :: vals, hu, .cons h hs => by
    simp only [List.zip_cons_cons, List.map_cons, List.flatten_cons, List.flatMap_cons,
      List.map_append]
    rw [fieldTextS_eq (hu f (List.mem_cons_self ..)) h,
      textS_flatten (fun g hg => hu g (List.mem_cons_of_mem _ hg)) hs]

/-- **A record's text (signed DISPLAY fields included) is the CP037 text of its bytes.** -/
theorem Schema.textS_eq {s : Schema} (hu : ∀ f ∈ s.fields, DisplayNumeric f) {vals : List FVal}
    (hv : s.Valid vals) : s.textS vals = (s.encode vals).map cp037Code :=
  textS_flatten hu hv

/-! ## The schema of a record, from the IR -/

/-- The elementary items of an item (flattened, copybook order; `REDEFINES` views skipped). -/
partial def elementary (it : Item) : List Item :=
  if it.children.isEmpty then [it]
  else (it.children.filter (·.redefines.isNone)).flatMap elementary

/-- The elementary items of an item, each occurrence of an item under `OCCURS` separately:
the item, the shift of its offset from the first occurrence's, its indices. -/
partial def elementaryOcc (L : Layout) (it : Item) (shift : Nat) (idx : List Nat) :
    List (Item × Nat × List Nat) :=
  let stride := ((L.find? it.id).map (·.desc.len)).getD 0
  let occ (k : Nat) : Nat × List Nat :=
    (shift + k * stride, if it.occurs == 1 then idx else idx ++ [k])
  (List.range it.occurs).flatMap fun k =>
    let (sh, ix) := occ k
    if it.children.isEmpty then [(it, sh, ix)]
    else (it.children.filter (·.redefines.isNone)).flatMap fun c => elementaryOcc L c sh ix

def findRecord? (items : List Item) (n : String) : Option Item :=
  items.find? (fun it => it.level == 1 && it.name == n)

/-- The schema of the 01-level record `rname` of a surface program. -/
def schemaOf (sp : Surface.Program) (rname : String) : Except String Schema := do
  let L := layout sp.config sp.data
  let some r := findRecord? sp.data rname | throw s!"no 01-level record {rname}"
  let some rp := L.find? r.id | throw s!"record {rname} is not placed"
  let mut fields : Array Field := #[]
  let mut nfill := 0
  let mut fillers : List (Nat × String) := []
  for (e, sh, ix) in elementaryOcc L r 0 [] do
    let some p := L.find? e.id | throw s!"field {e.name} is not placed"
    let (jn, rn) ←
      if e.name == "FILLER" || e.name == "" then
        -- a FILLER under OCCURS keeps one name for all its occurrences
        match fillers.lookup e.id with
        | some n => pure (n, n)
        | none =>
          nfill := nfill + 1
          fillers := (e.id, s!"filler{nfill}") :: fillers
          pure (s!"filler{nfill}", s!"filler{nfill}")
      else pure (javaName e.name, rustName e.name)
    fields := fields.push
      { cname := e.name, jname := jn, rname := rn, desc := { p.desc with off := p.desc.off + sh },
        roff := p.desc.off + sh - rp.desc.off, idx := ix }
  return { cname := rname, tname := typeName rname, len := rp.desc.len, fields := fields.toList }

deriving instance ToExpr for Field
deriving instance ToExpr for Schema

/-- `cobol_schema S from "p.ir.json" record "R"`: defines `S : Schema`, the schema of the 01-level
record `R` of the program in `p.ir.json` (path relative to this file). -/
elab "cobol_schema " id:ident " from " path:str " record " rec:str : command => do
  let fileName ← Elab.Command.liftCoreM getFileName
  let dir := (System.FilePath.mk fileName).parent.getD "."
  let p := dir / path.getString
  let txt ← IO.FS.readFile p
  let j ← match Json.parse txt with
    | .ok j => pure j
    | .error e => throwError "JSON parse error in {p}: {e}"
  let sp ← match surfaceOfJson j with
    | .ok sp => pure sp
    | .error e => throwError "{p}: {e}"
  let s ← match schemaOf sp rec.getString with
    | .ok s => pure s
    | .error e => throwError "{p}: {e}"
  let declName := (← getCurrNamespace) ++ id.getId
  Elab.Command.liftTermElabM do
    addAndCompile <| .defnDecl
      { name := declName, levelParams := [], type := mkConst ``Schema, value := toExpr s,
        hints := .abbrev, safety := .safe }
    setReducibleAttribute declName

/-! ## Observables of a COBOL run -/

/-- The DISPLAY lines of a run, oldest first. -/
def displays (st : State) : List (List UInt8) :=
  st.out.reverse.filterMap fun | .display bs => some bs | _ => none

/-- The records the run WROTE to file `f`, oldest first. -/
def writes (f : Nat) (st : State) : List (List UInt8) :=
  st.out.reverse.filterMap fun | .write g bs => if g = f then some bs else none | _ => none

/-- The records the run REWROTE in file `f`, oldest first. -/
def rewrites (f : Nat) (st : State) : List (List UInt8) :=
  st.out.reverse.filterMap fun | .rewrite g bs => if g = f then some bs else none | _ => none

/-- The value of the numeric item `d` (format `fmt`) at the end of a run, e.g. `RETURN-CODE`
(0 for bytes that do not decode). -/
def itemValue (d : FieldDesc) (fmt : NumFmt) (st : State) : Int :=
  (decodeNum {} fmt (st.mem.read d.off d.len)).getD 0

/-- The run ended with `CALL 'CEE3ABD'`. -/
def abended (sig : Signal) : Bool :=
  match sig with
  | .fault (.abend _) => true
  | _ => false

/-! ## The clock

`FUNCTION CURRENT-DATE` returns 21 characters: `YYYYMMDDhhmmsshh` (digits), the sign of the
offset from UTC, `hhmm` (digits).  The statements of programs that read the clock quantify over
such readings (`CurrentDate`), in EBCDIC like every byte of the COBOL run. -/

/-- A reading of `FUNCTION CURRENT-DATE` (EBCDIC): digits everywhere but position 16, which holds
`+` or `-`. -/
def CurrentDate (c : List UInt8) : Prop :=
  c.length = 21 ∧ (∀ i, i < 21 → i ≠ 16 → 0xF0 ≤ c.getD i 0 ∧ c.getD i 0 ≤ 0xF9) ∧
    (c.getD 16 0 = 0x4E ∨ c.getD 16 0 = 0x60)

/-! ## Inputs of indexed files

coblean's file model assumes that the initial contents of an indexed file are those of a VSAM
KSDS: ascending, unique record keys (`Cobol.Sem.File`).  `KsdsValid P f recs` states it for the
records `recs` of file `f`, with the keys of `f`'s declaration in `P` (record key, alternate keys
without `DUPLICATES`): the statements carry it as a hypothesis on each indexed input file. -/

/-- The records `recs` of file `f` of `P` are the contents of a KSDS: the record keys ascending
(unsigned byte order, VSAM's collating order, hence unique) and the alternate keys without
`DUPLICATES` unique.  True of a file that is not indexed. -/
def KsdsValid (P : Program) (f : Nat) (recs : List (List UInt8)) : Prop :=
  match Sem.fileDecl P f with
  | some d => d.org = .indexed →
      (∀ k, d.key = some k →
        recs.Pairwise (fun a b => Sem.bytesLt (Sem.keyOf k a) (Sem.keyOf k b) = true)) ∧
      (∀ k ∈ d.alt, k.dups = false → recs.Pairwise (fun a b => Sem.keyOf k a ≠ Sem.keyOf k b))
  | none => True

/-- The bytes of a hexadecimal text (whitespace ignored). -/
def bytesOfHex (txt : String) : Except String (Array UInt8) := do
  let ds := (txt.toList.filter (fun c => !c.isWhitespace)).toArray
  unless ds.size % 2 == 0 do throw "odd number of hex digits"
  let hexVal (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else throw s!"not a hex digit: {c}"
  let mut out : Array UInt8 := #[]
  for i in [0:ds.size / 2] do
    out := out.push (UInt8.ofNat (16 * (← hexVal ds[2 * i]!) + (← hexVal ds[2 * i + 1]!)))
  return out

/-- `cobol_mem_hex M from "init_mem.hex"`: defines `M : Mem`, the storage with the bytes of the
hexadecimal file (path relative to this file), e.g. the initial storage a test harness passes to
the COBOL run. -/
elab "cobol_mem_hex " id:ident " from " path:str : command => do
  let fileName ← Elab.Command.liftCoreM getFileName
  let dir := (System.FilePath.mk fileName).parent.getD "."
  let p := dir / path.getString
  let txt ← IO.FS.readFile p
  let bs ← match bytesOfHex txt with
    | .ok bs => pure bs
    | .error e => throwError "{p}: {e}"
  let declName := (← getCurrNamespace) ++ id.getId
  Elab.Command.liftTermElabM do
    addAndCompile <| .defnDecl
      { name := declName, levelParams := [], type := mkConst ``Mem,
        value := mkApp (mkConst ``Mem.mk) (toExpr bs), hints := .abbrev, safety := .safe }

end EquivLean.Cobol.Rec
