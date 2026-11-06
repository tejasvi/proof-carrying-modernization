import EquivLean.Bridge.Cobol.Records

/-!
# Subprograms: a callee's storage items as translation values

A CALLed subprogram (CardDemo's CBSTM03B) keeps its storage and its files from one call to the
next, so one call is a transition of (storage, file states).  The generated per-call statements
(`tools/modernize/genstmt.py --subprogram`) relate the state a translation keeps between calls,
and the parameter area it is passed, to coblean's storage:

* `Schema.At s m vals`: the record `s` holds the field values `vals` in the storage `m`, each
  field at its storage offset (coblean's layout, `Field.desc`);
* `Schema.BytesAt s m bs`: the group `s` holds the bytes `bs`, for a translation that keeps a group
  of alphanumeric items (a `FILE STATUS` item) as one byte array.
-/

open Cobol

namespace EquivLean.Cobol.Rec

/-- The record `s` holds the field values `vals` in the storage `m`. -/
def Schema.At (s : Schema) (m : Mem) (vals : List FVal) : Prop :=
  Forall2 (fun f v => m.read f.desc.off f.desc.len = f.encode v) s.fields vals

/-- The group `s` holds the bytes `bs` in the storage `m`. -/
def Schema.BytesAt (s : Schema) (m : Mem) (bs : List UInt8) : Prop :=
  bs.length = s.len ∧ ∀ f ∈ s.fields, m.read f.desc.off f.desc.len = f.bytes bs

/-! ## Field by field = the whole record

For a record whose fields tile it (`Contig`) and sit at storage offset `b + roff`, the field-wise
relations are the record-level ones `m.read b s.len = …` (both hypotheses are checked by `decide`
for a concrete schema). -/

theorem at_iff_read_aux (m : Mem) (b : Nat) : ∀ {fs : List Field} {vals : List FVal} {o n : Nat},
    Forall2 Field.Valid fs vals → tiles fs o n = true → (∀ f ∈ fs, f.desc.off = b + f.roff) →
    (Forall2 (fun f v => m.read f.desc.off f.desc.len = f.encode v) fs vals ↔
      m.read (b + o) (n - o) = (fs.zip vals).flatMap fun p => p.1.encode p.2)
  | [], [], o, n, .nil, ht, _ => by
    simp only [tiles, beq_iff_eq] at ht
    subst ht
    simp only [Nat.sub_self, Mem.read_zero, List.zip_nil_left, List.flatMap_nil, iff_true]
    exact .nil
  | f :: fs, v :: vals, o, n, .cons h hs, ht, hb => by
    simp only [tiles, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨hro, ht⟩ := ht
    have hsum := tiles_sum ht
    have hoff : f.desc.off = b + o := by rw [hb f (by simp), hro]
    have hlen := Field.length_encode h
    have ih := at_iff_read_aux m b hs ht (fun g hg => hb g (List.mem_cons_of_mem _ hg))
    rw [show n - o = f.desc.len + (n - (o + f.desc.len)) by omega, Mem.read_append,
      show b + o + f.desc.len = b + (o + f.desc.len) by omega]
    simp only [List.zip_cons_cons, List.flatMap_cons]
    constructor
    · intro hf
      cases hf with
      | cons h1 h2 => rw [← hoff, h1, ih.1 h2]
    · intro hr
      have hl : (m.read (b + o) f.desc.len).length = (f.encode v).length := by
        rw [Mem.length_read, hlen]
      obtain ⟨e1, e2⟩ := List.append_inj hr hl
      exact .cons (by rw [hoff]; exact e1) (ih.2 e2)

/-- **`Schema.At` is the record-level relation**: the record's bytes in storage are the
encoding of the field values. -/
theorem Schema.at_iff_read {s : Schema} (b : Nat) (hc : s.Contig)
    (hb : ∀ f ∈ s.fields, f.desc.off = b + f.roff) {vals : List FVal} (hv : s.Valid vals)
    (m : Mem) : s.At m vals ↔ m.read b s.len = s.encode vals := by
  have h := at_iff_read_aux m b hv hc hb
  simpa only [Schema.At, Schema.encode, Nat.add_zero, Nat.sub_zero] using h

theorem bytesAt_iff_read_aux (m : Mem) (b : Nat) (bs : List UInt8) :
    ∀ {fs : List Field} {o n : Nat}, tiles fs o n = true → (∀ f ∈ fs, f.desc.off = b + f.roff) →
      n ≤ bs.length →
      ((∀ f ∈ fs, m.read f.desc.off f.desc.len = f.bytes bs) ↔
        m.read (b + o) (n - o) = (bs.drop o).take (n - o))
  | [], o, n, ht, _, _ => by
    simp only [tiles, beq_iff_eq] at ht
    subst ht
    simp [Mem.read_zero]
  | f :: fs, o, n, ht, hb, hn => by
    simp only [tiles, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨hro, ht⟩ := ht
    have hsum := tiles_sum ht
    have hoff : f.desc.off = b + o := by rw [hb f (by simp), hro]
    have ih := bytesAt_iff_read_aux m b bs ht (fun g hg => hb g (List.mem_cons_of_mem _ hg)) hn
    have hsplit : (bs.drop o).take (f.desc.len + (n - (o + f.desc.len))) =
        (bs.drop o).take f.desc.len ++ (bs.drop (o + f.desc.len)).take (n - (o + f.desc.len)) := by
      rw [List.take_add, List.drop_drop]
    rw [show n - o = f.desc.len + (n - (o + f.desc.len)) by omega, Mem.read_append,
      show b + o + f.desc.len = b + (o + f.desc.len) by omega, hsplit]
    have hfb : f.bytes bs = (bs.drop o).take f.desc.len := by rw [Field.bytes, hro]
    constructor
    · intro hf
      rw [← hoff, hf f (by simp), hfb, ih.1 (fun g hg => hf g (List.mem_cons_of_mem _ hg))]
    · intro hr
      have hl : (m.read (b + o) f.desc.len).length = ((bs.drop o).take f.desc.len).length := by
        rw [Mem.length_read, List.length_take, List.length_drop]; omega
      obtain ⟨e1, e2⟩ := List.append_inj hr hl
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · rw [hoff, e1, hfb]
      · exact ih.2 e2 g hg

/-- **`Schema.BytesAt` is the record-level relation**: the group's bytes in storage are `bs`. -/
theorem Schema.bytesAt_iff_read {s : Schema} (b : Nat) (hc : s.Contig)
    (hb : ∀ f ∈ s.fields, f.desc.off = b + f.roff) {bs : List UInt8} (hl : bs.length = s.len)
    (m : Mem) : s.BytesAt m bs ↔ m.read b s.len = bs := by
  have h := bytesAt_iff_read_aux m b bs hc hb (Nat.le_of_eq hl.symm)
  simp only [Nat.add_zero, Nat.sub_zero, List.drop_zero] at h
  rw [List.take_of_length_le (Nat.le_of_eq hl)] at h
  exact ⟨fun h' => h.1 h'.2, fun h' => ⟨hl, h.2 h'⟩⟩

end EquivLean.Cobol.Rec
