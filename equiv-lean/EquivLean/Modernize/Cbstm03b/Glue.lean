import EquivLean.Modernize.Cbstm03b.Model
import EquivLean.Bridge.Cobol.Sub

/-!
# CBSTM03B: the model of one call against coblean's `call3b`

The relations of the generated per-call statement (`tools/modernize/genstmt.py --subprogram`), on the model's
values (`Model.lean`):

* `FileRel S f s`: the open flag, the records (valid field values of schema `S`, encoded), the read position and
  the end-of-file flag of coblean's file state `s` (its last record read, `cur`, is not part of it);
* `StateRel st cs`: the four files, the four FD record areas (`Schema.At`) and the four `FILE STATUS` items
  (`Schema.BytesAt` of the code points mapped by `ebcdicOfLatin1`), in the order of the generated `StateRel`;
* `LkM03bAreaRel a m`: the area's field values at their storage offsets;
* `EnvRel oe env`: the `OPEN INPUT` outcomes.

A translation state maps to the model's values field by field (records by `rust_record_vals`, statuses and
positions by `UScalar.val`), and the generated relations are these relations of the mapped values.

`call_glue`: for related states, area and environment, under the hypotheses of coblean's `cbstm03b_call` (for
operation `K`, a key length in `1 ..= 25` and, for ACCTFILE, digits), the model's state and area after the call are
related to `call3b`'s storage and files. `call_run`: the same against coblean's interpreter, whose run ends with
`GOBACK`. The proof goes file by file (`seq_glue` for TRNXFILE and XREFFILE, `key_glue` for CUSTFILE and ACCTFILE):
a call writes only the file's record area, its status item and the area's return code and record buffer, so the
other files' parts of the state stay related (`Frame`).
-/

open Cobol EquivLean.Cobol.Rec
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf retCode openIn
  closeF canRd seqRead keyRead seqCall keyCall Files st0 call3b custKeyOf acctKeyOf)

namespace EquivLean.Modernize.Cbstm03b.Glue

open Model

cobol_schema TrnxfileStatus from "../../../examples/cobol/carddemo/cbstm03b.ir.json" record "TRNXFILE-STATUS"
cobol_schema XreffileStatus from "../../../examples/cobol/carddemo/cbstm03b.ir.json" record "XREFFILE-STATUS"
cobol_schema CustfileStatus from "../../../examples/cobol/carddemo/cbstm03b.ir.json" record "CUSTFILE-STATUS"
cobol_schema AcctfileStatus from "../../../examples/cobol/carddemo/cbstm03b.ir.json" record "ACCTFILE-STATUS"

/-! ## The relations -/

/-- A file against coblean's file state: the open flag, the records, the read position, the end-of-file flag. -/
def FileRel (S : Schema) (f : FileM) (s : FileSt) : Prop :=
  s.mode = (if f.isOpen then some .input else none) ∧ (∀ r ∈ f.recs, S.Valid r) ∧
    s.recs = f.recs.map S.encode ∧ s.pos = f.pos ∧ s.eof = f.eof

/-- The state kept between calls against the callee's COBOL state: the files, the FD record areas and the
`FILE STATUS` items, at their storage offsets. -/
def StateRel (st : StM) (cs : Cobol.State) : Prop :=
  (∃ s, cs.files.lookup 1 = some s ∧ FileRel FdTrnxfileRec st.trnx s) ∧
    (∃ s, cs.files.lookup 2 = some s ∧ FileRel FdXreffileRec st.xref s) ∧
    (∃ s, cs.files.lookup 3 = some s ∧ FileRel FdCustfileRec st.cust s) ∧
    (∃ s, cs.files.lookup 4 = some s ∧ FileRel FdAcctfileRec st.acct s) ∧
    FdTrnxfileRec.Valid st.trnxRec ∧ FdTrnxfileRec.At cs.mem st.trnxRec ∧
    FdXreffileRec.Valid st.xrefRec ∧ FdXreffileRec.At cs.mem st.xrefRec ∧
    FdCustfileRec.Valid st.custRec ∧ FdCustfileRec.At cs.mem st.custRec ∧
    FdAcctfileRec.Valid st.acctRec ∧ FdAcctfileRec.At cs.mem st.acctRec ∧
    TrnxfileStatus.BytesAt cs.mem (st.trnxSt.map ebcdicOfLatin1) ∧
    XreffileStatus.BytesAt cs.mem (st.xrefSt.map ebcdicOfLatin1) ∧
    CustfileStatus.BytesAt cs.mem (st.custSt.map ebcdicOfLatin1) ∧
    AcctfileStatus.BytesAt cs.mem (st.acctSt.map ebcdicOfLatin1)

/-- The parameter area: its field values at their storage offsets. -/
def LkM03bAreaRel (a : List FVal) (m : Mem) : Prop := LkM03bArea.Valid a ∧ LkM03bArea.At m a

/-- The `OPEN INPUT` outcomes: `oe (i + 1)` is the status of a failed `OPEN INPUT` of file `i + 1`, or `none`. -/
def EnvRel (oe : OpenErrs) (env : Env) : Prop := ∀ i, i < 4 → oe (i + 1) = env.openError (i + 1) .input

/-! ## Lists of field values, position by position -/

theorem forall2_iff {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, Forall2 R l1 l2 ↔
      l1.length = l2.length ∧ ∀ i, i < l1.length → R (l1.getD i default) (l2.getD i default)
  | [], [] => ⟨fun _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun _ => .nil⟩
  | [], _ :: _ => ⟨fun h => (by cases h), fun h => absurd h.1 (by simp)⟩
  | _ :: _, [] => ⟨fun h => (by cases h), fun h => absurd h.1 (by simp)⟩
  | x :: xs, y :: ys => by
    constructor
    · intro h
      cases h with
      | cons hxy hrest =>
        obtain ⟨hl, hi⟩ := forall2_iff.1 hrest
        refine ⟨by simp [hl], fun i hi' => ?_⟩
        cases i with
        | zero => simpa using hxy
        | succ j => simpa using hi j (by simp at hi'; omega)
    · rintro ⟨hl, hi⟩
      exact .cons (by simpa using hi 0 (by simp))
        (forall2_iff.2 ⟨by simpa using hl, fun j hj => by simpa using hi (j + 1) (by simp; omega)⟩)

theorem getD_mem {α : Type} {l : List α} {i : Nat} {d : α} (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem getD_set_self {α : Type} {l : List α} {i : Nat} {a d : α} (h : i < l.length) :
    (l.set i a).getD i d = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

theorem getD_set_ne {α : Type} {l : List α} {i j : Nat} {a d : α} (h : i ≠ j) :
    (l.set i a).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

/-! ## Records in storage -/

/-- The fields of `s` are at `o` plus their offset in the record, inside the record. -/
def AtOff (s : Schema) (o : Nat) : Prop := ∀ f ∈ s.fields, f.desc.off = o + f.roff ∧ f.roff + f.desc.len ≤ s.len

instance (s : Schema) (o : Nat) : Decidable (AtOff s o) := by unfold AtOff; infer_instance

/-- `m'` holds the bytes of `m` in `[lo, hi)`. -/
def MemSame (m m' : Mem) (lo hi : Nat) : Prop := ∀ o n, lo ≤ o → o + n ≤ hi → m'.read o n = m.read o n

theorem same_trans {m1 m2 m3 : Mem} {lo hi : Nat} (h1 : MemSame m1 m2 lo hi) (h2 : MemSame m2 m3 lo hi) :
    MemSame m1 m3 lo hi :=
  fun o n a b => (h2 o n a b).trans (h1 o n a b)

theorem same_write {m : Mem} {lo hi o : Nat} {bs : List UInt8} (h : o + bs.length ≤ lo ∨ hi ≤ o) :
    MemSame m (m.write o bs) lo hi :=
  fun o' n a b => Mem.read_write_disjoint m o o' n bs (by omega)

theorem same_mono {m m' : Mem} {lo hi lo' hi' : Nat} (h : MemSame m m' lo hi) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    MemSame m m' lo' hi' :=
  fun o n a b => h o n (by omega) (by omega)

theorem at_getD {s : Schema} {m : Mem} {vals : List FVal} (h : s.At m vals) {i : Nat} (hi : i < s.fields.length) :
    m.read (s.fields.getD i default).desc.off (s.fields.getD i default).desc.len =
      (s.fields.getD i default).encode (vals.getD i default) := by
  unfold Schema.At at h
  exact (forall2_iff.1 h).2 i hi

theorem valid_getD {s : Schema} {vals : List FVal} (h : s.Valid vals) {i : Nat} (hi : i < s.fields.length) :
    (s.fields.getD i default).Valid (vals.getD i default) := by
  unfold Schema.Valid at h
  exact (forall2_iff.1 h).2 i hi

theorem at_same {s : Schema} {o : Nat} {m m' : Mem} {vals : List FVal} (ho : AtOff s o)
    (hs : MemSame m m' o (o + s.len)) (h : s.At m vals) : s.At m' vals := by
  unfold Schema.At at h ⊢
  rw [forall2_iff] at h ⊢
  refine ⟨h.1, fun i hi => ?_⟩
  obtain ⟨h1, h2⟩ := ho _ (getD_mem (d := default) hi)
  rw [hs _ _ (by omega) (by omega)]
  exact h.2 i hi

theorem bytesAt_same {s : Schema} {o : Nat} {m m' : Mem} {bs : List UInt8} (ho : AtOff s o)
    (hs : MemSame m m' o (o + s.len)) (h : s.BytesAt m bs) : s.BytesAt m' bs :=
  ⟨h.1, fun f hf => by
    obtain ⟨h1, h2⟩ := ho f hf
    rw [hs _ _ (by omega) (by omega)]
    exact h.2 f hf⟩

/-- A record written whole holds its field values. -/
theorem at_write_encode {s : Schema} {o : Nat} {m : Mem} {vals : List FVal} (hc : s.Contig) (ho : AtOff s o)
    (hv : s.Valid vals) (hsz : o + s.len ≤ m.size) : s.At (m.write o (s.encode vals)) vals := by
  have hl := Schema.length_encode hc hv
  unfold Schema.At
  rw [forall2_iff]
  refine ⟨hv.length_eq, fun i hi => ?_⟩
  obtain ⟨h1, h2⟩ := ho _ (getD_mem (d := default) hi)
  rw [h1, Mem.read_write_within _ _ _ _ _ (by omega) (by omega) (by omega), Nat.add_sub_cancel_left]
  exact Schema.bytes_encode_getD hc hv i hi

/-- A group written whole holds its bytes. -/
theorem bytesAt_write {s : Schema} {o : Nat} {m : Mem} {bs : List UInt8} (ho : AtOff s o) (hl : bs.length = s.len)
    (hsz : o + s.len ≤ m.size) : s.BytesAt (m.write o bs) bs :=
  ⟨hl, fun f hf => by
    obtain ⟨h1, h2⟩ := ho f hf
    rw [h1, Mem.read_write_within _ _ _ _ _ (by omega) (by omega) (by omega), Nat.add_sub_cancel_left]
    rfl⟩

/-- Writing the bytes of one field changes that field's value only. -/
theorem at_write_field {s : Schema} {m : Mem} {vals : List FVal} (h : s.At m vals) {i : Nat}
    (hi : i < s.fields.length) {w : FVal} {bs : List UInt8} (he : (s.fields.getD i default).encode w = bs)
    (hl : bs.length = (s.fields.getD i default).desc.len)
    (hd : ∀ j, j < s.fields.length → j ≠ i →
      (s.fields.getD j default).desc.off + (s.fields.getD j default).desc.len ≤
        (s.fields.getD i default).desc.off ∨
      (s.fields.getD i default).desc.off + (s.fields.getD i default).desc.len ≤
        (s.fields.getD j default).desc.off)
    (hsz : (s.fields.getD i default).desc.off + (s.fields.getD i default).desc.len ≤ m.size) :
    s.At (m.write (s.fields.getD i default).desc.off bs) (vals.set i w) := by
  unfold Schema.At at h ⊢
  rw [forall2_iff] at h ⊢
  obtain ⟨hlen, hall⟩ := h
  refine ⟨by rw [List.length_set]; exact hlen, fun j hj => ?_⟩
  by_cases hji : j = i
  · subst hji
    rw [Mem.read_write_same _ _ _ _ hl hsz, getD_set_self (by omega)]
    exact he.symm
  · have := hd j hj hji
    rw [Mem.read_write_disjoint _ _ _ _ _ (by omega), getD_set_ne (Ne.symm hji)]
    exact hall j hj

theorem valid_set {s : Schema} {vals : List FVal} (h : s.Valid vals) {i : Nat} (hi : i < s.fields.length)
    {w : FVal} (hw : (s.fields.getD i default).Valid w) : s.Valid (vals.set i w) := by
  unfold Schema.Valid at h ⊢
  rw [forall2_iff] at h ⊢
  obtain ⟨hlen, hall⟩ := h
  refine ⟨by rw [List.length_set]; exact hlen, fun j hj => ?_⟩
  by_cases hji : j = i
  · subst hji
    rw [getD_set_self (by omega)]
    exact hw
  · rw [getD_set_ne (Ne.symm hji)]
    exact hall j hj

theorem encode_str {f : Field} {v : FVal} (hv : f.Valid v) (hk : ∃ j, f.desc.kind = .alnum j) :
    f.encode v = strOf v ∧ (strOf v).length = f.desc.len := by
  cases v with
  | num x =>
    obtain ⟨fmt, h, -⟩ := hv
    obtain ⟨j, hj⟩ := hk
    rw [hj] at h
    cases h
  | str bs => exact ⟨rfl, hv.2⟩

theorem val_num {f : Field} {v : FVal} {fmt : NumFmt} (hv : f.Valid v) (hk : f.desc.kind = .num fmt) :
    v = .num (numOf v) ∧ fmt.Holds {} (numOf v) ∧ 0 < fmt.digits ∧ fmt.digits ≤ 18 := by
  cases v with
  | num x =>
    obtain ⟨fmt', h, h1, h2, h3, -⟩ := hv
    rw [hk] at h
    cases h
    exact ⟨rfl, h3, h1, h2⟩
  | str bs =>
    obtain ⟨⟨j, hj⟩, -⟩ := hv
    rw [hk] at hj
    cases hj

theorem read_take {m : Mem} {o n k : Nat} (hk : k ≤ n) : m.read o k = (m.read o n).take k := by
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  rw [Mem.read_append, List.take_left' (Mem.length_read _ _ _)]

/-- A two-byte group of two one-byte fields at `so` reads as its bytes. -/
theorem read2 {T : Schema} {so : Nat}
    (hT : T.fields.map (fun f => (f.desc.off, f.desc.len, f.roff)) = [(so, 1, 0), (so + 1, 1, 1)])
    (hl : T.len = 2) (m : Mem) (bs : List UInt8) (h : T.BytesAt m bs) : m.read so 2 = bs := by
  obtain ⟨hlen, hr⟩ := h
  rw [List.map_eq_cons_iff] at hT
  obtain ⟨f0, l1, hf, h0, hT⟩ := hT
  rw [List.map_eq_cons_iff] at hT
  obtain ⟨f1, l2, hl1, h1, -⟩ := hT
  simp only [Prod.mk.injEq] at h0 h1
  have e0 := hr f0 (by rw [hf]; exact List.mem_cons_self)
  have e1 := hr f1 (by rw [hf, hl1]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  rw [h0.1, h0.2.1] at e0
  rw [h1.1, h1.2.1] at e1
  rw [show (2 : Nat) = 1 + 1 from rfl, Mem.read_append, e0, e1]
  unfold Field.bytes
  rw [h0.2.1, h0.2.2, h1.2.1, h1.2.2]
  rw [hl] at hlen
  match bs, hlen with
  | [_, _], _ => rfl
  | [], h => simp at h
  | [_], h => simp at h
  | _ :: _ :: _ :: _, h => simp only [List.length_cons] at h; omega

/-! ## Status codes -/

theorem ebcdic_digit : ∀ d, d < 10 → ebcdicOfLatin1 (48 + d) = UInt8.ofNat (240 + d) := by decide +kernel

/-- The code points of a status code map to the bytes coblean stores. -/
theorem stCp_map (c : Nat) : (stCp c).map ebcdicOfLatin1 = stBytes c := by
  have h1 := ebcdic_digit (c / 10 % 10) (Nat.mod_lt _ (by decide))
  have h2 := ebcdic_digit (c % 10) (Nat.mod_lt _ (by decide))
  simp only [stCp, stBytes, List.map_cons, List.map_nil, h1, h2]

/-! ## The file operations -/

theorem openIn_rel {S : Schema} {fM : FileM} {f : FileSt} {env : Env} {id : Nat} {oe : Option Nat}
    (hf : FileRel S fM f) (hoe : oe = env.openError id .input) :
    (openIn env id f).1 = (openM oe fM).1 ∧ FileRel S (openM oe fM).2 (openIn env id f).2 := by
  obtain ⟨hmode, hv, hrecs, hpos, heof⟩ := hf
  cases hopen : fM.isOpen
  · have hm : f.mode = none := by simp [hmode, hopen]
    cases oe with
    | some c =>
      have e1 : openIn env id f = (c, f) := by
        simp only [openIn, hm, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, ← hoe]
      have e2 : openM (some c) fM = (c, fM) := by
        simp only [openM, hopen, Bool.false_eq_true, ↓reduceIte]
      rw [e1, e2]
      exact ⟨rfl, by simp [hm, hopen], hv, hrecs, hpos, heof⟩
    | none =>
      have e1 : openIn env id f = (0, { f with mode := some .input, pos := 0, eof := false, cur := none }) := by
        simp only [openIn, hm, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, ← hoe]
      have e2 : openM none fM = (0, { fM with isOpen := true, pos := 0, eof := false }) := by
        simp only [openM, hopen, Bool.false_eq_true, ↓reduceIte]
      rw [e1, e2]
      exact ⟨rfl, by simp, hv, hrecs, rfl, rfl⟩
  · have hm : f.mode = some .input := by simp [hmode, hopen]
    have e1 : openIn env id f = (41, { f with cur := none }) := by
      simp only [openIn, hm, Option.isSome_some, ↓reduceIte]
    have e2 : openM oe fM = (41, fM) := by simp only [openM, hopen, ↓reduceIte]
    rw [e1, e2]
    exact ⟨rfl, by simp [hm, hopen], hv, hrecs, hpos, heof⟩

theorem closeF_rel {S : Schema} {fM : FileM} {f : FileSt} (hf : FileRel S fM f) :
    (closeF f).1 = (closeM fM).1 ∧ FileRel S (closeM fM).2 (closeF f).2 := by
  obtain ⟨hmode, hv, hrecs, hpos, heof⟩ := hf
  cases hopen : fM.isOpen
  · have hm : f.mode = none := by simp [hmode, hopen]
    have e1 : closeF f = (42, f) := by simp only [closeF, hm]
    have e2 : closeM fM = (42, fM) := by simp only [closeM, hopen, Bool.false_eq_true, ↓reduceIte]
    rw [e1, e2]
    exact ⟨rfl, by simp [hm, hopen], hv, hrecs, hpos, heof⟩
  · have hm : f.mode = some .input := by simp [hmode, hopen]
    have e1 : closeF f = (0, { f with mode := none, cur := none }) := by simp only [closeF, hm]
    have e2 : closeM fM = (0, { fM with isOpen := false }) := by
      simp only [closeM, hopen, ↓reduceIte]
    rw [e1, e2]
    exact ⟨rfl, by simp, hv, hrecs, hpos, heof⟩

theorem seqRead_rel {S : Schema} {fM : FileM} {f : FileSt} (hf : FileRel S fM f) :
    (seqRead f).1 = (seqReadM fM).1 ∧ FileRel S (seqReadM fM).2.1 (seqRead f).2.1 ∧
      (seqRead f).2.2 = (seqReadM fM).2.2.map S.encode ∧ ∀ r, (seqReadM fM).2.2 = some r → S.Valid r := by
  obtain ⟨hmode, hv, hrecs, hpos, heof⟩ := hf
  cases hopen : fM.isOpen
  · have hc : canRd f = false := by unfold canRd; rw [hmode, hopen]; decide
    have e1 : seqRead f = (47, { f with cur := none }, none) := by
      simp only [seqRead, hc, Bool.not_false, ↓reduceIte]
    have e2 : seqReadM fM = (47, fM, none) := by
      simp only [seqReadM, hopen, Bool.not_false, ↓reduceIte]
    rw [e1, e2]
    exact ⟨rfl, ⟨by simp [hmode, hopen], hv, hrecs, hpos, heof⟩, rfl, fun r h => by cases h⟩
  · have hc : canRd f = true := by unfold canRd; rw [hmode, hopen]; decide
    cases he : fM.eof
    · cases hr : fM.recs[fM.pos]? with
      | none =>
        have hr' : f.recs[f.pos]? = none := by simp [hrecs, hpos, hr]
        have e1 : seqRead f = (10, { f with eof := true, cur := none }, none) := by
          simp only [seqRead, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heof, he, hr']
        have e2 : seqReadM fM = (10, { fM with eof := true }, none) := by
          simp only [seqReadM, hopen, he, hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [e1, e2]
        exact ⟨rfl, ⟨by simp [hmode, hopen], hv, hrecs, hpos, rfl⟩, rfl, fun r h => by cases h⟩
      | some r =>
        have hr' : f.recs[f.pos]? = some (S.encode r) := by simp [hrecs, hpos, hr]
        have e1 : seqRead f = (0, { f with pos := f.pos + 1, cur := some f.pos }, some (S.encode r)) := by
          simp only [seqRead, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heof, he, hr']
        have e2 : seqReadM fM = (0, { fM with pos := fM.pos + 1 }, some r) := by
          simp only [seqReadM, hopen, he, hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [e1, e2]
        exact ⟨rfl, ⟨by simp [hmode, hopen], hv, hrecs, by simp [hpos], heof⟩, rfl,
          fun r' h => by cases h; exact hv _ (List.mem_of_getElem? hr)⟩
    · have e1 : seqRead f = (46, { f with cur := none }, none) := by
        simp only [seqRead, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, heof, he]
      have e2 : seqReadM fM = (46, fM, none) := by
        simp only [seqReadM, hopen, he, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [e1, e2]
      exact ⟨rfl, ⟨by simp [hmode, hopen], hv, hrecs, hpos, heof⟩, rfl, fun r h => by cases h⟩

/-- A keyed lookup in encoded records is the first-match search of their values. -/
theorem findKey_idx {α : Type} (k : KeyDecl) (v : List UInt8) (g : α → List UInt8) (p : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, (Sem.keyOf k (g x) == v) = p x) → Sem.findKey k v (l.map g) = l.findIdx? p
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.map_cons, Sem.findKey, List.findIdx?_cons, h x List.mem_cons_self,
      findKey_idx k v g p xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem keyRead_rel {S : Schema} {fM : FileM} {f : FileSt} {kl : Nat} {key : List UInt8}
    {p : List FVal → Bool} (hf : FileRel S fM f)
    (hp : ∀ x ∈ fM.recs, (Sem.keyOf { off := 0, len := kl } (S.encode x) == key) = p x) :
    (keyRead kl key f).1 = (keyReadM p fM).1 ∧ FileRel S (keyReadM p fM).2.1 (keyRead kl key f).2.1 ∧
      (keyRead kl key f).2.2 = (keyReadM p fM).2.2.map S.encode ∧
      ∀ r, (keyReadM p fM).2.2 = some r → S.Valid r := by
  obtain ⟨hmode, hv, hrecs, hpos, heof⟩ := hf
  have hk : Sem.findKey { off := 0, len := kl } key f.recs = fM.recs.findIdx? p := by
    rw [hrecs]; exact findKey_idx _ _ _ _ _ hp
  cases hopen : fM.isOpen
  · have hc : canRd f = false := by unfold canRd; rw [hmode, hopen]; decide
    have e1 : keyRead kl key f = (47, { f with cur := none }, none) := by
      simp only [keyRead, hc, Bool.not_false, ↓reduceIte]
    have e2 : keyReadM p fM = (47, fM, none) := by
      simp only [keyReadM, hopen, Bool.not_false, ↓reduceIte]
    rw [e1, e2]
    exact ⟨rfl, ⟨by simp [hmode, hopen], hv, hrecs, hpos, heof⟩, rfl, fun r h => by cases h⟩
  · have hc : canRd f = true := by unfold canRd; rw [hmode, hopen]; decide
    cases hi : fM.recs.findIdx? p with
    | none =>
      have e1 : keyRead kl key f = (23, { f with cur := none }, none) := by
        simp only [keyRead, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hk, hi]
      have e2 : keyReadM p fM = (23, fM, none) := by
        simp only [keyReadM, hopen, hi, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [e1, e2]
      exact ⟨rfl, ⟨by simp [hmode, hopen], hv, hrecs, hpos, heof⟩, rfl, fun r h => by cases h⟩
    | some i =>
      obtain ⟨hlt, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
      have hg : f.recs.getD i [] = S.encode (fM.recs.getD i []) := by
        rw [hrecs, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hlt]
        rfl
      have e1 : keyRead kl key f =
          (0, { f with pos := i + 1, eof := false, cur := some i }, some (S.encode (fM.recs.getD i []))) := by
        simp only [keyRead, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hk, hi, hg]
      have e2 : keyReadM p fM = (0, { fM with pos := i + 1, eof := false }, some (fM.recs.getD i [])) := by
        simp only [keyReadM, hopen, hi, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [e1, e2]
      exact ⟨rfl, ⟨by simp [hmode, hopen], hv, hrecs, rfl, rfl⟩, rfl,
        fun r h => by cases h; exact hv _ (getD_mem hlt)⟩

/-! ## One file's slot in storage -/

/-- A file's record area at `ao` (schema `S`) and its status item at `so` (schema `T`, two bytes), below the
area. -/
structure Slot (S T : Schema) (ao so : Nat) : Prop where
  contig : S.Contig
  atOff : AtOff S ao
  below : ao + S.len ≤ 1200
  le1000 : S.len ≤ 1000
  stOff : AtOff T so
  stLen : T.len = 2
  stPos : 1200 ≤ so ∧ so + 2 ≤ 1208
  stRead : ∀ (m : Mem) (bs : List UInt8), T.BytesAt m bs → m.read so 2 = bs

theorem slotTrnx : Slot FdTrnxfileRec TrnxfileStatus 0 1200 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, read2 (by decide) (by decide)⟩
theorem slotXref : Slot FdXreffileRec XreffileStatus 350 1202 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, read2 (by decide) (by decide)⟩
theorem slotCust : Slot FdCustfileRec CustfileStatus 400 1204 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, read2 (by decide) (by decide)⟩
theorem slotAcct : Slot FdAcctfileRec AcctfileStatus 900 1206 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, read2 (by decide) (by decide)⟩

/-- `m'` holds the bytes of `m` below the area, outside the record area `[ao, ao + n)` and the status item
`[so, so + 2)`. -/
def Frame (ao n so : Nat) (m m' : Mem) : Prop :=
  MemSame m m' 0 ao ∧ MemSame m m' (ao + n) so ∧ MemSame m m' (so + 2) 1208

theorem frame_trans {ao n so : Nat} {m1 m2 m3 : Mem} (h1 : Frame ao n so m1 m2) (h2 : Frame ao n so m2 m3) :
    Frame ao n so m1 m3 :=
  ⟨same_trans h1.1 h2.1, same_trans h1.2.1 h2.2.1, same_trans h1.2.2 h2.2.2⟩

/-- A write in the area, in the record area or in the status item keeps the frame. -/
theorem frame_write {ao n so o : Nat} {m : Mem} {bs : List UInt8} (hs : ao + n ≤ so) (hs2 : so + 2 ≤ 1208)
    (h : 1208 ≤ o ∨ (ao ≤ o ∧ o + bs.length ≤ ao + n) ∨ (so ≤ o ∧ o + bs.length ≤ so + 2)) :
    Frame ao n so m (m.write o bs) :=
  ⟨same_write (by omega), same_write (by omega), same_write (by omega)⟩

theorem frame_same {ao n so : Nat} {m m' : Mem} (h : Frame ao n so m m') {lo hi : Nat}
    (hr : hi ≤ ao ∨ (ao + n ≤ lo ∧ hi ≤ so) ∨ (so + 2 ≤ lo ∧ hi ≤ 1208)) : MemSame m m' lo hi := by
  rcases hr with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact same_mono h.1 (Nat.zero_le _) h1
  · exact same_mono h.2.1 h1 h2
  · exact same_mono h.2.2 h1 h2

/-! ## The area -/

theorem lk_atOff : AtOff LkM03bArea 1208 := by decide

theorem area_write_out {a : List FVal} {m : Mem} {o : Nat} {bs : List UInt8} (h : LkM03bAreaRel a m)
    (ho : o + bs.length ≤ 1208) : LkM03bAreaRel a (m.write o bs) :=
  ⟨h.1, at_same lk_atOff (same_write (Or.inl ho)) h.2⟩

/-- Writing an alphanumeric field of the area. -/
theorem area_set {a : List FVal} {m : Mem} (hm : m.size = 2248) (h : LkM03bAreaRel a m) {i o n : Nat}
    (hi : i < LkM03bArea.fields.length) (hf : (LkM03bArea.fields.getD i default).desc = ⟨o, n, .alnum false⟩)
    (hd : ∀ j, j < LkM03bArea.fields.length → j ≠ i →
      (LkM03bArea.fields.getD j default).desc.off + (LkM03bArea.fields.getD j default).desc.len ≤ o ∨
      o + n ≤ (LkM03bArea.fields.getD j default).desc.off)
    (hsz : o + n ≤ 2248) {bs : List UInt8} (hl : bs.length = n) :
    LkM03bAreaRel (a.set i (.str bs)) (m.write o bs) := by
  have ho : (LkM03bArea.fields.getD i default).desc.off = o := by rw [hf]
  have hn : (LkM03bArea.fields.getD i default).desc.len = n := by rw [hf]
  have hk : (LkM03bArea.fields.getD i default).desc.kind = .alnum false := by rw [hf]
  refine ⟨valid_set h.1 hi ⟨⟨false, hk⟩, by rw [hl, hn]⟩, ?_⟩
  have := at_write_field h.2 hi (w := .str bs) (bs := bs) rfl (by rw [hl, hn]) (by rw [ho, hn]; exact hd)
    (by rw [ho, hn, hm]; exact hsz)
  rwa [ho] at this

theorem area_rc {a : List FVal} {m : Mem} (hm : m.size = 2248) (h : LkM03bAreaRel a m) {bs : List UInt8}
    (hl : bs.length = 2) : LkM03bAreaRel (setRc a bs) (m.write 1217 bs) :=
  area_set hm h (i := 2) (o := 1217) (n := 2) (by decide) (by decide) (by decide) (by decide) hl

theorem area_fldt {a : List FVal} {m : Mem} (hm : m.size = 2248) (h : LkM03bAreaRel a m) {bs : List UInt8}
    (hl : bs.length ≤ 1000) : LkM03bAreaRel (setFldt a bs) (m.write 1248 (intoBuf bs)) :=
  area_set hm h (i := 5) (o := 1248) (n := 1000) (by decide) (by decide) (by decide) (by decide)
    (by simp only [intoBuf, List.length_append, List.length_replicate]; omega)

/-- An alphanumeric field of the area, read from storage. -/
theorem area_str {a : List FVal} {m : Mem} (h : LkM03bAreaRel a m) {i o n : Nat}
    (hi : i < LkM03bArea.fields.length) (hf : (LkM03bArea.fields.getD i default).desc = ⟨o, n, .alnum false⟩) :
    m.read o n = strOf (a.getD i default) ∧ (strOf (a.getD i default)).length = n := by
  have ho : (LkM03bArea.fields.getD i default).desc.off = o := by rw [hf]
  have hn : (LkM03bArea.fields.getD i default).desc.len = n := by rw [hf]
  have hk : (LkM03bArea.fields.getD i default).desc.kind = .alnum false := by rw [hf]
  have e := at_getD h.2 hi
  obtain ⟨e1, e2⟩ := encode_str (valid_getD h.1 hi) ⟨false, hk⟩
  rw [ho, hn, e1] at e
  rw [hn] at e2
  exact ⟨e, e2⟩

theorem area_dd {a : List FVal} {m : Mem} (h : LkM03bAreaRel a m) : m.read 1208 8 = aDd a :=
  (area_str h (i := 0) (o := 1208) (n := 8) (by decide) (by decide)).1

theorem area_op {a : List FVal} {m : Mem} (h : LkM03bAreaRel a m) : m.read 1216 1 = [aOp a] := by
  obtain ⟨e, hl⟩ := area_str h (i := 1) (o := 1216) (n := 1) (by decide) (by decide)
  rw [e]
  unfold aOp
  generalize strOf (a.getD 1 default) = l at hl ⊢
  match l, hl with
  | [_], _ => rfl
  | [], h => simp at h
  | _ :: _ :: _, h => simp only [List.length_cons] at h; omega

theorem area_key {a : List FVal} {m : Mem} (h : LkM03bAreaRel a m) : m.read 1219 25 = aKey a ∧ (aKey a).length = 25 :=
  area_str h (i := 3) (o := 1219) (n := 25) (by decide) (by decide)

theorem area_keyln {a : List FVal} {m : Mem} (h : LkM03bAreaRel a m) :
    decodeNum {} CardDemo.Cbstm03b.LK_M03B_KEY_LN.fmt (m.read 1244 4) = some (aKeyLn a) := by
  have hk : (LkM03bArea.fields.getD 4 default).desc.kind = .num CardDemo.Cbstm03b.LK_M03B_KEY_LN.fmt := by decide
  have e := at_getD h.2 (i := 4) (by decide)
  obtain ⟨hv, hh, hd, hd18⟩ := val_num (valid_getD h.1 (i := 4) (by decide)) hk
  rw [show (LkM03bArea.fields.getD 4 default).desc.off = 1244 by decide,
    show (LkM03bArea.fields.getD 4 default).desc.len = 4 by decide, hv] at e
  rw [e]
  simp only [Field.encode, hk]
  exact decodeNum_encodeNum {} _ _ hd hd18 hh

/-! ## One call for one file -/

/-- After a call for one file: its record area holds `rec`, its status item the code points `st`, the area `a`,
and the frame is kept. -/
def After (S T : Schema) (ao so : Nat) (m m' : Mem) (rec : List FVal) (st : List Nat) (a : List FVal) : Prop :=
  S.At m' rec ∧ T.BytesAt m' (st.map ebcdicOfLatin1) ∧ LkM03bAreaRel a m' ∧ Frame ao S.len so m m'

/-- coblean's outcome `r` of a call for one file (storage, file) against the model's `q` (file, record area,
status item, area). -/
def Glued (S T : Schema) (ao so : Nat) (m : Mem) (r : Mem × FileSt)
    (q : FileM × List FVal × List Nat × List FVal) : Prop :=
  FileRel S q.1 r.2 ∧ S.Valid q.2.1 ∧ After S T ao so m r.1 q.2.1 q.2.2.1 q.2.2.2

/-- A status stored by `retCode`. -/
theorem ret_glue {S T : Schema} {ao so : Nat} (sl : Slot S T ao so) {m : Mem} (hm : m.size = 2248)
    {rec a : List FVal} (hr : S.At m rec) (ha : LkM03bAreaRel a m) (c : Nat) :
    After S T ao so m (retCode m so c) rec (stCp c) (setRc a (stBytes c)) := by
  have hl : (stBytes c).length = 2 := rfl
  have hso := sl.stPos
  have hb := sl.below
  have hT := sl.stLen
  unfold retCode
  refine ⟨at_same sl.atOff (same_trans (same_write (by omega)) (same_write (by omega))) hr, ?_, ?_, ?_⟩
  · rw [stCp_map]
    exact bytesAt_same sl.stOff (same_write (by omega))
      (bytesAt_write sl.stOff (by rw [hl, hT]) (by rw [hT, hm]; omega))
  · exact area_rc (by simp [hm]) (area_write_out ha (by omega)) hl
  · exact frame_trans (frame_write (by omega) (by omega) (Or.inr (Or.inr ⟨Nat.le_refl _, by omega⟩)))
      (frame_write (by omega) (by omega) (Or.inl (by omega)))

/-- A record read: written to the record area, its status stored, the record copied into the buffer. -/
theorem read_glue {S T : Schema} {ao so : Nat} (sl : Slot S T ao so) {m : Mem} (hm : m.size = 2248)
    {r a : List FVal} (hv : S.Valid r) (ha : LkM03bAreaRel a m) (c : Nat) :
    After S T ao so m ((retCode (m.write ao (S.encode r)) so c).write 1248 (intoBuf (S.encode r))) r (stCp c)
      (setFldt (setRc a (stBytes c)) (S.encode r)) := by
  have hle := Schema.length_encode sl.contig hv
  have hso := sl.stPos
  have hb := sl.below
  have hT := sl.stLen
  have h1k := sl.le1000
  have a1 : LkM03bAreaRel a (m.write ao (S.encode r)) := area_write_out ha (by omega)
  have r1 : S.At (m.write ao (S.encode r)) r := at_write_encode sl.contig sl.atOff hv (by omega)
  obtain ⟨g1, g2, g3, g4⟩ := ret_glue sl (by simp [hm]) r1 a1 c
  refine ⟨at_same sl.atOff (same_write (by omega)) g1, bytesAt_same sl.stOff (same_write (by omega)) g2,
    area_fldt (by simp [retCode, hm]) g3 (by omega), frame_trans (frame_write (by omega) (by omega) ?_)
      (frame_trans g4 (frame_write (by omega) (by omega) (Or.inl (by omega))))⟩
  exact Or.inr (Or.inl ⟨Nat.le_refl _, by omega⟩)

/-- Any other operation: the file's status moved into the return code. -/
theorem other_glue {S T : Schema} {ao so : Nat} (sl : Slot S T ao so) {m : Mem} (hm : m.size = 2248)
    {rec a : List FVal} {st : List Nat} (hr : S.At m rec) (hs : T.BytesAt m (st.map ebcdicOfLatin1))
    (ha : LkM03bAreaRel a m) :
    After S T ao so m (m.write 1217 (m.read so 2)) rec st (setRc a (st.map ebcdicOfLatin1)) := by
  have hso := sl.stPos
  have hb := sl.below
  have hT := sl.stLen
  have hl : (st.map ebcdicOfLatin1).length = 2 := by rw [hs.1, hT]
  rw [sl.stRead m _ hs]
  exact ⟨at_same sl.atOff (same_write (by omega)) hr, bytesAt_same sl.stOff (same_write (by omega)) hs,
    area_rc hm ha hl, frame_write (by omega) (by omega) (Or.inl (by omega))⟩

/-- **A sequentially read file** (TRNXFILE, XREFFILE): coblean's `seqCall` against the model's `seqStep`. -/
theorem seq_glue {S T : Schema} {ao so id : Nat} (sl : Slot S T ao so) {env : Env} {oe : Option Nat}
    (hoe : oe = env.openError id .input) {m : Mem} (hm : m.size = 2248) (op : UInt8) {fM : FileM}
    {f : FileSt} {rec : List FVal} {st : List Nat} {a : List FVal} (hf : FileRel S fM f) (hv : S.Valid rec)
    (hr : S.At m rec) (hs : T.BytesAt m (st.map ebcdicOfLatin1)) (ha : LkM03bAreaRel a m) :
    Glued S T ao so m (seqCall env id ao so op m f) (seqStep oe S op fM rec st a) := by
  unfold seqCall seqStep
  by_cases hO : op = opOpen
  · rw [ite_eq_left hO, ite_eq_left hO]
    obtain ⟨hc, hf'⟩ := openIn_rel hf hoe
    generalize openIn env id f = x at hc hf' ⊢
    generalize openM oe fM = y at hc hf' ⊢
    obtain ⟨c, f'⟩ := x
    obtain ⟨c', fM'⟩ := y
    obtain rfl : c = c' := hc
    exact ⟨hf', hv, ret_glue sl hm hr ha c⟩
  rw [ite_eq_right hO, ite_eq_right hO]
  by_cases hR : op = opRead
  · rw [ite_eq_left hR, ite_eq_left hR]
    obtain ⟨hc, hf', hr', hval⟩ := seqRead_rel (S := S) hf
    generalize seqRead f = x at hc hf' hr' ⊢
    generalize seqReadM fM = y at hc hf' hr' hval ⊢
    obtain ⟨c, f', _ | r⟩ := x <;> obtain ⟨c', fM', _ | r'⟩ := y
    · obtain rfl : c = c' := hc
      exact ⟨hf', hv, ret_glue sl hm hr ha c⟩
    · simp at hr'
    · simp at hr'
    · obtain rfl : c = c' := hc
      obtain rfl : r = S.encode r' := Option.some.inj hr'
      exact ⟨hf', hval r' rfl, read_glue sl hm (hval r' rfl) ha c⟩
  rw [ite_eq_right hR, ite_eq_right hR]
  by_cases hC : op = opClose
  · rw [ite_eq_left hC, ite_eq_left hC]
    obtain ⟨hc, hf'⟩ := closeF_rel (S := S) hf
    generalize closeF f = x at hc hf' ⊢
    generalize closeM fM = y at hc hf' ⊢
    obtain ⟨c, f'⟩ := x
    obtain ⟨c', fM'⟩ := y
    obtain rfl : c = c' := hc
    exact ⟨hf', hv, ret_glue sl hm hr ha c⟩
  rw [ite_eq_right hC, ite_eq_right hC]
  exact ⟨hf, hv, other_glue sl hm hr hs ha⟩

/-- **A file read by key** (CUSTFILE, ACCTFILE): coblean's `keyCall` against the model's `keyStep`, when the key
bytes `key` stored in the record area are the model's `setKey` and match records as the model's `p` does. -/
theorem key_glue {S T : Schema} {ao so id : Nat} (sl : Slot S T ao so) {env : Env} {oe : Option Nat}
    (hoe : oe = env.openError id .input) {m : Mem} (hm : m.size = 2248) (op : UInt8) (kl : Nat)
    (key : List UInt8) (setKey : List FVal → List FVal) (p : List FVal → Bool) {fM : FileM} {f : FileSt}
    {rec : List FVal} {st : List Nat} {a : List FVal} (hkl : key.length ≤ S.len)
    (hkey : op = opReadK → S.Valid (setKey rec) ∧ S.At (m.write ao key) (setKey rec))
    (hp : op = opReadK → ∀ x ∈ fM.recs, (Sem.keyOf { off := 0, len := kl } (S.encode x) == key) = p x)
    (hf : FileRel S fM f) (hv : S.Valid rec) (hr : S.At m rec) (hs : T.BytesAt m (st.map ebcdicOfLatin1))
    (ha : LkM03bAreaRel a m) :
    Glued S T ao so m (keyCall env id ao so kl key op m f) (keyStep oe S setKey p op fM rec st a) := by
  have hso := sl.stPos
  have hb := sl.below
  have m1s : (m.write ao key).size = 2248 := by simp [hm]
  have a1 : LkM03bAreaRel a (m.write ao key) := area_write_out ha (by omega)
  have fr1 : Frame ao S.len so m (m.write ao key) :=
    frame_write (by omega) (by omega) (Or.inr (Or.inl ⟨Nat.le_refl _, by omega⟩))
  unfold keyCall keyStep
  by_cases hO : op = opOpen
  · rw [ite_eq_left hO, ite_eq_left hO]
    obtain ⟨hc, hf'⟩ := openIn_rel hf hoe
    generalize openIn env id f = x at hc hf' ⊢
    generalize openM oe fM = y at hc hf' ⊢
    obtain ⟨c, f'⟩ := x
    obtain ⟨c', fM'⟩ := y
    obtain rfl : c = c' := hc
    exact ⟨hf', hv, ret_glue sl hm hr ha c⟩
  rw [ite_eq_right hO, ite_eq_right hO]
  by_cases hRK : op = opReadK
  · rw [ite_eq_left hRK, ite_eq_left hRK]
    obtain ⟨hvk, hrk⟩ := hkey hRK
    obtain ⟨hc, hf', hr', hval⟩ := keyRead_rel (kl := kl) (key := key) hf (hp hRK)
    generalize keyRead kl key f = x at hc hf' hr' ⊢
    generalize keyReadM p fM = y at hc hf' hr' hval ⊢
    obtain ⟨c, f', _ | r⟩ := x <;> obtain ⟨c', fM', _ | r'⟩ := y
    · obtain rfl : c = c' := hc
      obtain ⟨g1, g2, g3, g4⟩ := ret_glue sl m1s hrk a1 c
      exact ⟨hf', hvk, g1, g2, g3, frame_trans fr1 g4⟩
    · simp at hr'
    · simp at hr'
    · obtain rfl : c = c' := hc
      obtain rfl : r = S.encode r' := Option.some.inj hr'
      obtain ⟨g1, g2, g3, g4⟩ := read_glue sl m1s (hval r' rfl) a1 c
      exact ⟨hf', hval r' rfl, g1, g2, g3, frame_trans fr1 g4⟩
  rw [ite_eq_right hRK, ite_eq_right hRK]
  by_cases hC : op = opClose
  · rw [ite_eq_left hC, ite_eq_left hC]
    obtain ⟨hc, hf'⟩ := closeF_rel (S := S) hf
    generalize closeF f = x at hc hf' ⊢
    generalize closeM fM = y at hc hf' ⊢
    obtain ⟨c, f'⟩ := x
    obtain ⟨c', fM'⟩ := y
    obtain rfl : c = c' := hc
    exact ⟨hf', hv, ret_glue sl hm hr ha c⟩
  rw [ite_eq_right hC, ite_eq_right hC]
  exact ⟨hf, hv, other_glue sl hm hr hs ha⟩

/-! ## The keys -/

theorem custKeyOf_length (m : Mem) (k : Int) : (custKeyOf m k).length = 9 := by
  unfold custKeyOf
  simp only [List.length_take, List.length_append, Mem.length_read, List.length_replicate]
  omega

theorem custKeyOf_eq {a : List FVal} {m : Mem} (h : LkM03bAreaRel a m) {k : Int} (hk : k.toNat ≤ 25) :
    custKeyOf m k = Model.custKey (aKey a) k.toNat := by
  unfold custKeyOf Model.custKey
  rw [read_take (o := 1219) hk, (area_key h).1]

theorem acctKeyOf_length (v : Int) : (acctKeyOf v).length = 11 := by
  unfold acctKeyOf
  rw [length_encodeNum {} _ _ (by decide)]
  decide

theorem acctVal_eq {a : List FVal} {m : Mem} (h : LkM03bAreaRel a m) {k v : Int} (hk : k.toNat ≤ 25)
    (hv : decodeNum {} { digits := k.toNat } (m.read 1219 k.toNat) = some v) :
    acctVal (aKey a) k.toNat = (Sem.fitNum {} { digits := 11 } v).2 := by
  unfold acctVal
  rw [← (area_key h).1, ← read_take hk, hv]
  rfl

theorem cust_fmt : (FdCustfileRec.fields.getD 0 default).desc = ⟨400, 9, .alnum false⟩ := by decide

theorem acct_fmt : (FdAcctfileRec.fields.getD 0 default).desc = ⟨900, 11, .num { digits := 11 }⟩ := by decide

theorem cust_keyOf {x : List FVal} (hx : FdCustfileRec.Valid x) :
    Sem.keyOf { off := 0, len := 9 } (FdCustfileRec.encode x) = strOf (x.getD 0 default) := by
  have hb := Schema.bytes_encode_getD (by decide) hx 0 (by decide)
  have hr : (FdCustfileRec.fields.getD 0 default).roff = 0 := by decide
  have hn : (FdCustfileRec.fields.getD 0 default).desc.len = 9 := by rw [cust_fmt]
  have hk : (FdCustfileRec.fields.getD 0 default).desc.kind = .alnum false := by rw [cust_fmt]
  unfold Field.bytes at hb
  rw [hr, hn, (encode_str (valid_getD hx (by decide)) ⟨false, hk⟩).1] at hb
  exact hb

theorem acct_keyOf {x : List FVal} (hx : FdAcctfileRec.Valid x) :
    Sem.keyOf { off := 0, len := 11 } (FdAcctfileRec.encode x) =
        encodeNum {} { digits := 11 } (numOf (x.getD 0 default)) ∧
      NumFmt.Holds {} { digits := 11 } (numOf (x.getD 0 default)) := by
  have hb := Schema.bytes_encode_getD (by decide) hx 0 (by decide)
  have hr : (FdAcctfileRec.fields.getD 0 default).roff = 0 := by decide
  have hn : (FdAcctfileRec.fields.getD 0 default).desc.len = 11 := by rw [acct_fmt]
  have hk : (FdAcctfileRec.fields.getD 0 default).desc.kind = .num { digits := 11 } := by rw [acct_fmt]
  obtain ⟨hv, hh, -, -⟩ := val_num (valid_getD hx (by decide)) hk
  unfold Field.bytes at hb
  rw [hr, hn, hv] at hb
  refine ⟨?_, hh⟩
  show ((FdAcctfileRec.encode x).drop 0).take 11 = _
  rw [hb]
  simp only [Field.encode, hk]

theorem cust_set_key {rec : List FVal} {m : Mem} (hm : m.size = 2248) (hv : FdCustfileRec.Valid rec)
    (hr : FdCustfileRec.At m rec) {key : List UInt8} (hl : key.length = 9) :
    FdCustfileRec.Valid (rec.set 0 (.str key)) ∧ FdCustfileRec.At (m.write 400 key) (rec.set 0 (.str key)) := by
  have ho : (FdCustfileRec.fields.getD 0 default).desc.off = 400 := by rw [cust_fmt]
  have hn : (FdCustfileRec.fields.getD 0 default).desc.len = 9 := by rw [cust_fmt]
  have hk : (FdCustfileRec.fields.getD 0 default).desc.kind = .alnum false := by rw [cust_fmt]
  refine ⟨valid_set hv (by decide) ⟨⟨false, hk⟩, by rw [hl, hn]⟩, ?_⟩
  have := at_write_field hr (i := 0) (by decide) (w := .str key) (bs := key) rfl (by rw [hl, hn]) (by decide)
    (by rw [ho, hn, hm]; decide)
  rwa [ho] at this

theorem acct_set_key {rec : List FVal} {m : Mem} (hm : m.size = 2248) (hv : FdAcctfileRec.Valid rec)
    (hr : FdAcctfileRec.At m rec) {w : Int} (hw : NumFmt.Holds {} { digits := 11 } w) :
    FdAcctfileRec.Valid (rec.set 0 (.num w)) ∧
      FdAcctfileRec.At (m.write 900 (encodeNum {} { digits := 11 } w)) (rec.set 0 (.num w)) := by
  have ho : (FdAcctfileRec.fields.getD 0 default).desc.off = 900 := by rw [acct_fmt]
  have hn : (FdAcctfileRec.fields.getD 0 default).desc.len = 11 := by rw [acct_fmt]
  have hk : (FdAcctfileRec.fields.getD 0 default).desc.kind = .num { digits := 11 } := by rw [acct_fmt]
  have hl : (encodeNum {} { digits := 11 } w).length = 11 := by
    rw [length_encodeNum {} _ w (by decide)]; decide
  refine ⟨valid_set hv (by decide) ⟨{ digits := 11 }, hk, by decide, by decide, hw, by rw [hn]; decide⟩, ?_⟩
  have := at_write_field hr (i := 0) (by decide) (w := .num w) (bs := encodeNum {} { digits := 11 } w)
    (by simp only [Field.encode, hk])
    (by rw [hl, hn]) (by decide) (by rw [ho, hn, hm]; decide)
  rwa [ho] at this

/-! ## One call -/

/-- One file's part of `StateRel`: the file, its record area, its status item. -/
def Piece (S T : Schema) (fM : FileM) (rec : List FVal) (st : List Nat) (s : FileSt) (m : Mem) : Prop :=
  FileRel S fM s ∧ S.Valid rec ∧ S.At m rec ∧ T.BytesAt m (st.map ebcdicOfLatin1)

theorem stateRel_st0 {st : StM} {m : Mem} {fs : Files} :
    StateRel st (st0 m fs) ↔
      Piece FdTrnxfileRec TrnxfileStatus st.trnx st.trnxRec st.trnxSt fs.trnx m ∧
      Piece FdXreffileRec XreffileStatus st.xref st.xrefRec st.xrefSt fs.xref m ∧
      Piece FdCustfileRec CustfileStatus st.cust st.custRec st.custSt fs.cust m ∧
      Piece FdAcctfileRec AcctfileStatus st.acct st.acctRec st.acctSt fs.acct m := by
  constructor
  · rintro ⟨⟨s1, e1, h1⟩, ⟨s2, e2, h2⟩, ⟨s3, e3, h3⟩, ⟨s4, e4, h4⟩, v1, a1, v2, a2, v3, a3, v4, a4, b1, b2, b3, b4⟩
    cases e1; cases e2; cases e3; cases e4
    exact ⟨⟨h1, v1, a1, b1⟩, ⟨h2, v2, a2, b2⟩, ⟨h3, v3, a3, b3⟩, ⟨h4, v4, a4, b4⟩⟩
  · rintro ⟨⟨h1, v1, a1, b1⟩, ⟨h2, v2, a2, b2⟩, ⟨h3, v3, a3, b3⟩, ⟨h4, v4, a4, b4⟩⟩
    exact ⟨⟨_, rfl, h1⟩, ⟨_, rfl, h2⟩, ⟨_, rfl, h3⟩, ⟨_, rfl, h4⟩, v1, a1, v2, a2, v3, a3, v4, a4, b1, b2, b3, b4⟩

theorem piece_same {S T : Schema} {ao so : Nat} (sl : Slot S T ao so) {fM : FileM} {rec : List FVal}
    {st : List Nat} {s : FileSt} {m m' : Mem} (h1 : MemSame m m' ao (ao + S.len)) (h2 : MemSame m m' so (so + 2))
    (h : Piece S T fM rec st s m) : Piece S T fM rec st s m' :=
  ⟨h.1, h.2.1, at_same sl.atOff h1 h.2.2.1, bytesAt_same sl.stOff (by rw [sl.stLen]; exact h2) h.2.2.2⟩

theorem recs_len {S : Schema} (hc : S.Contig) {fM : FileM} {s : FileSt} (h : FileRel S fM s) :
    ∀ r ∈ s.recs, r.length = S.len := by
  intro r hr
  rw [h.2.2.1, List.mem_map] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  exact Schema.length_encode hc (h.2.1 x hx)

/-- **One call of CBSTM03B, the model against `call3b`.** For a state, an area and an environment related to
coblean's, under the hypotheses of `cbstm03b_call` on the key, the model's state and area after the call are
related to `call3b`'s storage and files. -/
theorem call_glue (env : Env) (m : Mem) (hm : m.size = 2248) (fs : Files) (k v : Int)
    (hK : m.read 1216 1 = [opReadK] → (m.read 1208 8 = ddCust ∨ m.read 1208 8 = ddAcct) →
      decodeNum {} CardDemo.Cbstm03b.LK_M03B_KEY_LN.fmt (m.read 1244 4) = some k ∧ 1 ≤ k ∧ k ≤ 25)
    (hA : m.read 1216 1 = [opReadK] → m.read 1208 8 = ddAcct →
      decodeNum {} { digits := k.toNat } (m.read 1219 k.toNat) = some v)
    (oe : OpenErrs) (st : StM) (a : List FVal) (hE : EnvRel oe env) (hS : StateRel st (st0 m fs))
    (hR : LkM03bAreaRel a m) :
    StateRel (Model.call oe st a).1 (st0 (call3b env m fs (custKeyOf m k) (acctKeyOf v)).1
        (call3b env m fs (custKeyOf m k) (acctKeyOf v)).2) ∧
      LkM03bAreaRel (Model.call oe st a).2 (call3b env m fs (custKeyOf m k) (acctKeyOf v)).1 := by
  obtain ⟨p1, p2, p3, p4⟩ := stateRel_st0.1 hS
  have hdd := area_dd hR
  have hop := area_op hR
  have hop' : (m.read 1216 1).headD 0 = aOp a := by rw [hop]; rfl
  have hk : aOp a = opReadK → (aDd a = ddCust ∨ aDd a = ddAcct) → k = aKeyLn a ∧ 1 ≤ k ∧ k ≤ 25 := by
    intro ho hd
    obtain ⟨h1, h2, h3⟩ := hK (by rw [hop, ho]) (by rw [hdd]; exact hd)
    rw [area_keyln hR] at h1
    exact ⟨(Option.some.inj h1).symm, h2, h3⟩
  simp only [Model.call, call3b, hdd, hop']
  by_cases hT : aDd a = ddTrnx
  · rw [ite_eq_left hT, ite_eq_left hT]
    have hoe : oe 1 = env.openError 1 .input := hE 0 (by decide)
    have g := seq_glue slotTrnx hoe hm (aOp a) p1.1 p1.2.1 p1.2.2.1 p1.2.2.2 hR
    generalize seqCall env 1 0 1200 (aOp a) m fs.trnx = res at g ⊢
    obtain ⟨m', f'⟩ := res
    obtain ⟨g1, g2, g3, g4, g5, fr⟩ := g
    exact ⟨stateRel_st0.2 ⟨⟨g1, g2, g3, g4⟩,
      piece_same slotXref (frame_same fr (by decide)) (frame_same fr (by decide)) p2,
      piece_same slotCust (frame_same fr (by decide)) (frame_same fr (by decide)) p3,
      piece_same slotAcct (frame_same fr (by decide)) (frame_same fr (by decide)) p4⟩, g5⟩
  rw [ite_eq_right hT, ite_eq_right hT]
  by_cases hX : aDd a = ddXref
  · rw [ite_eq_left hX, ite_eq_left hX]
    have hoe : oe 2 = env.openError 2 .input := hE 1 (by decide)
    have g := seq_glue slotXref hoe hm (aOp a) p2.1 p2.2.1 p2.2.2.1 p2.2.2.2 hR
    generalize seqCall env 2 350 1202 (aOp a) m fs.xref = res at g ⊢
    obtain ⟨m', f'⟩ := res
    obtain ⟨g1, g2, g3, g4, g5, fr⟩ := g
    exact ⟨stateRel_st0.2 ⟨piece_same slotTrnx (frame_same fr (by decide)) (frame_same fr (by decide)) p1,
      ⟨g1, g2, g3, g4⟩,
      piece_same slotCust (frame_same fr (by decide)) (frame_same fr (by decide)) p3,
      piece_same slotAcct (frame_same fr (by decide)) (frame_same fr (by decide)) p4⟩, g5⟩
  rw [ite_eq_right hX, ite_eq_right hX]
  by_cases hC : aDd a = ddCust
  · rw [ite_eq_left hC, ite_eq_left hC]
    have hoe : oe 3 = env.openError 3 .input := hE 2 (by decide)
    have ek : aOp a = opReadK → custKeyOf m k = Model.custKey (aKey a) (aKeyLn a).toNat := fun ho => by
      obtain ⟨h1, -, h3⟩ := hk ho (Or.inl hC)
      rw [← h1]
      exact custKeyOf_eq hR (by omega)
    have g := key_glue slotCust hoe hm (aOp a) 9 (custKeyOf m k)
      (fun rec => rec.set 0 (.str (Model.custKey (aKey a) (aKeyLn a).toNat)))
      (fun x => strOf (x.getD 0 default) == Model.custKey (aKey a) (aKeyLn a).toNat)
      (by rw [custKeyOf_length]; decide)
      (fun ho => by rw [← ek ho]; exact cust_set_key hm p3.2.1 p3.2.2.1 (custKeyOf_length m k))
      (fun ho x hx => by rw [cust_keyOf (p3.1.2.1 x hx), ek ho])
      p3.1 p3.2.1 p3.2.2.1 p3.2.2.2 hR
    generalize keyCall env 3 400 1204 9 (custKeyOf m k) (aOp a) m fs.cust = res at g ⊢
    obtain ⟨m', f'⟩ := res
    obtain ⟨g1, g2, g3, g4, g5, fr⟩ := g
    exact ⟨stateRel_st0.2 ⟨piece_same slotTrnx (frame_same fr (by decide)) (frame_same fr (by decide)) p1,
      piece_same slotXref (frame_same fr (by decide)) (frame_same fr (by decide)) p2,
      ⟨g1, g2, g3, g4⟩,
      piece_same slotAcct (frame_same fr (by decide)) (frame_same fr (by decide)) p4⟩, g5⟩
  rw [ite_eq_right hC, ite_eq_right hC]
  by_cases hAc : aDd a = ddAcct
  · rw [ite_eq_left hAc, ite_eq_left hAc]
    have hoe : oe 4 = env.openError 4 .input := hE 3 (by decide)
    have ev : aOp a = opReadK → acctVal (aKey a) (aKeyLn a).toNat = (Sem.fitNum {} { digits := 11 } v).2 :=
      fun ho => by
        obtain ⟨h1, -, h3⟩ := hk ho (Or.inr hAc)
        rw [← h1]
        exact acctVal_eq hR (by omega) (hA (by rw [hop, ho]) (by rw [hdd]; exact hAc))
    have g := key_glue slotAcct hoe hm (aOp a) 11 (acctKeyOf v)
      (fun rec => rec.set 0 (.num (acctVal (aKey a) (aKeyLn a).toNat)))
      (fun x => numOf (x.getD 0 default) == acctVal (aKey a) (aKeyLn a).toNat)
      (by rw [acctKeyOf_length]; decide)
      (fun ho => by rw [ev ho]; exact acct_set_key hm p4.2.1 p4.2.2.1 (fitNum_holds {} _ v))
      (fun ho x hx => by
        obtain ⟨e, hh⟩ := acct_keyOf (p4.1.2.1 x hx)
        rw [e, ev ho]
        exact encodeNum_beq (by decide) (by decide) hh (fitNum_holds {} _ v))
      p4.1 p4.2.1 p4.2.2.1 p4.2.2.2 hR
    generalize keyCall env 4 900 1206 11 (acctKeyOf v) (aOp a) m fs.acct = res at g ⊢
    obtain ⟨m', f'⟩ := res
    obtain ⟨g1, g2, g3, g4, g5, fr⟩ := g
    exact ⟨stateRel_st0.2 ⟨piece_same slotTrnx (frame_same fr (by decide)) (frame_same fr (by decide)) p1,
      piece_same slotXref (frame_same fr (by decide)) (frame_same fr (by decide)) p2,
      piece_same slotCust (frame_same fr (by decide)) (frame_same fr (by decide)) p3,
      ⟨g1, g2, g3, g4⟩⟩, g5⟩
  rw [ite_eq_right hAc, ite_eq_right hAc]
  exact ⟨hS, hR⟩

/-- **One call of CBSTM03B, the model against coblean's interpreter**: the run ends with `GOBACK`, and the model's
state and area after the call are related to the run's storage and files (`call_glue` and `cbstm03b_call`). -/
theorem call_run (env : Env) (m : Mem) (hm : m.size = 2248) (fs : Files) (k v : Int)
    (hK : m.read 1216 1 = [opReadK] → (m.read 1208 8 = ddCust ∨ m.read 1208 8 = ddAcct) →
      decodeNum {} CardDemo.Cbstm03b.LK_M03B_KEY_LN.fmt (m.read 1244 4) = some k ∧ 1 ≤ k ∧ k ≤ 25)
    (hA : m.read 1216 1 = [opReadK] → m.read 1208 8 = ddAcct →
      decodeNum {} { digits := k.toNat } (m.read 1219 k.toNat) = some v)
    (oe : OpenErrs) (st : StM) (a : List FVal) (hE : EnvRel oe env) (hS : StateRel st (st0 m fs))
    (hR : LkM03bAreaRel a m) :
    (CardDemo.Cbstm03b.run env 50 (st0 m fs)).1 = .stop .goback ∧
      StateRel (Model.call oe st a).1 (CardDemo.Cbstm03b.run env 50 (st0 m fs)).2 ∧
      LkM03bAreaRel (Model.call oe st a).2 (CardDemo.Cbstm03b.run env 50 (st0 m fs)).2.mem := by
  obtain ⟨p1, p2, p3, p4⟩ := stateRel_st0.1 hS
  rw [CardDemo.Cbstm03b.cbstm03b_call env m hm fs k v
    (fun r hr => (recs_len slotTrnx.contig p1.1 r hr).trans (by decide))
    (fun r hr => (recs_len slotXref.contig p2.1 r hr).trans (by decide))
    (fun r hr => (recs_len slotCust.contig p3.1 r hr).trans (by decide))
    (fun r hr => (recs_len slotAcct.contig p4.1 r hr).trans (by decide)) hK hA]
  exact ⟨rfl, call_glue env m hm fs k v hK hA oe st a hE hS hR⟩

/-! ## What a translation's proof may assume

The Java contract (`JavaProof.runSpec`) assumes valid values (`ValidSt`, a valid area) and the key that
`cbstm03b_call`'s hypotheses and the statements' domain give (`KeyOk`); both follow from the generated statement's
hypotheses (`validSt_of_stateRel`, `keyOk_of`). -/

/-- The state's values are valid: the files' records and the FD record areas; two-character statuses. -/
def ValidSt (st : StM) : Prop :=
  (∀ r ∈ st.trnx.recs, FdTrnxfileRec.Valid r) ∧ (∀ r ∈ st.xref.recs, FdXreffileRec.Valid r) ∧
    (∀ r ∈ st.cust.recs, FdCustfileRec.Valid r) ∧ (∀ r ∈ st.acct.recs, FdAcctfileRec.Valid r) ∧
    FdTrnxfileRec.Valid st.trnxRec ∧ FdXreffileRec.Valid st.xrefRec ∧ FdCustfileRec.Valid st.custRec ∧
    FdAcctfileRec.Valid st.acctRec ∧
    st.trnxSt.length = 2 ∧ st.xrefSt.length = 2 ∧ st.custSt.length = 2 ∧ st.acctSt.length = 2

/-- The key of a keyed `READ` as `cbstm03b_call` and the statements' domain (`Domain.lean`) assume it: a key length
in `1 ..= 25` and, for ACCTFILE, a key whose first `k` bytes decode as a number and are CP037 digits. -/
def KeyOk (a : List FVal) : Prop :=
  (aOp a = opReadK → (aDd a = ddCust ∨ aDd a = ddAcct) → 1 ≤ aKeyLn a ∧ aKeyLn a ≤ 25) ∧
    (aOp a = opReadK → aDd a = ddAcct →
      (∃ v, decodeNum {} { digits := (aKeyLn a).toNat } ((aKey a).take (aKeyLn a).toNat) = some v) ∧
      ∀ b ∈ (aKey a).take (aKeyLn a).toNat, 240 ≤ b ∧ b ≤ 249)

theorem validSt_of_stateRel {st : StM} {cs : Cobol.State} (h : StateRel st cs) : ValidSt st := by
  obtain ⟨⟨_, -, f1⟩, ⟨_, -, f2⟩, ⟨_, -, f3⟩, ⟨_, -, f4⟩, v1, -, v2, -, v3, -, v4, -, b1, b2, b3, b4⟩ := h
  have l1 := b1.1
  have l2 := b2.1
  have l3 := b3.1
  have l4 := b4.1
  rw [List.length_map] at l1 l2 l3 l4
  exact ⟨f1.2.1, f2.2.1, f3.2.1, f4.2.1, v1, v2, v3, v4, l1.trans (by decide), l2.trans (by decide),
    l3.trans (by decide), l4.trans (by decide)⟩

theorem keyOk_of {a : List FVal} {m : Mem} (hR : LkM03bAreaRel a m) {k v : Int}
    (hK : m.read 1216 1 = [opReadK] → (m.read 1208 8 = ddCust ∨ m.read 1208 8 = ddAcct) →
      decodeNum {} CardDemo.Cbstm03b.LK_M03B_KEY_LN.fmt (m.read 1244 4) = some k ∧ 1 ≤ k ∧ k ≤ 25)
    (hA : m.read 1216 1 = [opReadK] → m.read 1208 8 = ddAcct →
      decodeNum {} { digits := k.toNat } (m.read 1219 k.toNat) = some v)
    (hD : m.read 1216 1 = [opReadK] → m.read 1208 8 = ddAcct → ∀ b ∈ m.read 1219 k.toNat, 240 ≤ b ∧ b ≤ 249) :
    KeyOk a := by
  have hop := area_op hR
  have hdd := area_dd hR
  have hk : aOp a = opReadK → (aDd a = ddCust ∨ aDd a = ddAcct) → k = aKeyLn a ∧ 1 ≤ k ∧ k ≤ 25 := by
    intro ho hd
    obtain ⟨h1, h2, h3⟩ := hK (by rw [hop, ho]) (by rw [hdd]; exact hd)
    rw [area_keyln hR] at h1
    exact ⟨(Option.some.inj h1).symm, h2, h3⟩
  refine ⟨fun ho hd => ?_, fun ho hd => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hk ho hd
    rw [← h1]
    exact ⟨h2, h3⟩
  · obtain ⟨h1, -, h3⟩ := hk ho (Or.inr hd)
    rw [← h1, ← (area_key hR).1, ← read_take (o := 1219) (n := 25) (by omega)]
    exact ⟨⟨v, hA (by rw [hop, ho]) (by rw [hdd]; exact hd)⟩, hD (by rw [hop, ho]) (by rw [hdd]; exact hd)⟩

end EquivLean.Modernize.Cbstm03b.Glue
