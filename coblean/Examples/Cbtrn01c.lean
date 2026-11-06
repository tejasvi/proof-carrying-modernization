/-
# CardDemo CBTRN01C (daily transaction verification), extracted by the front end

`examples/carddemo/cbtrn01c.ir.json` is the output of `tools/cobolfe` on `app/cbl/CBTRN01C.cbl`
of AWS CardDemo, unchanged.  For each daily transaction the program displays the record, looks
up its card in the cross-reference file and, when found, the account in the account file, and
displays what it found.  The lookups are outside the loop's `IF END-OF-DAILY-TRANS-FILE = 'N'`:
after the end-of-file `READ` they run once more on the last record read, so the last
transaction's lookup messages are displayed twice.
-/
import Cobol
open Cobol

namespace CardDemo

cobol_program Cbtrn01c from "../examples/carddemo/cbtrn01c.ir.json"

namespace Cbtrn01c

def displays (st : State) : List (List UInt8) :=
  st.out.reverse.filterMap fun | .display bs => some bs | _ => none

/-- `START OF EXECUTION OF PROGRAM CBTRN01C` in EBCDIC. -/
def startMsg : List UInt8 := [226, 227, 193, 217, 227, 64, 214, 198, 64, 197, 231, 197, 195, 228, 227, 201, 214, 213, 64, 214, 198, 64, 215, 217, 214, 199, 217, 193, 212, 64, 195, 194, 227, 217, 213, 240, 241, 195]

/-- `END OF EXECUTION OF PROGRAM CBTRN01C` in EBCDIC. -/
def endMsg : List UInt8 := [197, 213, 196, 64, 214, 198, 64, 197, 231, 197, 195, 228, 227, 201, 214, 213, 64, 214, 198, 64, 215, 217, 214, 199, 217, 193, 212, 64, 195, 194, 227, 217, 213, 240, 241, 195]

/-- `SUCCESSFUL READ OF XREF` in EBCDIC. -/
def okXrefMsg : List UInt8 := [226, 228, 195, 195, 197, 226, 226, 198, 228, 211, 64, 217, 197, 193, 196, 64, 214, 198, 64, 231, 217, 197, 198]

/-- `CARD NUMBER: ` in EBCDIC. -/
def cardNumMsg : List UInt8 := [195, 193, 217, 196, 64, 213, 228, 212, 194, 197, 217, 122, 64]

/-- `ACCOUNT ID : ` in EBCDIC. -/
def acctIdMsg : List UInt8 := [193, 195, 195, 214, 228, 213, 227, 64, 201, 196, 64, 122, 64]

/-- `CUSTOMER ID: ` in EBCDIC. -/
def custIdMsg : List UInt8 := [195, 228, 226, 227, 214, 212, 197, 217, 64, 201, 196, 122, 64]

/-- `SUCCESSFUL READ OF ACCOUNT FILE` in EBCDIC. -/
def okAcctMsg : List UInt8 := [226, 228, 195, 195, 197, 226, 226, 198, 228, 211, 64, 217, 197, 193, 196, 64, 214, 198, 64, 193, 195, 195, 214, 228, 213, 227, 64, 198, 201, 211, 197]

/-- `INVALID CARD NUMBER FOR XREF` in EBCDIC. -/
def invCardMsg : List UInt8 := [201, 213, 229, 193, 211, 201, 196, 64, 195, 193, 217, 196, 64, 213, 228, 212, 194, 197, 217, 64, 198, 214, 217, 64, 231, 217, 197, 198]

/-- `CARD NUMBER ` in EBCDIC. -/
def cardMsg : List UInt8 := [195, 193, 217, 196, 64, 213, 228, 212, 194, 197, 217, 64]

/-- ` COULD NOT BE VERIFIED. SKIPPING TRANSACTION ID-` in EBCDIC. -/
def skipMsg : List UInt8 := [64, 195, 214, 228, 211, 196, 64, 213, 214, 227, 64, 194, 197, 64, 229, 197, 217, 201, 198, 201, 197, 196, 75, 64, 226, 210, 201, 215, 215, 201, 213, 199, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 201, 196, 96]

/-- `INVALID ACCOUNT NUMBER FOUND` in EBCDIC. -/
def invAcctMsg : List UInt8 := [201, 213, 229, 193, 211, 201, 196, 64, 193, 195, 195, 214, 228, 213, 227, 64, 213, 228, 212, 194, 197, 217, 64, 198, 214, 228, 213, 196]

/-- `ACCOUNT ` in EBCDIC. -/
def acctMsg : List UInt8 := [193, 195, 195, 214, 228, 213, 227, 64]

/-- ` NOT FOUND` in EBCDIC. -/
def notFoundMsg : List UInt8 := [64, 213, 214, 227, 64, 198, 214, 228, 213, 196]

theorem startMsg_eq : Codepage.encode037 "START OF EXECUTION OF PROGRAM CBTRN01C" = some startMsg := by decide +kernel
theorem endMsg_eq : Codepage.encode037 "END OF EXECUTION OF PROGRAM CBTRN01C" = some endMsg := by decide +kernel
theorem okXrefMsg_eq : Codepage.encode037 "SUCCESSFUL READ OF XREF" = some okXrefMsg := by decide +kernel
theorem cardNumMsg_eq : Codepage.encode037 "CARD NUMBER: " = some cardNumMsg := by decide +kernel
theorem acctIdMsg_eq : Codepage.encode037 "ACCOUNT ID : " = some acctIdMsg := by decide +kernel
theorem custIdMsg_eq : Codepage.encode037 "CUSTOMER ID: " = some custIdMsg := by decide +kernel
theorem okAcctMsg_eq : Codepage.encode037 "SUCCESSFUL READ OF ACCOUNT FILE" = some okAcctMsg := by decide +kernel
theorem invCardMsg_eq : Codepage.encode037 "INVALID CARD NUMBER FOR XREF" = some invCardMsg := by decide +kernel
theorem cardMsg_eq : Codepage.encode037 "CARD NUMBER " = some cardMsg := by decide +kernel
theorem skipMsg_eq : Codepage.encode037 " COULD NOT BE VERIFIED. SKIPPING TRANSACTION ID-" = some skipMsg := by decide +kernel
theorem invAcctMsg_eq : Codepage.encode037 "INVALID ACCOUNT NUMBER FOUND" = some invAcctMsg := by decide +kernel
theorem acctMsg_eq : Codepage.encode037 "ACCOUNT " = some acctMsg := by decide +kernel
theorem notFoundMsg_eq : Codepage.encode037 " NOT FOUND" = some notFoundMsg := by decide +kernel

/-- A card cross-reference record: card number, customer id, account id, filler. -/
structure Xref where
  card : List UInt8
  cust : Int
  acct : Int
  fill : List UInt8
  deriving Inhabited

def Xref.valid (x : Xref) : Prop :=
  x.card.length = 16 ∧ x.cust.natAbs < 1000000000 ∧ 0 ≤ x.cust ∧
    x.acct.natAbs < 100000000000 ∧ 0 ≤ x.acct ∧ x.fill.length = 14

def Xref.bytes (x : Xref) : List UInt8 :=
  x.card ++ encodeNum {} XREF_CUST_ID.fmt x.cust ++ encodeNum {} XREF_ACCT_ID.fmt x.acct ++ x.fill

/-- What the lookups display for the transaction record `t` (card number at 262). -/
def lookupMsgs (xrefs : List Xref) (accts : List (List UInt8)) (t : List UInt8) :
    List (List UInt8) :=
  let card := (t.drop 262).take 16
  match Sem.findKey { off := 0, len := 16 } card (xrefs.map Xref.bytes) with
  | none => [invCardMsg, cardMsg ++ card ++ skipMsg ++ t.take 16]
  | some i =>
    let x := xrefs.getD i default
    [okXrefMsg, cardNumMsg ++ x.card, acctIdMsg ++ encodeNum {} XREF_ACCT_ID.fmt x.acct,
      custIdMsg ++ encodeNum {} XREF_CUST_ID.fmt x.cust] ++
    match Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt x.acct) accts with
    | none => [invAcctMsg, acctMsg ++ encodeNum {} ACCT_ID.fmt x.acct ++ notFoundMsg]
    | some _ => [okAcctMsg]

theorem findKey_lt {k : KeyDecl} {v : List UInt8} :
    ∀ {l : List (List UInt8)} {i : Nat}, Sem.findKey k v l = some i → i < l.length
  | [], _, h => by simp [Sem.findKey] at h
  | r :: rs, i, h => by
    simp only [Sem.findKey] at h
    split at h
    · simp at h; subst h; simp
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      have := findKey_lt hj
      simp; omega

theorem getD_map_bytes (xrefs : List Xref) {i : Nat} (h : i < xrefs.length) :
    (xrefs.map Xref.bytes).getD i [] = (xrefs.getD i default).bytes := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_mem {α : Type} [Inhabited α] {l : List α} {i : Nat} (h : i < l.length) :
    l.getD i default ∈ l := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- Loop invariant, indexed by the outcomes of the remaining `READ`s. -/
def Inv (m : Mem) (xrefs : List Xref) (accts trans : List (List UInt8))
    (inp0 : List (Nat × List (List UInt8))) (rest : List (Option (List UInt8))) (st : State) :
    Prop :=
  ∃ done todo, trans = done ++ todo ∧
    ((rest = [] ∧ todo = []) ∨ rest = todo.map some ++ [none]) ∧
    st.idx = [] ∧ st.slots = [] ∧ st.active = [] ∧ st.clockN = 0 ∧ st.inp = inp0 ∧
    st.mem.size = 3441 ∧
    st.mem.read 3424 1 = (if rest.isEmpty then [232] else [213]) ∧
    st.mem.read 1700 350 = done.getLast?.getD (m.read 1700 350) ∧
    (∃ f1 f2 f3 f4 f5 f6 : FileSt, st.files = [(1, f1), (2, f2), (3, f3), (4, f4), (5, f5), (6, f6)] ∧
      f1.mode = some .input ∧ f1.recs = trans ∧ f1.pos = done.length ∧ f1.eof = rest.isEmpty ∧
      f2.mode = some .input ∧ f3.mode = some .input ∧ f3.recs = xrefs.map Xref.bytes ∧
      f4.mode = some .input ∧ f5.mode = some .input ∧ f5.recs = accts ∧ f6.mode = some .input) ∧
    displays st = [startMsg] ++ done.flatMap (fun t => t :: lookupMsgs xrefs accts t) ++
      (if rest.isEmpty then lookupMsgs xrefs accts (done.getLast?.getD (m.read 1700 350)) else [])

-- the messages, the display list and what the lookups display, for the closing `simp`s
attribute [local simp] startMsg endMsg okXrefMsg cardNumMsg acctIdMsg custIdMsg okAcctMsg invCardMsg cardMsg skipMsg invAcctMsg acctMsg notFoundMsg displays lookupMsgs

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **CBTRN01C verifies every daily transaction, the last one twice.**  For every daily
transaction file (any number of 350-byte records), cross-reference file (valid records) and
account file (300-byte records), and any initial storage, the program ends with `GOBACK` and
displays the start message, each transaction followed by what its lookups display, the
lookups of the last transaction once more (of the record area's initial contents when the
file is empty), and the end message. -/
theorem cbtrn01c_verifies (m : Mem) (hm : m.size = 3441) (trans : List (List UInt8))
    (htr : ∀ t ∈ trans, t.length = 350) (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid)
    (accts : List (List UInt8)) (hac : ∀ a ∈ accts, a.length = 300) (n : Nat)
    (hn : trans.length < n) :
    let r := Cbtrn01c.run {} (n + 40)
      (Cbtrn01c.initState m [(1, trans), (3, xrefs.map Xref.bytes), (5, accts)])
    r.1 = .stop .goback ∧
      displays r.2 = [startMsg] ++ trans.flatMap (fun t => t :: lookupMsgs xrefs accts t) ++
        lookupMsgs xrefs accts (trans.getLast?.getD (m.read 1700 350)) ++ [endMsg] := by
  intro r
  simp only [r]
  cobol_auto
  cobol_loop (Inv m xrefs accts trans [(1, trans), (3, xrefs.map Xref.bytes), (5, accts)])
    (trans.map some ++ [none])
  · -- after the loop: six CLOSEs, DISPLAY, GOBACK
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := loopState
    obtain ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, rfl, hsz, heof, -,
      ⟨f1, f2, f3, f4, f5, f6, rfl, h1m, -, -, -, h2m, h3m, -, h4m, h5m, -, h6m⟩, hdisp⟩ := hloopInv
    rcases hrest with ⟨-, rfl⟩ | h
    · simp only [List.append_nil] at hd
      subst hd
      dsimp only at hsz heof hdisp
      simp only [List.isEmpty_nil, ↓reduceIte] at heof hdisp
      cobol_auto
      simp only [displays, List.filterMap_reverse] at hdisp ⊢
      simp [hdisp, endMsg]
    · simp at h
  · -- before the loop: the start message only, the files at their start
    cobol_inv with [], trans
  · simp; omega
  · -- the loop ends exactly after the end-of-file READ
    rintro ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ ⟨-, -, -, -, -, -, -, -, -, -, heof, -⟩
    simp only [List.isEmpty_nil, ↓reduceIte] at heof
    cobol_auto
  · -- one iteration: READ the next transaction (or the end of the file), then the lookups
    rintro y ys ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, rfl, hsz, heof, h1700,
        ⟨f1, f2, f3, f4, f5, f6, rfl, h1m, h1r, h1p, h1e, h2m, h3m, h3r, h4m, h5m, h5r, h6m⟩, hdisp⟩
    dsimp only at hsz heof h1700 hdisp
    rcases hrest with ⟨h, -⟩ | hrest
    · simp at h
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at heof h1e hdisp
    refine ⟨by cobol_auto, ?_⟩
    simp only [displays, List.filterMap_reverse] at hdisp
    cases todo with
    | nil =>
      -- the end-of-file READ: the lookups run once more on the last record read
      simp only [List.map_nil, List.nil_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      simp only [List.append_nil] at hd
      subst hd
      have hnone : f1.recs[f1.pos]? = none := by rw [h1r, h1p]; simp
      have hlast : (trans.getLast?.getD (m.read 1700 350)).length = 350 := by
        cases h : trans.getLast? with
        | none => simp
        | some t => simpa using htr t (List.mem_of_getLast? h)
      generalize hL : trans.getLast?.getD (m.read 1700 350) = last at h1700 hlast
      rcases hx : Sem.findKey { off := 0, len := 16 } ((last.drop 262).take 16)
          (xrefs.map Xref.bytes) with _ | i
      · -- the card is not in the cross-reference file
        cobol_auto
        cobol_inv with trans, []
      · have hi := findKey_lt hx
        simp only [List.length_map] at hi
        obtain ⟨hxc, hxcu, hxcu0, hxa, hxa0, hxf⟩ := hxv _ (getD_mem hi)
        have hxg := getD_map_bytes xrefs hi
        rcases ha : Sem.findKey { off := 0, len := 11 }
            (encodeNum {} FD_ACCT_ID.fmt (xrefs.getD i default).acct) accts with _ | j
        · -- the account is not in the account file
          cobol_auto [Xref.bytes]
          cobol_inv [Xref.bytes] with trans, []
        · have haj : (accts.getD j []).length = 300 := hac _ (getD_mem (findKey_lt ha))
          cobol_auto [Xref.bytes]
          cobol_inv [Xref.bytes] with trans, []
    | cons t todo' =>
      -- the next transaction `t`: displayed, then its lookups
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      subst hd
      have ht : t.length = 350 := htr t (by simp)
      have hsome : f1.recs[f1.pos]? = some t := by rw [h1r, h1p]; simp
      rcases hx : Sem.findKey { off := 0, len := 16 } ((t.drop 262).take 16)
          (xrefs.map Xref.bytes) with _ | i
      · -- the card is not in the cross-reference file
        cobol_auto
        cobol_inv with done ++ [t], todo'
      · have hi := findKey_lt hx
        simp only [List.length_map] at hi
        obtain ⟨hxc, hxcu, hxcu0, hxa, hxa0, hxf⟩ := hxv _ (getD_mem hi)
        have hxg := getD_map_bytes xrefs hi
        rcases ha : Sem.findKey { off := 0, len := 11 }
            (encodeNum {} FD_ACCT_ID.fmt (xrefs.getD i default).acct) accts with _ | j
        · -- the account is not in the account file
          cobol_auto [Xref.bytes]
          cobol_inv [Xref.bytes] with done ++ [t], todo'
        · have haj : (accts.getD j []).length = 300 := hac _ (getD_mem (findKey_lt ha))
          cobol_auto [Xref.bytes]
          cobol_inv [Xref.bytes] with done ++ [t], todo'

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **`cbtrn01c_verifies` with every input file given.**  The customer, card and transaction files
(2, 4, 6) are opened and closed but never read, so their records (`custs`, `cards`, `tr6`, any)
do not change the result.  The rest as in `cbtrn01c_verifies`:  For every daily
transaction file (any number of 350-byte records), cross-reference file (valid records) and
account file (300-byte records), and any initial storage, the program ends with `GOBACK` and
displays the start message, each transaction followed by what its lookups display, the
lookups of the last transaction once more (of the record area's initial contents when the
file is empty), and the end message. -/
theorem cbtrn01c_verifies_all (m : Mem) (hm : m.size = 3441) (trans : List (List UInt8))
    (htr : ∀ t ∈ trans, t.length = 350) (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid)
    (accts : List (List UInt8)) (hac : ∀ a ∈ accts, a.length = 300)
    (custs cards tr6 : List (List UInt8)) (n : Nat)
    (hn : trans.length < n) :
    let r := Cbtrn01c.run {} (n + 40)
      (Cbtrn01c.initState m [(1, trans), (2, custs), (3, xrefs.map Xref.bytes), (4, cards),
        (5, accts), (6, tr6)])
    r.1 = .stop .goback ∧
      displays r.2 = [startMsg] ++ trans.flatMap (fun t => t :: lookupMsgs xrefs accts t) ++
        lookupMsgs xrefs accts (trans.getLast?.getD (m.read 1700 350)) ++ [endMsg] := by
  intro r
  simp only [r]
  cobol_auto
  cobol_loop (Inv m xrefs accts trans [(1, trans), (2, custs), (3, xrefs.map Xref.bytes), (4, cards),
      (5, accts), (6, tr6)])
    (trans.map some ++ [none])
  · -- after the loop: six CLOSEs, DISPLAY, GOBACK
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := loopState
    obtain ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, rfl, hsz, heof, -,
      ⟨f1, f2, f3, f4, f5, f6, rfl, h1m, -, -, -, h2m, h3m, -, h4m, h5m, -, h6m⟩, hdisp⟩ := hloopInv
    rcases hrest with ⟨-, rfl⟩ | h
    · simp only [List.append_nil] at hd
      subst hd
      dsimp only at hsz heof hdisp
      simp only [List.isEmpty_nil, ↓reduceIte] at heof hdisp
      cobol_auto
      simp only [displays, List.filterMap_reverse] at hdisp ⊢
      simp [hdisp, endMsg]
    · simp at h
  · -- before the loop: the start message only, the files at their start
    cobol_inv with [], trans
  · simp; omega
  · -- the loop ends exactly after the end-of-file READ
    rintro ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ ⟨-, -, -, -, -, -, -, -, -, -, heof, -⟩
    simp only [List.isEmpty_nil, ↓reduceIte] at heof
    cobol_auto
  · -- one iteration: READ the next transaction (or the end of the file), then the lookups
    rintro y ys ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, rfl, hsz, heof, h1700,
        ⟨f1, f2, f3, f4, f5, f6, rfl, h1m, h1r, h1p, h1e, h2m, h3m, h3r, h4m, h5m, h5r, h6m⟩, hdisp⟩
    dsimp only at hsz heof h1700 hdisp
    rcases hrest with ⟨h, -⟩ | hrest
    · simp at h
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at heof h1e hdisp
    refine ⟨by cobol_auto, ?_⟩
    simp only [displays, List.filterMap_reverse] at hdisp
    cases todo with
    | nil =>
      -- the end-of-file READ: the lookups run once more on the last record read
      simp only [List.map_nil, List.nil_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      simp only [List.append_nil] at hd
      subst hd
      have hnone : f1.recs[f1.pos]? = none := by rw [h1r, h1p]; simp
      have hlast : (trans.getLast?.getD (m.read 1700 350)).length = 350 := by
        cases h : trans.getLast? with
        | none => simp
        | some t => simpa using htr t (List.mem_of_getLast? h)
      generalize hL : trans.getLast?.getD (m.read 1700 350) = last at h1700 hlast
      rcases hx : Sem.findKey { off := 0, len := 16 } ((last.drop 262).take 16)
          (xrefs.map Xref.bytes) with _ | i
      · -- the card is not in the cross-reference file
        cobol_auto
        cobol_inv with trans, []
      · have hi := findKey_lt hx
        simp only [List.length_map] at hi
        obtain ⟨hxc, hxcu, hxcu0, hxa, hxa0, hxf⟩ := hxv _ (getD_mem hi)
        have hxg := getD_map_bytes xrefs hi
        rcases ha : Sem.findKey { off := 0, len := 11 }
            (encodeNum {} FD_ACCT_ID.fmt (xrefs.getD i default).acct) accts with _ | j
        · -- the account is not in the account file
          cobol_auto [Xref.bytes]
          cobol_inv [Xref.bytes] with trans, []
        · have haj : (accts.getD j []).length = 300 := hac _ (getD_mem (findKey_lt ha))
          cobol_auto [Xref.bytes]
          cobol_inv [Xref.bytes] with trans, []
    | cons t todo' =>
      -- the next transaction `t`: displayed, then its lookups
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      subst hd
      have ht : t.length = 350 := htr t (by simp)
      have hsome : f1.recs[f1.pos]? = some t := by rw [h1r, h1p]; simp
      rcases hx : Sem.findKey { off := 0, len := 16 } ((t.drop 262).take 16)
          (xrefs.map Xref.bytes) with _ | i
      · -- the card is not in the cross-reference file
        cobol_auto
        cobol_inv with done ++ [t], todo'
      · have hi := findKey_lt hx
        simp only [List.length_map] at hi
        obtain ⟨hxc, hxcu, hxcu0, hxa, hxa0, hxf⟩ := hxv _ (getD_mem hi)
        have hxg := getD_map_bytes xrefs hi
        rcases ha : Sem.findKey { off := 0, len := 11 }
            (encodeNum {} FD_ACCT_ID.fmt (xrefs.getD i default).acct) accts with _ | j
        · -- the account is not in the account file
          cobol_auto [Xref.bytes]
          cobol_inv [Xref.bytes] with done ++ [t], todo'
        · have haj : (accts.getD j []).length = 300 := hac _ (getD_mem (findKey_lt ha))
          cobol_auto [Xref.bytes]
          cobol_inv [Xref.bytes] with done ++ [t], todo'

end Cbtrn01c
end CardDemo

#print axioms CardDemo.Cbtrn01c.cbtrn01c_verifies
#print axioms CardDemo.Cbtrn01c.cbtrn01c_verifies_all
