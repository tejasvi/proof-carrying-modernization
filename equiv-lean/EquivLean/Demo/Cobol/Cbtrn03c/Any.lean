-- Copied unchanged from coblean (frozen snapshot ~/coblean_snapshots/coblean-20261024T1830Z,
-- Examples/Cbtrn03cAny.lean); only the import differs. coblean and JimpleLean both have a library
-- named `Examples`, so equiv-lean cannot import the original module next to JimpleLean.
/-
# CardDemo CBTRN03C on any input

`cbtrn03c_report` assumes every transaction date is in the report's range and every lookup
succeeds; `cbtrn03c_stops` covers a date outside the range. `cbtrn03c_any` drops both
assumptions and the non-empty file. Per transaction, in program order:
- a date outside the range ends the loop (`NEXT SENTENCE`, see `Examples/Cbtrn03cStop.lean`);
- otherwise the record is displayed; on a new card the previous card's account total is written
  (not before the first detail) and the card is looked up in the cross-reference file; then the
  transaction type and category are looked up. A failed lookup (`INVALID KEY`) displays its
  message and the key, the file status 23, `ABENDING PROGRAM`, and abends with code 999;
- otherwise the report lines of `step3`.
At the end of the file the record area still holds the last record (for an empty file: whatever
the area held before, `t00`); its date is tested again, and if it is in the range its amount is
added again and the page and grand totals are written (`eofEvents`).
-/
import EquivLean.Demo.Cobol.Cbtrn03c.Stop
import Cobol.Logic.LoopExit

open Cobol

namespace CardDemo
namespace Cbtrn03c

instance (parm : List UInt8) (t : Tran) : Decidable (inRange parm t) := by
  unfold inRange; infer_instance

/-- `INVALID CARD NUMBER : ` in EBCDIC. -/
def invCardMsg : List UInt8 := [201, 213, 229, 193, 211, 201, 196, 64, 195, 193, 217, 196, 64, 213,
  228, 212, 194, 197, 217, 64, 122, 64]
/-- `INVALID TRANSACTION TYPE : ` in EBCDIC. -/
def invTypeMsg : List UInt8 := [201, 213, 229, 193, 211, 201, 196, 64, 227, 217, 193, 213, 226, 193,
  195, 227, 201, 214, 213, 64, 227, 232, 215, 197, 64, 122, 64]
/-- `INVALID TRAN CATG KEY : ` in EBCDIC. -/
def invCatMsg : List UInt8 := [201, 213, 229, 193, 211, 201, 196, 64, 227, 217, 193, 213, 64, 195,
  193, 227, 199, 64, 210, 197, 232, 64, 122, 64]
/-- `FILE STATUS IS: NNNN` in EBCDIC. -/
def statusMsg : List UInt8 := [198, 201, 211, 197, 64, 226, 227, 193, 227, 228, 226, 64, 201, 226, 122,
  64, 213, 213, 213, 213]
/-- `ABENDING PROGRAM` in EBCDIC. -/
def abendMsg : List UInt8 := [193, 194, 197, 213, 196, 201, 213, 199, 64, 215, 217, 214, 199, 217, 193,
  212]

theorem invCardMsg_eq : Codepage.encode037 "INVALID CARD NUMBER : " = some invCardMsg := by
  decide +kernel
theorem invTypeMsg_eq : Codepage.encode037 "INVALID TRANSACTION TYPE : " = some invTypeMsg := by
  decide +kernel
theorem invCatMsg_eq : Codepage.encode037 "INVALID TRAN CATG KEY : " = some invCatMsg := by
  decide +kernel
theorem statusMsg_eq : Codepage.encode037 "FILE STATUS IS: NNNN" = some statusMsg := by
  decide +kernel
theorem abendMsg_eq : Codepage.encode037 "ABENDING PROGRAM" = some abendMsg := by decide +kernel

/-- The events of a failed lookup (newest first): its message with the key, the file status 23,
the abend message. -/
def abendEvents (msg : List UInt8) : List Event :=
  [.display abendMsg, .display (statusMsg ++ [240, 240, 242, 243]), .display msg]

/-- The report so far (`go`), or how it ended early: a date outside the range (`stop`, no
events for that transaction) or a failed lookup (`abend`, its events included). -/
inductive X3 where
  | go (s : M3)
  | stop (s : M3)
  | abend (s : M3)

/-- One transaction, in program order: the date check, `DISPLAY`, on a new card the previous
card's account total and the cross-reference lookup, the type and category lookups, then the
report lines (`step3`). -/
def step3x (xrefs : List Xref) (types catgs : List (List UInt8)) (parm : List UInt8) :
    X3 → Tran → X3
  | .go s, t =>
    if inRange parm t then
      let out1 := Event.display t.bytes :: s.out
      let same := decide (s.card = t.card)
      let out2 := if same || s.first then out1 else
        .write 5 hdr2Line :: .write 5 (acctLine s.acct) :: out1
      if !same && (Sem.findKey { off := 0, len := 16 } t.card (xrefs.map Xref.bytes)).isNone then
        .abend { s with out := abendEvents (invCardMsg ++ t.card) ++ out2 }
      else if (Sem.findKey { off := 0, len := 2 } t.ty types).isNone then
        .abend { s with out := abendEvents (invTypeMsg ++ t.ty) ++ out2 }
      else if (Sem.findKey { off := 0, len := 6 } (t.ty ++ encodeNum {} FD_TRAN_CAT_CD.fmt t.cat)
          catgs).isNone then
        .abend { s with out := abendEvents (invCatMsg ++ t.ty ++
          encodeNum {} FD_TRAN_CAT_CD.fmt t.cat) ++ out2 }
      else .go (step3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) s t)
    else .stop s
  | .stop s, _ => .stop s
  | .abend s, _ => .abend s

/-- The model after the transactions `ts`. -/
def report3x (xrefs : List Xref) (types catgs : List (List UInt8)) (parm : List UInt8)
    (ts : List Tran) : X3 :=
  ts.foldl (step3x xrefs types catgs parm) (.go ⟨List.replicate 16 64, true, 0, 0, 0, 0, 0, []⟩)

/-- The first two events (newest first): the date range, the start message. -/
def header3 (parm : List UInt8) : List Event :=
  [.display (reportingMsg ++ parm.take 10 ++ toMsg ++ (parm.drop 11).take 10), .display startMsg]

/-- The end of the run and all its events (newest first), given the record `tl` left in the
record area at the end of the file. -/
def result3 (parm : List UInt8) (tl : Tran) : X3 → Signal × List Event
  | .go s => (.stop .goback, [.display endMsg] ++ (if inRange parm tl then eofEvents s tl else []) ++
      s.out ++ header3 parm)
  | .stop s => (.stop .goback, [.display endMsg] ++ s.out ++ header3 parm)
  | .abend s => (.fault (.abend 999), s.out ++ header3 parm)


/-! ## The model's lemmas -/

theorem report3x_append (xrefs : List Xref) (types catgs : List (List UInt8)) (parm : List UInt8)
    (ts : List Tran) (t : Tran) :
    report3x xrefs types catgs parm (ts ++ [t]) =
      step3x xrefs types catgs parm (report3x xrefs types catgs parm ts) t := by
  simp [report3x, List.foldl_append]

theorem foldl_step3x_stop (xrefs : List Xref) (types catgs : List (List UInt8))
    (parm : List UInt8) (s : M3) :
    ∀ ts : List Tran, ts.foldl (step3x xrefs types catgs parm) (.stop s) = .stop s
  | [] => rfl
  | _ :: ts => by simp only [List.foldl_cons, step3x]; exact foldl_step3x_stop xrefs types catgs parm s ts

theorem foldl_step3x_abend (xrefs : List Xref) (types catgs : List (List UInt8))
    (parm : List UInt8) (s : M3) :
    ∀ ts : List Tran, ts.foldl (step3x xrefs types catgs parm) (.abend s) = .abend s
  | [] => rfl
  | _ :: ts => by simp only [List.foldl_cons, step3x]; exact foldl_step3x_abend xrefs types catgs parm s ts

/-- After `done` the model goes on with `S`; the next transaction `t` gives `x`; then the model of
the whole file is `x` when `x` stopped. -/
theorem report3x_stop_at (xrefs : List Xref) (types catgs : List (List UInt8)) (parm : List UInt8)
    (done todo : List Tran) (t : Tran) (S S' : M3)
    (h : report3x xrefs types catgs parm done = .go S)
    (hs : step3x xrefs types catgs parm (.go S) t = .stop S') :
    report3x xrefs types catgs parm (done ++ t :: todo) = .stop S' := by
  simp only [report3x, List.foldl_append, List.foldl_cons] at h ⊢
  rw [h, hs]; exact foldl_step3x_stop xrefs types catgs parm S' todo

theorem report3x_abend_at (xrefs : List Xref) (types catgs : List (List UInt8)) (parm : List UInt8)
    (done todo : List Tran) (t : Tran) (S S' : M3)
    (h : report3x xrefs types catgs parm done = .go S)
    (hs : step3x xrefs types catgs parm (.go S) t = .abend S') :
    report3x xrefs types catgs parm (done ++ t :: todo) = .abend S' := by
  simp only [report3x, List.foldl_append, List.foldl_cons] at h ⊢
  rw [h, hs]; exact foldl_step3x_abend xrefs types catgs parm S' todo

/-- A transaction in the range whose lookups succeed: `step3`. -/
theorem step3x_go (xrefs : List Xref) (types catgs : List (List UInt8)) (parm : List UInt8)
    (s : M3) (t : Tran) (hin : inRange parm t)
    (hx : s.card ≠ t.card → (Sem.findKey { off := 0, len := 16 } t.card (xrefs.map Xref.bytes)).isSome)
    (hty : (Sem.findKey { off := 0, len := 2 } t.ty types).isSome)
    (hcat : (Sem.findKey { off := 0, len := 6 } (t.ty ++ encodeNum {} FD_TRAN_CAT_CD.fmt t.cat)
      catgs).isSome) :
    step3x xrefs types catgs parm (.go s) t =
      .go (step3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) s t) := by
  simp only [step3x, hin, ↓reduceIte]
  by_cases hc : s.card = t.card
  · simp [hc, Option.isSome_iff_ne_none.mp hty, Option.isSome_iff_ne_none.mp hcat]
  · simp [hc, Option.isSome_iff_ne_none.mp (hx hc), Option.isSome_iff_ne_none.mp hty,
      Option.isSome_iff_ne_none.mp hcat]

theorem report3x_nil (xrefs : List Xref) (types catgs : List (List UInt8)) (parm : List UInt8) :
    report3x xrefs types catgs parm [] = .go ⟨List.replicate 16 64, true, 0, 0, 0, 0, 0, []⟩ := rfl

/-! ## The proof -/

/-- Loop invariant: `Inv` of `cbtrn03c_report`, with the model still going (`report3x` of `done`
is `go` of `report3` of `done`), the record area holding `t00` while an empty file has not been
read, and `t00` as the record left at the end of an empty file. -/
def InvA (xrefs : List Xref) (types catgs : List (List UInt8)) (parm : List UInt8)
    (trans : List Tran) (t00 : Tran) (m733 : List UInt8) (inp0 : List (Nat × List (List UInt8)))
    (rest : List (Option Tran)) (st : State) : Prop :=
  ∃ done todo, trans = done ++ todo ∧
    ((rest = [] ∧ todo = []) ∨ rest = todo.map some ++ [none]) ∧
    report3x xrefs types catgs parm done =
      .go (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done) ∧
    st.idx = [] ∧ st.slots = [] ∧ st.active = [] ∧ st.inp = inp0 ∧ st.mem.size = 2309 ∧
    st.mem.read 2300 1 = (if rest.isEmpty then [232] else [213]) ∧
    st.mem.read 2272 16 = (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).card ∧
    st.mem.read 2098 1 = (if done = [] then [232] else [213]) ∧
    (rest ≠ [] → st.mem.read 2099 5 = encodeNum {} WS_LINE_COUNTER.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).lines ∧
      st.mem.read 2239 11 = encodeNum {} WS_PAGE_TOTAL.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).page ∧
      st.mem.read 2250 11 = encodeNum {} WS_ACCOUNT_TOTAL.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).acct ∧
      st.mem.read 2261 11 = encodeNum {} WS_GRAND_TOTAL.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).grand) ∧
    st.mem.read 2077 21 = parm.take 21 ∧
    st.mem.read 2104 2 = encodeNum {} WS_PAGE_SIZE.fmt 20 ∧
    st.mem.read 2106 133 = blankLine ∧ st.mem.read 1490 114 = header1 ∧
    st.mem.read 1604 133 = hdr2Line ∧ st.mem.read 1261 91 = nameHead ∧ st.mem.read 1362 4 = toMsg ∧
    st.mem.read 1737 97 = pageHead ∧ st.mem.read 1849 97 = acctHead ∧
    st.mem.read 1961 97 = grandHead ∧
    st.mem.read 1392 1 = [64] ∧ st.mem.read 1404 1 = [64] ∧ st.mem.read 1407 1 = [96] ∧
    st.mem.read 1423 1 = [64] ∧ st.mem.read 1428 1 = [96] ∧ st.mem.read 1458 1 = [64] ∧
    st.mem.read 1469 4 = [64, 64, 64, 64] ∧ st.mem.read 1488 2 = [64, 64] ∧
    ((done = [] ∧ st.mem.read 733 350 = m733) ∨
      (done ≠ [] ∧ st.mem.read 1352 10 = parm.take 10 ∧ st.mem.read 1366 10 = (parm.drop 11).take 10 ∧
        st.mem.read 1110 11 = encodeNum {} XREF_ACCT_ID.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).xacct ∧
        (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).xacct.natAbs < 100000000000 ∧ 0 ≤ (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).xacct ∧
        st.mem.read 733 350 = (done.getLast?.getD default).bytes)) ∧
    (rest = [] → inRange parm (done.getLast?.getD t00)) ∧
    (∃ f1 f2 f3 f4 f5 f6 : FileSt,
      st.files = [(1, f1), (5, f5), (2, f2), (3, f3), (4, f4), (6, f6)] ∧
      f1.mode = some .input ∧ f1.recs = trans.map Tran.bytes ∧ f1.pos = done.length ∧
      f1.eof = rest.isEmpty ∧
      f2.mode = some .input ∧ f2.recs = xrefs.map Xref.bytes ∧ f3.mode = some .input ∧
      f3.recs = types ∧ f4.mode = some .input ∧ f4.recs = catgs ∧ f5.mode = some .output ∧
      f6.mode = some .input) ∧
    st.out = (if rest.isEmpty then eofEvents (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done) (done.getLast?.getD t00) else []) ++
      (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).out ++
      [.display (reportingMsg ++ parm.take 10 ++ toMsg ++ (parm.drop 11).take 10), .display startMsg]

/-- How the loop can stop early: `NEXT SENTENCE` (a date outside the range; for an empty file
also the end-of-file iteration) with the six files open, or the abend of a failed lookup; in
both cases the model's end and events, `res`, are already determined by the state. -/
def ExitX3 (res : Signal × List Event) (inp0 : List (Nat × List (List UInt8))) (r : Sem.Res) :
    Prop :=
  (r.1 = .nextSentence ∧ r.2.idx = [] ∧ r.2.slots = [] ∧ r.2.active = [] ∧ r.2.inp = inp0 ∧
    r.2.mem.size = 2309 ∧
    (∃ f1 f2 f3 f4 f5 f6 : FileSt,
      r.2.files = [(1, f1), (5, f5), (2, f2), (3, f3), (4, f4), (6, f6)] ∧
      f1.mode = some .input ∧ f2.mode = some .input ∧ f3.mode = some .input ∧
      f4.mode = some .input ∧ f5.mode = some .output ∧ f6.mode = some .input) ∧
    res.1 = .stop .goback ∧ res.2 = [.display endMsg] ++ r.2.out) ∨
  (r.1 = .fault (.abend 999) ∧ res.1 = .fault (.abend 999) ∧ res.2 = r.2.out)

set_option maxHeartbeats 60000000 in
set_option maxRecDepth 20000 in
/-- **CBTRN03C on any input.** For every transaction file (valid records, possibly empty, no date
or lookup assumption), every cross-reference, type and category file, every parameter record and
every initial storage: CBTRN03C ends as `result3` says, with its events. `t00` is the record
area's initial contents, which only an empty file leaves in place for the end-of-file test. The
one remaining assumption: no card number is blank (blank is the initial current card, so a blank
first card would skip the cross-reference lookup). -/
theorem cbtrn03c_any (m : Mem) (hm : m.size = 2309)
    (trans : List Tran) (htv : ∀ t ∈ trans, t.valid) (hlen : trans.length < 10000000)
    (t00 : Tran) (ht00 : trans = [] → t00.valid ∧ m.read 733 350 = t00.bytes)
    (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid)
    (types catgs : List (List UInt8)) (htyl : ∀ r ∈ types, r.length = 60)
    (hcgl : ∀ r ∈ catgs, r.length = 60)
    (parm : List UInt8) (hpl : parm.length = 80) (prest : List (List UInt8))
    (hcard : ∀ t ∈ trans, t.card ≠ List.replicate 16 64)
    (n : Nat) (hn : trans.length < n) :
    let r := Cbtrn03c.run {} (n + 60) (Cbtrn03c.initState m
      [(1, trans.map Tran.bytes), (2, xrefs.map Xref.bytes), (3, types), (4, catgs),
        (6, parm :: prest)])
    let res := result3 parm (trans.getLast?.getD t00) (report3x xrefs types catgs parm trans)
    r.1 = res.1 ∧ r.2.out = res.2 := by
  intro r res
  simp only [r]
  cobol_auto
  cobol_loop_exit (InvA xrefs types catgs parm trans t00 (m.read 733 350)
      [(1, trans.map Tran.bytes), (2, xrefs.map Xref.bytes), (3, types), (4, catgs),
        (6, parm :: prest)]) (trans.map some ++ [none])
    (ExitX3 res [(1, trans.map Tran.bytes), (2, xrefs.map Xref.bytes), (3, types), (4, catgs),
        (6, parm :: prest)])
  · -- the loop ended normally: the end-of-file iteration found the last record's date in the
    -- range; six CLOSEs, DISPLAY, GOBACK
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := loopState
    obtain ⟨done, todo, hd, hrest, hX, rfl, rfl, rfl, rfl, hsz, heof, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, hinr,
      ⟨f1, f2, f3, f4, f5, f6, rfl, h1m, -, -, -, h2m, -, h3m, -, h4m, -, h5m, h6m⟩, hout⟩ := hloopInv
    rcases hrest with ⟨-, rfl⟩ | h
    · simp only [List.append_nil] at hd
      subst hd
      have hin := hinr rfl
      dsimp only at hsz heof hout
      simp only [List.isEmpty_nil, ↓reduceIte] at heof hout
      cobol_auto
      simp only [res, hX, result3, hin, ↓reduceIte, header3] at hout ⊢
      simp [hout, endMsg]
    · simp at h
  · -- the loop stopped early
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := exitState
    rcases hexitInv with
      ⟨rfl, hx1, hx2, hx3, hx4, hsz, ⟨f1, f2, f3, f4, f5, f6, hfs, h1m, h2m, h3m, h4m, h5m, h6m⟩,
        hres1, hres2⟩ | ⟨rfl, hres1, hres2⟩
    · -- `NEXT SENTENCE`: six CLOSEs, DISPLAY, GOBACK
      dsimp only at hx1 hx2 hx3 hx4 hsz hfs hres2
      subst hx1 hx2 hx3 hx4 hfs
      cobol_auto
      simp [endMsg]
    · -- the abend of a failed lookup: nothing more runs
      dsimp only at hres2
      cobol_auto
  · -- before the loop: the date range read, nothing else
    cobol_inv [report3_nil, report3x_nil, blankLine, hdr2Line, header1, nameHead, toMsg, pageHead,
      acctHead, grandHead, reportingMsg, startMsg, List.drop_take, List.take_take, enc_total_zero,
      enc_lines_zero] with [], trans
  · simp; omega
  · -- the loop ends exactly after the end-of-file READ
    rintro ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨-, -, -, -, -, -, -, -, -, -, heof, -⟩
    simp only [List.isEmpty_nil, ↓reduceIte] at heof
    cobol_auto
  · -- one iteration: READ the next transaction; report it, stop at a date outside the range or
    -- at a failed lookup, or reach the end of the file
    rintro y ys ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨done, todo, hd, hrest, hX, rfl, rfl, rfl, rfl, hsz, heof, hcard', hfirst, hnum, hdp, hps, hbl,
        hh1, hh2, hnh, hto, hph, hah, hgh, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hphase, hinr,
        ⟨f1, f2, f3, f4, f5, f6, rfl, h1m, h1r, h1p, h1e, h2m, h2r, h3m, h3r, h4m, h4r, h5m, h6m⟩,
        hout⟩
    dsimp only at hsz heof hcard' hfirst hnum hdp hps hbl hh1 hh2 hnh hto hph hah hgh
    dsimp only at hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hphase hout
    rcases hrest with ⟨h, -⟩ | hrest
    · simp at h
    obtain ⟨hlines, hpage, hacct, hgrand⟩ := hnum (by simp)
    clear hnum hinr
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at heof h1e hout
    refine ⟨by cobol_auto, ?_⟩
    -- the model after `done`
    have hb := report3_bounds xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done
    have hlb := report3_lines xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done
    have hcl := report3_card_length xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done
      (fun t ht => (htv t (by simp [hd, ht])).2.2.2.2.2.2.2.2.1)
    generalize hS : report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done = S
      at hcard' hlines hpage hacct hgrand hphase hout hb hlb hcl hX
    obtain ⟨hpb, hab, hgb⟩ := hb
    have hdl : done.length < 10000000 := by
      have := hlen; rw [hd] at this; simp only [List.length_append] at this; omega
    have hl0 : S.lines < 130000000 := by omega
    cases todo with
    | nil =>
      -- the end-of-file READ; the record area still holds the last record (t00 for an empty file)
      simp only [List.map_nil, List.nil_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      simp only [List.append_nil] at hd
      subst hd
      have hnone : f1.recs[f1.pos]? = none := by rw [h1r, h1p]; simp
      rcases hphase with ⟨h0, hm0⟩ | ⟨h0, hsd, hed, hxa, hxa1, hxa2, htr⟩
      · -- the empty file
        subst h0
        obtain ⟨ht0v, ht0m⟩ := ht00 rfl
        have harea : mem.read 733 350 = t00.bytes := hm0.trans ht0m
        have tb := Tran.length_bytes t00 ht0v
        have tfa := Tran.field_amt t00 ht0v
        have tfp := Tran.field_proc10 t00 ht0v
        obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := ht0v
        by_cases hin : inRange parm t00
        · -- in the range: the amount is added again, page and grand totals
          obtain ⟨hd1, hd2⟩ := id hin
          left
          cobol_auto [edit_plus, editPlus_length, List.take_take, List.drop_take, pageHead_length,
            grandHead_length, hdr2Line_length, harea]
          cobol_inv [eofEvents, pageLine, grandLine, pageMsg, amtMsg, hout, editPlus_length,
            pageHead_length, grandHead_length, hdr2Line_length, hS, fitTot, hin, hm0] with [], []
        · -- outside the range: `NEXT SENTENCE`, no totals
          right
          simp only [ExitX3, res, hX, result3, hin, ↓reduceIte, header3, List.getLast?_nil,
            Option.getD_none]
          by_cases hlo : Sem.cmpBytes (t00.proc.take 10) (parm.take 10) = .lt
          · cobol_auto [hlo, List.take_take, List.drop_take, harea]
            cobol_inv [hout, hS]
          · have hhi : Sem.cmpBytes (t00.proc.take 10) ((parm.drop 11).take 10) = .gt :=
              Classical.byContradiction fun h => hin ⟨hlo, h⟩
            cobol_auto [hhi, List.take_take, List.drop_take, harea]
            cobol_inv [hout, hS]
      · -- a non-empty file: the last transaction
        have hne : trans ≠ [] := h0
        have hlm : trans.getLast?.getD t00 ∈ trans := by
          cases h : trans.getLast? with
          | none => simp at h; exact absurd h hne
          | some t => simpa using List.mem_of_getLast? h
        have hLd : trans.getLast?.getD default = trans.getLast?.getD t00 := by
          cases h : trans.getLast? with
          | none => simp at h; exact absurd h hne
          | some t => simp
        rw [hLd] at htr
        generalize hL : trans.getLast?.getD t00 = tl at htr hlm hout
        have htl := htv tl hlm
        have tb := Tran.length_bytes tl htl
        have tfa := Tran.field_amt tl htl
        have tfp := Tran.field_proc10 tl htl
        obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := htl
        by_cases hin : inRange parm tl
        · obtain ⟨hd1, hd2⟩ := id hin
          left
          cobol_auto [edit_plus, editPlus_length, List.take_take, List.drop_take, pageHead_length,
            grandHead_length, hdr2Line_length]
          cobol_inv [eofEvents, pageLine, grandLine, pageMsg, amtMsg, hout, editPlus_length,
            pageHead_length, grandHead_length, hdr2Line_length, hS, hL, fitTot, hin] with trans, []
        · right
          simp only [ExitX3, res, hX, result3, hL, hin, ↓reduceIte, header3]
          by_cases hlo : Sem.cmpBytes (tl.proc.take 10) (parm.take 10) = .lt
          · cobol_auto [hlo, List.take_take, List.drop_take]
            cobol_inv [hout, hS]
          · have hhi : Sem.cmpBytes (tl.proc.take 10) ((parm.drop 11).take 10) = .gt :=
              Classical.byContradiction fun h => hin ⟨hlo, h⟩
            cobol_auto [hhi, List.take_take, List.drop_take]
            cobol_inv [hout, hS]
    | cons t todo' =>
      -- a transaction: READ, the date check, DISPLAY, the lookups, the report lines
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      subst hd
      have htm : t ∈ done ++ t :: todo' := by simp
      have hc0 := hcard t htm
      have htv' := htv t htm
      have hsome : f1.recs[f1.pos]? = some t.bytes := by rw [h1r, h1p]; simp
      have tb := Tran.length_bytes t htv'
      have tf1 := Tran.field_id t htv'
      have tf2 := Tran.field_ty t htv'
      have tf3 := Tran.field_cat t htv'
      have tf4 := Tran.field_src t htv'
      have tf6 := Tran.field_amt t htv'
      have tf11 := Tran.field_card t htv'
      have tfp := Tran.field_proc10 t htv'
      obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := htv'
      by_cases hin : inRange parm t
      · -- in the range: DISPLAY, the lookups, the report lines (or the abend of a failed lookup)
        obtain ⟨hd1, hd2⟩ := id hin
        have hnum23 : List.all [242, 243] (fun b => (Config.decDigit {} b).isSome) = true := by
          decide
        by_cases hc : S.card = t.card
        · -- the card of the previous transaction (so not the first one): no cross-reference lookup
          have hdn : done ≠ [] := by
            rintro rfl
            rw [report3_nil] at hS
            exact hc0 (by rw [← hc, ← hS])
          have hSf : S.first = false := by rw [← hS]; exact report3_first _ _ _ _ _ done hdn
          simp only [hdn, ↓reduceIte] at hfirst
          rcases hphase with ⟨h0, -⟩ | ⟨-, hsd, hed, hxa, hxa1, hxa2, htr⟩
          · exact absurd h0 hdn
          have hnl := name_read mem parm hnh hsd hto hed
          rcases hit : Sem.findKey { off := 0, len := 2 } t.ty types with _ | it
          · -- LEAF-SAME-TYPE: the type is missing
            right
            have hs : step3x xrefs types catgs parm (.go S) t =
                .abend { S with out := (abendEvents (invTypeMsg ++ t.ty) ++
                  Event.display t.bytes :: S.out) } := by
              simp [step3x, hin, hc, hit]
            have hR := report3x_abend_at xrefs types catgs parm done todo' t S _ hX hs
            simp only [ExitX3, res, hR, result3, header3]
            cobol_auto [List.take_take, List.drop_take, hc, hit, hnum23]
            cobol_inv [hout, abendEvents, invTypeMsg, statusMsg, abendMsg]
          · have hitl := findKey_lt hit
            have htyr := htyl _ (getD_mem' hitl)
            rcases hic : Sem.findKey { off := 0, len := 6 }
                (t.ty ++ encodeNum {} FD_TRAN_CAT_CD.fmt t.cat) catgs with _ | ic
            · -- LEAF-SAME-CAT: the category is missing
              right
              have hs : step3x xrefs types catgs parm (.go S) t =
                  .abend { S with out := (abendEvents (invCatMsg ++ t.ty ++
                    encodeNum {} FD_TRAN_CAT_CD.fmt t.cat) ++ Event.display t.bytes :: S.out) } := by
                simp [step3x, hin, hc, hit, hic]
              have hR := report3x_abend_at xrefs types catgs parm done todo' t S _ hX hs
              simp only [ExitX3, res, hR, result3, header3]
              cobol_auto [List.take_take, List.drop_take, hc, hit, hic, htyr, hnum23]
              cobol_inv [hout, abendEvents, invCatMsg, statusMsg, abendMsg]
            · -- LEAF-SAME-FOUND
              have hicl := findKey_lt hic
              have hcgr := hcgl _ (getD_mem' hicl)
              have hX' : report3x xrefs types catgs parm (done ++ [t]) =
                  .go (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) (done ++ [t])) := by
                rw [report3x_append, hX, report3_append, hS,
                  step3x_go xrefs types catgs parm S t hin (fun h => absurd hc h) (by simp [hit])
                    (by simp [hic])]
              left
              by_cases hb : S.lines % 20 = 0
              · -- a page break before the detail line
                have hm := compare_mod20_eq (x := (S.lines : Int)) (by omega)
                cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length,
                  List.take_take, List.drop_take, pageHead_length, nameHead_length, header1_length,
                  toMsg_length, hdr2Line_length, blankLine_length, mod20, hm, hc, hit, hic, htyr, hcgr,
                  hnl]
                cobol_inv [report3_append, step3, hS, hout, hSf, hc, hb, headers, hdr1Line, nameLine,
                  pageLine, detailLine, typeDesc, catDesc, hit, hic, fitTot, editPlus_length,
                  editMinus_length, pageHead_length, nameHead_length, header1_length, toMsg_length,
                  hdr2Line_length, blankLine_length, Int.natCast_add, Int.add_assoc,
                  hX'] with done ++ [t], todo'
              · -- no page break
                have hm := compare_mod20_gt (x := (S.lines : Int)) (by omega)
                cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length,
                  List.take_take, List.drop_take, mod20, hm, hc, hit, hic, htyr, hcgr]
                cobol_inv [report3_append, step3, hS, hout, hSf, hc, hb, detailLine, typeDesc, catDesc,
                  hit, hic, fitTot, editMinus_length, Int.natCast_add, Int.add_assoc,
                  hX'] with done ++ [t], todo'
        · by_cases hdn : done = []
          · -- the first transaction: no account total; the cross-reference lookup
            have hS0 : report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done =
                ⟨List.replicate 16 64, true, 0, 0, 0, 0, 0, []⟩ := by rw [hdn]; rfl
            have hSl : S.lines = 0 := by rw [← hS, hS0]
            have hSp : S.page = 0 := by rw [← hS, hS0]
            have hSa : S.acct = 0 := by rw [← hS, hS0]
            have hSg : S.grand = 0 := by rw [← hS, hS0]
            have hSf : S.first = true := by rw [← hS, hS0]
            have hSo : S.out = [] := by rw [← hS, hS0]
            simp [hdn] at hfirst
            rcases hix : Sem.findKey { off := 0, len := 16 } t.card (xrefs.map Xref.bytes) with _ | ix
            · -- LEAF-FIRST-XREF: the card is missing
              right
              have hs : step3x xrefs types catgs parm (.go S) t =
                  .abend { S with out := (abendEvents (invCardMsg ++ t.card) ++
                    Event.display t.bytes :: S.out) } := by
                simp [step3x, hin, hc, hix, hSf]
              have hR := report3x_abend_at xrefs types catgs parm done todo' t S _ hX hs
              simp only [ExitX3, res, hR, result3, header3]
              cobol_auto [List.take_take, List.drop_take, hc, hix, hnum23, hSl, hSp, hSa, hSg]
              cobol_inv [hout, abendEvents, invCardMsg, statusMsg, abendMsg, hSo]
            · have hixl := findKey_lt hix
              simp only [List.length_map] at hixl
              obtain ⟨x1, x2, x3, x4, x5⟩ := hxv _ (getD_mem hixl)
              have hxg := getD_map Xref.bytes xrefs hixl
              rcases hit : Sem.findKey { off := 0, len := 2 } t.ty types with _ | it
              · -- LEAF-FIRST-TYPE
                right
                have hs : step3x xrefs types catgs parm (.go S) t =
                    .abend { S with out := (abendEvents (invTypeMsg ++ t.ty) ++
                      Event.display t.bytes :: S.out) } := by
                  simp [step3x, hin, hc, hix, hit, hSf]
                have hR := report3x_abend_at xrefs types catgs parm done todo' t S _ hX hs
                simp only [ExitX3, res, hR, result3, header3]
                cobol_auto [List.take_take, List.drop_take, hc, hix, hit, hnum23, Xref.bytes, hxg, hSl,
                  hSp, hSa, hSg]
                cobol_inv [hout, abendEvents, invTypeMsg, statusMsg, abendMsg, hSo]
              · have hitl := findKey_lt hit
                have htyr := htyl _ (getD_mem' hitl)
                rcases hic : Sem.findKey { off := 0, len := 6 }
                    (t.ty ++ encodeNum {} FD_TRAN_CAT_CD.fmt t.cat) catgs with _ | ic
                · -- LEAF-FIRST-CAT
                  right
                  have hs : step3x xrefs types catgs parm (.go S) t =
                      .abend { S with out := (abendEvents (invCatMsg ++ t.ty ++
                        encodeNum {} FD_TRAN_CAT_CD.fmt t.cat) ++ Event.display t.bytes :: S.out) } := by
                    simp [step3x, hin, hc, hix, hit, hic, hSf]
                  have hR := report3x_abend_at xrefs types catgs parm done todo' t S _ hX hs
                  simp only [ExitX3, res, hR, result3, header3]
                  cobol_auto [List.take_take, List.drop_take, hc, hix, hit, hic, htyr, hnum23, Xref.bytes,
                    hxg, hSl, hSp, hSa, hSg]
                  cobol_inv [hout, abendEvents, invCatMsg, statusMsg, abendMsg, hSo]
                · -- LEAF-FIRST-FOUND
                  have hicl := findKey_lt hic
                  have hcgr := hcgl _ (getD_mem' hicl)
                  have hX' : report3x xrefs types catgs parm (done ++ [t]) =
                      .go (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) (done ++ [t])) := by
                    rw [report3x_append, hX, report3_append, hS,
                      step3x_go xrefs types catgs parm S t hin (fun _ => by simp [hix]) (by simp [hit])
                        (by simp [hic])]
                  left
                  have hm : compare ((4 : Int) % 20) 0 = .gt := by decide
                  have hm' : compare (4 : Int) 0 = .gt := by decide
                  cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length,
                    List.take_take, List.drop_take, nameHead_length, header1_length, toMsg_length,
                    hdr2Line_length, blankLine_length, mod20, hm, hm', hc, hSl, hSp, hSa, hSg, Xref.bytes,
                    hxg, hix, hit, hic, htyr, hcgr]
                  cobol_inv [report3_append, step3, hS, hout, hSl, hSp, hSa, hSg, hSf, hSo, hc, headers,
                    hdr1Line, nameLine, detailLine, typeDesc, catDesc, xrefOf, hix, hit, hic, fitTot,
                    editMinus_length, nameHead_length, header1_length, toMsg_length, hdr2Line_length,
                    blankLine_length, Int.natCast_add, Int.add_assoc, hX'] with done ++ [t], todo'
          · -- a new card: the account total of the previous card, the cross-reference lookup
            have hSf : S.first = false := by rw [← hS]; exact report3_first _ _ _ _ _ done hdn
            simp only [hdn, ↓reduceIte] at hfirst
            rcases hphase with ⟨h0, -⟩ | ⟨-, hsd, hed, hxa, hxa1, hxa2, htr⟩
            · exact absurd h0 hdn
            have hnl := name_read mem parm hnh hsd hto hed
            rcases hix : Sem.findKey { off := 0, len := 16 } t.card (xrefs.map Xref.bytes) with _ | ix
            · -- LEAF-NEW-XREF
              right
              have hs : step3x xrefs types catgs parm (.go S) t =
                  .abend { S with out := (abendEvents (invCardMsg ++ t.card) ++
                    .write 5 hdr2Line :: .write 5 (acctLine S.acct) :: Event.display t.bytes :: S.out) } := by
                simp [step3x, hin, hc, hix, hSf]
              have hR := report3x_abend_at xrefs types catgs parm done todo' t S _ hX hs
              simp only [ExitX3, res, hR, result3, header3]
              cobol_auto [edit_plus, editPlus_length, List.take_take, List.drop_take, acctHead_length,
                hdr2Line_length, hc, hix, hnum23]
              cobol_inv [hout, abendEvents, invCardMsg, statusMsg, abendMsg, acctLine, editPlus_length,
                acctHead_length, hdr2Line_length]
            · have hixl := findKey_lt hix
              simp only [List.length_map] at hixl
              obtain ⟨x1, x2, x3, x4, x5⟩ := hxv _ (getD_mem hixl)
              have hxg := getD_map Xref.bytes xrefs hixl
              rcases hit : Sem.findKey { off := 0, len := 2 } t.ty types with _ | it
              · -- LEAF-NEW-TYPE
                right
                have hs : step3x xrefs types catgs parm (.go S) t =
                    .abend { S with out := (abendEvents (invTypeMsg ++ t.ty) ++
                      .write 5 hdr2Line :: .write 5 (acctLine S.acct) :: Event.display t.bytes :: S.out) } := by
                  simp [step3x, hin, hc, hix, hit, hSf]
                have hR := report3x_abend_at xrefs types catgs parm done todo' t S _ hX hs
                simp only [ExitX3, res, hR, result3, header3]
                cobol_auto [edit_plus, editPlus_length, List.take_take, List.drop_take, acctHead_length,
                  hdr2Line_length, hc, hix, hit, hnum23, Xref.bytes, hxg]
                cobol_inv [hout, abendEvents, invTypeMsg, statusMsg, abendMsg, acctLine, editPlus_length,
                  acctHead_length, hdr2Line_length]
              · have hitl := findKey_lt hit
                have htyr := htyl _ (getD_mem' hitl)
                rcases hic : Sem.findKey { off := 0, len := 6 }
                    (t.ty ++ encodeNum {} FD_TRAN_CAT_CD.fmt t.cat) catgs with _ | ic
                · -- LEAF-NEW-CAT
                  right
                  have hs : step3x xrefs types catgs parm (.go S) t =
                      .abend { S with out := (abendEvents (invCatMsg ++ t.ty ++
                        encodeNum {} FD_TRAN_CAT_CD.fmt t.cat) ++ .write 5 hdr2Line ::
                        .write 5 (acctLine S.acct) :: Event.display t.bytes :: S.out) } := by
                    simp [step3x, hin, hc, hix, hit, hic, hSf]
                  have hR := report3x_abend_at xrefs types catgs parm done todo' t S _ hX hs
                  simp only [ExitX3, res, hR, result3, header3]
                  cobol_auto [edit_plus, editPlus_length, List.take_take, List.drop_take, acctHead_length,
                    hdr2Line_length, hc, hix, hit, hic, htyr, hnum23, Xref.bytes, hxg]
                  cobol_inv [hout, abendEvents, invCatMsg, statusMsg, abendMsg, acctLine, editPlus_length,
                    acctHead_length, hdr2Line_length]
                · -- LEAF-NEW-FOUND
                  have hicl := findKey_lt hic
                  have hcgr := hcgl _ (getD_mem' hicl)
                  have hX' : report3x xrefs types catgs parm (done ++ [t]) =
                      .go (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) (done ++ [t])) := by
                    rw [report3x_append, hX, report3_append, hS,
                      step3x_go xrefs types catgs parm S t hin (fun _ => by simp [hix]) (by simp [hit])
                        (by simp [hic])]
                  left
                  by_cases hb : (S.lines + 2) % 20 = 0
                  · have hm := compare_mod20_eq (x := (S.lines : Int) + 1 + 1) (by omega)
                    cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length,
                      List.take_take, List.drop_take, pageHead_length, acctHead_length, nameHead_length,
                      header1_length, toMsg_length, hdr2Line_length, blankLine_length, mod20, hm, hc,
                      Xref.bytes, hxg, hix, hit, hic, htyr, hcgr, hnl]
                    cobol_inv [report3_append, step3, hS, hout, hSf, hc, hb, headers, hdr1Line, nameLine,
                      pageLine, acctLine, detailLine, typeDesc, catDesc, xrefOf, hix, hit, hic, fitTot,
                      editPlus_length, editMinus_length, pageHead_length, acctHead_length,
                      nameHead_length, header1_length, toMsg_length, hdr2Line_length, blankLine_length,
                      Int.natCast_add, Int.add_assoc, hX'] with done ++ [t], todo'
                  · have hm := compare_mod20_gt (x := (S.lines : Int) + 1 + 1) (by omega)
                    cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length,
                      List.take_take, List.drop_take, acctHead_length, hdr2Line_length, mod20, hm, hc,
                      Xref.bytes, hxg, hix, hit, hic, htyr, hcgr]
                    cobol_inv [report3_append, step3, hS, hout, hSf, hc, hb, acctLine, detailLine,
                      typeDesc, catDesc, xrefOf, hix, hit, hic, fitTot, editPlus_length,
                      editMinus_length, acctHead_length, hdr2Line_length, Int.natCast_add,
                      Int.add_assoc, hX'] with done ++ [t], todo'
      · -- outside the range: `NEXT SENTENCE` leaves the loop
        right
        have hs : step3x xrefs types catgs parm (.go S) t = .stop S := by simp [step3x, hin]
        have hR := report3x_stop_at xrefs types catgs parm done todo' t S S hX hs
        simp only [ExitX3, res, hR, result3, header3]
        by_cases hlo : Sem.cmpBytes (t.proc.take 10) (parm.take 10) = .lt
        · cobol_auto [hlo, List.take_take, List.drop_take]
          cobol_inv [hout, hS]
        · have hhi : Sem.cmpBytes (t.proc.take 10) ((parm.drop 11).take 10) = .gt :=
            Classical.byContradiction fun h => hin ⟨hlo, h⟩
          cobol_auto [hhi, List.take_take, List.drop_take]
          cobol_inv [hout, hS]
end Cbtrn03c
end CardDemo

#print axioms CardDemo.Cbtrn03c.cbtrn03c_any
