-- Copied unchanged from coblean (frozen snapshot ~/coblean_snapshots/coblean-20261024T1004Z,
-- Examples/Cbact04cEvents.lean); only the import differs. coblean and JimpleLean both have a library
-- named `Examples`, so equiv-lean cannot import the original module next to JimpleLean.
/-
# CBACT04C on any input: every event

`cbact04c_all` fixes CBACT04C's account `REWRITE`s and the number of its transaction `WRITE`s.
`cbact04c_events` fixes the whole event list: every `DISPLAY`, every transaction record written
(all 350 bytes) and every account record rewritten, in order, as a fold over the
category-balance records (`model4`).  The transaction records contain bytes the program never
sets: the tail of `TRAN-DESC` (`STRING` does not pad) and the `FILLER` of `TRAN-RECORD`; they
are the initial storage's (parameters `descTail`, `fill`), as is `PARM-DATE` (the linkage
section, parameter `parm`).
-/
import EquivLean.Demo.Cobol.Cbact04c.All
open Cobol

namespace CardDemo.Cbact04c

/-- `START OF EXECUTION OF PROGRAM CBACT04C` in EBCDIC. -/
def startMsg : List UInt8 := [226, 227, 193, 217, 227, 64, 214, 198, 64, 197, 231, 197, 195, 228, 227, 201, 214, 213, 64, 214, 198, 64, 215, 217, 214, 199, 217, 193, 212, 64, 195, 194, 193, 195, 227, 240, 244, 195]

/-- `END OF EXECUTION OF PROGRAM CBACT04C` in EBCDIC. -/
def endMsg : List UInt8 := [197, 213, 196, 64, 214, 198, 64, 197, 231, 197, 195, 228, 227, 201, 214, 213, 64, 214, 198, 64, 215, 217, 214, 199, 217, 193, 212, 64, 195, 194, 193, 195, 227, 240, 244, 195]

/-- `System    ` (`TRAN-SOURCE`) in EBCDIC. -/
def systemSrc : List UInt8 := [226, 168, 162, 163, 133, 148, 64, 64, 64, 64]

/-- `Int. for a/c ` (the start of `TRAN-DESC`) in EBCDIC. -/
def descHead : List UInt8 := [201, 149, 163, 75, 64, 134, 150, 153, 64, 129, 97, 131, 64]

theorem startMsg_eq : Codepage.encode037 "START OF EXECUTION OF PROGRAM CBACT04C" = some startMsg := by decide +kernel
theorem endMsg_eq : Codepage.encode037 "END OF EXECUTION OF PROGRAM CBACT04C" = some endMsg := by decide +kernel
theorem systemSrc_eq : Codepage.encode037 "System    " = some systemSrc := by decide +kernel
theorem descHead_eq : Codepage.encode037 "Int. for a/c " = some descHead := by decide +kernel

/-- 110 EBCDIC spaces (merchant name, city and zip). -/
def spaces110 : List UInt8 := [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64]

/-- `Z-GET-DB2-FORMAT-TIMESTAMP` of a clock reading (`FUNCTION CURRENT-DATE`):
`YYYY-MM-DD-hh.mm.ss.ff0000`. -/
def db2ts (c : List UInt8) : List UInt8 :=
  c.take 4 ++ [96] ++ (c.drop 4).take 2 ++ [96] ++ (c.drop 6).take 2 ++ [96] ++
    (c.drop 8).take 2 ++ [75] ++ (c.drop 10).take 2 ++ [75] ++ (c.drop 12).take 2 ++ [75] ++
    (c.drop 14).take 2 ++ [240, 240, 240, 240]

/-- The monthly interest of category `c` at rate `r` (`WS-MONTHLY-INT`). -/
def monthly (c : Cat) (r : Int) : Int :=
  (Sem.fitNum {} WS_MONTHLY_INT.fmt (divRound .truncation (c.bal * r) 120000)).2

/-- The `k`-th interest transaction record (from 0), for account `a` and amount `amt`
(`1300-B-WRITE-TX`): id `PARM-DATE` and the 6-digit count, type `01`, category `0005`, source
`System`, description `Int. for a/c ` and the account id (then the rest of `TRAN-DESC`, never
set), the amount, merchant 0, spaces, the card number, the clock reading twice, and `FILLER`. -/
def txRec (parm descTail fill : List UInt8) (clk : Nat → List UInt8) (k : Nat) (a : Acc)
    (amt : Int) : List UInt8 :=
  parm ++ encodeNum {} WS_TRANID_SUFFIX.fmt ((k : Int) + 1) ++ [240, 241] ++
    encodeNum {} TRAN_CAT_CD.fmt 5 ++ systemSrc ++ descHead ++ encodeNum {} ACCT_ID.fmt a.id ++
    descTail ++ encodeNum {} TRAN_AMT.fmt amt ++ encodeNum {} TRAN_MERCHANT_ID.fmt 0 ++ spaces110 ++
    a.xrec.take 16 ++ db2ts (clk k) ++ db2ts (clk k) ++ fill

/-- What CBACT04C has done after some category records: the account of the last record, its
interest so far (`WS-TOTAL-INT`), the transactions written, the events (newest first). -/
structure M4 where
  last : Option Acc
  total : Int
  k : Nat
  out : List Event

/-- One category record `c` of account `a`: `DISPLAY` it; on a new account, `REWRITE` the
previous one with its interest; on a nonzero rate, add the monthly interest and `WRITE` its
transaction. -/
def step4 (rate : Acc → Cat → Int) (parm descTail fill : List UInt8) (clk : Nat → List UInt8)
    (s : M4) (p : Acc × Cat) : M4 :=
  let out1 := Event.display (Cat.bytes p.1.id p.2) :: s.out
  let (out2, total) : List Event × Int := match s.last with
    | some l => if l.id = p.1.id then (out1, s.total) else (.rewrite 3 (l.posted s.total) :: out1, 0)
    | none => (out1, 0)
  if rate p.1 p.2 = 0 then { last := some p.1, total, k := s.k, out := out2 }
  else
    let amt := monthly p.2 (rate p.1 p.2)
    { last := some p.1, total := (Sem.fitNum {} WS_TOTAL_INT.fmt (total + amt)).2, k := s.k + 1,
      out := .write 5 (txRec parm descTail fill clk s.k p.1 amt) :: out2 }

/-- The model after the category records `ps`. -/
def model4 (rate : Acc → Cat → Int) (parm descTail fill : List UInt8) (clk : Nat → List UInt8)
    (ps : List (Acc × Cat)) : M4 :=
  ps.foldl (step4 rate parm descTail fill clk) ⟨none, 0, 0, []⟩

/-! ## The model: lemmas -/

section ModelLemmas
variable (rate : Acc → Cat → Int) (parm descTail fill : List UInt8) (clk : Nat → List UInt8)

theorem model4_append (ps : List (Acc × Cat)) (p : Acc × Cat) :
    model4 rate parm descTail fill clk (ps ++ [p]) =
      step4 rate parm descTail fill clk (model4 rate parm descTail fill clk ps) p := by
  simp [model4, List.foldl_append]

theorem model4_append2 (ps qs : List (Acc × Cat)) (p : Acc × Cat) :
    model4 rate parm descTail fill clk (ps ++ (qs ++ [p])) =
      step4 rate parm descTail fill clk (model4 rate parm descTail fill clk (ps ++ qs)) p := by
  rw [← List.append_assoc, model4_append]

theorem foldl_step4_last :
    ∀ (ps : List (Acc × Cat)) (s : M4),
      (ps.foldl (step4 rate parm descTail fill clk) s).last = (ps.getLast?.map Prod.fst).or s.last
  | [], s => by simp
  | p :: ps, s => by
    rw [List.foldl_cons, foldl_step4_last ps]
    cases ps with
    | nil => simp [step4]; split <;> rfl
    | cons q qs =>
      cases h : (q :: qs).getLast? with
      | none => simp at h
      | some x => simp [h]

theorem foldl_step4_k :
    ∀ (ps : List (Acc × Cat)) (s : M4),
      (ps.foldl (step4 rate parm descTail fill clk) s).k = s.k + nTxA rate ps
  | [], s => by simp [nTxA]
  | p :: ps, s => by
    rw [List.foldl_cons, foldl_step4_k ps]
    simp only [nTxA, List.filter_cons]
    unfold step4
    by_cases h : rate p.1 p.2 = 0 <;> simp [h] <;> omega

theorem model4_k (ps : List (Acc × Cat)) :
    (model4 rate parm descTail fill clk ps).k = nTxA rate ps := by
  simp [model4, foldl_step4_k]

/-- The records of one account, from a state whose last account is another one: the account
becomes the last, its interest is its categories' (`totalInt`). -/
theorem foldl_step4_acc (a : Acc) :
    ∀ (dc : List Cat) (s : M4), dc ≠ [] → (∀ l, s.last = some l → l.id ≠ a.id) →
      (dc.map (Prod.mk a)).foldl (step4 rate parm descTail fill clk) s =
        { (dc.map (Prod.mk a)).foldl (step4 rate parm descTail fill clk) s with
          last := some a, total := totalInt (rate a) dc }
  | [], _, h, _ => absurd rfl h
  | c :: cs, s, _, hl => by
    -- after the first record the account is `a` and the total `addInt … 0 c`
    have h1 : (step4 rate parm descTail fill clk s (a, c)).last = some a ∧
        (step4 rate parm descTail fill clk s (a, c)).total = addInt (rate a) 0 c := by
      unfold step4 addInt monthly
      cases hs : s.last with
      | none => by_cases hr : rate a c = 0 <;> simp [hr]
      | some l =>
        have := hl l hs
        by_cases hr : rate a c = 0 <;> simp [hr, this]
    -- the later records stay with `a`
    have rest : ∀ (cs : List Cat) (t : M4), t.last = some a →
        (cs.map (Prod.mk a)).foldl (step4 rate parm descTail fill clk) t =
          { (cs.map (Prod.mk a)).foldl (step4 rate parm descTail fill clk) t with
            last := some a, total := cs.foldl (addInt (rate a)) t.total } := by
      intro cs
      induction cs with
      | nil => intro t ht; cases t; simp_all
      | cons c' cs ih =>
        intro t ht
        rw [List.map_cons, List.foldl_cons, ih]
        · simp only [List.foldl_cons]
          congr 2
          unfold step4 addInt monthly
          by_cases hr : rate a c' = 0 <;> simp [ht, hr]
        · unfold step4
          simp only [ht]
          by_cases hr : rate a c' = 0 <;> simp [hr]
    rw [List.map_cons, List.foldl_cons, rest cs _ h1.1, h1.2]
    simp [totalInt]

/-- After complete accounts `pre` and the first records `dc` of account `cur`: the last account
is `cur` and its interest so far is `dc`'s. -/
theorem model4_cur (pre : List Acc) (cur : Acc) (dc : List Cat) (hdc : dc ≠ [])
    (hpre : ∀ a ∈ pre, a.id ≠ cur.id) :
    (model4 rate parm descTail fill clk (items pre ++ dc.map (Prod.mk cur))).last = some cur ∧
      (model4 rate parm descTail fill clk (items pre ++ dc.map (Prod.mk cur))).total =
        totalInt (rate cur) dc := by
  have hl : ∀ l, (model4 rate parm descTail fill clk (items pre)).last = some l → l.id ≠ cur.id := by
    intro l h
    simp only [model4, foldl_step4_last, Option.or_none] at h
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    have hm : p ∈ items pre := List.mem_of_getLast? hp
    simp only [items, List.mem_flatMap, List.mem_map] at hm
    obtain ⟨a, ha, c, -, rfl⟩ := hm
    exact hpre a ha
  have := foldl_step4_acc rate parm descTail fill clk cur dc _ hdc hl
  simp only [model4, List.foldl_append] at this ⊢
  rw [this]
  exact ⟨rfl, rfl⟩

end ModelLemmas

/-! ## The loop invariant -/

/-- `InvA` with the events: before the first record only the start message; after complete
accounts `pre` and the first records `dc` of `cur`, the model's events. `PARM-DATE`, the tail
of `TRAN-DESC` and the `FILLER` of `TRAN-RECORD` keep their initial bytes. -/
def InvE (m : Mem) (clk : Nat → List UInt8) (accs : List Acc) (rate : Acc → Cat → Int)
    (ai : Acc → Nat) (inp0 : List (Nat × List (List UInt8))) (tcat xrefs discs : List (List UInt8))
    (rest : List (Option (Acc × Cat))) (st : State) : Prop :=
  st.idx = [] ∧ st.slots = [] ∧ st.active = [] ∧ st.inp = inp0 ∧ st.mem.size = 1739 ∧
  st.mem.read 1622 1 = (if rest.isEmpty then [232] else [213]) ∧
  st.mem.read 1729 10 = m.read 1729 10 ∧ st.mem.read 1314 76 = m.read 1314 76 ∧
  st.mem.read 1588 20 = m.read 1588 20 ∧
  ∃ f1 f2 f4 f3 f5 : FileSt, st.files = [(1, f1), (2, f2), (4, f4), (3, f3), (5, f5)] ∧
    f1.mode = some .input ∧ f1.recs = tcat ∧ f1.eof = rest.isEmpty ∧
    f2.mode = some .input ∧ f2.recs = xrefs ∧ f4.mode = some .input ∧ f4.recs = discs ∧
    f3.mode = some .io ∧ f5.mode = some .output ∧
    (∀ b ∈ accs, Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt b.id) f3.recs =
      some (ai b)) ∧
    -- nothing read yet
    ((f1.pos = 0 ∧ (rest = (items accs).map some ++ [none] ∨ (rest = [] ∧ items accs = [])) ∧
      st.clockN = 0 ∧ st.out = [.display startMsg] ∧
      (∀ b ∈ accs, f3.recs.getD (ai b) [] = b.bytes) ∧
      st.mem.read 1711 1 = [232] ∧ st.mem.read 1678 11 = spaces11 ∧
      st.mem.read 1712 9 = encodeNum {} WS_RECORD_COUNT.fmt 0 ∧
      st.mem.read 1721 6 = encodeNum {} WS_TRANID_SUFFIX.fmt 0) ∨
    -- the records of the accounts `pre` and the first records `dc` of account `cur` processed
     (∃ pre cur post dc tc, accs = pre ++ cur :: post ∧ cur.cats = dc ++ tc ∧ dc ≠ [] ∧
      f1.pos = (items pre).length + dc.length ∧
      ((rest = [] ∧ tc = [] ∧ post = []) ∨
        rest = (tc.map (Prod.mk cur) ++ items post).map some ++ [none]) ∧
      st.clockN = nTxA rate (items pre ++ dc.map (Prod.mk cur)) ∧
      st.out = (model4 rate (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
        (items pre ++ dc.map (Prod.mk cur))).out ++ [.display startMsg] ∧
      (∀ b ∈ cur :: post, f3.recs.getD (ai b) [] = b.bytes) ∧
      st.mem.read 1711 1 = [213] ∧ st.mem.read 1678 11 = Sem.digitChars {} 11 cur.id.natAbs ∧
      st.mem.read 956 300 = cur.bytes ∧ st.mem.read 852 16 = cur.xrec.take 16 ∧
      st.mem.read 1700 11 = encodeNum {} WS_TOTAL_INT.fmt (totalInt (rate cur) dc) ∧
      st.mem.read 1712 9 = encodeNum {} WS_RECORD_COUNT.fmt ((items pre).length + dc.length) ∧
      st.mem.read 1721 6 =
        encodeNum {} WS_TRANID_SUFFIX.fmt (nTxA rate (items pre ++ dc.map (Prod.mk cur)))))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **CBACT04C on any input: every event.**  For every input as in `cbact04c_all`, CBACT04C ends
with `GOBACK` and its events are the start message, then for each category record (in file
order) what `step4` says (`DISPLAY` of the record, the `REWRITE` of the previous account on a
change of account, the interest transaction for a nonzero rate), then the end message. -/
theorem cbact04c_events (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
    (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧
      0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post)
    (accs : List Acc) (hval : ∀ a ∈ accs, a.valid)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) (hlen : (items accs).length < 999999)
    (accts xrefs discs : List (List UInt8)) (ai xi : Acc → Nat)
    (hacct : ∀ a ∈ accs, Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt a.id)
      accts = some (ai a) ∧ accts.getD (ai a) [] = a.bytes)
    (hxref : ∀ a ∈ accs, Sem.findKey { off := 25, len := 11 }
      (encodeNum {} FD_XREF_ACCT_ID.fmt a.id) xrefs = some (xi a) ∧ xrefs.getD (xi a) [] = a.xrec)
    (rate : Acc → Cat → Int) (di : Acc → Cat → Nat) (dfill : Acc → Cat → List UInt8)
    (hdisc : ∀ a ∈ accs, ∀ c ∈ a.cats, Sem.findKey { off := 0, len := 16 }
        (a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat) discs = some (di a c) ∧
      discs.getD (di a c) [] = a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat ++
        encodeNum {} DIS_INT_RATE.fmt (rate a c) ++ dfill a c ∧
      (dfill a c).length = 28 ∧ (rate a c).natAbs < 1000000)
    (n : Nat) (hn : (items accs).length < n) :
    let r := Cbact04c.run { clock := clk } (n + 60)
      (Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)), (2, xrefs),
        (3, accts), (4, discs)])
    let s := model4 rate (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk (items accs)
    r.1 = .stop .goback ∧ r.2.out = [.display endMsg] ++ s.out ++ [.display startMsg] := by
  intro r s
  simp only [r, s]
  cobol_auto
  cobol_loop (InvE m clk accs rate ai
      [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)), (2, xrefs), (3, accts), (4, discs)]
      ((items accs).map (fun p => Cat.bytes p.1.id p.2)) xrefs discs) ((items accs).map some ++ [none])
  · -- after the loop: five CLOSEs, DISPLAY, GOBACK
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := loopState
    obtain ⟨rfl, rfl, rfl, rfl, hsz, heof, -, -, -, f1, f2, f4, f3, f5, rfl, h1m, -, -, h2m, -, h4m, -,
      h3m, h5m, -, hph⟩ := hloopInv
    simp only [List.isEmpty_nil, ↓reduceIte] at heof
    rcases hph with ⟨-, hrest, -, hout, -⟩ | ⟨pre, cur, post, dc, tc, hacc, hcur, -, -, hrest, -, hout, -⟩
    · rcases hrest with h | ⟨-, hi⟩
      · simp at h
      have h0 : accs = [] := by
        cases accs with
        | nil => rfl
        | cons a as =>
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hne, -⟩ := hval a (by simp)
          cases hc : a.cats with
          | nil => exact absurd hc hne
          | cons c cs => simp [items, hc] at hi
      subst h0
      cobol_auto
      simp [hout, items, model4, endMsg]
    · rcases hrest with ⟨-, rfl, rfl⟩ | h
      · simp only [List.append_nil] at hcur
        subst hacc
        cobol_auto
        simp [hout, items_concat, hcur, endMsg]
      · simp at h
  · -- before the loop: nothing read, the counters and flags have their VALUEs
    cobol_inv [startMsg, spaces11]
    · exact fun b hb => (hacct b hb).1
    · exact fun b hb => (hacct b hb).2
  · simp; omega
  · -- the loop ends exactly after the end-of-file READ
    rintro ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨-, -, -, -, -, heof, -⟩
    simp only [List.isEmpty_nil, ↓reduceIte] at heof
    cobol_auto
  · -- one iteration: READ the next record and process it, or reach the end of the file
    rintro y ys ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨rfl, rfl, rfl, rfl, hsz, heof, hparm, hdesc, hfil, f1, f2, f4, f3, f5, rfl, h1m, h1r, h1e, h2m,
        h2r, h4m, h4r, h3m, h5m, hfk, hph⟩
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at heof h1e
    replace hsz : mem.size = 1739 := hsz
    refine ⟨by cobol_auto, ?_⟩
    rcases hph with ⟨h1p, hrest, hclk0, hout, hgd, h1711, h1678, hcnt, hsuf⟩ |
      ⟨pre, cur, post, dc, tc, hacc, hcur, hdc, h1p, hrest, hclk0, hout, hgd, h1711, h1678, h956,
        h852, h1700, hcnt, hsuf⟩
    · -- nothing read yet
      dsimp only at h1711 h1678 hcnt hsuf hclk0 hout
      replace hrest : y :: ys = (items accs).map some ++ [none] := by
        rcases hrest with h | ⟨h, -⟩
        · exact h
        · simp at h
      cases accs with
      | nil =>
        -- the first READ reaches the end of the file
        simp only [items, List.flatMap_nil, List.map_nil, List.nil_append, List.cons.injEq] at hrest
        obtain ⟨rfl, rfl⟩ := hrest
        have hnone : f1.recs[f1.pos]? = none := by rw [h1r, h1p]; simp [items]
        cobol_auto
        cobol_inv [items]
      | cons a0 accs' =>
        -- the first record: read its account and cross-reference
        obtain ⟨hid, hid0, hs, hbal, hmid, hcc, hcd, hzip, hgrp, haf, hxrec, hcne, hcv⟩ :=
          hval a0 (by simp)
        obtain ⟨c0, cs, hc0⟩ : ∃ c cs, a0.cats = c :: cs := by
          cases h : a0.cats with
          | nil => exact absurd h hcne
          | cons c cs => exact ⟨c, cs, rfl⟩
        have hrest' := hrest
        simp only [items, List.flatMap_cons, hc0, List.map_cons, List.cons_append, List.map_append,
          List.cons.injEq] at hrest'
        obtain ⟨rfl, hys⟩ := hrest'
        obtain ⟨hty, hfill, hcat, hcat0, hcbal⟩ := hcv c0 (by simp [hc0])
        obtain ⟨hdi, hdg, hdf, hrate⟩ := hdisc a0 (by simp) c0 (by simp [hc0])
        obtain ⟨hxi, hxg⟩ := hxref a0 (by simp)
        have hfk0 := hfk a0 (by simp)
        have hgd0 := hgd a0 (by simp)
        have hsome : f1.recs[f1.pos]? = some (Cat.bytes a0.id c0) := by
          rw [h1r, h1p]; simp [items, hc0]
        obtain ⟨pre, mil, post, hpre, hpost, hmil, hmil0, hck⟩ := hclk 0
        by_cases hr0 : rate a0 c0 = 0
        · cobol_auto [hclk0, Acc.bytes, Cat.bytes, spaces11]
          cobol_inv [Acc.bytes, Cat.bytes, totalInt, addInt, fitNum_idem, items, nTxA, hys, model4, step4,
            txRec, monthly, db2ts, hout, systemSrc, descHead, spaces110, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt]
            with _, _, _, _, _, [], a0, accs', [c0], cs
        · cobol_auto [hclk0, Acc.bytes, Cat.bytes, spaces11]
          cobol_inv [Acc.bytes, Cat.bytes, totalInt, addInt, fitNum_idem, items, nTxA, hys, model4, step4,
            txRec, monthly, db2ts, hout, systemSrc, descHead, spaces110, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt]
            with _, _, _, _, _, [], a0, accs', [c0], cs
    · -- the records of `pre` and `dc` processed
      dsimp only at h1711 h1678 h956 h852 h1700 hcnt hsuf hclk0 hout
      replace hrest : y :: ys = (tc.map (Prod.mk cur) ++ items post).map some ++ [none] := by
        rcases hrest with ⟨h, -⟩ | h
        · simp at h
        · exact h
      obtain ⟨hid, hid0, hs, hbal, hmid, hcc, hcd, hzip, hgrp, haf, hxrec, hcne, hcv⟩ :=
        hval cur (by simp [hacc])
      have hT := totalInt_bound (rate cur) dc
      -- the record count and the transaction-id suffix stay below their capacities
      have hcntb : (items pre).length + dc.length < 999999 := by
        have : (items accs).length = (items pre).length + (dc.length + tc.length) + (items post).length := by
          rw [hacc, items_mid, hcur]; simp; omega
        omega
      -- (the count is stored as `↑(items pre).length + ↑dc.length`: bounds for both terms)
      have hpl : (items pre).length < 999999 := by omega
      have hdl : dc.length < 999999 := by omega
      have hntxb : nTxA rate (items pre ++ dc.map (Prod.mk cur)) < 999999 := by
        have := List.length_filter_le (fun p => decide (rate p.1 p.2 ≠ 0)) (items pre ++ dc.map (Prod.mk cur))
        simp only [nTxA]; simp only [List.length_append, List.length_map] at this ⊢; omega
      -- the model after these records: last account `cur`, its interest so far, the transactions
      have hpreid : ∀ a ∈ pre, a.id ≠ cur.id := by
        intro a ha
        rw [hacc] at hdist
        exact (List.pairwise_append.1 hdist).2.2 a ha cur (by simp)
      obtain ⟨hmL, hmT⟩ := model4_cur rate (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk pre cur
        dc hdc hpreid
      have hmK := model4_k rate (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
        (items pre ++ dc.map (Prod.mk cur))
      cases tc with
      | cons c tc' =>
        -- a later record of the same account
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at hrest
        obtain ⟨rfl, hys⟩ := hrest
        obtain ⟨hty, hfill, hcat, hcat0, hcbal⟩ := hcv c (by simp [hcur])
        obtain ⟨hdi, hdg, hdf, hrate⟩ := hdisc cur (by simp [hacc]) c (by simp [hcur])
        have hsome : f1.recs[f1.pos]? = some (Cat.bytes cur.id c) := by
          rw [h1r, h1p, hacc]; exact tcat_mid _ pre post cur dc tc' c hcur
        obtain ⟨pre', mil, post', hpre, hpost, hmil, hmil0, hck⟩ :=
          hclk (nTxA rate (items pre ++ dc.map (Prod.mk cur)))
        by_cases hr0 : rate cur c = 0
        · cobol_auto [hclk0, Acc.bytes, Cat.bytes]
          cobol_inv [Cat.bytes, totalInt_append, addInt, nTxA, List.filter_append, hys, model4_append2,
            step4, txRec, monthly, db2ts, hout, systemSrc, descHead, spaces110, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt,
            WS_MONTHLY_INT.fmt, Int.add_assoc] with _, _, _, _, _, pre, cur, post, dc ++ [c], tc'
        · cobol_auto [hclk0, Acc.bytes, Cat.bytes]
          cobol_inv [Cat.bytes, totalInt_append, addInt, nTxA, List.filter_append, hys, model4_append2,
            step4, txRec, monthly, db2ts, hout, systemSrc, descHead, spaces110, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt,
            WS_MONTHLY_INT.fmt, Int.add_assoc] with _, _, _, _, _, pre, cur, post, dc ++ [c], tc'
      | nil =>
        simp only [List.append_nil] at hcur
        cases post with
        | nil =>
          -- the READ reaches the end of the file
          simp only [List.map_nil, List.nil_append, items, List.flatMap_nil, List.cons.injEq] at hrest
          obtain ⟨rfl, rfl⟩ := hrest
          have hnone : f1.recs[f1.pos]? = none := by
            rw [h1r, h1p, hacc]; simp [items, hcur]
          cobol_auto
          cobol_inv with _, _, _, _, _, pre, cur, [], dc, []
        | cons nxt post' =>
          -- the first record of the next account: post the interest of `cur`, read the next one
          have hnv := hval nxt (by simp [hacc])
          obtain ⟨nid, nid0, ns, nbal, nmid, ncc, ncd, nzip, ngrp, naf, nxrec, ncne, ncv⟩ := hnv
          obtain ⟨c, cs, hnc⟩ : ∃ c cs, nxt.cats = c :: cs := by
            cases h : nxt.cats with
            | nil => exact absurd h ncne
            | cons c cs => exact ⟨c, cs, rfl⟩
          simp only [List.map_nil, List.nil_append, items, List.flatMap_cons, hnc, List.map_cons,
            List.cons_append, List.cons.injEq] at hrest
          obtain ⟨rfl, hys⟩ := hrest
          replace hys : ys = (cs.map (Prod.mk nxt) ++ items post').map some ++ [none] := by
            rw [hys]; simp [items]
          obtain ⟨hty, hfill, hcat, hcat0, hcbal⟩ := ncv c (by simp [hnc])
          obtain ⟨hdi, hdg, hdf, hrate⟩ := hdisc nxt (by simp [hacc]) c (by simp [hnc])
          obtain ⟨hxi, hxg⟩ := hxref nxt (by simp [hacc])
          have hfkc := hfk cur (by simp [hacc])
          have hfkn := hfk nxt (by simp [hacc])
          have hgc := hgd cur (by simp)
          have hgn := hgd nxt (by simp)
          -- `cur` precedes every later account, so its id differs from theirs
          have hlater : ∀ b ∈ nxt :: post', cur.id ≠ b.id := by
            rw [hacc] at hdist
            exact (List.pairwise_cons.1 (List.pairwise_append.1 hdist).2.1).1
          have hcn : cur.id ≠ nxt.id := hlater nxt (by simp)
          have hcv' := hval cur (by simp [hacc])
          have hai : ∀ b ∈ nxt :: post', ai cur ≠ ai b := fun b hb =>
            ai_ne hcv' (hval b (by simp [hacc, hb])) (hlater b hb) hgc (hgd b (by simp [hb]))
          have hain := hai nxt (by simp)
          have hne1 : nxt.id.natAbs ≠ cur.id.natAbs := fun h => hlater nxt (by simp) (by omega)
          have hmc : cur.id.natAbs % 100000000000 = cur.id.natAbs := Nat.mod_eq_of_lt hid
          have hmn : nxt.id.natAbs % 100000000000 = nxt.id.natAbs := Nat.mod_eq_of_lt nid
          have hsome : f1.recs[f1.pos]? = some (Cat.bytes nxt.id c) := by
            rw [h1r, h1p, hacc, ← hcur]; exact tcat_next _ pre post' cur nxt c cs hnc
          obtain ⟨pre', mil, post'', hpre, hpost, hmil, hmil0, hck⟩ :=
            hclk (nTxA rate (items pre ++ dc.map (Prod.mk cur)))
          by_cases hr0 : rate nxt c = 0
          · cobol_auto [hclk0, findKey_set, getD_set_ne, Acc.bytes, Cat.bytes]
            cobol_inv [Acc.bytes, Cat.bytes, Acc.posted, hacc, hys, items_concat, nTxA,
              List.filter_append, totalInt, addInt, List.foldl_cons, List.foldl_nil, fitNum_idem,
              Int.zero_add, model4_append2, step4, txRec, monthly, db2ts, hout, systemSrc, descHead,
              spaces110, WS_RECORD_COUNT.fmt,
              WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt, WS_MONTHLY_INT.fmt, Int.add_assoc]
              with _, _, _, _, _, pre ++ [cur], nxt, post', [c], cs
            · -- the REWRITE keeps every record key, so every lookup still finds its account
              intro b hb
              rw [findKey_set]
              · exact hfk b hb
              · rw [hgc]
                simp only [Sem.keyOf, List.drop_zero, Acc.bytes, List.append_assoc]
                rw [List.take_left' (length_encodeNum_acct _), List.take_left' (length_encodeNum_acct _)]
            · -- the other accounts' records are unchanged
              intro b hb
              rw [getD_set_ne _ _ (hai b hb)]
              exact hgd b (by simp [hb])
          · cobol_auto [hclk0, findKey_set, getD_set_ne, Acc.bytes, Cat.bytes]
            cobol_inv [Acc.bytes, Cat.bytes, Acc.posted, hacc, hys, items_concat, nTxA,
              List.filter_append, totalInt, addInt, List.foldl_cons, List.foldl_nil, fitNum_idem,
              Int.zero_add, model4_append2, step4, txRec, monthly, db2ts, hout, systemSrc, descHead,
              spaces110, WS_RECORD_COUNT.fmt,
              WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt, WS_MONTHLY_INT.fmt, Int.add_assoc]
              with _, _, _, _, _, pre ++ [cur], nxt, post', [c], cs
            · -- the REWRITE keeps every record key, so every lookup still finds its account
              intro b hb
              rw [findKey_set]
              · exact hfk b hb
              · rw [hgc]
                simp only [Sem.keyOf, List.drop_zero, Acc.bytes, List.append_assoc]
                rw [List.take_left' (length_encodeNum_acct _), List.take_left' (length_encodeNum_acct _)]
            · -- the other accounts' records are unchanged
              intro b hb
              rw [getD_set_ne _ _ (hai b hb)]
              exact hgd b (by simp [hb])

#print axioms cbact04c_events

end CardDemo.Cbact04c
