/-
# CBACT04C on any input: any number of accounts, each with any number of category balances

The category-balance file holds the records of the accounts `accs`, grouped by account. For
every such input CBACT04C ends with `GOBACK`, writes one interest transaction per category with
a nonzero rate, and `REWRITE`s every account but the last with its balance plus its total
monthly interest and zero cycle credit and debit; the last account is never updated.
-/
import Examples.Cbact04cAny
open Cobol

namespace CardDemo.Cbact04c

/-- An account of the input: the fields of its record, its card cross-reference record and its
category balances (in file order). -/
structure Acc where
  id : Int
  s : List UInt8
  bal : Int
  mid : List UInt8
  cc : Int
  cd : Int
  zip : List UInt8
  grp : List UInt8
  af : List UInt8
  xrec : List UInt8
  cats : List Cat

def Acc.valid (a : Acc) : Prop :=
  a.id.natAbs < 100000000000 ∧ 0 ≤ a.id ∧ a.s.length = 1 ∧ a.bal.natAbs < 1000000000000 ∧
    a.mid.length = 54 ∧ a.cc.natAbs < 1000000000000 ∧ a.cd.natAbs < 1000000000000 ∧
    a.zip.length = 10 ∧ a.grp.length = 10 ∧ a.af.length = 178 ∧ a.xrec.length = 50 ∧
    a.cats ≠ [] ∧ ∀ c ∈ a.cats, c.valid

/-- Its record in the account file. -/
def Acc.bytes (a : Acc) : List UInt8 :=
  encodeNum {} ACCT_ID.fmt a.id ++ a.s ++ encodeNum {} ACCT_CURR_BAL.fmt a.bal ++ a.mid ++
    encodeNum {} ACCT_CURR_CYC_CREDIT.fmt a.cc ++ encodeNum {} ACCT_CURR_CYC_DEBIT.fmt a.cd ++
    a.zip ++ a.grp ++ a.af

/-- The record after posting interest `t`: balance `bal + t` (high-order truncated like any
`ADD` without `ON SIZE ERROR`), cycle credit and debit zero. -/
def Acc.posted (a : Acc) (t : Int) : List UInt8 :=
  encodeNum {} ACCT_ID.fmt a.id ++ a.s ++
    encodeNum {} ACCT_CURR_BAL.fmt (Sem.fitNum {} ACCT_CURR_BAL.fmt (a.bal + t)).2 ++ a.mid ++
    encodeNum {} ACCT_CURR_CYC_CREDIT.fmt 0 ++ encodeNum {} ACCT_CURR_CYC_DEBIT.fmt 0 ++
    a.zip ++ a.grp ++ a.af

/-- The running interest total after one more category: its monthly interest
`TRAN-CAT-BAL * DIS-INT-RATE / 1200` (truncated to cents) is added, nothing for a zero rate. -/
def addInt (r : Cat → Int) (v : Int) (c : Cat) : Int :=
  if r c = 0 then v
  else (Sem.fitNum {} WS_TOTAL_INT.fmt
    (v + (Sem.fitNum {} WS_MONTHLY_INT.fmt (divRound .truncation (c.bal * r c) 120000)).2)).2

/-- The interest of an account's categories. -/
def totalInt (r : Cat → Int) (cs : List Cat) : Int := cs.foldl (addInt r) 0

/-- The category records in file order, with their accounts. -/
def items (accs : List Acc) : List (Acc × Cat) := accs.flatMap fun a => a.cats.map (Prod.mk a)

/-- Interest transactions for the processed records: one per nonzero rate. -/
def nTxA (rate : Acc → Cat → Int) (done : List (Acc × Cat)) : Nat :=
  (done.filter (fun p => rate p.1 p.2 ≠ 0)).length

theorem totalInt_bound (r : Cat → Int) (cs : List Cat) :
    (totalInt r cs).natAbs < 100000000000 := by
  suffices h : ∀ v : Int, v.natAbs < 100000000000 →
      (cs.foldl (addInt r) v).natAbs < 100000000000 from h 0 (by decide)
  induction cs with
  | nil => intro v hv; exact hv
  | cons c cs ih =>
    intro v hv
    apply ih
    unfold addInt
    split
    · exact hv
    · exact fitNum_total_bound _

theorem fitNum_idem (c : Config) (f : NumFmt) (v : Int) :
    (Sem.fitNum c f (Sem.fitNum c f v).2).2 = (Sem.fitNum c f v).2 := by
  rw [fitNum_of_holds (fitNum_holds c f v)]

theorem totalInt_append (r : Cat → Int) (cs : List Cat) (c : Cat) :
    totalInt r (cs ++ [c]) = addInt r (totalInt r cs) c := by
  simp [totalInt, List.foldl_append]

/-- `REWRITE` of a record with the same key leaves every key lookup unchanged. -/
theorem findKey_set (k : KeyDecl) (v : List UInt8) :
    ∀ (l : List (List UInt8)) (i : Nat) (r : List UInt8),
      Sem.keyOf k r = Sem.keyOf k (l.getD i []) → Sem.findKey k v (l.set i r) = Sem.findKey k v l
  | [], _, _, _ => rfl
  | x :: xs, 0, r, h => by simp at h; simp [Sem.findKey, h]
  | x :: xs, i + 1, r, h => by simp at h; simp [Sem.findKey, findKey_set k v xs i r h]

theorem getD_set_ne (l : List (List UInt8)) {i j : Nat} (r : List UInt8) (h : i ≠ j) :
    (l.set i r).getD j [] = l.getD j [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, h]

theorem items_mid (pre : List Acc) (cur : Acc) (post : List Acc) :
    items (pre ++ cur :: post) = items pre ++ (cur.cats.map (Prod.mk cur) ++ items post) := by
  simp [items]

theorem items_concat (pre : List Acc) (cur : Acc) :
    items (pre ++ [cur]) = items pre ++ cur.cats.map (Prod.mk cur) := by
  simp [items]

theorem length_encodeNum_acct (x : Int) : (encodeNum {} ACCT_ID.fmt x).length = 11 := by
  rw [length_encodeNum _ _ _ (by decide)]; rfl

theorem getElem?_mid {α : Type} (A B C : List α) (x : α) :
    (A ++ (B ++ x :: C))[A.length + B.length]? = some x := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_right (by omega), Nat.sub_self]
  rfl

/-- Account ids are stored as 11 unsigned digits: distinct ids have distinct encodings. -/
theorem acct_id_inj {a b : Int} (ha : a.natAbs < 100000000000) (ha0 : 0 ≤ a)
    (hb : b.natAbs < 100000000000) (hb0 : 0 ≤ b)
    (h : encodeNum {} ACCT_ID.fmt a = encodeNum {} ACCT_ID.fmt b) : a = b := by
  have h1 := decodeNum_encodeNum_of_holds (c := {}) (f := ACCT_ID.fmt) (v := a) (by decide) (by decide)
    (by simp [NumFmt.Holds, NumFmt.fullBinary, ACCT_ID.fmt]; omega)
  have h2 := decodeNum_encodeNum_of_holds (c := {}) (f := ACCT_ID.fmt) (v := b) (by decide) (by decide)
    (by simp [NumFmt.Holds, NumFmt.fullBinary, ACCT_ID.fmt]; omega)
  rw [h, h2] at h1
  exact (Option.some.inj h1).symm

/-- Two accounts of the input with different ids occupy different records of the account file. -/
theorem ai_ne {l : List (List UInt8)} {ai : Acc → Nat} {a b : Acc} (ha : a.valid) (hb : b.valid)
    (hne : a.id ≠ b.id) (hga : l.getD (ai a) [] = a.bytes) (hgb : l.getD (ai b) [] = b.bytes) :
    ai a ≠ ai b := by
  intro h
  rw [h, hgb] at hga
  obtain ⟨hid, hid0, hs, -⟩ := ha
  obtain ⟨hid', hid0', hs', -⟩ := hb
  have hl : ∀ x : Int, (encodeNum {} ACCT_ID.fmt x).length = 11 := fun x => by
    rw [length_encodeNum _ _ _ (by decide)]; rfl
  have h3 := congrArg (List.take 11) hga
  simp only [Acc.bytes, List.append_assoc] at h3
  rw [List.take_left' (hl _), List.take_left' (hl _)] at h3
  exact hne (acct_id_inj hid hid0 hid' hid0' h3.symm)

theorem tcat_mid (f : Acc × Cat → List UInt8) (pre post : List Acc) (cur : Acc)
    (dc tc : List Cat) (c : Cat) (hcur : cur.cats = dc ++ c :: tc) :
    ((items (pre ++ cur :: post)).map f)[(items pre).length + dc.length]? = some (f (cur, c)) := by
  rw [items_mid, hcur, List.getElem?_map]
  have := getElem?_mid (items pre) (dc.map (Prod.mk cur)) (tc.map (Prod.mk cur) ++ items post) (cur, c)
  simp only [List.length_map] at this
  simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append, this]
  rfl

theorem tcat_next (f : Acc × Cat → List UInt8) (pre post : List Acc) (cur nxt : Acc) (c : Cat)
    (cs : List Cat) (hn : nxt.cats = c :: cs) :
    ((items (pre ++ cur :: nxt :: post)).map f)[(items pre).length + cur.cats.length]? =
      some (f (nxt, c)) := by
  rw [items_mid, List.getElem?_map]
  have := getElem?_mid (items pre) (cur.cats.map (Prod.mk cur))
    (cs.map (Prod.mk nxt) ++ items post) (nxt, c)
  simp only [List.length_map] at this
  simp only [items, List.flatMap_cons, hn, List.map_cons, List.cons_append] at this ⊢
  rw [this]
  rfl

/-- Loop invariant, indexed by the records still to read (`none`: the end of the file). -/
def InvA (accs : List Acc) (rate : Acc → Cat → Int) (ai : Acc → Nat)
    (inp0 : List (Nat × List (List UInt8))) (tcat xrefs discs : List (List UInt8))
    (rest : List (Option (Acc × Cat))) (st : State) : Prop :=
  st.idx = [] ∧ st.slots = [] ∧ st.active = [] ∧ st.inp = inp0 ∧ st.mem.size = 1739 ∧
  st.mem.read 1622 1 = (if rest.isEmpty then [232] else [213]) ∧
  ∃ f1 f2 f4 f3 f5 : FileSt, st.files = [(1, f1), (2, f2), (4, f4), (3, f3), (5, f5)] ∧
    f1.mode = some .input ∧ f1.recs = tcat ∧ f1.eof = rest.isEmpty ∧
    f2.mode = some .input ∧ f2.recs = xrefs ∧ f4.mode = some .input ∧ f4.recs = discs ∧
    f3.mode = some .io ∧ f5.mode = some .output ∧
    (∀ b ∈ accs, Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt b.id) f3.recs =
      some (ai b)) ∧
    -- nothing read yet
    ((f1.pos = 0 ∧ (rest = (items accs).map some ++ [none] ∨ (rest = [] ∧ items accs = [])) ∧
      st.clockN = 0 ∧ acctRewrites st = [] ∧ tranWrites st = [] ∧
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
      acctRewrites st = pre.map (fun a => a.posted (totalInt (rate a) a.cats)) ∧
      (tranWrites st).length = nTxA rate (items pre ++ dc.map (Prod.mk cur)) ∧
      (∀ b ∈ cur :: post, f3.recs.getD (ai b) [] = b.bytes) ∧
      st.mem.read 1711 1 = [213] ∧ st.mem.read 1678 11 = Sem.digitChars {} 11 cur.id.natAbs ∧
      st.mem.read 956 300 = cur.bytes ∧ st.mem.read 852 16 = cur.xrec.take 16 ∧
      st.mem.read 1700 11 = encodeNum {} WS_TOTAL_INT.fmt (totalInt (rate cur) dc) ∧
      st.mem.read 1712 9 = encodeNum {} WS_RECORD_COUNT.fmt ((items pre).length + dc.length) ∧
      st.mem.read 1721 6 =
        encodeNum {} WS_TRANID_SUFFIX.fmt (nTxA rate (items pre ++ dc.map (Prod.mk cur)))))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **CBACT04C on any input.** For every list of accounts `accs` (distinct ids, each with its
category balances, any number of accounts and of records), whose account and cross-reference
records are found by key and whose disclosure groups are found (any rates, zero included), any
initial storage and any clock readings, CBACT04C ends with `GOBACK`, writes one interest
transaction per category with a nonzero rate, and `REWRITE`s exactly the accounts before the
last one, in input order, each with its balance plus its total monthly interest
(`Acc.posted`, `totalInt`) and zero cycle credit and debit. The last account is never updated
(CardDemo issue #64). Proof: induction over the records (`cobol_loop`, invariant `InvA`); each
iteration (first record, a later record of the same account, the first record of the next
account with the update of the previous one, end of file; zero or nonzero rate) by symbolic
execution. -/
theorem cbact04c_all (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
    (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧
      0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post)
    (accs : List Acc) (hval : ∀ a ∈ accs, a.valid)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) (hlen : (items accs).length < 999999)
    -- each account's record and cross-reference, found by key
    (accts xrefs discs : List (List UInt8)) (ai xi : Acc → Nat)
    (hacct : ∀ a ∈ accs, Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt a.id)
      accts = some (ai a) ∧ accts.getD (ai a) [] = a.bytes)
    (hxref : ∀ a ∈ accs, Sem.findKey { off := 25, len := 11 }
      (encodeNum {} FD_XREF_ACCT_ID.fmt a.id) xrefs = some (xi a) ∧ xrefs.getD (xi a) [] = a.xrec)
    -- each category's disclosure group (its rate may be zero)
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
    r.1 = .stop .goback ∧
      acctRewrites r.2 = accs.dropLast.map (fun a => a.posted (totalInt (rate a) a.cats)) ∧
      (tranWrites r.2).length = nTxA rate (items accs) := by
  intro r
  simp only [r]
  cobol_auto
  cobol_loop (InvA accs rate ai
      [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)), (2, xrefs), (3, accts), (4, discs)]
      ((items accs).map (fun p => Cat.bytes p.1.id p.2)) xrefs discs) ((items accs).map some ++ [none])
  · -- after the loop: five CLOSEs, DISPLAY, GOBACK
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := loopState
    obtain ⟨rfl, rfl, rfl, rfl, hsz, heof, f1, f2, f4, f3, f5, rfl, h1m, -, -, h2m, -, h4m, -, h3m,
      h5m, -, hph⟩ := hloopInv
    simp only [List.isEmpty_nil, ↓reduceIte] at heof
    rcases hph with ⟨-, hrest, -, hrw, htw, -⟩ | ⟨pre, cur, post, dc, tc, hacc, hcur, -, -, hrest, -, hrw,
      htw, -⟩
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
      simp only [acctRewrites, tranWrites] at hrw htw
      cobol_auto
      simp [acctRewrites, tranWrites, hrw, htw, nTxA, items]
    · rcases hrest with ⟨-, rfl, rfl⟩ | h
      · simp only [List.append_nil] at hcur
        subst hacc
        simp only [acctRewrites, tranWrites] at hrw htw
        cobol_auto
        simp only [List.filterMap_reverse, List.length_reverse] at htw
        simp [acctRewrites, tranWrites, hrw, htw, nTxA, items, hcur]
      · simp at h
  · -- before the loop: nothing read, the counters and flags have their VALUEs
    cobol_inv [acctRewrites, tranWrites, spaces11]
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
      ⟨rfl, rfl, rfl, rfl, hsz, heof, f1, f2, f4, f3, f5, rfl, h1m, h1r, h1e, h2m, h2r, h4m, h4r, h3m,
        h5m, hfk, hph⟩
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at heof h1e
    replace hsz : mem.size = 1739 := hsz
    refine ⟨by cobol_auto, ?_⟩
    rcases hph with ⟨h1p, hrest, hclk0, hrw, htw, hgd, h1711, h1678, hcnt, hsuf⟩ |
      ⟨pre, cur, post, dc, tc, hacc, hcur, hdc, h1p, hrest, hclk0, hrw, htw, hgd, h1711, h1678, h956,
        h852, h1700, hcnt, hsuf⟩
    · -- nothing read yet
      dsimp only at h1711 h1678 hcnt hsuf hclk0
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
        cobol_inv [items, acctRewrites, tranWrites]
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
          simp only [acctRewrites, List.filterMap_reverse, List.reverse_eq_nil_iff] at hrw
          simp only [tranWrites, List.filterMap_reverse, List.reverse_eq_nil_iff] at htw
          cobol_inv [Acc.bytes, Cat.bytes, totalInt, addInt, fitNum_idem, items, nTxA, hys, acctRewrites,
            tranWrites, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt]
            with _, _, _, _, _, [], a0, accs', [c0], cs
        · cobol_auto [hclk0, Acc.bytes, Cat.bytes, spaces11]
          simp only [acctRewrites, List.filterMap_reverse, List.reverse_eq_nil_iff] at hrw
          simp only [tranWrites, List.filterMap_reverse, List.reverse_eq_nil_iff] at htw
          cobol_inv [Acc.bytes, Cat.bytes, totalInt, addInt, fitNum_idem, items, nTxA, hys, acctRewrites,
            tranWrites, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt]
            with _, _, _, _, _, [], a0, accs', [c0], cs
    · -- the records of `pre` and `dc` processed
      dsimp only at h1711 h1678 h956 h852 h1700 hcnt hsuf hclk0
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
          cobol_inv [Cat.bytes, totalInt_append, addInt, nTxA, List.filter_append, hys, acctRewrites,
            tranWrites, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt, WS_MONTHLY_INT.fmt,
            Int.add_assoc] with _, _, _, _, _, pre, cur, post, dc ++ [c], tc'
        · cobol_auto [hclk0, Acc.bytes, Cat.bytes]
          cobol_inv [Cat.bytes, totalInt_append, addInt, nTxA, List.filter_append, hys, acctRewrites,
            tranWrites, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt, WS_MONTHLY_INT.fmt,
            Int.add_assoc] with _, _, _, _, _, pre, cur, post, dc ++ [c], tc'
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
          cobol_inv [acctRewrites, tranWrites] with _, _, _, _, _, pre, cur, [], dc, []
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
            cobol_inv [Acc.bytes, Cat.bytes, Acc.posted, hacc, hys, items, items_concat, nTxA,
              List.filter_append, totalInt, addInt, List.foldl_cons, List.foldl_nil, fitNum_idem,
              Int.zero_add, acctRewrites, tranWrites, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt,
              WS_TOTAL_INT.fmt, WS_MONTHLY_INT.fmt, Int.add_assoc]
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
            cobol_inv [Acc.bytes, Cat.bytes, Acc.posted, hacc, hys, items, items_concat, nTxA,
              List.filter_append, totalInt, addInt, List.foldl_cons, List.foldl_nil, fitNum_idem,
              Int.zero_add, acctRewrites, tranWrites, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt,
              WS_TOTAL_INT.fmt, WS_MONTHLY_INT.fmt, Int.add_assoc]
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


#print axioms cbact04c_all

end CardDemo.Cbact04c
