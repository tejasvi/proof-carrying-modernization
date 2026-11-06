import EquivLean.Demo.Jimple.Cbact04c.Arith

/-!
# The Java loop on CBACT04C's inputs computes coblean's specification

`jRun` (the main loop of `Cbact04c.run`, `Cb.Model`) on the category records of the accounts
`accs`, grouped by account as in the COBOL input file, rewrites every account but the last with
its posted interest (`Acc.posted (totalInt …)` of coblean's `cbact04c_all`, as Java values) and
counts the transactions `nTxA`.  Pure list induction with the arithmetic of `Cb.Arith`.
-/

open Cobol CardDemo.Cbact04c Jimple

namespace EquivLean.Demo.Cbact04c

/-- A Java string for COBOL bytes: the CP037 (EBCDIC) characters, one UTF-16 unit each. -/
def strOf (bs : List UInt8) : JStr := bs.map fun b => BitVec.ofNat 16 (Codepage.cp037Char b).toNat

def jcat (a : Acc) (c : Cat) : JCat :=
  ⟨BitVec.ofInt 64 a.id, strOf c.ty, BitVec.ofInt 32 c.cat, BitVec.ofInt 64 c.bal⟩

def jacct (a : Acc) : JAcct :=
  ⟨BitVec.ofInt 64 a.id, BitVec.ofInt 64 a.bal, BitVec.ofInt 64 a.cc, BitVec.ofInt 64 a.cd, strOf a.grp⟩

/-- The category records in file order, as Java objects hold them. -/
def jcats (accs : List Acc) : List JCat := (items accs).map fun p => jcat p.1 p.2

/-- coblean's rewritten account record `a.posted t`, as the fields of a Java account. -/
def jposted (a : Acc) (t : Int) : JAcct :=
  ⟨BitVec.ofInt 64 a.id, BitVec.ofInt 64 (Sem.fitNum {} ACCT_CURR_BAL.fmt (a.bal + t)).2, 0, 0,
    strOf a.grp⟩

/-- The loop state after the accounts `pre` and the first categories `dc` of the account `cur`. -/
def S (rate : Acc → Cat → Int) (pre : List Acc) (cur : Acc) (dc : List Cat) : JState :=
  ⟨pre.map (fun a => jposted a (totalInt (rate a) a.cats)),
   BitVec.ofNat 32 (nTxA rate (items pre ++ dc.map (Prod.mk cur))),
   false, BitVec.ofInt 64 cur.id, BitVec.ofInt 64 (totalInt (rate cur) dc), jacct cur⟩

section
variable (rate : Acc → Cat → Int) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)

theorem totalInt_concat (r : Cat → Int) (dc : List Cat) (c : Cat) :
    totalInt r (dc ++ [c]) = addInt r (totalInt r dc) c := by
  simp [totalInt, List.foldl_append]

theorem nTxA_concat (done : List (Acc × Cat)) (p : Acc × Cat) :
    nTxA rate (done ++ [p]) = nTxA rate done + (if rate p.1 p.2 ≠ 0 then 1 else 0) := by
  unfold nTxA
  rw [List.filter_append, List.length_append]
  by_cases h : rate p.1 p.2 ≠ 0 <;> simp [h]

/-- The account-change part of `jStep`. -/
def chg (acctOf : I64 → JAcct) (s : JState) (c : JCat) : JState :=
  if s.first || c.acct != s.last then
    { rewrites := if s.first then s.rewrites else s.rewrites ++ [jPost s.acct s.total],
      tx := s.tx, first := false, last := c.acct, total := 0, acct := acctOf c.acct }
  else s

/-- The rate part of `jStep`. -/
def rstep (rateOf : JStr → JStr → I32 → I64) (s1 : JState) (c : JCat) : JState :=
  if rateOf s1.acct.grp c.ty c.cat = 0 then s1
  else { s1 with total := (s1.total + ((c.bal * rateOf s1.acct.grp c.ty c.cat).sdiv 120000).srem
                    100000000000).srem 100000000000,
                 tx := s1.tx + 1 }

theorem jStep_eq (s : JState) (c : JCat) : jStep acctOf rateOf s c = rstep rateOf (chg acctOf s c) c := rfl

/-- The rate step of one category `c` of the current account `cur`. -/
theorem rate_step (pre : List Acc) (cur : Acc) (dc : List Cat) (c : Cat)
    (hc : c.valid) (hr : (rate cur c).natAbs < 1000000)
    (hro : rateOf (strOf cur.grp) (strOf c.ty) (BitVec.ofInt 32 c.cat) = BitVec.ofInt 64 (rate cur c)) :
    rstep rateOf (S rate pre cur dc) (jcat cur c) = S rate pre cur (dc ++ [c]) := by
  simp only [rstep, S, jcat, jacct, hro]
  have hcb : c.bal.natAbs < 100000000000 := hc.2.2.2.2
  have htot := totalInt_bound (rate cur) dc
  by_cases h0 : rate cur c = 0
  · have hz : BitVec.ofInt 64 (0 : Int) = 0 := rfl
    simp only [h0, hz, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
      nTxA_concat, ne_eq, not_true_eq_false, totalInt_concat, addInt, Nat.add_zero]
  · have : BitVec.ofInt 64 (rate cur c) ≠ 0 := fun h => h0 ((ofInt64_eq_zero_iff _ hr).mp h)
    simp only [this, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, ← List.append_assoc,
      nTxA_concat, h0, ne_eq, not_false_eq_true, totalInt_concat, addInt]
    rw [jtotal_step _ _ _ htot hcb hr, ofNat32_succ]

/-- A record of the current account: no account change. -/
theorem chg_same (pre : List Acc) (cur : Acc) (dc : List Cat) (c : Cat) :
    chg acctOf (S rate pre cur dc) (jcat cur c) = S rate pre cur dc := by
  simp [chg, S, jcat]

/-- The first record of the next account `nxt`: `cur` is posted. -/
theorem chg_next (pre : List Acc) (cur nxt : Acc) (c : Cat) (hcur : cur.valid) (hnxt : nxt.valid)
    (hne : nxt.id ≠ cur.id) (hacct : acctOf (BitVec.ofInt 64 nxt.id) = jacct nxt) :
    chg acctOf (S rate pre cur cur.cats) (jcat nxt c) = S rate (pre ++ [cur]) nxt [] := by
  have hni : BitVec.ofInt 64 nxt.id ≠ BitVec.ofInt 64 cur.id := fun h =>
    hne ((ofInt64_inj hnxt.1 hcur.1).mp h)
  have hbal : cur.bal.natAbs < 1000000000000 := hcur.2.2.2.1
  have hpost : jPost (jacct cur) (BitVec.ofInt 64 (totalInt (rate cur) cur.cats)) =
      jposted cur (totalInt (rate cur) cur.cats) := by
    simp only [jPost, jacct, jposted]
    rw [jpost_bal _ _ hbal (totalInt_bound _ _)]
  simp only [chg, S, jcat, Bool.false_or, bne_iff_ne, ne_eq, hni, not_false_eq_true, ↓reduceIte, Bool.false_eq_true, hacct, hpost, List.map_append, List.map_cons,
    List.map_nil, items_concat, List.map_nil, List.append_nil]
  simp [totalInt]

/-- The first record of the file. -/
theorem chg_first (a : Acc) (c : Cat) (hacct : acctOf (BitVec.ofInt 64 a.id) = jacct a) :
    chg acctOf jInit (jcat a c) = S rate [] a [] := by
  simp [chg, jInit, S, jcat, hacct, items, nTxA, totalInt]

/-- The records of the current account. -/
theorem fold_cats (pre : List Acc) (cur : Acc) :
    ∀ (cs dc : List Cat), (∀ c ∈ cs, c.valid ∧ (rate cur c).natAbs < 1000000 ∧
      rateOf (strOf cur.grp) (strOf c.ty) (BitVec.ofInt 32 c.cat) = BitVec.ofInt 64 (rate cur c)) →
    (cs.map (jcat cur)).foldl (jStep acctOf rateOf) (S rate pre cur dc) = S rate pre cur (dc ++ cs)
  | [], dc, _ => by simp
  | c :: cs, dc, h => by
    have hc := h c (List.mem_cons_self ..)
    rw [List.map_cons, List.foldl_cons, jStep_eq, chg_same, rate_step rate rateOf pre cur dc c hc.1 hc.2.1 hc.2.2,
      fold_cats pre cur cs (dc ++ [c]) (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    simp

/-- What every account of the input satisfies (validity, its record and its rates found). -/
def AccOk (a : Acc) : Prop :=
  a.valid ∧ acctOf (BitVec.ofInt 64 a.id) = jacct a ∧
    ∀ c ∈ a.cats, (rate a c).natAbs < 1000000 ∧
      rateOf (strOf a.grp) (strOf c.ty) (BitVec.ofInt 32 c.cat) = BitVec.ofInt 64 (rate a c)

theorem jcats_cons (a : Acc) (rest : List Acc) :
    jcats (a :: rest) = a.cats.map (jcat a) ++ jcats rest := by
  simp [jcats, items, List.map_flatMap, Function.comp_def]

/-- The accounts after the current one. -/
theorem fold_accounts : ∀ (rest pre : List Acc) (cur : Acc),
    (∀ a ∈ cur :: rest, AccOk rate acctOf rateOf a) → (cur :: rest).Pairwise (fun a b => a.id ≠ b.id) →
    (jcats rest).foldl (jStep acctOf rateOf) (S rate pre cur cur.cats) =
      S rate (pre ++ (cur :: rest).dropLast) ((cur :: rest).getLast (List.cons_ne_nil _ _))
        ((cur :: rest).getLast (List.cons_ne_nil _ _)).cats
  | [], pre, cur, _, _ => by simp [jcats, items]
  | nxt :: rest, pre, cur, hok, hd => by
    have hcur := hok cur (List.mem_cons_self ..)
    have hnxt := hok nxt (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hne : nxt.id ≠ cur.id := fun h => (List.rel_of_pairwise_cons hd (List.mem_cons_self ..)) h.symm
    obtain ⟨c0, cs, hcs⟩ : ∃ c0 cs, nxt.cats = c0 :: cs := by
      cases h : nxt.cats with
      | nil => exact absurd h hnxt.1.2.2.2.2.2.2.2.2.2.2.2.1
      | cons c0 cs => exact ⟨c0, cs, rfl⟩
    have hc0 := hnxt.2.2 c0 (by rw [hcs]; exact List.mem_cons_self ..)
    have hc0v : c0.valid := hnxt.1.2.2.2.2.2.2.2.2.2.2.2.2 c0 (by rw [hcs]; exact List.mem_cons_self ..)
    rw [jcats_cons, List.foldl_append, hcs, List.map_cons, List.foldl_cons, jStep_eq,
      chg_next rate acctOf pre cur nxt c0 hcur.1 hnxt.1 hne hnxt.2.1,
      rate_step rate rateOf (pre ++ [cur]) nxt [] c0 hc0v hc0.1 hc0.2, List.nil_append,
      fold_cats rate acctOf rateOf (pre ++ [cur]) nxt cs [c0] (fun c hc =>
        ⟨hnxt.1.2.2.2.2.2.2.2.2.2.2.2.2 c (by rw [hcs]; exact List.mem_cons_of_mem _ hc),
         hnxt.2.2 c (by rw [hcs]; exact List.mem_cons_of_mem _ hc)⟩)]
    have hrest := fold_accounts rest (pre ++ [cur]) nxt (fun a ha => hok a (List.mem_cons_of_mem _ ha))
      (List.Pairwise.of_cons hd)
    rw [show [c0] ++ cs = nxt.cats by rw [hcs]; rfl, hrest]
    simp [List.dropLast_cons_cons, List.getLast_cons]

end

/-- **The Java loop on CBACT04C's input** (records of the accounts `accs` in file order, each
account's record and rates found): the rewrites are coblean's `a.posted (totalInt …)` for every
account but the last, and the transaction count is `nTxA`. -/
theorem jRun_cbact04c (rate : Acc → Cat → Int) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (accs : List Acc) (hok : ∀ a ∈ accs, AccOk rate acctOf rateOf a)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) :
    (jRun acctOf rateOf (jcats accs)).rewrites =
        accs.dropLast.map (fun a => jposted a (totalInt (rate a) a.cats)) ∧
      (jRun acctOf rateOf (jcats accs)).tx = BitVec.ofNat 32 (nTxA rate (items accs)) := by
  cases accs with
  | nil => simp [jRun, jcats, items, jInit, nTxA]
  | cons a rest =>
    have ha := hok a (List.mem_cons_self ..)
    obtain ⟨c0, cs, hcs⟩ : ∃ c0 cs, a.cats = c0 :: cs := by
      cases h : a.cats with
      | nil => exact absurd h ha.1.2.2.2.2.2.2.2.2.2.2.2.1
      | cons c0 cs => exact ⟨c0, cs, rfl⟩
    have hc0 := ha.2.2 c0 (by rw [hcs]; exact List.mem_cons_self ..)
    have hc0v : c0.valid := ha.1.2.2.2.2.2.2.2.2.2.2.2.2 c0 (by rw [hcs]; exact List.mem_cons_self ..)
    simp only [jRun]
    rw [jcats_cons, List.foldl_append, hcs, List.map_cons, List.foldl_cons, jStep_eq,
      chg_first rate acctOf a c0 ha.2.1, rate_step rate rateOf [] a [] c0 hc0v hc0.1 hc0.2,
      List.nil_append, fold_cats rate acctOf rateOf [] a cs [c0] (fun c hc =>
        ⟨ha.1.2.2.2.2.2.2.2.2.2.2.2.2 c (by rw [hcs]; exact List.mem_cons_of_mem _ hc),
         ha.2.2 c (by rw [hcs]; exact List.mem_cons_of_mem _ hc)⟩),
      show [c0] ++ cs = a.cats by rw [hcs]; rfl,
      fold_accounts rate acctOf rateOf rest [] a hok hdist]
    refine ⟨by simp [S], ?_⟩
    simp only [S, List.nil_append]
    congr 2
    rw [← items_concat, List.dropLast_concat_getLast]

end EquivLean.Demo.Cbact04c
