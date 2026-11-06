/-
# CardDemo CBACT04C on every input: the error paths and the DEFAULT disclosure group

`cbact04c_events` assumes that every account, cross-reference and disclosure-group lookup
succeeds. `cbact04c_every` drops those assumptions: the account file, the cross-reference
file and the disclosure-group file are any lists of well-formed records, read the way the
file model reads a KSDS (the first record with the key). The model `model4x` follows the
program on every path: a missing account record or cross-reference abends (999) after
`ACCOUNT NOT FOUND: `, the error line and the file status; a missing disclosure group is
replaced by group `DEFAULT` after two `DISPLAY`s, and a missing `DEFAULT` group abends too.
On CardDemo's own sample data every account's group is blank, so every record takes the
`DEFAULT` path: `cbact04c_events` does not cover that data, `cbact04c_every` does.
-/
import Examples.Cbact04cEvents
import Cobol.Logic.LoopExit
open Cobol

namespace CardDemo.Cbact04c

/-! ## The input records -/

/-- A disclosure-group record (`DIS-GROUP-RECORD`, 50 bytes): its key (group, transaction type,
category), its interest rate (`DIS-INT-RATE`, `S9(04)V99`) and the rest. -/
structure Disc where
  key : List UInt8
  rate : Int
  fill : List UInt8

def Disc.bytes (d : Disc) : List UInt8 := d.key ++ encodeNum {} DIS_INT_RATE.fmt d.rate ++ d.fill

def Disc.valid (d : Disc) : Prop := d.key.length = 16 ∧ d.rate.natAbs < 1000000 ∧ d.fill.length = 28

def disc0 : Disc := ⟨[], 0, []⟩

/-- An account record of the account file: an `Acc` whose cross-reference and categories are
not used (`Acc.bytes` ignores them). -/
def Acc.validRec (a : Acc) : Prop :=
  a.id.natAbs < 100000000000 ∧ 0 ≤ a.id ∧ a.s.length = 1 ∧ a.bal.natAbs < 1000000000000 ∧
    a.mid.length = 54 ∧ a.cc.natAbs < 1000000000000 ∧ a.cd.natAbs < 1000000000000 ∧
    a.zip.length = 10 ∧ a.grp.length = 10 ∧ a.af.length = 178

/-- An account of the category-balance file: its id and its category records (the other fields
are not used). -/
def Acc.validIn (a : Acc) : Prop :=
  a.id.natAbs < 100000000000 ∧ 0 ≤ a.id ∧ a.cats ≠ [] ∧ ∀ c ∈ a.cats, c.valid

def acc0 : Acc := ⟨0, [], 0, [], 0, 0, [], [], [], [], []⟩

/-! ## The messages of the error paths (EBCDIC) -/

/-- `ACCOUNT NOT FOUND: ` -/
def notFoundMsg : List UInt8 := [193, 195, 195, 214, 228, 213, 227, 64, 213, 214, 227, 64, 198, 214, 228, 213, 196, 122, 64]
/-- `ERROR READING ACCOUNT FILE` -/
def errAcctMsg : List UInt8 := [197, 217, 217, 214, 217, 64, 217, 197, 193, 196, 201, 213, 199, 64, 193, 195, 195, 214, 228, 213, 227, 64, 198, 201, 211, 197]
/-- `ERROR READING XREF FILE` -/
def errXrefMsg : List UInt8 := [197, 217, 217, 214, 217, 64, 217, 197, 193, 196, 201, 213, 199, 64, 231, 217, 197, 198, 64, 198, 201, 211, 197]
/-- `DISCLOSURE GROUP RECORD MISSING` -/
def missingMsg : List UInt8 := [196, 201, 226, 195, 211, 214, 226, 228, 217, 197, 64, 199, 217, 214, 228, 215, 64, 217, 197, 195, 214, 217, 196, 64, 212, 201, 226, 226, 201, 213, 199]
/-- `TRY WITH DEFAULT GROUP CODE` -/
def tryDefaultMsg : List UInt8 := [227, 217, 232, 64, 230, 201, 227, 200, 64, 196, 197, 198, 193, 228, 211, 227, 64, 199, 217, 214, 228, 215, 64, 195, 214, 196, 197]
/-- `ERROR READING DEFAULT DISCLOSURE GROUP` -/
def errDefaultMsg : List UInt8 := [197, 217, 217, 214, 217, 64, 217, 197, 193, 196, 201, 213, 199, 64, 196, 197, 198, 193, 228, 211, 227, 64, 196, 201, 226, 195, 211, 214, 226, 228, 217, 197, 64, 199, 217, 214, 228, 215]
/-- `FILE STATUS IS: NNNN0023` (`9910-DISPLAY-IO-STATUS` for status 23) -/
def status23Msg : List UInt8 := [198, 201, 211, 197, 64, 226, 227, 193, 227, 228, 226, 64, 201, 226, 122, 64, 213, 213, 213, 213, 240, 240, 242, 243]
/-- `ABENDING PROGRAM` -/
def abendMsg : List UInt8 := [193, 194, 197, 213, 196, 201, 213, 199, 64, 215, 217, 214, 199, 217, 193, 212]
/-- `DEFAULT   ` (the group id of the default disclosure records) -/
def defaultGrp : List UInt8 := [196, 197, 198, 193, 228, 211, 227, 64, 64, 64]

theorem notFoundMsg_eq : Codepage.encode037 "ACCOUNT NOT FOUND: " = some notFoundMsg := by decide +kernel
theorem errAcctMsg_eq : Codepage.encode037 "ERROR READING ACCOUNT FILE" = some errAcctMsg := by decide +kernel
theorem errXrefMsg_eq : Codepage.encode037 "ERROR READING XREF FILE" = some errXrefMsg := by decide +kernel
theorem missingMsg_eq : Codepage.encode037 "DISCLOSURE GROUP RECORD MISSING" = some missingMsg := by decide +kernel
theorem tryDefaultMsg_eq : Codepage.encode037 "TRY WITH DEFAULT GROUP CODE" = some tryDefaultMsg := by decide +kernel
theorem errDefaultMsg_eq : Codepage.encode037 "ERROR READING DEFAULT DISCLOSURE GROUP" = some errDefaultMsg := by decide +kernel
theorem status23Msg_eq : Codepage.encode037 "FILE STATUS IS: NNNN0023" = some status23Msg := by decide +kernel
theorem abendMsg_eq : Codepage.encode037 "ABENDING PROGRAM" = some abendMsg := by decide +kernel
theorem defaultGrp_eq : Codepage.encode037 "DEFAULT   " = some defaultGrp := by decide +kernel

/-- The last three events of a failed lookup (newest first): `ABENDING PROGRAM`, the file
status, the error line. -/
def abendEvents4 (msg : List UInt8) : List Event :=
  [.display abendMsg, .display status23Msg, .display msg]

/-! ## The lookups (first record with the key, as the file model reads a KSDS) -/

def acctIdx (accts : List Acc) (id : Int) : Option Nat :=
  Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt id) (accts.map Acc.bytes)

def xrefIdx (xrefs : List (List UInt8)) (id : Int) : Option Nat :=
  Sem.findKey { off := 25, len := 11 } (encodeNum {} FD_XREF_ACCT_ID.fmt id) xrefs

def discIdx (discs : List Disc) (grp : List UInt8) (c : Cat) : Option Nat :=
  Sem.findKey { off := 0, len := 16 } (grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat)
    (discs.map Disc.bytes)

/-! ## The model -/

/-- The `k`-th interest transaction record (from 0) for account id `aid`, card `card` and amount
`amt`: `txRec` with the account record's id and the cross-reference record's card number. -/
def txRecX (parm descTail fill : List UInt8) (clk : Nat → List UInt8) (k : Nat) (aid : Int)
    (card : List UInt8) (amt : Int) : List UInt8 :=
  parm ++ encodeNum {} WS_TRANID_SUFFIX.fmt ((k : Int) + 1) ++ [240, 241] ++
    encodeNum {} TRAN_CAT_CD.fmt 5 ++ systemSrc ++ descHead ++ encodeNum {} ACCT_ID.fmt aid ++
    descTail ++ encodeNum {} TRAN_AMT.fmt amt ++ encodeNum {} TRAN_MERCHANT_ID.fmt 0 ++ spaces110 ++
    card ++ db2ts (clk k) ++ db2ts (clk k) ++ fill

/-- What CBACT04C has done after some category records: the account id of the last record, its
account record and card number, its interest so far, the transactions written, the events
(newest first), and whether the run has abended. -/
structure M4x where
  last : Option Int
  acct : Acc
  card : List UInt8
  total : Int
  k : Nat
  out : List Event
  stop : Bool

/-- The interest of category `c` of the current account, after the events `out`
(`1200-GET-INTEREST-RATE`, `1200-A-GET-DEFAULT-INT-RATE`, `1300-COMPUTE-INTEREST`): the rate of
the account's disclosure group, else (two `DISPLAY`s) the rate of group `DEFAULT`, else an abend;
a nonzero rate adds the monthly interest and writes its transaction. -/
def rateX (discs : List Disc) (parm descTail fill : List UInt8) (clk : Nat → List UInt8)
    (s : M4x) (c : Cat) (out : List Event) : M4x :=
  match discIdx discs s.acct.grp c with
  | some i => withRateX parm descTail fill clk s c (discs.getD i disc0).rate out
  | none =>
    match discIdx discs defaultGrp c with
    | some i => withRateX parm descTail fill clk s c (discs.getD i disc0).rate
        (.display tryDefaultMsg :: .display missingMsg :: out)
    | none => { s with out := (abendEvents4 errDefaultMsg ++
        (.display tryDefaultMsg :: .display missingMsg :: out)), stop := true }
where
  withRateX (parm descTail fill : List UInt8) (clk : Nat → List UInt8) (s : M4x) (c : Cat)
      (r : Int) (out : List Event) : M4x :=
    if r = 0 then { s with out := out }
    else
      { s with total := (Sem.fitNum {} WS_TOTAL_INT.fmt (s.total + monthly c r)).2, k := s.k + 1,
               out := (.write 5 (txRecX parm descTail fill clk s.k s.acct.id s.card (monthly c r)) ::
                 out) }

/-- One category record `c` of account id `p.1.id`: `DISPLAY` it; on a new account, `REWRITE`
the previous one (not before the first), read its account record and cross-reference (an abend
if one is missing); then the interest (`rateX`). Nothing after an abend. -/
def step4x (accts : List Acc) (xrefs : List (List UInt8)) (discs : List Disc)
    (parm descTail fill : List UInt8) (clk : Nat → List UInt8) (s : M4x) (p : Acc × Cat) : M4x :=
  if s.stop then s
  else if s.last = some p.1.id then
    rateX discs parm descTail fill clk s p.2 (.display (Cat.bytes p.1.id p.2) :: s.out)
  else
    let out2 := if s.last.isSome then
        Event.rewrite 3 (s.acct.posted s.total) :: Event.display (Cat.bytes p.1.id p.2) :: s.out
      else Event.display (Cat.bytes p.1.id p.2) :: s.out
    match acctIdx accts p.1.id with
    | none => { s with out := (abendEvents4 errAcctMsg ++
        Event.display (notFoundMsg ++ encodeNum {} FD_ACCT_ID.fmt p.1.id) :: out2), stop := true }
    | some i =>
      match xrefIdx xrefs p.1.id with
      | none => { s with out := (abendEvents4 errXrefMsg ++
          Event.display (notFoundMsg ++ encodeNum {} FD_XREF_ACCT_ID.fmt p.1.id) :: out2), stop := true }
      | some j =>
        rateX discs parm descTail fill clk
          { s with last := some p.1.id, acct := accts.getD i acc0,
                   card := (xrefs.getD j []).take 16, total := 0 } p.2 out2

/-- The model after the category records `ps`. -/
def model4x (accts : List Acc) (xrefs : List (List UInt8)) (discs : List Disc)
    (parm descTail fill : List UInt8) (clk : Nat → List UInt8) (ps : List (Acc × Cat)) : M4x :=
  ps.foldl (step4x accts xrefs discs parm descTail fill clk) ⟨none, acc0, [], 0, 0, [], false⟩

/-! ## The model: lemmas -/

section ModelLemmas
variable (accts : List Acc) (xrefs : List (List UInt8)) (discs : List Disc)
  (parm descTail fill : List UInt8) (clk : Nat → List UInt8)

theorem model4x_append (ps : List (Acc × Cat)) (p : Acc × Cat) :
    model4x accts xrefs discs parm descTail fill clk (ps ++ [p]) =
      step4x accts xrefs discs parm descTail fill clk (model4x accts xrefs discs parm descTail fill clk ps) p := by
  simp [model4x, List.foldl_append]

theorem model4x_append2 (ps qs : List (Acc × Cat)) (p : Acc × Cat) :
    model4x accts xrefs discs parm descTail fill clk (ps ++ (qs ++ [p])) =
      step4x accts xrefs discs parm descTail fill clk
        (model4x accts xrefs discs parm descTail fill clk (ps ++ qs)) p := by
  rw [← List.append_assoc, model4x_append]

theorem foldl_step4x_stop :
    ∀ (ps : List (Acc × Cat)) (s : M4x), s.stop = true →
      ps.foldl (step4x accts xrefs discs parm descTail fill clk) s = s
  | [], _, _ => rfl
  | p :: ps, s, h => by
    rw [List.foldl_cons]
    have : step4x accts xrefs discs parm descTail fill clk s p = s := by simp [step4x, h]
    rw [this, foldl_step4x_stop ps s h]

/-- After an abend the later records change nothing. -/
theorem model4x_stop_append (ps qs : List (Acc × Cat))
    (h : (model4x accts xrefs discs parm descTail fill clk ps).stop = true) :
    model4x accts xrefs discs parm descTail fill clk (ps ++ qs) =
      model4x accts xrefs discs parm descTail fill clk ps := by
  simp only [model4x, List.foldl_append]
  exact foldl_step4x_stop accts xrefs discs parm descTail fill clk qs _ h

theorem model4x_nil : model4x accts xrefs discs parm descTail fill clk [] =
    ⟨none, acc0, [], 0, 0, [], false⟩ := rfl

end ModelLemmas

/-! ## Lookups: lemmas -/

theorem findKey_lt4 {k : KeyDecl} {v : List UInt8} :
    ∀ {l : List (List UInt8)} {i : Nat}, Sem.findKey k v l = some i → i < l.length
  | [], _, h => by simp [Sem.findKey] at h
  | r :: rs, i, h => by
    simp only [Sem.findKey] at h
    split at h
    · simp at h; subst h; simp
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      have := findKey_lt4 hj
      simp; omega

theorem findKey_key4 {k : KeyDecl} {v : List UInt8} :
    ∀ {l : List (List UInt8)} {i : Nat}, Sem.findKey k v l = some i → Sem.keyOf k (l.getD i []) = v
  | [], _, h => by simp [Sem.findKey] at h
  | r :: rs, i, h => by
    simp only [Sem.findKey] at h
    split at h
    · rename_i hr
      simp at h; subst h; simpa using hr
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa using findKey_key4 hj

theorem getD_map4 {α : Type} (f : α → List UInt8) (l : List α) (d : α) {i : Nat}
    (h : i < l.length) : (l.map f).getD i [] = f (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]

theorem getD_mem4 {α : Type} {l : List α} (d : α) {i : Nat} (h : i < l.length) :
    l.getD i d ∈ l := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- Two different keys are found at different records. -/
theorem findKey_ne4 {k : KeyDecl} {v w : List UInt8} {l : List (List UInt8)} {i j : Nat}
    (hi : Sem.findKey k v l = some i) (hj : Sem.findKey k w l = some j) (hvw : v ≠ w) : i ≠ j := by
  intro h
  subst h
  exact hvw ((findKey_key4 hi).symm.trans (findKey_key4 hj))

theorem acctIdx_lt {accts : List Acc} {id : Int} {i : Nat} (h : acctIdx accts id = some i) :
    i < accts.length := by
  have := findKey_lt4 h
  simpa using this

theorem acct_rec {accts : List Acc} {id : Int} {i : Nat} (h : acctIdx accts id = some i) :
    (accts.map Acc.bytes).getD i [] = (accts.getD i acc0).bytes :=
  getD_map4 _ _ _ (acctIdx_lt h)

theorem disc_rec {discs : List Disc} {g : List UInt8} {c : Cat} {i : Nat}
    (h : discIdx discs g c = some i) :
    (discs.map Disc.bytes).getD i [] = (discs.getD i disc0).bytes :=
  getD_map4 _ _ _ (by have := findKey_lt4 h; simpa using this)

theorem disc_valid {discs : List Disc} (hdv : ∀ d ∈ discs, d.valid) {g : List UInt8} {c : Cat}
    {i : Nat} (h : discIdx discs g c = some i) : (discs.getD i disc0).valid :=
  hdv _ (getD_mem4 _ (by have := findKey_lt4 h; simpa using this))

theorem acct_valid {accts : List Acc} (hav : ∀ a ∈ accts, a.validRec) {id : Int} {i : Nat}
    (h : acctIdx accts id = some i) : (accts.getD i acc0).validRec :=
  hav _ (getD_mem4 _ (acctIdx_lt h))

/-- The record found for an account id has that id. -/
theorem acct_id_of_idx {accts : List Acc} (hav : ∀ a ∈ accts, a.validRec) {id : Int} {i : Nat}
    (hid : id.natAbs < 100000000000) (hid0 : 0 ≤ id) (h : acctIdx accts id = some i) :
    (accts.getD i acc0).id = id := by
  have hk := findKey_key4 h
  rw [acct_rec h] at hk
  obtain ⟨h1, h2, -⟩ := acct_valid hav h
  simp only [Sem.keyOf, List.drop_zero, Acc.bytes, List.append_assoc] at hk
  rw [List.take_left' (length_encodeNum_acct _)] at hk
  exact acct_id_inj h1 h2 hid hid0 hk


section StepLemmas
variable (accts : List Acc) (xrefs : List (List UInt8)) (discs : List Disc)
  (parm descTail fill : List UInt8) (clk : Nat → List UInt8)

theorem rateX_k_le (s : M4x) (c : Cat) (out : List Event) :
    (rateX discs parm descTail fill clk s c out).k ≤ s.k + 1 := by
  simp only [rateX, rateX.withRateX]
  repeat' split
  all_goals simp

theorem rateX_total (s : M4x) (c : Cat) (out : List Event) (h : s.total.natAbs < 100000000000) :
    (rateX discs parm descTail fill clk s c out).total.natAbs < 100000000000 := by
  simp only [rateX, rateX.withRateX]
  repeat' split
  all_goals first | exact h | exact fitNum_total_bound _

/-- A later record of the current account: only the interest step. -/
theorem step4x_same (s : M4x) (p : Acc × Cat) (h1 : s.stop = false) (h2 : s.last = some p.1.id) :
    step4x accts xrefs discs parm descTail fill clk s p =
      rateX discs parm descTail fill clk s p.2 (.display (Cat.bytes p.1.id p.2) :: s.out) := by
  simp [step4x, h1, h2]

end StepLemmas

section StepLemmas2
variable (accts : List Acc) (xrefs : List (List UInt8)) (discs : List Disc)
  (parm descTail fill : List UInt8) (clk : Nat → List UInt8)

theorem step4x_k_le (s : M4x) (p : Acc × Cat) :
    (step4x accts xrefs discs parm descTail fill clk s p).k ≤ s.k + 1 := by
  simp only [step4x]
  split
  · simp
  split
  · exact rateX_k_le _ _ _ _ _ _ _ _
  split
  · simp
  split
  · simp
  · exact rateX_k_le _ _ _ _ _ _ _ _

end StepLemmas2

/-! ## The loop invariant -/

/-- `InvE` for every input. The model is `model4x`. The account file keeps every key where it
was, and the records of the accounts still to come are unchanged; the current account's record
and card number are the model state's. -/
def InvX (m : Mem) (clk : Nat → List UInt8) (accs accts : List Acc) (xrefs : List (List UInt8))
    (discs : List Disc) (inp0 : List (Nat × List (List UInt8))) (tcat : List (List UInt8))
    (rest : List (Option (Acc × Cat))) (st : State) : Prop :=
  st.idx = [] ∧ st.slots = [] ∧ st.active = [] ∧ st.inp = inp0 ∧ st.mem.size = 1739 ∧
  st.mem.read 1622 1 = (if rest.isEmpty then [232] else [213]) ∧
  st.mem.read 1729 10 = m.read 1729 10 ∧ st.mem.read 1314 76 = m.read 1314 76 ∧
  st.mem.read 1588 20 = m.read 1588 20 ∧
  ∃ f1 f2 f4 f3 f5 : FileSt, st.files = [(1, f1), (2, f2), (4, f4), (3, f3), (5, f5)] ∧
    f1.mode = some .input ∧ f1.recs = tcat ∧ f1.eof = rest.isEmpty ∧
    f2.mode = some .input ∧ f2.recs = xrefs ∧ f4.mode = some .input ∧
    f4.recs = discs.map Disc.bytes ∧ f3.mode = some .io ∧ f5.mode = some .output ∧
    (∀ v, Sem.findKey { off := 0, len := 11 } v f3.recs =
      Sem.findKey { off := 0, len := 11 } v (accts.map Acc.bytes)) ∧
    -- nothing read yet
    ((f1.pos = 0 ∧ (rest = (items accs).map some ++ [none] ∨ (rest = [] ∧ items accs = [])) ∧
      st.clockN = 0 ∧ st.out = [.display startMsg] ∧ f3.recs = accts.map Acc.bytes ∧
      st.mem.read 1711 1 = [232] ∧ st.mem.read 1678 11 = spaces11 ∧
      st.mem.read 1712 9 = encodeNum {} WS_RECORD_COUNT.fmt 0 ∧
      st.mem.read 1721 6 = encodeNum {} WS_TRANID_SUFFIX.fmt 0) ∨
    -- the records of the accounts `pre` and the first records `dc` of account `cur` processed
     (∃ pre cur post dc tc, accs = pre ++ cur :: post ∧ cur.cats = dc ++ tc ∧ dc ≠ [] ∧
      f1.pos = (items pre).length + dc.length ∧
      ((rest = [] ∧ tc = [] ∧ post = []) ∨
        rest = (tc.map (Prod.mk cur) ++ items post).map some ++ [none]) ∧
      ∃ S : M4x, model4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
          (items pre ++ dc.map (Prod.mk cur)) = S ∧
        S.stop = false ∧ S.last = some cur.id ∧
        (∃ i, acctIdx accts cur.id = some i ∧ S.acct = accts.getD i acc0) ∧
        S.card.length = 16 ∧ S.total.natAbs < 100000000000 ∧
        S.k ≤ (items pre).length + dc.length ∧
        (∀ b ∈ post, ∀ i, acctIdx accts b.id = some i →
          f3.recs.getD i [] = (accts.map Acc.bytes).getD i []) ∧
        st.clockN = S.k ∧ st.out = S.out ++ [.display startMsg] ∧
        st.mem.read 1711 1 = [213] ∧ st.mem.read 1678 11 = Sem.digitChars {} 11 cur.id.natAbs ∧
        st.mem.read 956 300 = S.acct.bytes ∧ st.mem.read 852 16 = S.card ∧
        st.mem.read 1700 11 = encodeNum {} WS_TOTAL_INT.fmt S.total ∧
        st.mem.read 1712 9 = encodeNum {} WS_RECORD_COUNT.fmt ((items pre).length + dc.length) ∧
        st.mem.read 1721 6 = encodeNum {} WS_TRANID_SUFFIX.fmt S.k))

/-- How the loop ends on an abend: the run's signal, and the model over all records stopped
with these events. -/
def ExitX (m : Mem) (clk : Nat → List UInt8) (accs accts : List Acc) (xrefs : List (List UInt8))
    (discs : List Disc) (r : Sem.Res) : Prop :=
  r.1 = .fault (.abend 999) ∧
    (model4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
      (items accs)).stop = true ∧
    r.2.out = (model4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
      (items accs)).out ++ [.display startMsg]

set_option maxHeartbeats 60000000 in
set_option maxRecDepth 20000 in
/-- **CBACT04C on every input.**  For every category-balance file grouped by account (`items
accs`, distinct account ids), every account file, cross-reference file and disclosure-group file
of well-formed records, every initial storage and every clock: CBACT04C ends as the model
`model4x` says, with all its events. A missing account record or cross-reference abends (999)
after `ACCOUNT NOT FOUND: `, the error line and the file status; a missing disclosure group is
replaced by group `DEFAULT` after two `DISPLAY`s, and a missing `DEFAULT` group abends too.
Otherwise the run ends with `GOBACK`; as in `cbact04c_events`, the last account is never
rewritten. -/
theorem cbact04c_every (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
    (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧
      0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post)
    (accs : List Acc) (hval : ∀ a ∈ accs, a.validIn)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) (hlen : (items accs).length < 999999)
    (accts : List Acc) (hav : ∀ a ∈ accts, a.validRec)
    (xrefs : List (List UInt8)) (hxl : ∀ r ∈ xrefs, r.length = 50)
    (discs : List Disc) (hdv : ∀ d ∈ discs, d.valid)
    (n : Nat) (hn : (items accs).length < n) :
    let r := Cbact04c.run { clock := clk } (n + 60)
      (Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)), (2, xrefs),
        (3, accts.map Acc.bytes), (4, discs.map Disc.bytes)])
    let s := model4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
      (items accs)
    if s.stop then r.1 = .fault (.abend 999) ∧ r.2.out = s.out ++ [.display startMsg]
    else r.1 = .stop .goback ∧ r.2.out = [.display endMsg] ++ s.out ++ [.display startMsg] := by
  intro r s
  simp only [r, s]
  cobol_auto
  cobol_loop_exit (InvX m clk accs accts xrefs discs
      [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)), (2, xrefs), (3, accts.map Acc.bytes),
        (4, discs.map Disc.bytes)]
      ((items accs).map (fun p => Cat.bytes p.1.id p.2))) ((items accs).map some ++ [none])
    (ExitX m clk accs accts xrefs discs)
  · -- the normal end: five CLOSEs, DISPLAY, GOBACK
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := loopState
    obtain ⟨rfl, rfl, rfl, rfl, hsz, heof, -, -, -, f1, f2, f4, f3, f5, rfl, h1m, -, -, h2m, -, h4m, -,
      h3m, h5m, -, hph⟩ := hloopInv
    simp only [List.isEmpty_nil, ↓reduceIte] at heof
    rcases hph with ⟨-, hrest, -, hout, -⟩ |
      ⟨pre, cur, post, dc, tc, hacc, hcur, -, -, hrest, S, hS, hstop, -, -, -, -, -, -, -, hout, -⟩
    · rcases hrest with h | ⟨-, hi⟩
      · simp at h
      have h0 : accs = [] := by
        cases accs with
        | nil => rfl
        | cons a as =>
          obtain ⟨-, -, hne, -⟩ := hval a (by simp)
          cases hc : a.cats with
          | nil => exact absurd hc hne
          | cons c cs => simp [items, hc] at hi
      subst h0
      cobol_auto
      simp [items, model4x, endMsg]
    · rcases hrest with ⟨-, rfl, rfl⟩ | h
      · simp only [List.append_nil] at hcur
        subst hacc
        have hM : model4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
            (items (pre ++ [cur])) = S := by rw [items_concat, hcur]; exact hS
        cobol_auto
        all_goals simp [hM, hstop, hout, endMsg]
      · simp at h
  · -- an abend left the loop: it ends the run
    obtain ⟨rfl, hst, hout⟩ := hexitInv
    cobol_auto
    all_goals (simp only [hst, ↓reduceIte]; exact ⟨rfl, hout⟩)
  · -- before the loop: nothing read, the counters and flags have their VALUEs
    cobol_inv [startMsg, spaces11]
  · simp; omega
  · -- the loop ends exactly after the end-of-file READ
    rintro ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨-, -, -, -, -, heof, -⟩
    simp only [List.isEmpty_nil, ↓reduceIte] at heof
    cobol_auto
  · -- one iteration: READ the next record and process it, or reach the end of the file
    rintro y ys ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨rfl, rfl, rfl, rfl, hsz, heof, hparm, hdesc, hfil, f1, f2, f4, f3, f5, rfl, h1m, h1r, h1e, h2m,
        h2r, h4m, h4r, h3m, h5m, h3k, hph⟩
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at heof h1e
    replace hsz : mem.size = 1739 := hsz
    refine ⟨by cobol_auto, ?_⟩
    have hnum : List.all [242, 243] (fun b => (Config.decDigit {} b).isSome) = true := by decide
    rcases hph with ⟨h1p, hrest, hclk0, hout, h3r, h1711, h1678, hcnt, hsuf⟩ |
      ⟨pre, cur, post, dc, tc, hacc, hcur, hdc, h1p, hrest, S, hS, hstop, hlast, ⟨iC, hiC, hSacc⟩,
        hcardl, htot, hkb, hpost, hclk0, hout, h1711, h1678, h956, h852, h1700, hcnt, hsuf⟩
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
        left
        cobol_auto
        cobol_inv [items]
      | cons a0 accs' =>
        -- the first record: its account, cross-reference and disclosure group
        obtain ⟨hid, hid0, hcne, hcv⟩ := hval a0 (by simp)
        obtain ⟨c0, cs, hc0⟩ : ∃ c cs, a0.cats = c :: cs := by
          cases h : a0.cats with
          | nil => exact absurd h hcne
          | cons c cs => exact ⟨c, cs, rfl⟩
        have hrest' := hrest
        simp only [items, List.flatMap_cons, hc0, List.map_cons, List.cons_append, List.map_append,
          List.cons.injEq] at hrest'
        obtain ⟨rfl, hys⟩ := hrest'
        obtain ⟨hty, hfill, hcat, hcat0, hcbal⟩ := hcv c0 (by simp [hc0])
        have hsome : f1.recs[f1.pos]? = some (Cat.bytes a0.id c0) := by
          rw [h1r, h1p]; simp [items, hc0]
        obtain ⟨pre, mil, post, hpre, hpost, hmil, hmil0, hck⟩ := hclk 0
        have hall : items (a0 :: accs') = (a0, c0) :: (cs.map (Prod.mk a0) ++ items accs') := by
          simp [items, hc0]
        -- if the first record abends, the model stops there
        have hX : (step4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
              ⟨none, acc0, [], 0, 0, [], false⟩ (a0, c0)).stop = true →
            model4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
              (items (a0 :: accs')) = step4x accts xrefs discs (m.read 1729 10) (m.read 1314 76)
                (m.read 1588 20) clk ⟨none, acc0, [], 0, 0, [], false⟩ (a0, c0) := by
          intro h
          rw [hall]
          simp only [model4x, List.foldl_cons]
          exact foldl_step4x_stop _ _ _ _ _ _ _ _ _ h
        rcases ha : acctIdx accts a0.id with _ | i
        · -- no account record: abend
          right
          have hX' := (hX (by simp [step4x, ha]))
          simp only [ExitX, hX', step4x, ha]
          simp only [acctIdx] at ha
          cobol_auto [hclk0, h3r, Cat.bytes, spaces11, hnum]
          cobol_inv [abendEvents4, hout, notFoundMsg, errAcctMsg, status23Msg, abendMsg]
        · obtain ⟨aid, aid0, as, abal, amid, acc, acd, azip, agrp, aaf⟩ := acct_valid hav ha
          have haid := acct_id_of_idx hav hid hid0 ha
          have har := acct_rec ha
          generalize hA : accts.getD i acc0 = A at aid aid0 as abal amid acc acd azip agrp aaf haid har
          rcases hx : xrefIdx xrefs a0.id with _ | j
          · -- no cross-reference: abend
            right
            have hX' := (hX (by simp [step4x, ha, hx]))
            simp only [ExitX, hX', step4x, ha, hx]
            simp only [acctIdx] at ha
            simp only [xrefIdx] at hx
            cobol_auto [hclk0, h3r, Cat.bytes, Acc.bytes, spaces11, hnum]
            cobol_inv [abendEvents4, hout, notFoundMsg, errXrefMsg, status23Msg, abendMsg]
          · have hxj : (xrefs.getD j []).length = 50 := hxl _ (getD_mem4 [] (findKey_lt4 hx))
            have ha' := ha
            have hx' := hx
            simp only [acctIdx] at ha'
            simp only [xrefIdx] at hx'
            -- the account's disclosure group, else DEFAULT
            rcases hd : discIdx discs A.grp c0 with _ | k
            · have hdu := hd
              simp only [discIdx] at hdu
              rcases hd' : discIdx discs defaultGrp c0 with _ | k'
              · -- no DEFAULT group either: abend
                right
                have hX' := hX (by simp [-List.getD_eq_getElem?_getD, step4x, ha, hx, hA, rateX, hd, hd'])
                simp only [ExitX, hX', step4x, ha, hx, hA, rateX, hd, hd']
                simp only [discIdx, defaultGrp, List.cons_append, List.nil_append] at hd'
                cobol_auto [hclk0, h3r, Cat.bytes, Acc.bytes, spaces11, hnum, har, List.take_take]
                cobol_inv [abendEvents4, hout, missingMsg, tryDefaultMsg, errDefaultMsg, status23Msg,
                  abendMsg]
              · -- the DEFAULT group's rate
                obtain ⟨dkl, drate, dfl⟩ := disc_valid hdv hd'
                have hdr := disc_rec hd'
                generalize hD : discs.getD k' disc0 = D at dkl drate dfl hdr
                have hdu' := hd'
                simp only [discIdx, defaultGrp, List.cons_append, List.nil_append] at hdu'
                left
                by_cases hr0 : D.rate = 0
                · cobol_auto [hclk0, h3r, Acc.bytes, Cat.bytes, Disc.bytes, spaces11, har, hdr]
                  cobol_inv [Acc.bytes, Cat.bytes, Disc.bytes, fitNum_idem, items, hys, model4x, step4x,
                    rateX, rateX.withRateX, txRecX, monthly, db2ts, hout, systemSrc, descHead, spaces110,
                    missingMsg, tryDefaultMsg, ha, hx, hA, hd, hd', hD, hr0, fitNum_total_bound,
                    List.length_take, hxj, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt]
                    with _, _, _, _, _, [], a0, accs', [c0], cs, _, i
                · cobol_auto [hclk0, h3r, Acc.bytes, Cat.bytes, Disc.bytes, spaces11, har, hdr]
                  cobol_inv [Acc.bytes, Cat.bytes, Disc.bytes, fitNum_idem, items, hys, model4x, step4x,
                    rateX, rateX.withRateX, txRecX, monthly, db2ts, hout, systemSrc, descHead, spaces110,
                    missingMsg, tryDefaultMsg, ha, hx, hA, hd, hd', hD, hr0, fitNum_total_bound,
                    List.length_take, hxj, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt]
                    with _, _, _, _, _, [], a0, accs', [c0], cs, _, i
            · -- the account's group is found
              obtain ⟨dkl, drate, dfl⟩ := disc_valid hdv hd
              have hdr := disc_rec hd
              generalize hD : discs.getD k disc0 = D at dkl drate dfl hdr
              have hdu := hd
              simp only [discIdx] at hdu
              left
              by_cases hr0 : D.rate = 0
              · cobol_auto [hclk0, h3r, Acc.bytes, Cat.bytes, Disc.bytes, spaces11, har, hdr]
                cobol_inv [Acc.bytes, Cat.bytes, Disc.bytes, fitNum_idem, items, hys, model4x, step4x,
                  rateX, rateX.withRateX, txRecX, monthly, db2ts, hout, systemSrc, descHead, spaces110,
                  ha, hx, hA, hd, hD, hr0, fitNum_total_bound, List.length_take, hxj,
                  WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt]
                  with _, _, _, _, _, [], a0, accs', [c0], cs, _, i
              · cobol_auto [hclk0, h3r, Acc.bytes, Cat.bytes, Disc.bytes, spaces11, har, hdr]
                cobol_inv [Acc.bytes, Cat.bytes, Disc.bytes, fitNum_idem, items, hys, model4x, step4x,
                  rateX, rateX.withRateX, txRecX, monthly, db2ts, hout, systemSrc, descHead, spaces110,
                  ha, hx, hA, hd, hD, hr0, fitNum_total_bound, List.length_take, hxj,
                  WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt]
                  with _, _, _, _, _, [], a0, accs', [c0], cs, _, i


    · -- the records of `pre` and `dc` processed
      dsimp only at h1711 h1678 h956 h852 h1700 hcnt hsuf hclk0 hout
      replace hrest : y :: ys = (tc.map (Prod.mk cur) ++ items post).map some ++ [none] := by
        rcases hrest with ⟨h, -⟩ | h
        · simp at h
        · exact h
      obtain ⟨cid, cid0, ccne, ccv⟩ := hval cur (by simp [hacc])
      -- the record count and the transaction-id suffix stay below their capacities
      have hcntb : (items pre).length + dc.length < 999999 := by
        have : (items accs).length = (items pre).length + (dc.length + tc.length) + (items post).length := by
          rw [hacc, items_mid, hcur]; simp; omega
        omega
      have hpl : (items pre).length < 999999 := by omega
      have hdl : dc.length < 999999 := by omega
      have hkb' : S.k < 999999 := by omega
      -- the current account's record (the one read for `cur`)
      have hSid : S.acct.id = cur.id := by rw [hSacc]; exact acct_id_of_idx hav cid cid0 hiC
      have hSv : S.acct.validRec := by rw [hSacc]; exact acct_valid hav hiC
      obtain ⟨sid, sid0, ss, sbal, smid, scc, scd, szip, sgrp, saf⟩ := hSv
      cases tc with
      | cons c tc' =>
        -- a later record of the same account
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at hrest
        obtain ⟨rfl, hys⟩ := hrest
        have hye : ys.isEmpty = false := by rw [hys]; simp
        obtain ⟨hty, hfill, hcat, hcat0, hcbal⟩ := ccv c (by simp [hcur])
        have hsome : f1.recs[f1.pos]? = some (Cat.bytes cur.id c) := by
          rw [h1r, h1p, hacc]; exact tcat_mid _ pre post cur dc tc' c hcur
        obtain ⟨pre', mil, post', hpre, hpost', hmil, hmil0, hck⟩ := hclk S.k
        have hM : model4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
            (items pre ++ (dc ++ [c]).map (Prod.mk cur)) =
              step4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk S (cur, c) := by
          rw [List.map_append, List.map_singleton, model4x_append2, hS]
        have hX : (step4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk S
              (cur, c)).stop = true →
            model4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk (items accs) =
              step4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk S (cur, c) := by
          intro h
          have hi : items accs = (items pre ++ (dc ++ [c]).map (Prod.mk cur)) ++
              (tc'.map (Prod.mk cur) ++ items post) := by
            rw [hacc, items_mid, hcur]; simp
          rw [hi, model4x_stop_append _ _ _ _ _ _ _ _ _ (by rw [hM]; exact h), hM]
        rcases hd : discIdx discs S.acct.grp c with _ | k
        · have hdu := hd
          simp only [discIdx] at hdu
          rcases hd' : discIdx discs defaultGrp c with _ | k'
          · -- no DEFAULT group either: abend
            right
            have hX' := hX (by simp [-List.getD_eq_getElem?_getD, step4x, hstop, hlast, rateX, hd, hd'])
            simp only [ExitX, hX', step4x, hstop, hlast, rateX, hd, hd']
            simp only [discIdx, defaultGrp, List.cons_append, List.nil_append] at hd'
            cobol_auto [hclk0, Acc.bytes, Cat.bytes, hnum, List.take_take]
            cobol_inv [abendEvents4, hout, missingMsg, tryDefaultMsg, errDefaultMsg, status23Msg,
              abendMsg]
          · -- the DEFAULT group's rate
            obtain ⟨dkl, drate, dfl⟩ := disc_valid hdv hd'
            have hdr := disc_rec hd'
            generalize hD : discs.getD k' disc0 = D at dkl drate dfl hdr
            have hdu' := hd'
            simp only [discIdx, defaultGrp, List.cons_append, List.nil_append] at hdu'
            left
            by_cases hr0 : D.rate = 0
            · cobol_auto [hclk0, Acc.bytes, Cat.bytes, Disc.bytes, hdr]
              cobol_inv [Acc.bytes, Cat.bytes, Disc.bytes, fitNum_idem, hys, hye, hM, step4x, hstop, hlast,
                rateX, rateX.withRateX, txRecX, monthly, db2ts, hout, systemSrc, descHead, spaces110,
                missingMsg, tryDefaultMsg, hd, hd', hD, hr0, fitNum_total_bound, hcardl,
                WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt, WS_MONTHLY_INT.fmt,
                Int.add_assoc] with _, _, _, _, _, pre, cur, post, dc ++ [c], tc', _, iC
              all_goals (rw [hM, step4x_same _ _ _ _ _ _ _ S (cur, c) hstop hlast]; first
                | exact rateX_total _ _ _ _ _ _ _ _ htot
                | (have := rateX_k_le discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk S c
                    (.display (Cat.bytes cur.id c) :: S.out)
                   simp only [List.length_append, List.length_singleton]; omega))
            · cobol_auto [hclk0, Acc.bytes, Cat.bytes, Disc.bytes, hdr]
              cobol_inv [Acc.bytes, Cat.bytes, Disc.bytes, fitNum_idem, hys, hye, hM, step4x, hstop, hlast,
                rateX, rateX.withRateX, txRecX, monthly, db2ts, hout, systemSrc, descHead, spaces110,
                missingMsg, tryDefaultMsg, hd, hd', hD, hr0, fitNum_total_bound, hcardl,
                WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt, WS_MONTHLY_INT.fmt,
                Int.add_assoc] with _, _, _, _, _, pre, cur, post, dc ++ [c], tc', _, iC
              all_goals (rw [hM, step4x_same _ _ _ _ _ _ _ S (cur, c) hstop hlast]; first
                | exact rateX_total _ _ _ _ _ _ _ _ htot
                | (have := rateX_k_le discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk S c
                    (.display (Cat.bytes cur.id c) :: S.out)
                   simp only [List.length_append, List.length_singleton]; omega))
        · -- the account's group is found
          obtain ⟨dkl, drate, dfl⟩ := disc_valid hdv hd
          have hdr := disc_rec hd
          generalize hD : discs.getD k disc0 = D at dkl drate dfl hdr
          have hdu := hd
          simp only [discIdx] at hdu
          left
          by_cases hr0 : D.rate = 0
          · cobol_auto [hclk0, Acc.bytes, Cat.bytes, Disc.bytes, hdr]
            cobol_inv [Acc.bytes, Cat.bytes, Disc.bytes, fitNum_idem, hys, hye, hM, step4x, hstop, hlast,
              rateX, rateX.withRateX, txRecX, monthly, db2ts, hout, systemSrc, descHead, spaces110,
              hd, hD, hr0, fitNum_total_bound, hcardl, WS_RECORD_COUNT.fmt,
              WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt, WS_MONTHLY_INT.fmt, Int.add_assoc]
              with _, _, _, _, _, pre, cur, post, dc ++ [c], tc', _, iC
            all_goals (rw [hM, step4x_same _ _ _ _ _ _ _ S (cur, c) hstop hlast]; first
              | exact rateX_total _ _ _ _ _ _ _ _ htot
              | (have := rateX_k_le discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk S c
                  (.display (Cat.bytes cur.id c) :: S.out)
                 simp only [List.length_append, List.length_singleton]; omega))
          · cobol_auto [hclk0, Acc.bytes, Cat.bytes, Disc.bytes, hdr]
            cobol_inv [Acc.bytes, Cat.bytes, Disc.bytes, fitNum_idem, hys, hye, hM, step4x, hstop, hlast,
              rateX, rateX.withRateX, txRecX, monthly, db2ts, hout, systemSrc, descHead, spaces110,
              hd, hD, hr0, fitNum_total_bound, hcardl, WS_RECORD_COUNT.fmt,
              WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt, WS_MONTHLY_INT.fmt, Int.add_assoc]
              with _, _, _, _, _, pre, cur, post, dc ++ [c], tc', _, iC
            all_goals (rw [hM, step4x_same _ _ _ _ _ _ _ S (cur, c) hstop hlast]; first
              | exact rateX_total _ _ _ _ _ _ _ _ htot
              | (have := rateX_k_le discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk S c
                  (.display (Cat.bytes cur.id c) :: S.out)
                 simp only [List.length_append, List.length_singleton]; omega))
      | nil =>
        simp only [List.append_nil] at hcur
        cases post with
        | nil =>
          -- the READ reaches the end of the file
          simp only [List.map_nil, List.nil_append, items, List.flatMap_nil, List.cons.injEq] at hrest
          obtain ⟨rfl, rfl⟩ := hrest
          have hnone : f1.recs[f1.pos]? = none := by
            rw [h1r, h1p, hacc]; simp [items, hcur]
          left
          cobol_auto
          cobol_inv [hS] with _, _, _, _, _, pre, cur, [], dc, [], _, iC
        | cons nxt post' =>
          -- the first record of the next account: post the interest of `cur`, then as the first one
          obtain ⟨nid, nid0, ncne, ncv⟩ := hval nxt (by simp [hacc])
          obtain ⟨c, cs, hnc⟩ : ∃ c cs, nxt.cats = c :: cs := by
            cases h : nxt.cats with
            | nil => exact absurd h ncne
            | cons c cs => exact ⟨c, cs, rfl⟩
          simp only [List.map_nil, List.nil_append, items, List.flatMap_cons, hnc, List.map_cons,
            List.cons_append, List.cons.injEq] at hrest
          obtain ⟨rfl, hys⟩ := hrest
          replace hys : ys = (cs.map (Prod.mk nxt) ++ items post').map some ++ [none] := by
            rw [hys]; simp [items]
          have hye : ys.isEmpty = false := by rw [hys]; simp
          obtain ⟨hty, hfill, hcat, hcat0, hcbal⟩ := ncv c (by simp [hnc])
          -- `cur` precedes every later account, so its id differs from theirs
          have hlater : ∀ b ∈ nxt :: post', cur.id ≠ b.id := by
            rw [hacc] at hdist
            exact (List.pairwise_cons.1 (List.pairwise_append.1 hdist).2.1).1
          have hcn : cur.id ≠ nxt.id := hlater nxt (by simp)
          have hne1 : nxt.id.natAbs ≠ cur.id.natAbs := fun h => hcn (by omega)
          have hmc : cur.id.natAbs % 100000000000 = cur.id.natAbs := Nat.mod_eq_of_lt cid
          have hmn : nxt.id.natAbs % 100000000000 = nxt.id.natAbs := Nat.mod_eq_of_lt nid
          have hsome : f1.recs[f1.pos]? = some (Cat.bytes nxt.id c) := by
            rw [h1r, h1p, hacc, ← hcur]; exact tcat_next _ pre post' cur nxt c cs hnc
          obtain ⟨pre', mil, post'', hpre, hpost', hmil, hmil0, hck⟩ := hclk S.k
          -- the REWRITE of `cur`'s record: found where it was read, keys unchanged
          have hfC : Sem.findKey { off := 0, len := 11 } (encodeNum {} ACCT_ID.fmt S.acct.id) f3.recs =
              some iC := by
            rw [h3k, hSid]; simpa [acctIdx] using hiC
          have hkC : Sem.keyOf { off := 0, len := 11 } (f3.recs.getD iC []) =
              encodeNum {} ACCT_ID.fmt S.acct.id := findKey_key4 hfC
          have hkC2 : (f3.recs.getD iC []).take 11 = encodeNum {} ACCT_ID.fmt S.acct.id := by
            have := hkC; simpa [Sem.keyOf] using this
          have hkeyC : Sem.keyOf { off := 0, len := 11 } (S.acct.posted S.total) =
              Sem.keyOf { off := 0, len := 11 } (f3.recs.getD iC []) := by
            rw [findKey_key4 hfC]
            simp only [Sem.keyOf, List.drop_zero, Acc.posted, List.append_assoc]
            rw [List.take_left' (length_encodeNum_acct _)]
          have hM : model4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
              (items (pre ++ [cur]) ++ [c].map (Prod.mk nxt)) =
                step4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk S (nxt, c) := by
            rw [items_concat, hcur, List.map_singleton, model4x_append, hS]
          have hX : (step4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk S
                (nxt, c)).stop = true →
              model4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk (items accs) =
                step4x accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk S (nxt, c) := by
            intro h
            have hi : items accs = (items (pre ++ [cur]) ++ [c].map (Prod.mk nxt)) ++
                (cs.map (Prod.mk nxt) ++ items post') := by
              rw [hacc]; simp [items, hnc]
            rw [hi, model4x_stop_append _ _ _ _ _ _ _ _ _ (by rw [hM]; exact h), hM]
          have hlastn : S.last ≠ some nxt.id := by rw [hlast]; simpa using hcn
          rcases ha : acctIdx accts nxt.id with _ | i
          · -- no account record for `nxt`: abend after the REWRITE
            right
            have hX' := hX (by simp [-List.getD_eq_getElem?_getD, step4x, hstop, hlastn, ha])
            simp only [ExitX, hX', step4x, hstop, hlastn, ha, if_false, hlast, Option.isSome_some,
              if_true]
            have hau := ha
            simp only [acctIdx] at hau
            have hfn : Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt nxt.id) f3.recs = none := by
              rw [h3k]; exact hau
            cobol_auto [hclk0, findKey_set, hkC, hkC2, hfC, hfn, Acc.bytes, Cat.bytes, hnum]
            cobol_inv [abendEvents4, hout, notFoundMsg, errAcctMsg, status23Msg, abendMsg, Acc.posted, List.append_assoc]
          · -- the record of `nxt`: found, where it was and unchanged
            obtain ⟨aid, aid0, as, abal, amid, acc, acd, azip, agrp, aaf⟩ := acct_valid hav ha
            have haid := acct_id_of_idx hav nid nid0 ha
            have har := acct_rec ha
            have hgi : f3.recs.getD i [] = (accts.map Acc.bytes).getD i [] := hpost nxt (by simp) i ha
            have hiC_ne : iC ≠ i := findKey_ne4 (by simpa [acctIdx] using hiC) (by simpa [acctIdx] using ha)
              (fun h => hcn (acct_id_inj cid cid0 nid nid0 h))
            have hfn : Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt nxt.id) f3.recs =
                some i := by
              rw [h3k]; simpa [acctIdx] using ha
            -- the later accounts' records are not the one rewritten
            have hlat : ∀ b ∈ post', ∀ i', acctIdx accts b.id = some i' → iC ≠ i' := by
              intro b hb i' hi'
              obtain ⟨bid, bid0, -⟩ := hval b (by simp [hacc, hb])
              exact findKey_ne4 (by simpa [acctIdx] using hiC) (by simpa [acctIdx] using hi')
                (fun h => hlater b (by simp [hb]) (acct_id_inj cid cid0 bid bid0 h))
            generalize hA : accts.getD i acc0 = A at aid aid0 as abal amid acc acd azip agrp aaf haid har
            rcases hx : xrefIdx xrefs nxt.id with _ | j
            · -- no cross-reference: abend after the REWRITE
              right
              have hX' := hX (by simp [-List.getD_eq_getElem?_getD, step4x, hstop, hlastn, ha, hx])
              simp only [ExitX, hX', step4x, hstop, ha, hx, if_false, hlast, Option.isSome_some, if_true]
              have hxu := hx
              simp only [xrefIdx] at hxu
              cobol_auto [hclk0, findKey_set, getD_set_ne, hkC, hkC2, hfC, hfn, hgi, har, hiC_ne,
                Acc.bytes, Cat.bytes, hnum]
              cobol_inv [abendEvents4, hout, notFoundMsg, errXrefMsg, status23Msg, abendMsg, Acc.posted,
                List.append_assoc]
            · have hxj : (xrefs.getD j []).length = 50 := hxl _ (getD_mem4 [] (findKey_lt4 hx))
              have hxu := hx
              simp only [xrefIdx] at hxu
              rcases hd : discIdx discs A.grp c with _ | k
              · have hdu := hd
                simp only [discIdx] at hdu
                rcases hd' : discIdx discs defaultGrp c with _ | k'
                · -- no DEFAULT group either: abend
                  right
                  have hX' := hX (by simp [-List.getD_eq_getElem?_getD, step4x, hstop, hlastn, ha, hx, hA,
                    rateX, hd, hd'])
                  simp only [ExitX, hX', step4x, hstop, ha, hx, hA, rateX, hd, hd', if_false, hlast,
                    Option.isSome_some, if_true]
                  simp only [discIdx, defaultGrp, List.cons_append, List.nil_append] at hd'
                  cobol_auto [hclk0, findKey_set, getD_set_ne, hkC, hkC2, hfC, hfn, hgi, har, hiC_ne,
                    Acc.bytes, Cat.bytes, hnum, List.take_take]
                  cobol_inv [abendEvents4, hout, missingMsg, tryDefaultMsg, errDefaultMsg, status23Msg,
                    abendMsg, Acc.posted, List.append_assoc]
                · -- the DEFAULT group's rate
                  obtain ⟨dkl, drate, dfl⟩ := disc_valid hdv hd'
                  have hdr := disc_rec hd'
                  generalize hD : discs.getD k' disc0 = D at dkl drate dfl hdr
                  have hdu' := hd'
                  simp only [discIdx, defaultGrp, List.cons_append, List.nil_append] at hdu'
                  left
                  by_cases hr0 : D.rate = 0
                  · cobol_auto [hclk0, findKey_set, getD_set_ne, hkC, hkC2, hfC, hfn, hgi, har, hiC_ne,
                      Acc.bytes, Cat.bytes, Disc.bytes, hdr]
                    cobol_inv [Acc.bytes, Cat.bytes, Disc.bytes, Acc.posted, List.append_assoc, fitNum_idem,
                      hys, hye, items_concat, hcur, h1p, List.length_append, List.length_map,
                      List.length_singleton, hM, step4x, hstop, hlast, rateX, rateX.withRateX, txRecX, monthly, db2ts,
                      hout, systemSrc, descHead, spaces110, missingMsg, tryDefaultMsg, ha, hx, hA, hd, hd',
                      hD, hr0, fitNum_total_bound, List.length_take, hxj, WS_RECORD_COUNT.fmt,
                      WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt, WS_MONTHLY_INT.fmt, Int.add_assoc]
                      with _, _, _, _, _, pre ++ [cur], nxt, post', [c], cs, _, i
                    all_goals first
                      | (intro v; rw [findKey_set _ _ _ _ _ (by rw [hkC]; simp only [Sem.keyOf, List.drop_zero]; exact List.take_left' (length_encodeNum_acct _))]; exact h3k v)
                      | (intro b hb i' hi'; rw [getD_set_ne _ _ (hlat b hb i' hi')]
                         exact hpost b (by simp [hb]) i' hi')
                      | (rw [hM]
                         have := step4x_k_le accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
                           S (nxt, c)
                         simp only [items_concat, hcur, List.length_append, List.length_map,
                           List.length_singleton] at this ⊢
                         omega)
                      | (rw [h1p, items_concat, hcur]; simp)
                  · cobol_auto [hclk0, findKey_set, getD_set_ne, hkC, hkC2, hfC, hfn, hgi, har, hiC_ne,
                      Acc.bytes, Cat.bytes, Disc.bytes, hdr]
                    cobol_inv [Acc.bytes, Cat.bytes, Disc.bytes, Acc.posted, List.append_assoc, fitNum_idem,
                      hys, hye, items_concat, hcur, h1p, List.length_append, List.length_map,
                      List.length_singleton, hM, step4x, hstop, hlast, rateX, rateX.withRateX, txRecX, monthly, db2ts,
                      hout, systemSrc, descHead, spaces110, missingMsg, tryDefaultMsg, ha, hx, hA, hd, hd',
                      hD, hr0, fitNum_total_bound, List.length_take, hxj, WS_RECORD_COUNT.fmt,
                      WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt, WS_MONTHLY_INT.fmt, Int.add_assoc]
                      with _, _, _, _, _, pre ++ [cur], nxt, post', [c], cs, _, i
                    all_goals first
                      | (intro v; rw [findKey_set _ _ _ _ _ (by rw [hkC]; simp only [Sem.keyOf, List.drop_zero]; exact List.take_left' (length_encodeNum_acct _))]; exact h3k v)
                      | (intro b hb i' hi'; rw [getD_set_ne _ _ (hlat b hb i' hi')]
                         exact hpost b (by simp [hb]) i' hi')
                      | (rw [hM]
                         have := step4x_k_le accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
                           S (nxt, c)
                         simp only [items_concat, hcur, List.length_append, List.length_map,
                           List.length_singleton] at this ⊢
                         omega)
                      | (rw [h1p, items_concat, hcur]; simp)
              · -- the account's group is found
                obtain ⟨dkl, drate, dfl⟩ := disc_valid hdv hd
                have hdr := disc_rec hd
                generalize hD : discs.getD k disc0 = D at dkl drate dfl hdr
                have hdu := hd
                simp only [discIdx] at hdu
                left
                by_cases hr0 : D.rate = 0
                · cobol_auto [hclk0, findKey_set, getD_set_ne, hkC, hkC2, hfC, hfn, hgi, har, hiC_ne,
                    Acc.bytes, Cat.bytes, Disc.bytes, hdr]
                  cobol_inv [Acc.bytes, Cat.bytes, Disc.bytes, Acc.posted, List.append_assoc, fitNum_idem,
                    hys, hye, items_concat, hcur, h1p, List.length_append, List.length_map,
                      List.length_singleton, hM, step4x, hstop, hlast, rateX, rateX.withRateX, txRecX, monthly, db2ts,
                    hout, systemSrc, descHead, spaces110, ha, hx, hA, hd, hD, hr0, fitNum_total_bound,
                    List.length_take, hxj, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt,
                    WS_MONTHLY_INT.fmt, Int.add_assoc]
                    with _, _, _, _, _, pre ++ [cur], nxt, post', [c], cs, _, i
                  all_goals first
                    | (intro v; rw [findKey_set _ _ _ _ _ (by rw [hkC]; simp only [Sem.keyOf, List.drop_zero]; exact List.take_left' (length_encodeNum_acct _))]; exact h3k v)
                    | (intro b hb i' hi'; rw [getD_set_ne _ _ (hlat b hb i' hi')]
                       exact hpost b (by simp [hb]) i' hi')
                    | (rw [hM]
                       have := step4x_k_le accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
                         S (nxt, c)
                       simp only [items_concat, hcur, List.length_append, List.length_map,
                         List.length_singleton] at this ⊢
                       omega)
                    | (rw [h1p, items_concat, hcur]; simp)
                · cobol_auto [hclk0, findKey_set, getD_set_ne, hkC, hkC2, hfC, hfn, hgi, har, hiC_ne,
                    Acc.bytes, Cat.bytes, Disc.bytes, hdr]
                  cobol_inv [Acc.bytes, Cat.bytes, Disc.bytes, Acc.posted, List.append_assoc, fitNum_idem,
                    hys, hye, items_concat, hcur, h1p, List.length_append, List.length_map,
                      List.length_singleton, hM, step4x, hstop, hlast, rateX, rateX.withRateX, txRecX, monthly, db2ts,
                    hout, systemSrc, descHead, spaces110, ha, hx, hA, hd, hD, hr0, fitNum_total_bound,
                    List.length_take, hxj, WS_RECORD_COUNT.fmt, WS_TRANID_SUFFIX.fmt, WS_TOTAL_INT.fmt,
                    WS_MONTHLY_INT.fmt, Int.add_assoc]
                    with _, _, _, _, _, pre ++ [cur], nxt, post', [c], cs, _, i
                  all_goals first
                    | (intro v; rw [findKey_set _ _ _ _ _ (by rw [hkC]; simp only [Sem.keyOf, List.drop_zero]; exact List.take_left' (length_encodeNum_acct _))]; exact h3k v)
                    | (intro b hb i' hi'; rw [getD_set_ne _ _ (hlat b hb i' hi')]
                       exact hpost b (by simp [hb]) i' hi')
                    | (rw [hM]
                       have := step4x_k_le accts xrefs discs (m.read 1729 10) (m.read 1314 76) (m.read 1588 20) clk
                         S (nxt, c)
                       simp only [items_concat, hcur, List.length_append, List.length_map,
                         List.length_singleton] at this ⊢
                       omega)
                    | (rw [h1p, items_concat, hcur]; simp)

#print axioms cbact04c_every

end CardDemo.Cbact04c
