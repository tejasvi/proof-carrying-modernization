-- Copied unchanged from coblean (frozen snapshot ~/coblean_snapshots/coblean-20261024T1445Z,
-- Examples/Cbtrn02c.lean); only the IR path differs. coblean and JimpleLean both have a library
-- named `Examples`, so equiv-lean cannot import the original module next to JimpleLean.
/-
# CardDemo CBTRN02C (daily transaction posting), extracted by the front end

`examples/carddemo/cbtrn02c.ir.json` is the output of `tools/cobolfe` on `app/cbl/CBTRN02C.cbl`
of AWS CardDemo, unchanged.  For each daily transaction the program looks up its card in the
cross-reference file and the card's account in the account file, and checks the credit limit
and the expiration date.  A transaction that fails is written to the rejects file with a
reason code.  A valid one updates the transaction category balance file (a new record when its
key is not there), adds the amount to the account (balance and cycle credit or debit), and is
written to the transaction file with the processing timestamp from the clock.
-/
import Cobol
open Cobol

namespace CardDemo

cobol_program Cbtrn02c from "../../../../examples/cobol/carddemo/cbtrn02c.ir.json"

namespace Cbtrn02c

/-- `START OF EXECUTION OF PROGRAM CBTRN02C` in EBCDIC. -/
def startMsg : List UInt8 := [226, 227, 193, 217, 227, 64, 214, 198, 64, 197, 231, 197, 195, 228, 227, 201, 214, 213, 64, 214, 198, 64, 215, 217, 214, 199, 217, 193, 212, 64, 195, 194, 227, 217, 213, 240, 242, 195]

/-- `END OF EXECUTION OF PROGRAM CBTRN02C` in EBCDIC. -/
def endMsg : List UInt8 := [197, 213, 196, 64, 214, 198, 64, 197, 231, 197, 195, 228, 227, 201, 214, 213, 64, 214, 198, 64, 215, 217, 214, 199, 217, 193, 212, 64, 195, 194, 227, 217, 213, 240, 242, 195]

/-- `TRANSACTIONS PROCESSED :` in EBCDIC. -/
def procMsg : List UInt8 := [227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 226, 64, 215, 217, 214, 195, 197, 226, 226, 197, 196, 64, 122]

/-- `TRANSACTIONS REJECTED  :` in EBCDIC. -/
def rejMsg : List UInt8 := [227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 226, 64, 217, 197, 209, 197, 195, 227, 197, 196, 64, 64, 122]

/-- `TCATBAL record not found for key : ` in EBCDIC. -/
def noCatMsg : List UInt8 := [227, 195, 193, 227, 194, 193, 211, 64, 153, 133, 131, 150, 153, 132, 64, 149, 150, 163, 64, 134, 150, 164, 149, 132, 64, 134, 150, 153, 64, 146, 133, 168, 64, 122, 64]

/-- `.. Creating.` in EBCDIC. -/
def creatingMsg : List UInt8 := [75, 75, 64, 195, 153, 133, 129, 163, 137, 149, 135, 75]

/-- `INVALID CARD NUMBER FOUND` in EBCDIC. -/
def badCardDesc : List UInt8 := [201, 213, 229, 193, 211, 201, 196, 64, 195, 193, 217, 196, 64, 213, 228, 212, 194, 197, 217, 64, 198, 214, 228, 213, 196]

/-- `ACCOUNT RECORD NOT FOUND` in EBCDIC. -/
def noAcctDesc : List UInt8 := [193, 195, 195, 214, 228, 213, 227, 64, 217, 197, 195, 214, 217, 196, 64, 213, 214, 227, 64, 198, 214, 228, 213, 196]

/-- `OVERLIMIT TRANSACTION` in EBCDIC. -/
def overLimitDesc : List UInt8 := [214, 229, 197, 217, 211, 201, 212, 201, 227, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213]

/-- `TRANSACTION RECEIVED AFTER ACCT EXPIRATION` in EBCDIC. -/
def expiredDesc : List UInt8 := [227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 217, 197, 195, 197, 201, 229, 197, 196, 64, 193, 198, 227, 197, 217, 64, 193, 195, 195, 227, 64, 197, 231, 215, 201, 217, 193, 227, 201, 214, 213]

theorem startMsg_eq : Codepage.encode037 "START OF EXECUTION OF PROGRAM CBTRN02C" = some startMsg := by decide +kernel
theorem endMsg_eq : Codepage.encode037 "END OF EXECUTION OF PROGRAM CBTRN02C" = some endMsg := by decide +kernel
theorem procMsg_eq : Codepage.encode037 "TRANSACTIONS PROCESSED :" = some procMsg := by decide +kernel
theorem rejMsg_eq : Codepage.encode037 "TRANSACTIONS REJECTED  :" = some rejMsg := by decide +kernel
theorem noCatMsg_eq : Codepage.encode037 "TCATBAL record not found for key : " = some noCatMsg := by decide +kernel
theorem creatingMsg_eq : Codepage.encode037 ".. Creating." = some creatingMsg := by decide +kernel
theorem badCardDesc_eq : Codepage.encode037 "INVALID CARD NUMBER FOUND" = some badCardDesc := by decide +kernel
theorem noAcctDesc_eq : Codepage.encode037 "ACCOUNT RECORD NOT FOUND" = some noAcctDesc := by decide +kernel
theorem overLimitDesc_eq : Codepage.encode037 "OVERLIMIT TRANSACTION" = some overLimitDesc := by decide +kernel
theorem expiredDesc_eq : Codepage.encode037 "TRANSACTION RECEIVED AFTER ACCT EXPIRATION" = some expiredDesc := by decide +kernel

/-- A daily transaction record (`CVTRA06Y`, 350 bytes). -/
structure Tran where
  id : List UInt8
  ty : List UInt8
  cat : Int
  src : List UInt8
  desc : List UInt8
  amt : Int
  merch : Int
  mname : List UInt8
  mcity : List UInt8
  mzip : List UInt8
  card : List UInt8
  orig : List UInt8
  proc : List UInt8
  fill : List UInt8
  deriving Inhabited

def Tran.bytes (t : Tran) : List UInt8 :=
  t.id ++ t.ty ++ encodeNum {} DALYTRAN_CAT_CD.fmt t.cat ++ t.src ++ t.desc ++
    encodeNum {} DALYTRAN_AMT.fmt t.amt ++ encodeNum {} DALYTRAN_MERCHANT_ID.fmt t.merch ++
    t.mname ++ t.mcity ++ t.mzip ++ t.card ++ t.orig ++ t.proc ++ t.fill

def Tran.valid (t : Tran) : Prop :=
  t.id.length = 16 ∧ t.ty.length = 2 ∧ t.cat.natAbs < 10000 ∧ 0 ≤ t.cat ∧ t.src.length = 10 ∧
    t.desc.length = 100 ∧ t.amt.natAbs < 100000000000 ∧ t.merch.natAbs < 1000000000 ∧
    0 ≤ t.merch ∧ t.mname.length = 50 ∧ t.mcity.length = 50 ∧ t.mzip.length = 10 ∧
    t.card.length = 16 ∧ t.orig.length = 26 ∧ t.proc.length = 26 ∧ t.fill.length = 20

/-- A card cross-reference record (`CVACT03Y`): card number, customer id (not read), account
id, filler. -/
structure Xref where
  card : List UInt8
  cust : List UInt8
  acct : Int
  fill : List UInt8
  deriving Inhabited

def Xref.bytes (x : Xref) : List UInt8 :=
  x.card ++ x.cust ++ encodeNum {} XREF_ACCT_ID.fmt x.acct ++ x.fill

def Xref.valid (x : Xref) : Prop :=
  x.card.length = 16 ∧ x.cust.length = 9 ∧ x.acct.natAbs < 100000000000 ∧ 0 ≤ x.acct ∧
    x.fill.length = 14

/-- An account record (`CVACT01Y`, 300 bytes); the fields the program does not read are bytes. -/
structure Acct where
  id : List UInt8
  st : List UInt8
  bal : Int
  limit : Int
  mid : List UInt8
  exp : List UInt8
  reis : List UInt8
  cc : Int
  cd : Int
  rest : List UInt8
  deriving Inhabited

def Acct.bytes (a : Acct) : List UInt8 :=
  a.id ++ a.st ++ encodeNum {} ACCT_CURR_BAL.fmt a.bal ++ encodeNum {} ACCT_CREDIT_LIMIT.fmt a.limit ++
    a.mid ++ a.exp ++ a.reis ++ encodeNum {} ACCT_CURR_CYC_CREDIT.fmt a.cc ++
    encodeNum {} ACCT_CURR_CYC_DEBIT.fmt a.cd ++ a.rest

def Acct.valid (a : Acct) : Prop :=
  a.id.length = 11 ∧ a.st.length = 1 ∧ a.bal.natAbs < 1000000000000 ∧
    a.limit.natAbs < 1000000000000 ∧ a.mid.length = 22 ∧ a.exp.length = 10 ∧ a.reis.length = 10 ∧
    a.cc.natAbs < 1000000000000 ∧ a.cd.natAbs < 1000000000000 ∧ a.rest.length = 198

/-- A transaction category balance record (`CVTRA01Y`, 50 bytes): key (account id, type,
category), balance, filler. -/
structure TCat where
  key : List UInt8
  bal : Int
  fill : List UInt8
  deriving Inhabited

def TCat.bytes (c : TCat) : List UInt8 := c.key ++ encodeNum {} TRAN_CAT_BAL.fmt c.bal ++ c.fill

def TCat.valid (c : TCat) : Prop :=
  c.key.length = 17 ∧ c.bal.natAbs < 100000000000 ∧ c.fill.length = 22

/-- `WRITE` of a new record into the category balance file (in key order, as `insertByKey`). -/
def insertCat (c : TCat) : List TCat → List TCat
  | [] => [c]
  | x :: xs => if Sem.bytesLt c.key x.key then c :: x :: xs else x :: insertCat c xs

/-- `Z-GET-DB2-FORMAT-TIMESTAMP` of a clock reading (`FUNCTION CURRENT-DATE`):
`YYYY-MM-DD-hh.mm.ss.ff0000`. -/
def db2ts (c : List UInt8) : List UInt8 :=
  c.take 4 ++ [96] ++ (c.drop 4).take 2 ++ [96] ++ (c.drop 6).take 2 ++ [96] ++
    (c.drop 8).take 2 ++ [75] ++ (c.drop 10).take 2 ++ [75] ++ (c.drop 12).take 2 ++ [75] ++
    (c.drop 14).take 2 ++ [240, 240, 240, 240]

/-- The transaction file record of a posted transaction (`CVTRA05Y`): the daily record's fields,
the processing timestamp `ts`, and the `FILLER` of WORKING-STORAGE's `TRAN-RECORD` (`fill`,
never written by the program). -/
def tranRec (t : Tran) (ts fill : List UInt8) : List UInt8 :=
  t.id ++ t.ty ++ encodeNum {} TRAN_CAT_CD.fmt t.cat ++ t.src ++ t.desc ++
    encodeNum {} TRAN_AMT.fmt t.amt ++ encodeNum {} TRAN_MERCHANT_ID.fmt t.merch ++
    t.mname ++ t.mcity ++ t.mzip ++ t.card ++ t.orig ++ ts ++ fill

/-- The validation trailer of a rejected transaction: reason code and description. -/
def trailer (code : Int) (desc : List UInt8) : List UInt8 :=
  encodeNum {} WS_VALIDATION_FAIL_REASON.fmt code ++ desc ++ List.replicate (76 - desc.length) 64

/-- What the program has done after some transactions: the account and category balance files,
the `FILLER` of WORKING-STORAGE's `TRAN-CAT-BAL-RECORD` (it ends up in new category records),
the number of transactions posted (= clock readings) and rejected, and the events (newest
first, as `State.out`). -/
structure Model where
  accts : List Acct
  cats : List TCat
  catFill : List UInt8
  posted : Nat
  rejects : Nat
  out : List Event

/-- A rejected transaction: written to the rejects file with its reason. -/
def Model.reject (s : Model) (t : Tran) (code : Int) (desc : List UInt8) : Model :=
  { s with rejects := s.rejects + 1, out := .write 4 (t.bytes ++ trailer code desc) :: s.out }

/-- A valid transaction of card cross-reference `x` and account `a` (record `j`):
`2700-UPDATE-TCATBAL`, `2800-UPDATE-ACCOUNT-REC`, `2900-WRITE-TRANSACTION-FILE`. -/
def Model.post (clk : Nat → List UInt8) (tfill : List UInt8) (s : Model) (t : Tran) (x : Xref)
    (j : Nat) (a : Acct) : Model :=
  let key := encodeNum {} FD_TRANCAT_ACCT_ID.fmt x.acct ++ t.ty ++ encodeNum {} FD_TRANCAT_CD.fmt t.cat
  let a' : Acct := { a with
    bal := (Sem.fitNum {} ACCT_CURR_BAL.fmt (a.bal + t.amt)).2,
    cc := if 0 ≤ t.amt then (Sem.fitNum {} ACCT_CURR_CYC_CREDIT.fmt (a.cc + t.amt)).2 else a.cc,
    cd := if 0 ≤ t.amt then a.cd else (Sem.fitNum {} ACCT_CURR_CYC_DEBIT.fmt (a.cd + t.amt)).2 }
  let done (cats : List TCat) (catFill : List UInt8) (ev : List Event) : Model :=
    { s with accts := s.accts.set j a', cats, catFill, posted := s.posted + 1,
             out := .write 2 (tranRec t (db2ts (clk s.posted)) tfill) :: .rewrite 5 a'.bytes ::
               (ev ++ s.out) }
  match Sem.findKey { off := 0, len := 17 } key (s.cats.map TCat.bytes) with
  | none =>
    let c : TCat := { key, bal := t.amt, fill := s.catFill }
    done (insertCat c s.cats) s.catFill [.write 6 c.bytes, .display (noCatMsg ++ key ++ creatingMsg)]
  | some k =>
    let c := s.cats.getD k default
    let c' : TCat := { c with bal := (Sem.fitNum {} TRAN_CAT_BAL.fmt (c.bal + t.amt)).2 }
    done (s.cats.set k c') c.fill [.rewrite 6 c'.bytes]

/-- One daily transaction: `1500-VALIDATE-TRAN`, then post or reject. -/
def step (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8) (s : Model) (t : Tran) :
    Model :=
  match Sem.findKey { off := 0, len := 16 } t.card (xrefs.map Xref.bytes) with
  | none => s.reject t 100 badCardDesc
  | some i =>
    let x := xrefs.getD i default
    match Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt x.acct)
        (s.accts.map Acct.bytes) with
    | none => s.reject t 101 noAcctDesc
    | some j =>
      let a := s.accts.getD j default
      if Sem.cmpBytes a.exp (t.orig.take 10) = .lt then s.reject t 103 expiredDesc
      else if a.limit < (Sem.fitNum {} WS_TEMP_BAL.fmt (a.cc - a.cd + t.amt)).2 then
        s.reject t 102 overLimitDesc
      else s.post clk tfill t x j a

/-- The model after the transactions `ts`. -/
def model (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8) (s0 : Model)
    (ts : List Tran) : Model :=
  ts.foldl (step xrefs clk tfill) s0

/-! ## The model: lemmas -/

theorem model_append (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8) (s0 : Model)
    (ts : List Tran) (t : Tran) :
    model xrefs clk tfill s0 (ts ++ [t]) = step xrefs clk tfill (model xrefs clk tfill s0 ts) t := by
  simp [model, List.foldl_append]

theorem fitNum_bal (v : Int) :
    (Sem.fitNum {} { digits := 12, scale := 2, signed := true } v).2.natAbs < 1000000000000 := by
  have h := fitNum_holds {} { digits := 12, scale := 2, signed := true } v
  unfold NumFmt.Holds at h
  simp [NumFmt.fullBinary] at h
  omega

theorem fitNum_catBal (v : Int) :
    (Sem.fitNum {} { digits := 11, scale := 2, signed := true } v).2.natAbs < 100000000000 := by
  have h := fitNum_holds {} { digits := 11, scale := 2, signed := true } v
  unfold NumFmt.Holds at h
  simp [NumFmt.fullBinary] at h
  omega

/-- The files of the model hold well-formed records. -/
structure Model.valid (s : Model) : Prop where
  accts : ∀ a ∈ s.accts, a.valid
  cats : ∀ c ∈ s.cats, c.valid
  fill : s.catFill.length = 22

theorem mem_insertCat {c x : TCat} : ∀ {cats : List TCat}, x ∈ insertCat c cats → x = c ∨ x ∈ cats
  | [], h => by simp [insertCat] at h; exact Or.inl h
  | y :: ys, h => by
    simp only [insertCat] at h
    split at h
    · simpa using h
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr (by simp [h])
      · rcases mem_insertCat h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])

theorem getD_mem {α : Type} [Inhabited α] {l : List α} {i : Nat} (h : i < l.length) :
    l.getD i default ∈ l := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

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

theorem step_valid (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8) (s : Model)
    (t : Tran) (hs : s.valid) (ht : t.valid) (hxv : ∀ x ∈ xrefs, x.valid) :
    (step xrefs clk tfill s t).valid := by
  obtain ⟨hid, hty, hcat, hcat0, -, -, hamt, -⟩ := ht
  have keep : ∀ (c : Int) (d : List UInt8), (s.reject t c d).valid :=
    fun _ _ => ⟨hs.accts, hs.cats, hs.fill⟩
  unfold step
  split
  · exact keep _ _
  rename_i i hi
  try dsimp only
  split
  · exact keep _ _
  rename_i j hj
  have hj' : j < s.accts.length := by simpa using findKey_lt hj
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hs.accts _ (getD_mem hj')
  try dsimp only
  split
  · exact keep _ _
  split
  · exact keep _ _
  have hacct : ∀ (a' : Acct), a'.valid → ∀ b ∈ s.accts.set j a', b.valid := by
    intro a' ha' b hb
    rcases List.mem_or_eq_of_mem_set hb with hb | rfl
    · exact hs.accts b hb
    · exact ha'
  have ha' : ({ s.accts.getD j default with
      bal := (Sem.fitNum {} ACCT_CURR_BAL.fmt ((s.accts.getD j default).bal + t.amt)).2,
      cc := if 0 ≤ t.amt then (Sem.fitNum {} ACCT_CURR_CYC_CREDIT.fmt
        ((s.accts.getD j default).cc + t.amt)).2 else (s.accts.getD j default).cc,
      cd := if 0 ≤ t.amt then (s.accts.getD j default).cd else (Sem.fitNum {} ACCT_CURR_CYC_DEBIT.fmt
        ((s.accts.getD j default).cd + t.amt)).2 } : Acct).valid := by
    refine ⟨a1, a2, fitNum_bal _, a4, a5, a6, a7, ?_, ?_, a10⟩
    · dsimp only
      split
      · exact fitNum_bal _
      · exact a8
    · dsimp only
      split
      · exact a9
      · exact fitNum_bal _
  unfold Model.post
  try dsimp only
  split
  · refine ⟨hacct _ ha', ?_, hs.fill⟩
    intro c hc
    rcases mem_insertCat hc with rfl | hc
    · exact ⟨by cobol_auto, hamt, hs.fill⟩
    · exact hs.cats c hc
  · rename_i k hk
    have hk' : k < s.cats.length := by simpa using findKey_lt hk
    obtain ⟨c1, c2, c3⟩ := hs.cats _ (getD_mem hk')
    refine ⟨hacct _ ha', ?_, c3⟩
    intro c hc
    rcases List.mem_or_eq_of_mem_set hc with hc | rfl
    · exact hs.cats c hc
    · exact ⟨c1, fitNum_catBal _, c3⟩

theorem model_valid (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8)
    (hxv : ∀ x ∈ xrefs, x.valid) :
    ∀ (ts : List Tran) (s0 : Model), s0.valid → (∀ t ∈ ts, t.valid) →
      (model xrefs clk tfill s0 ts).valid
  | [], _, h, _ => h
  | t :: ts, s0, h, ht => by
    simp only [model, List.foldl_cons]
    exact model_valid xrefs clk tfill hxv ts _
      (step_valid xrefs clk tfill s0 t h (ht t (by simp)) hxv) (fun t' h' => ht t' (by simp [h']))

/-- Every transaction is posted or rejected. -/
theorem step_counts (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8) (s : Model)
    (t : Tran) :
    (step xrefs clk tfill s t).posted + (step xrefs clk tfill s t).rejects = s.posted + s.rejects + 1 := by
  unfold step
  split
  · simp [Model.reject]; omega
  try dsimp only
  split
  · simp [Model.reject]; omega
  try dsimp only
  split
  · simp [Model.reject]; omega
  split
  · simp [Model.reject]; omega
  unfold Model.post
  try dsimp only
  split <;> simp <;> omega

theorem model_counts (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8) :
    ∀ (ts : List Tran) (s0 : Model), (model xrefs clk tfill s0 ts).posted +
      (model xrefs clk tfill s0 ts).rejects = s0.posted + s0.rejects + ts.length
  | [], _ => by simp [model]
  | t :: ts, s0 => by
    have := model_counts xrefs clk tfill ts (step xrefs clk tfill s0 t)
    simp only [model, List.foldl_cons] at this ⊢
    rw [this, step_counts]
    simp; omega

/-! ## The daily transaction record's fields

Symbolic execution keeps `t.bytes` folded (it is moved and written as a whole); a field read
from it is `(t.bytes.drop o).take n`, which these lemmas turn into the field. -/

theorem Tran.length_bytes (t : Tran) (h : t.valid) : t.bytes.length = 350 := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, h1, h2, h5, h6, h10, h11, h12, h13, h14, h15, h16]

theorem Tran.field_id (t : Tran) (h : t.valid) : t.bytes.take 16 = t.id := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h1, h2, h5, h6,
    h10, h11, h12, h13, h14, h15, h16]

theorem Tran.field_ty (t : Tran) (h : t.valid) : (t.bytes.drop 16).take 2 = t.ty := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h1, h2, h5, h6,
    h10, h11, h12, h13, h14, h15, h16]

theorem Tran.field_cat (t : Tran) (h : t.valid) : (t.bytes.drop 18).take 4 = encodeNum {} DALYTRAN_CAT_CD.fmt t.cat := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h1, h2, h5, h6,
    h10, h11, h12, h13, h14, h15, h16]

theorem Tran.field_src (t : Tran) (h : t.valid) : (t.bytes.drop 22).take 10 = t.src := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h1, h2, h5, h6,
    h10, h11, h12, h13, h14, h15, h16]

theorem Tran.field_desc (t : Tran) (h : t.valid) : (t.bytes.drop 32).take 100 = t.desc := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h1, h2, h5, h6,
    h10, h11, h12, h13, h14, h15, h16]

theorem Tran.field_amt (t : Tran) (h : t.valid) : (t.bytes.drop 132).take 11 = encodeNum {} DALYTRAN_AMT.fmt t.amt := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h1, h2, h5, h6,
    h10, h11, h12, h13, h14, h15, h16]

theorem Tran.field_merch (t : Tran) (h : t.valid) : (t.bytes.drop 143).take 9 = encodeNum {} DALYTRAN_MERCHANT_ID.fmt t.merch := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h1, h2, h5, h6,
    h10, h11, h12, h13, h14, h15, h16]

theorem Tran.field_mname (t : Tran) (h : t.valid) : (t.bytes.drop 152).take 50 = t.mname := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h1, h2, h5, h6,
    h10, h11, h12, h13, h14, h15, h16]

theorem Tran.field_mcity (t : Tran) (h : t.valid) : (t.bytes.drop 202).take 50 = t.mcity := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h1, h2, h5, h6,
    h10, h11, h12, h13, h14, h15, h16]

theorem Tran.field_mzip (t : Tran) (h : t.valid) : (t.bytes.drop 252).take 10 = t.mzip := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h1, h2, h5, h6,
    h10, h11, h12, h13, h14, h15, h16]

theorem Tran.field_card (t : Tran) (h : t.valid) : (t.bytes.drop 262).take 16 = t.card := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h1, h2, h5, h6,
    h10, h11, h12, h13, h14, h15, h16]

theorem Tran.field_orig (t : Tran) (h : t.valid) : (t.bytes.drop 278).take 26 = t.orig := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h1, h2, h5, h6,
    h10, h11, h12, h13, h14, h15, h16]

theorem Tran.field_proc (t : Tran) (h : t.valid) : (t.bytes.drop 304).take 26 = t.proc := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h1, h2, h5, h6,
    h10, h11, h12, h13, h14, h15, h16]

theorem Tran.field_fill (t : Tran) (h : t.valid) : (t.bytes.drop 330).take 20 = t.fill := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h1, h2, h5, h6,
    h10, h11, h12, h13, h14, h15, h16]

/-- `DALYTRAN-ORIG-TS (1:10)`, the date the expiration check compares. -/
theorem Tran.field_orig10 (t : Tran) (h : t.valid) : (t.bytes.drop 278).take 10 = t.orig.take 10 := by
  rw [← Tran.field_orig t h, List.take_take]
  simp

/-! ## Keyed files: lemmas -/

theorem keyOf_cat (c : TCat) (h : c.key.length = 17) :
    Sem.keyOf { off := 0, len := 17 } c.bytes = c.key := by
  simp [Sem.keyOf, TCat.bytes, List.take_append, h]

theorem insertCat_bytes (c : TCat) (hc : c.key.length = 17) :
    ∀ cats : List TCat, (∀ x ∈ cats, x.key.length = 17) →
      (insertCat c cats).map TCat.bytes =
        Sem.insertByKey { off := 0, len := 17 } c.bytes (cats.map TCat.bytes)
  | [], _ => by simp [insertCat, Sem.insertByKey]
  | x :: xs, h => by
    simp only [insertCat, List.map_cons, Sem.insertByKey, keyOf_cat c hc, keyOf_cat x (h x (by simp))]
    split
    · simp
    · simp [insertCat_bytes c hc xs (fun y hy => h y (by simp [hy]))]

theorem mem_insertByKey (k : KeyDecl) (r x : List UInt8) :
    ∀ (l : List (List UInt8)), x ∈ Sem.insertByKey k r l → x = r ∨ x ∈ l
  | [], h => by simpa [Sem.insertByKey] using h
  | y :: ys, h => by
    simp only [Sem.insertByKey] at h
    split at h
    · simpa using h
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr (by simp [h])
      · rcases mem_insertByKey k r x ys h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])

theorem findKey_eq_none {k : KeyDecl} {v : List UInt8} :
    ∀ {l : List (List UInt8)}, (∀ r ∈ l, Sem.keyOf k r ≠ v) → Sem.findKey k v l = none
  | [], _ => rfl
  | r :: rs, h => by
    simp only [Sem.findKey]
    have h1 := h r (by simp)
    simp [h1, findKey_eq_none (l := rs) (fun r' hr' => h r' (by simp [hr']))]

theorem findKey_key {k : KeyDecl} {v : List UInt8} :
    ∀ {l : List (List UInt8)} {i : Nat}, Sem.findKey k v l = some i → Sem.keyOf k (l.getD i []) = v
  | [], _, h => by simp [Sem.findKey] at h
  | r :: rs, i, h => by
    simp only [Sem.findKey] at h
    split at h
    · rename_i hr
      simp at h; subst h; simpa using hr
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa using findKey_key hj

theorem getD_map {α : Type} [Inhabited α] (f : α → List UInt8) (l : List α) {i : Nat}
    (h : i < l.length) : (l.map f).getD i [] = f (l.getD i default) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-! ## The loop invariant -/

/-- Loop invariant, indexed by the outcomes of the remaining `READ`s: after the transactions
`done`, the counters, the end-of-file flag, the clock, the files and the events are those of
the model, and the transaction file holds records of `done` only. -/
def Inv (m : Mem) (clk : Nat → List UInt8) (xrefs : List Xref) (trans : List Tran) (s0 : Model)
    (inp0 : List (Nat × List (List UInt8))) (rest : List (Option Tran)) (st : State) : Prop :=
  ∃ done todo, trans = done ++ todo ∧
    ((rest = [] ∧ todo = []) ∨ rest = todo.map some ++ [none]) ∧
    st.idx = [] ∧ st.slots = [] ∧ st.active = [] ∧ st.inp = inp0 ∧
    st.clockN = (model xrefs clk (m.read 2212 20) s0 done).posted ∧
    st.mem.size = 3252 ∧
    st.mem.read 2654 1 = (if rest.isEmpty then [232] else [213]) ∧
    st.mem.read 3220 9 = encodeNum {} WS_TRANSACTION_COUNT.fmt done.length ∧
    st.mem.read 3229 9 = encodeNum {} WS_REJECT_COUNT.fmt (model xrefs clk (m.read 2212 20) s0 done).rejects ∧
    st.mem.read 2618 22 = (model xrefs clk (m.read 2212 20) s0 done).catFill ∧
    st.mem.read 2212 20 = m.read 2212 20 ∧
    st.mem.read 3250 2 = encodeNum {} RETURN_CODE.fmt 0 ∧
    (∃ f1 f2 f3 f4 f5 f6 : FileSt,
      st.files = [(1, f1), (2, f2), (3, f3), (4, f4), (5, f5), (6, f6)] ∧
      f1.mode = some .input ∧ f1.recs = trans.map Tran.bytes ∧ f1.pos = done.length ∧
      f1.eof = rest.isEmpty ∧
      f2.mode = some .output ∧ (∀ r ∈ f2.recs, ∃ t ∈ done, r.take 16 = t.id) ∧
      f3.mode = some .input ∧ f3.recs = xrefs.map Xref.bytes ∧ f4.mode = some .output ∧
      f5.mode = some .io ∧ f5.recs = (model xrefs clk (m.read 2212 20) s0 done).accts.map Acct.bytes ∧
      f6.mode = some .io ∧ f6.recs = (model xrefs clk (m.read 2212 20) s0 done).cats.map TCat.bytes) ∧
    st.out = (model xrefs clk (m.read 2212 20) s0 done).out ++ [.display startMsg]

set_option maxHeartbeats 60000000 in
set_option maxRecDepth 20000 in
theorem cbtrn02c_posts (m : Mem) (hm : m.size = 3252) (clk : Nat → List UInt8)
    (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧
      0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post)
    (trans : List Tran) (htv : ∀ t ∈ trans, t.valid) (hids : (trans.map Tran.id).Nodup)
    (hlen : trans.length < 1000000000)
    (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid)
    (accts : List Acct) (hav : ∀ a ∈ accts, a.valid)
    (cats : List TCat) (hcv : ∀ c ∈ cats, c.valid) (n : Nat) (hn : trans.length < n) :
    let r := Cbtrn02c.run { clock := clk } (n + 60)
      (Cbtrn02c.initState m [(1, trans.map Tran.bytes), (3, xrefs.map Xref.bytes),
        (5, accts.map Acct.bytes), (6, cats.map TCat.bytes)])
    let s := model xrefs clk (m.read 2212 20) ⟨accts, cats, m.read 2618 22, 0, 0, []⟩ trans
    r.1 = .stop .goback ∧
      r.2.out = [.display endMsg, .display (rejMsg ++ encodeNum {} WS_REJECT_COUNT.fmt s.rejects),
        .display (procMsg ++ encodeNum {} WS_TRANSACTION_COUNT.fmt trans.length)] ++ s.out ++
        [.display startMsg] ∧
      r.2.mem.read 3250 2 = encodeNum {} RETURN_CODE.fmt (if 0 < s.rejects then 4 else 0) := by
  intro r s
  simp only [r]
  cobol_auto
  cobol_loop (Inv m clk xrefs trans ⟨accts, cats, m.read 2618 22, 0, 0, []⟩
      [(1, trans.map Tran.bytes), (3, xrefs.map Xref.bytes), (5, accts.map Acct.bytes),
        (6, cats.map TCat.bytes)]) (trans.map some ++ [none])
  · -- after the loop: six CLOSEs, the counts, RETURN-CODE, GOBACK
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := loopState
    obtain ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, -, hsz, heof, hcnt, hrej, -, -, hrc,
      ⟨f1, f2, f3, f4, f5, f6, rfl, h1m, -, -, -, h2m, -, h3m, -, h4m, h5m, -, h6m, -⟩, hout⟩ :=
      hloopInv
    rcases hrest with ⟨-, rfl⟩ | h
    · simp only [List.append_nil] at hd
      subst hd
      dsimp only at hsz heof hcnt hrej hrc hout
      simp only [List.isEmpty_nil, ↓reduceIte] at heof
      have hrb : (model xrefs clk (m.read 2212 20) ⟨accts, cats, m.read 2618 22, 0, 0, []⟩ trans).rejects <
          1000000000 := by
        have := model_counts xrefs clk (m.read 2212 20) trans ⟨accts, cats, m.read 2618 22, 0, 0, []⟩
        simp at this; omega
      cobol_auto
      simp only [s]
      refine ⟨⟨by simp [endMsg], by simp [rejMsg], by simp [procMsg], hout⟩, ?_⟩
      split <;> simp_all
    · simp at h
  · -- before the loop: nothing read, the counters and flags have their VALUEs
    cobol_inv [model] with [], trans
  · simp; omega
  · -- the loop ends exactly after the end-of-file READ
    rintro ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨-, -, -, -, -, -, -, -, -, -, heof, -⟩
    simp only [List.isEmpty_nil, ↓reduceIte] at heof
    cobol_auto
  · -- one iteration: READ the next transaction and post or reject it, or reach the end
    rintro y ys ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, hclk0, hsz, heof, hcnt, hrej, hcf, htf, hrc,
        ⟨f1, f2, f3, f4, f5, f6, rfl, h1m, h1r, h1p, h1e, h2m, h2r, h3m, h3r, h4m, h5m, h5r, h6m, h6r⟩,
        hout⟩
    dsimp only at hclk0 hsz heof hcnt hrej hcf htf hrc hout
    rcases hrest with ⟨h, -⟩ | hrest
    · simp at h
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at heof h1e
    refine ⟨by cobol_auto, ?_⟩
    have hsv := model_valid xrefs clk (m.read 2212 20) hxv done ⟨accts, cats, m.read 2618 22, 0, 0, []⟩
      ⟨hav, hcv, by simpa using Mem.length_read m 2618 22⟩ (fun t ht => htv t (by simp [hd, ht]))
    have hcount := model_counts xrefs clk (m.read 2212 20) done ⟨accts, cats, m.read 2618 22, 0, 0, []⟩
    generalize hS : model xrefs clk (m.read 2212 20) ⟨accts, cats, m.read 2618 22, 0, 0, []⟩ done = S
      at hclk0 hrej hcf h5r h6r hout hsv hcount
    simp only [Nat.zero_add] at hcount
    cases todo with
    | nil =>
      -- the end-of-file READ
      simp only [List.map_nil, List.nil_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      simp only [List.append_nil] at hd
      subst hd
      have hnone : f1.recs[f1.pos]? = none := by rw [h1r, h1p]; simp
      cobol_auto
      cobol_inv with trans, []
    | cons t todo' =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      subst hd
      have htv' := htv t (by simp)
      -- the record stays folded; its fields
      have tb := Tran.length_bytes t htv'
      have tf1 := Tran.field_id t htv'
      have tf2 := Tran.field_ty t htv'
      have tf3 := Tran.field_cat t htv'
      have tf4 := Tran.field_src t htv'
      have tf5 := Tran.field_desc t htv'
      have tf6 := Tran.field_amt t htv'
      have tf7 := Tran.field_merch t htv'
      have tf8 := Tran.field_mname t htv'
      have tf9 := Tran.field_mcity t htv'
      have tf10 := Tran.field_mzip t htv'
      have tf11 := Tran.field_card t htv'
      have tf12 := Tran.field_orig t htv'
      have tf13 := Tran.field_proc t htv'
      have tf14 := Tran.field_fill t htv'
      have tf15 := Tran.field_orig10 t htv'
      obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16⟩ := htv'
      have hsome : f1.recs[f1.pos]? = some t.bytes := by rw [h1r, h1p]; simp
      -- the counters stay below their capacity
      have hdl : done.length < 999999999 := by
        have := hlen; simp only [List.length_append, List.length_cons] at this; omega
      have hrb : S.rejects < 999999999 := by omega
      have hf2 : ∀ r ∈ f2.recs, ∃ t' ∈ done ++ [t], r.take 16 = t'.id := fun r hr => by
        obtain ⟨t', ht', h⟩ := h2r r hr
        exact ⟨t', by simp [ht'], h⟩
      rcases hx : Sem.findKey { off := 0, len := 16 } t.card (xrefs.map Xref.bytes) with _ | i
      · -- the card is not in the cross-reference file: rejected (100)
        cobol_auto
        cobol_inv [model_append, step, Model.reject, trailer, hout, badCardDesc] with done ++ [t], todo'
      · -- the card's cross-reference record
        have hi := findKey_lt hx
        simp only [List.length_map] at hi
        obtain ⟨x1, x2, x3, x4, x5⟩ := hxv _ (getD_mem hi)
        have hxg := getD_map Xref.bytes xrefs hi
        rcases ha : Sem.findKey { off := 0, len := 11 }
            (encodeNum {} FD_ACCT_ID.fmt (xrefs.getD i default).acct) (S.accts.map Acct.bytes) with _ | j
        · -- the account is not in the account file: rejected (101)
          cobol_auto [Xref.bytes]
          cobol_inv [model_append, step, Model.reject, trailer, hout, noAcctDesc] with done ++ [t], todo'
        · -- the account record
          have hj := findKey_lt ha
          simp only [List.length_map] at hj
          obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hsv.accts _ (getD_mem hj)
          have hag := getD_map Acct.bytes S.accts hj
          have haid : (S.accts.getD j default).id = encodeNum {} FD_ACCT_ID.fmt (xrefs.getD i default).acct := by
            have := findKey_key ha
            rw [hag] at this
            simp only [Sem.keyOf, List.drop_zero, Acct.bytes, List.append_assoc] at this
            rwa [List.take_left' a1] at this
          by_cases hexp : Sem.cmpBytes (S.accts.getD j default).exp (t.orig.take 10) = .lt
          · -- received after the expiration date: rejected (103)
            cobol_auto [Xref.bytes, Acct.bytes]
            cobol_inv [model_append, step, Model.reject, trailer, hout, expiredDesc] with done ++ [t], todo'
          by_cases hlim : (S.accts.getD j default).limit < (Sem.fitNum {} WS_TEMP_BAL.fmt
              ((S.accts.getD j default).cc - (S.accts.getD j default).cd + t.amt)).2
          · -- over the credit limit: rejected (102); the program compares with `compare`
            have hcmp : compare (S.accts.getD j default).limit (Sem.fitNum {} WS_TEMP_BAL.fmt
                ((S.accts.getD j default).cc - (S.accts.getD j default).cd + t.amt)).2 = .lt := by
              simp only [compare, compareOfLessAndEq, if_pos hlim]
            cobol_auto [Xref.bytes, Acct.bytes]
            cobol_inv [model_append, step, Model.reject, trailer, hout, overLimitDesc, hlim] with done ++ [t], todo'
          · -- valid: posted
            have hcmp : compare (S.accts.getD j default).limit (Sem.fitNum {} WS_TEMP_BAL.fmt
                ((S.accts.getD j default).cc - (S.accts.getD j default).cd + t.amt)).2 ≠ .lt := by
              simp only [compare, compareOfLessAndEq, if_neg hlim]
              split <;> simp
            -- the clock reading of this posting
            obtain ⟨pre, mil, post, hpre, hpost, hmil, hmil0, hck⟩ := hclk S.posted
            have hcfl : S.catFill.length = 22 := hsv.fill
            -- no transaction record with this id yet (the ids are distinct)
            have hnot : ∀ t' ∈ done, t'.id ≠ t.id := by
              intro t' ht' heq
              have := List.nodup_append.1 (by simpa using hids)
              exact this.2.2 t'.id (List.mem_map.2 ⟨t', ht', rfl⟩) t.id (by simp) heq
            have hf2n : Sem.findKey { off := 0, len := 16 } t.id f2.recs = none := by
              apply findKey_eq_none
              intro r hr hkey
              obtain ⟨t', ht', h⟩ := h2r r hr
              simp only [Sem.keyOf, List.drop_zero] at hkey
              exact hnot t' ht' (h.symm.trans hkey)
            rcases hk : Sem.findKey { off := 0, len := 17 }
                (encodeNum {} FD_TRANCAT_ACCT_ID.fmt (xrefs.getD i default).acct ++ t.ty ++ encodeNum {} FD_TRANCAT_CD.fmt t.cat)
                (S.cats.map TCat.bytes) with _ | k
            · -- a new category balance record
              have hins := insertCat_bytes
                ⟨encodeNum {} FD_TRANCAT_ACCT_ID.fmt (xrefs.getD i default).acct ++ t.ty ++ encodeNum {} FD_TRANCAT_CD.fmt t.cat,
                  t.amt, S.catFill⟩ (by cobol_auto) S.cats (fun x hx => (hsv.cats x hx).1)
              by_cases hpos : 0 ≤ t.amt
              · have hc0 : compare t.amt 0 ≠ .lt := by
                  simp only [compare, compareOfLessAndEq, if_neg (Int.not_lt.2 hpos)]
                  split <;> simp
                cobol_auto [hclk0, haid, Xref.bytes, Acct.bytes, TCat.bytes]
                cobol_inv [model_append, step, Model.post, tranRec, db2ts, hout, hlim, noCatMsg, creatingMsg, Acct.bytes, TCat.bytes, hins, hpos] with done ++ [t], todo'
                -- the transaction file: the new record has this transaction's id
                intro r hr
                rcases mem_insertByKey _ _ _ _ hr with rfl | hr
                · exact ⟨t, by simp, by simp [List.append_assoc, List.take_append, List.take_of_length_le, t1]⟩
                · obtain ⟨t', ht', h⟩ := h2r r hr
                  exact ⟨t', by simp [ht'], h⟩
              · have hc0 : compare t.amt 0 = .lt := by
                  simp only [compare, compareOfLessAndEq, if_pos (Int.not_le.1 hpos)]
                cobol_auto [hclk0, haid, Xref.bytes, Acct.bytes, TCat.bytes]
                cobol_inv [model_append, step, Model.post, tranRec, db2ts, hout, hlim, noCatMsg, creatingMsg, Acct.bytes, TCat.bytes, hins, hpos] with done ++ [t], todo'
                -- the transaction file: the new record has this transaction's id
                intro r hr
                rcases mem_insertByKey _ _ _ _ hr with rfl | hr
                · exact ⟨t, by simp, by simp [List.append_assoc, List.take_append, List.take_of_length_le, t1]⟩
                · obtain ⟨t', ht', h⟩ := h2r r hr
                  exact ⟨t', by simp [ht'], h⟩
            · -- an existing one: rewritten
              have hk' := findKey_lt hk
              simp only [List.length_map] at hk'
              obtain ⟨c1, c2, c3⟩ := hsv.cats _ (getD_mem hk')
              have hcg := getD_map TCat.bytes S.cats hk'
              have hckey : (S.cats.getD k default).key = encodeNum {} FD_TRANCAT_ACCT_ID.fmt
                  (xrefs.getD i default).acct ++ t.ty ++ encodeNum {} FD_TRANCAT_CD.fmt t.cat := by
                have := findKey_key hk
                rw [hcg] at this
                simp only [Sem.keyOf, List.drop_zero, TCat.bytes, List.append_assoc] at this
                rwa [List.take_left' c1] at this
              by_cases hpos : 0 ≤ t.amt
              · have hc0 : compare t.amt 0 ≠ .lt := by
                  simp only [compare, compareOfLessAndEq, if_neg (Int.not_lt.2 hpos)]
                  split <;> simp
                cobol_auto [hclk0, haid, hckey, Xref.bytes, Acct.bytes, TCat.bytes]
                cobol_inv [model_append, step, Model.post, tranRec, db2ts, hout, hlim, noCatMsg, creatingMsg, Acct.bytes, TCat.bytes, hpos] with done ++ [t], todo'
                -- the transaction file: the new record has this transaction's id
                intro r hr
                rcases mem_insertByKey _ _ _ _ hr with rfl | hr
                · exact ⟨t, by simp, by simp [List.append_assoc, List.take_append, List.take_of_length_le, t1]⟩
                · obtain ⟨t', ht', h⟩ := h2r r hr
                  exact ⟨t', by simp [ht'], h⟩
              · have hc0 : compare t.amt 0 = .lt := by
                  simp only [compare, compareOfLessAndEq, if_pos (Int.not_le.1 hpos)]
                cobol_auto [hclk0, haid, hckey, Xref.bytes, Acct.bytes, TCat.bytes]
                cobol_inv [model_append, step, Model.post, tranRec, db2ts, hout, hlim, noCatMsg, creatingMsg, Acct.bytes, TCat.bytes, hpos] with done ++ [t], todo'
                -- the transaction file: the new record has this transaction's id
                intro r hr
                rcases mem_insertByKey _ _ _ _ hr with rfl | hr
                · exact ⟨t, by simp, by simp [List.append_assoc, List.take_append, List.take_of_length_le, t1]⟩
                · obtain ⟨t', ht', h⟩ := h2r r hr
                  exact ⟨t', by simp [ht'], h⟩

end Cbtrn02c
end CardDemo

#print axioms CardDemo.Cbtrn02c.cbtrn02c_posts
