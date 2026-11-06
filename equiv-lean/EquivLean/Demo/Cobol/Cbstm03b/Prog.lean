-- Copied unchanged from coblean (frozen snapshot ~/coblean_snapshots/coblean-pin2306Z-cbstm03b-20261027T0112Z,
-- Examples/Cbstm03b.lean); only the IR path differs. coblean and JimpleLean both have a library
-- named `Examples`, so equiv-lean cannot import the original module next to JimpleLean.
/-
# CardDemo CBSTM03B (file access subroutine): the functional model

`examples/carddemo/cbstm03b.ir.json` is the front end's output (`--sub`) on `app/cbl/CBSTM03B.CBL`
of AWS CardDemo, unchanged. CBSTM03B is called with one 1040-byte parameter area
`LK-M03B-AREA`: a DD name (8 bytes), an operation (1 byte), a return code (2 bytes, set by the
call), a key (25 bytes), a key length (`S9(4)`) and a 1000-byte record buffer. It opens, reads or
closes one of four indexed files, chosen by the DD name, and returns the file status in the
return code. Its files and its storage persist between calls, so one call is a transition of
(storage, file states); this file states that transition as a function, in terms of the file
model's rules for `OPEN INPUT`, `CLOSE`, sequential `READ` and keyed `READ`.

Storage layout (2248 bytes): the four record areas (TRNX 0..350, XREF 350..400, CUST 400..900 with
`FD-CUST-ID` at 400, ACCT 900..1200 with `FD-ACCT-ID PIC 9(11)` at 900), the four file status
items (1200, 1202, 1204, 1206) and the parameter area (1208..2248: DD 1208, operation 1216,
return code 1217, key 1219, key length 1244, record buffer 1248).
-/
import Cobol
open Cobol

namespace CardDemo

cobol_program Cbstm03b from "../../../../examples/cobol/carddemo/cbstm03b.ir.json"

namespace Cbstm03b

/-! ## The parameter values (EBCDIC) -/

/-- `TRNXFILE`, `XREFFILE`, `CUSTFILE`, `ACCTFILE` in EBCDIC (`dd_eq`). -/
def ddTrnx : List UInt8 := [227, 217, 213, 231, 198, 201, 211, 197]
def ddXref : List UInt8 := [231, 217, 197, 198, 198, 201, 211, 197]
def ddCust : List UInt8 := [195, 228, 226, 227, 198, 201, 211, 197]
def ddAcct : List UInt8 := [193, 195, 195, 227, 198, 201, 211, 197]

theorem dd_eq : Codepage.encode037 "TRNXFILE" = some ddTrnx ∧ Codepage.encode037 "XREFFILE" = some ddXref ∧
    Codepage.encode037 "CUSTFILE" = some ddCust ∧ Codepage.encode037 "ACCTFILE" = some ddAcct := by
  decide +kernel

/-- The operations `O` (open), `R` (read next), `K` (read by key), `C` (close) in EBCDIC. -/
def opOpen : UInt8 := 214
def opRead : UInt8 := 217
def opReadK : UInt8 := 210
def opClose : UInt8 := 195

theorem op_eq : Codepage.encode037 "ORKC" = some [opOpen, opRead, opReadK, opClose] := by
  decide +kernel

/-- A file status code as the two EBCDIC digits the `FILE STATUS` item holds. -/
def stBytes (code : Nat) : List UInt8 :=
  [UInt8.ofNat (240 + code / 10 % 10), UInt8.ofNat (240 + code % 10)]

/-! ## The file operations (the file model's rules, `Cobol/Sem/File.lean`) -/

/-- `OPEN INPUT` of file `id`: status 41 if the file is open (it stays open), else the
environment's open error if it reports one (the file stays closed), else status 00 and the file
is open for input at its first record. -/
def openIn (env : Env) (id : Nat) (f : FileSt) : Nat × FileSt :=
  if f.mode.isSome then (41, { f with cur := none })
  else match env.openError id .input with
    | some code => (code, f)
    | none => (0, { f with mode := some .input, pos := 0, eof := false, cur := none })

/-- `CLOSE`: status 42 if the file is closed, else 00 and the file is closed. -/
def closeF (f : FileSt) : Nat × FileSt :=
  match f.mode with
  | none => (42, f)
  | some _ => (0, { f with mode := none, cur := none })

/-- The file is open for reading. -/
def canRd (f : FileSt) : Bool := f.mode == some .input || f.mode == some .io

/-- Sequential `READ`: status 47 if the file is not open for reading, 46 after the end of the
file, 10 at the end of the file, else 00 with the next record. -/
def seqRead (f : FileSt) : Nat × FileSt × Option (List UInt8) :=
  if !canRd f then (47, { f with cur := none }, none)
  else if f.eof then (46, { f with cur := none }, none)
  else match f.recs[f.pos]? with
    | none => (10, { f with eof := true, cur := none }, none)
    | some r => (0, { f with pos := f.pos + 1, cur := some f.pos }, some r)

/-- Keyed `READ` by the record key (the first `len` bytes of a record) with value `v`: status 47
if the file is not open for reading, 23 if no record has the key, else 00 with the first record
that has it. -/
def keyRead (len : Nat) (v : List UInt8) (f : FileSt) : Nat × FileSt × Option (List UInt8) :=
  if !canRd f then (47, { f with cur := none }, none)
  else match Sem.findKey { off := 0, len } v f.recs with
    | none => (23, { f with cur := none }, none)
    | some i => (0, { f with pos := i + 1, eof := false, cur := some i }, some (f.recs.getD i []))

/-! ## One call -/

/-- Space-padded record buffer (`READ … INTO LK-M03B-FLDT`, 1000 bytes). -/
def intoBuf (r : List UInt8) : List UInt8 := r ++ List.replicate (1000 - r.length) 64

/-- The status `code` stored in the file's status item (at `so`) and in the return code. -/
def retCode (m : Mem) (so code : Nat) : Mem := (m.write so (stBytes code)).write 1217 (stBytes code)

/-- One call for a sequentially read file (TRNX, XREF): record area at `ao`, status at `so`. -/
def seqCall (env : Env) (id ao so : Nat) (op : UInt8) (m : Mem) (f : FileSt) : Mem × FileSt :=
  if op = opOpen then let (c, f') := openIn env id f; (retCode m so c, f')
  else if op = opRead then
    match seqRead f with
    | (c, f', some r) => ((retCode (m.write ao r) so c).write 1248 (intoBuf r), f')
    | (c, f', none) => (retCode m so c, f')
  else if op = opClose then let (c, f') := closeF f; (retCode m so c, f')
  else (m.write 1217 (m.read so 2), f)

/-- One call for a keyed file (CUST, ACCT): the key `key` is first stored in the record key field
(at `ao`, `kl` bytes) by `set`, then the keyed read runs. -/
def keyCall (env : Env) (id ao so kl : Nat) (key : List UInt8) (op : UInt8) (m : Mem) (f : FileSt) :
    Mem × FileSt :=
  if op = opOpen then let (c, f') := openIn env id f; (retCode m so c, f')
  else if op = opReadK then
    let m1 := m.write ao key
    match keyRead kl key f with
    | (c, f', some r) => ((retCode (m1.write ao r) so c).write 1248 (intoBuf r), f')
    | (c, f', none) => (retCode m1 so c, f')
  else if op = opClose then let (c, f') := closeF f; (retCode m so c, f')
  else (m.write 1217 (m.read so 2), f)

/-- The four file states. -/
structure Files where
  trnx : FileSt
  xref : FileSt
  cust : FileSt
  acct : FileSt

/-- The callee state CBSTM03B starts a call in: its storage and its files. -/
def st0 (m : Mem) (fs : Files) : State :=
  { mem := m, files := [(1, fs.trnx), (2, fs.xref), (3, fs.cust), (4, fs.acct)] }

/-- **The model of one call.** `custKey` / `acctKey` are the bytes the `MOVE` of
`LK-M03B-KEY (1:LK-M03B-KEY-LN)` stores in `FD-CUST-ID` (9 bytes) / `FD-ACCT-ID` (11 digits);
they matter only for operation `K`. -/
def call3b (env : Env) (m : Mem) (fs : Files) (custKey acctKey : List UInt8) : Mem × Files :=
  let dd := m.read 1208 8
  let op := (m.read 1216 1).headD 0
  if dd = ddTrnx then let (m', f) := seqCall env 1 0 1200 op m fs.trnx; (m', { fs with trnx := f })
  else if dd = ddXref then let (m', f) := seqCall env 2 350 1202 op m fs.xref; (m', { fs with xref := f })
  else if dd = ddCust then
    let (m', f) := keyCall env 3 400 1204 9 custKey op m fs.cust; (m', { fs with cust := f })
  else if dd = ddAcct then
    let (m', f) := keyCall env 4 900 1206 11 acctKey op m fs.acct; (m', { fs with acct := f })
  else (m, fs)


/-! ## Two facts about keyed lookups -/


/-- A record found by key is in the file. -/
theorem findKey_lt {k : KeyDecl} {v : List UInt8} :
    ∀ {rs : List (List UInt8)} {i : Nat}, Sem.findKey k v rs = some i → i < rs.length
  | [], i, h => by simp [Sem.findKey] at h
  | r :: rs, i, h => by
    simp only [Sem.findKey] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp
    · cases h' : Sem.findKey k v rs with
      | none => simp [h'] at h
      | some j =>
        simp only [h', Option.map_some, Option.some.injEq] at h
        have := findKey_lt h'
        simp only [List.length_cons]
        omega

theorem getD_mem_of_lt {rs : List (List UInt8)} {i : Nat} (h : i < rs.length) : rs.getD i [] ∈ rs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-- The bytes `MOVE LK-M03B-KEY (1:k) TO FD-CUST-ID` stores (9 bytes, space-padded). -/
def custKeyOf (m : Mem) (k : Int) : List UInt8 := (m.read 1219 k.toNat ++ List.replicate (9 - k.toNat) 64).take 9


/-- The bytes `MOVE LK-M03B-KEY (1:k) TO FD-ACCT-ID` stores (`PIC 9(11)`): the key's digits as
a number `v`, stored with the `MOVE`'s high-order truncation to 11 digits. -/
def acctKeyOf (v : Int) : List UInt8 := encodeNum {} { digits := 11 } (Sem.fitNum {} { digits := 11 } v).2

/-! ## One call, by DD name -/


set_option maxHeartbeats 8000000 in
set_option maxRecDepth 40000 in
/-- One call with DD name `TRNXFILE`. -/
theorem call_trnx (env : Env) (m : Mem) (hm : m.size = 2248) (fs : Files) (o : UInt8)
    (h1 : ∀ r ∈ fs.trnx.recs, r.length = 350)
    (hdd : m.read 1208 8 = ddTrnx) (hop : m.read 1216 1 = [o]) (ck ak : List UInt8) :
    Cbstm03b.run env 50 (st0 m fs) =
      (.stop .goback, st0 (call3b env m fs ck ak).1 (call3b env m fs ck ak).2) := by
  obtain ⟨f1, f2, f3, f4⟩ := fs
  simp only [ddTrnx] at hdd
  simp only at h1
  by_cases hO : o = opOpen
  · subst hO
    rcases hmo : f1.mode with _ | md
    · rcases hoe : env.openError 1 .input with _ | code
      · cobol_sym [hm, hdd, hop, hmo, hoe, call3b, seqCall, openIn, retCode, stBytes, st0, ddTrnx, opOpen]
      · cobol_sym [hm, hdd, hop, hmo, hoe, call3b, seqCall, openIn, retCode, stBytes, st0, ddTrnx, opOpen]
    · cobol_sym [hm, hdd, hop, hmo, call3b, seqCall, openIn, retCode, stBytes, st0, ddTrnx, opOpen]
  by_cases hR : o = opRead
  · subst hR
    rcases hc : (f1.mode == some OpenMode.input || f1.mode == some OpenMode.io) with _ | _
    · cobol_sym [hm, hdd, hop, hc, call3b, seqCall, seqRead, canRd, retCode, stBytes, st0, ddTrnx,
        opOpen, opRead]
    · rcases he : f1.eof with _ | _
      · rcases hg : f1.recs[f1.pos]? with _ | r
        · cobol_sym [hm, hdd, hop, hc, he, hg, call3b, seqCall, seqRead, canRd, retCode, stBytes, st0,
            ddTrnx, opOpen, opRead]
        · have hr : r.length = 350 := h1 r (List.mem_of_getElem? hg)
          cobol_sym [hm, hdd, hop, hc, he, hg, hr, call3b, seqCall, seqRead, canRd, retCode, stBytes,
            intoBuf, st0, ddTrnx, opOpen, opRead]
      · cobol_sym [hm, hdd, hop, hc, he, call3b, seqCall, seqRead, canRd, retCode, stBytes, st0, ddTrnx,
          opOpen, opRead]
  by_cases hC : o = opClose
  · subst hC
    rcases hmo : f1.mode with _ | md
    · cobol_sym [hm, hdd, hop, hmo, call3b, seqCall, closeF, retCode, stBytes, st0, ddTrnx, opOpen,
        opRead, opClose]
    · cobol_sym [hm, hdd, hop, hmo, call3b, seqCall, closeF, retCode, stBytes, st0, ddTrnx, opOpen,
        opRead, opClose]
  simp only [opOpen, opRead, opClose] at hO hR hC
  cobol_sym [hm, hdd, hop, hO, hR, hC, call3b, seqCall, st0, ddTrnx, opOpen, opRead, opClose, List.headD_cons]



set_option maxHeartbeats 8000000 in
set_option maxRecDepth 40000 in
/-- One call with DD name `XREFFILE`. -/
theorem call_xref (env : Env) (m : Mem) (hm : m.size = 2248) (fs : Files) (o : UInt8)
    (h1 : ∀ r ∈ fs.xref.recs, r.length = 50)
    (hdd : m.read 1208 8 = ddXref) (hop : m.read 1216 1 = [o]) (ck ak : List UInt8) :
    Cbstm03b.run env 50 (st0 m fs) =
      (.stop .goback, st0 (call3b env m fs ck ak).1 (call3b env m fs ck ak).2) := by
  obtain ⟨f1, f2, f3, f4⟩ := fs
  simp only [ddXref] at hdd
  simp only at h1
  by_cases hO : o = opOpen
  · subst hO
    rcases hmo : f2.mode with _ | md
    · rcases hoe : env.openError 2 .input with _ | code
      · cobol_sym [hm, hdd, hop, hmo, hoe, call3b, seqCall, openIn, retCode, stBytes, st0, ddTrnx, ddXref, opOpen]
      · cobol_sym [hm, hdd, hop, hmo, hoe, call3b, seqCall, openIn, retCode, stBytes, st0, ddTrnx, ddXref, opOpen]
    · cobol_sym [hm, hdd, hop, hmo, call3b, seqCall, openIn, retCode, stBytes, st0, ddTrnx, ddXref, opOpen]
  by_cases hR : o = opRead
  · subst hR
    rcases hc : (f2.mode == some OpenMode.input || f2.mode == some OpenMode.io) with _ | _
    · cobol_sym [hm, hdd, hop, hc, call3b, seqCall, seqRead, canRd, retCode, stBytes, st0, ddTrnx, ddXref,
        opOpen, opRead]
    · rcases he : f2.eof with _ | _
      · rcases hg : f2.recs[f2.pos]? with _ | r
        · cobol_sym [hm, hdd, hop, hc, he, hg, call3b, seqCall, seqRead, canRd, retCode, stBytes, st0,
            ddTrnx, ddXref, opOpen, opRead]
        · have hr : r.length = 50 := h1 r (List.mem_of_getElem? hg)
          cobol_sym [hm, hdd, hop, hc, he, hg, hr, call3b, seqCall, seqRead, canRd, retCode, stBytes,
            intoBuf, st0, ddTrnx, ddXref, opOpen, opRead]
      · cobol_sym [hm, hdd, hop, hc, he, call3b, seqCall, seqRead, canRd, retCode, stBytes, st0, ddTrnx, ddXref,
          opOpen, opRead]
  by_cases hC : o = opClose
  · subst hC
    rcases hmo : f2.mode with _ | md
    · cobol_sym [hm, hdd, hop, hmo, call3b, seqCall, closeF, retCode, stBytes, st0, ddTrnx, ddXref, opOpen,
        opRead, opClose]
    · cobol_sym [hm, hdd, hop, hmo, call3b, seqCall, closeF, retCode, stBytes, st0, ddTrnx, ddXref, opOpen,
        opRead, opClose]
  simp only [opOpen, opRead, opClose] at hO hR hC
  cobol_sym [hm, hdd, hop, hO, hR, hC, call3b, seqCall, st0, ddTrnx, ddXref, opOpen, opRead, opClose, List.headD_cons]


set_option maxHeartbeats 40000000 in
set_option maxRecDepth 40000 in
/-- One call with DD name `CUSTFILE`. For operation `K`, the key length `LK-M03B-KEY-LN` is a
valid `S9(4)` value `k` with `1 ≤ k ≤ 25` (else the reference modification is out of range). -/
theorem call_cust (env : Env) (m : Mem) (hm : m.size = 2248) (fs : Files) (o : UInt8) (k : Int)
    (h3 : ∀ r ∈ fs.cust.recs, r.length = 500)
    (hdd : m.read 1208 8 = ddCust) (hop : m.read 1216 1 = [o])
    (hK : o = opReadK → decodeNum {} LK_M03B_KEY_LN.fmt (m.read 1244 4) = some k ∧ 1 ≤ k ∧ k ≤ 25)
    (ak : List UInt8) :
    Cbstm03b.run env 50 (st0 m fs) =
      (.stop .goback, st0 (call3b env m fs (custKeyOf m k) ak).1 (call3b env m fs (custKeyOf m k) ak).2) := by
  obtain ⟨f1, f2, f3, f4⟩ := fs
  simp only [ddCust] at hdd
  simp only at h3
  by_cases hO : o = opOpen
  · subst hO
    rcases hmo : f3.mode with _ | md
    · rcases hoe : env.openError 3 .input with _ | code
      · cobol_sym [hm, hdd, hop, hmo, hoe, call3b, keyCall, openIn, retCode, stBytes, st0, ddTrnx, ddXref,
          ddCust, opOpen]
      · cobol_sym [hm, hdd, hop, hmo, hoe, call3b, keyCall, openIn, retCode, stBytes, st0, ddTrnx, ddXref,
          ddCust, opOpen]
    · cobol_sym [hm, hdd, hop, hmo, call3b, keyCall, openIn, retCode, stBytes, st0, ddTrnx, ddXref, ddCust,
        opOpen]
  by_cases hRK : o = opReadK
  · obtain ⟨hkl, hk1, hk2⟩ := hK hRK
    subst hRK
    generalize hkey : custKeyOf m k = key
    have hkeyl : key.length = 9 := by
      rw [← hkey]; simp only [custKeyOf, List.length_take, List.length_append, Mem.length_read,
        List.length_replicate]; omega
    rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
        k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨
        k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · cobol_sym [custKeyOf] at hkey
      rcases hc : (f3.mode == some OpenMode.input || f3.mode == some OpenMode.io) with _ | _
      · cobol_sym [hm, hdd, hop, hkl, hkey, hkeyl, hc, call3b, keyCall, keyRead, canRd, retCode, stBytes,
          st0, ddTrnx, ddXref, ddCust, opOpen, opReadK]
      · rcases hf : Sem.findKey { off := 0, len := 9 } key f3.recs with _ | i
        · cobol_sym [hm, hdd, hop, hkl, hkey, hkeyl, hc, hf, call3b, keyCall, keyRead, canRd, retCode,
            stBytes, st0, ddTrnx, ddXref, ddCust, opOpen, opReadK]
        · have hr : (f3.recs.getD i []).length = 500 := by
            have hi : i < f3.recs.length := by
              have := findKey_lt hf
              exact this
            exact h3 _ (getD_mem_of_lt hi)
          cobol_sym [hm, hdd, hop, hkl, hkey, hkeyl, hc, hf, hr, call3b, keyCall, keyRead, canRd, retCode,
            stBytes, intoBuf, st0, ddTrnx, ddXref, ddCust, opOpen, opReadK]
  by_cases hC : o = opClose
  · subst hC
    rcases hmo : f3.mode with _ | md
    · cobol_sym [hm, hdd, hop, hmo, call3b, keyCall, closeF, retCode, stBytes, st0, ddTrnx, ddXref, ddCust,
        opOpen, opReadK, opClose]
    · cobol_sym [hm, hdd, hop, hmo, call3b, keyCall, closeF, retCode, stBytes, st0, ddTrnx, ddXref, ddCust,
        opOpen, opReadK, opClose]
  simp only [opOpen, opReadK, opClose] at hO hRK hC
  cobol_sym [hm, hdd, hop, hO, hRK, hC, call3b, keyCall, st0, ddTrnx, ddXref, ddCust, opOpen, opReadK,
    opClose, List.headD_cons]


set_option maxHeartbeats 40000000 in
set_option maxRecDepth 40000 in
/-- One call with DD name `ACCTFILE`. For operation `K`, the key length `LK-M03B-KEY-LN` is a
valid `S9(4)` value `k` with `1 ≤ k ≤ 25`, and the key's first `k` bytes are the digits of `v`
(the `MOVE` to the numeric `FD-ACCT-ID` reads them as a number). -/
theorem call_acct (env : Env) (m : Mem) (hm : m.size = 2248) (fs : Files) (o : UInt8) (k v : Int)
    (h4 : ∀ r ∈ fs.acct.recs, r.length = 300)
    (hdd : m.read 1208 8 = ddAcct) (hop : m.read 1216 1 = [o])
    (hK : o = opReadK → decodeNum {} LK_M03B_KEY_LN.fmt (m.read 1244 4) = some k ∧ 1 ≤ k ∧ k ≤ 25 ∧
      decodeNum {} { digits := k.toNat } (m.read 1219 k.toNat) = some v)
    (ck : List UInt8) :
    Cbstm03b.run env 50 (st0 m fs) =
      (.stop .goback, st0 (call3b env m fs ck (acctKeyOf v)).1 (call3b env m fs ck (acctKeyOf v)).2) := by
  obtain ⟨f1, f2, f3, f4⟩ := fs
  simp only [ddAcct] at hdd
  simp only at h4
  by_cases hO : o = opOpen
  · subst hO
    rcases hmo : f4.mode with _ | md
    · rcases hoe : env.openError 4 .input with _ | code
      · cobol_sym [hm, hdd, hop, hmo, hoe, call3b, keyCall, openIn, retCode, stBytes, st0, ddTrnx, ddXref,
          ddCust, ddAcct, opOpen]
      · cobol_sym [hm, hdd, hop, hmo, hoe, call3b, keyCall, openIn, retCode, stBytes, st0, ddTrnx, ddXref,
          ddCust, ddAcct, opOpen]
    · cobol_sym [hm, hdd, hop, hmo, call3b, keyCall, openIn, retCode, stBytes, st0, ddTrnx, ddXref, ddCust,
        ddAcct, opOpen]
  by_cases hRK : o = opReadK
  · obtain ⟨hkl, hk1, hk2, hdec⟩ := hK hRK
    subst hRK
    generalize hkey : acctKeyOf v = key
    have hkeyl : key.length = 11 := by
      rw [← hkey, acctKeyOf, length_encodeNum _ _ _ (by decide)]; decide
    rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
        k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨
        k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [Int.reduceToNat] at hdec
      simp only [acctKeyOf] at hkey
      rcases hc : (f4.mode == some OpenMode.input || f4.mode == some OpenMode.io) with _ | _
      · cobol_sym [hm, hdd, hop, hkl, hdec, hkey, hkeyl, hc, call3b, keyCall, keyRead, canRd, retCode,
          stBytes, st0, ddTrnx, ddXref, ddCust, ddAcct, opOpen, opReadK]
      · rcases hf : Sem.findKey { off := 0, len := 11 } key f4.recs with _ | i
        · cobol_sym [hm, hdd, hop, hkl, hdec, hkey, hkeyl, hc, hf, call3b, keyCall, keyRead, canRd, retCode,
            stBytes, st0, ddTrnx, ddXref, ddCust, ddAcct, opOpen, opReadK]
        · have hr : (f4.recs.getD i []).length = 300 := h4 _ (getD_mem_of_lt (findKey_lt hf))
          cobol_sym [hm, hdd, hop, hkl, hdec, hkey, hkeyl, hc, hf, hr, call3b, keyCall, keyRead, canRd,
            retCode, stBytes, intoBuf, st0, ddTrnx, ddXref, ddCust, ddAcct, opOpen, opReadK]
  by_cases hC : o = opClose
  · subst hC
    rcases hmo : f4.mode with _ | md
    · cobol_sym [hm, hdd, hop, hmo, call3b, keyCall, closeF, retCode, stBytes, st0, ddTrnx, ddXref, ddCust,
        ddAcct, opOpen, opReadK, opClose]
    · cobol_sym [hm, hdd, hop, hmo, call3b, keyCall, closeF, retCode, stBytes, st0, ddTrnx, ddXref, ddCust,
        ddAcct, opOpen, opReadK, opClose]
  simp only [opOpen, opReadK, opClose] at hO hRK hC
  cobol_sym [hm, hdd, hop, hO, hRK, hC, call3b, keyCall, st0, ddTrnx, ddXref, ddCust, ddAcct, opOpen, opReadK,
    opClose, List.headD_cons]



set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
/-- One call with any other DD name: nothing happens (`WHEN OTHER GO TO 9999-GOBACK`). -/
theorem call_other (env : Env) (m : Mem) (hm : m.size = 2248) (fs : Files)
    (h1 : m.read 1208 8 ≠ ddTrnx) (h2 : m.read 1208 8 ≠ ddXref) (h3 : m.read 1208 8 ≠ ddCust)
    (h4 : m.read 1208 8 ≠ ddAcct) (ck ak : List UInt8) :
    Cbstm03b.run env 50 (st0 m fs) =
      (.stop .goback, st0 (call3b env m fs ck ak).1 (call3b env m fs ck ak).2) := by
  obtain ⟨f1, f2, f3, f4⟩ := fs
  generalize hd : m.read 1208 8 = d at h1 h2 h3 h4
  have hdl : d.length = 8 := by rw [← hd]; exact Mem.length_read m 1208 8
  simp only [ddTrnx, ddXref, ddCust, ddAcct] at h1 h2 h3 h4
  cobol_sym [hm, hd, hdl, h1, h2, h3, h4, call3b, st0, ddTrnx, ddXref, ddCust, ddAcct]

/-- **CBSTM03B, one call, on every input.** For every storage (any parameter area, any file
status items and record areas, as left by earlier calls) and every state of the four files
(open or closed, any position, any records of the declared lengths), one call of CBSTM03B ends
with `GOBACK`, and its storage and file states are those of the model `call3b`. The model
dispatches on the DD name and the operation: `O` opens the file for input, `R` reads the next
record of TRNXFILE or XREFFILE, `K` reads CUSTFILE or ACCTFILE by key, `C` closes the file; each
stores the file status in the file's status item and in the return code `LK-M03B-RC`, and a
successful read copies the record, space-padded, into `LK-M03B-FLDT`. Any other operation only
copies the file's last status into the return code; any other DD name changes nothing.
The only assumptions, besides the record lengths, concern operation `K`: the key length is a
valid value `k` in `1 ..= 25` (else the reference modification `LK-M03B-KEY (1:k)` is out of
range), and for ACCTFILE the key's first `k` bytes are digits, with value `v`. -/
theorem cbstm03b_call (env : Env) (m : Mem) (hm : m.size = 2248) (fs : Files) (k v : Int)
    (h1 : ∀ r ∈ fs.trnx.recs, r.length = 350) (h2 : ∀ r ∈ fs.xref.recs, r.length = 50)
    (h3 : ∀ r ∈ fs.cust.recs, r.length = 500) (h4 : ∀ r ∈ fs.acct.recs, r.length = 300)
    (hK : m.read 1216 1 = [opReadK] → (m.read 1208 8 = ddCust ∨ m.read 1208 8 = ddAcct) →
      decodeNum {} LK_M03B_KEY_LN.fmt (m.read 1244 4) = some k ∧ 1 ≤ k ∧ k ≤ 25)
    (hA : m.read 1216 1 = [opReadK] → m.read 1208 8 = ddAcct →
      decodeNum {} { digits := k.toNat } (m.read 1219 k.toNat) = some v) :
    Cbstm03b.run env 50 (st0 m fs) =
      (.stop .goback, st0 (call3b env m fs (custKeyOf m k) (acctKeyOf v)).1
        (call3b env m fs (custKeyOf m k) (acctKeyOf v)).2) := by
  obtain ⟨o, hop⟩ : ∃ o, m.read 1216 1 = [o] := by
    have hl := Mem.length_read m 1216 1
    revert hl
    cases m.read 1216 1 with
    | nil => simp
    | cons a t => cases t with
      | nil => intro; exact ⟨a, rfl⟩
      | cons b t' => simp
  by_cases hT : m.read 1208 8 = ddTrnx
  · exact call_trnx env m hm fs o h1 hT hop _ _
  by_cases hX : m.read 1208 8 = ddXref
  · exact call_xref env m hm fs o h2 hX hop _ _
  by_cases hC : m.read 1208 8 = ddCust
  · exact call_cust env m hm fs o k h3 hC hop (fun ho => hK (ho ▸ hop) (Or.inl hC)) _
  by_cases hA' : m.read 1208 8 = ddAcct
  · exact call_acct env m hm fs o k v h4 hA' hop
      (fun ho => ⟨(hK (ho ▸ hop) (Or.inr hA')).1, (hK (ho ▸ hop) (Or.inr hA')).2.1,
        (hK (ho ▸ hop) (Or.inr hA')).2.2, hA (ho ▸ hop) hA'⟩) _
  exact call_other env m hm fs hT hX hC hA' _ _

#print axioms cbstm03b_call

end Cbstm03b
end CardDemo
