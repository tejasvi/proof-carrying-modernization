-- Copied unchanged from coblean (frozen snapshot ~/coblean_snapshots/coblean-20261024T2306Z,
-- Examples/Cbtrn02cDup.lean); only the import differs. coblean and JimpleLean both have a library
-- named `Examples`, so equiv-lean cannot import the original module next to JimpleLean.
/-
# CardDemo CBTRN02C (daily transaction posting) with any transaction ids

`cbtrn02c_posts` assumes distinct transaction ids. Without that assumption, a posted
transaction whose id is already in the transaction file makes its `WRITE` fail with status 22.
The file is indexed with `ACCESS MODE IS RANDOM` and opened `OUTPUT`, so it holds exactly the
transactions this run has posted; rejected transactions are never written to it.
`2900-WRITE-TRANSACTION-FILE` then displays the error and the status, and `9999-ABEND-PROGRAM`
abends with code 999. By then `2700-UPDATE-TCATBAL` and `2800-UPDATE-ACCOUNT-REC` have already
written the category balance and the account. `cbtrn02c_any` covers every input; `modelX` is
the posting model `model` with that stop.
-/
import EquivLean.Demo.Cobol.Cbtrn02c.Prog
import Cobol.Logic.LoopExit

open Cobol

namespace CardDemo
namespace Cbtrn02c

/-- `ERROR WRITING TO TRANSACTION FILE` in EBCDIC (`errWriteMsg_eq`). -/
def errWriteMsg : List UInt8 := [197, 217, 217, 214, 217, 64, 230, 217, 201, 227, 201, 213, 199, 64,
  227, 214, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 198, 201, 211, 197]

/-- `FILE STATUS IS: NNNN0022`, the line `9910-DISPLAY-IO-STATUS` displays for status 22. -/
def status22Msg : List UInt8 := [198, 201, 211, 197, 64, 226, 227, 193, 227, 228, 226, 64, 201, 226,
  122, 64, 213, 213, 213, 213, 240, 240, 242, 242]

/-- `ABENDING PROGRAM`. -/
def abendMsg : List UInt8 := [193, 194, 197, 213, 196, 201, 213, 199, 64, 215, 217, 214, 199, 217,
  193, 212]

theorem errWriteMsg_eq : Codepage.encode037 "ERROR WRITING TO TRANSACTION FILE" = some errWriteMsg := by
  decide +kernel
theorem status22Msg_eq : Codepage.encode037 "FILE STATUS IS: NNNN0022" = some status22Msg := by
  decide +kernel
theorem abendMsg_eq : Codepage.encode037 "ABENDING PROGRAM" = some abendMsg := by decide +kernel

/-! ## The model with the duplicate-key stop -/

/-- The posting model `m`, the ids of the transactions written to the transaction file (newest
first), and whether a `WRITE` met a duplicate key: then the program has abended, and `m.out`
ends with the abend's events. -/
structure MX where
  m : Model
  ids : List (List UInt8)
  stop : Bool

/-- The events of the failed `WRITE` (newest first): the error line, the status line, the abend
message. -/
def dupEvents : List Event := [.display abendMsg, .display status22Msg, .display errWriteMsg]

/-- One daily transaction. `step` has posted it when its `posted` count went up. A posted
transaction whose id has already been written stops the run: its events are the posting's
without the transaction record, then `dupEvents`. -/
def stepX (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8) (s : MX) (t : Tran) :
    MX :=
  if s.stop then s
  else
    let s' := step xrefs clk tfill s.m t
    if s'.posted = s.m.posted + 1 then
      if t.id ∈ s.ids then ⟨{ s' with out := dupEvents ++ s'.out.tail }, s.ids, true⟩
      else ⟨s', t.id :: s.ids, false⟩
    else ⟨s', s.ids, false⟩

/-- The model after the transactions `ts`. -/
def modelX (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8) (s0 : Model)
    (ts : List Tran) : MX :=
  ts.foldl (stepX xrefs clk tfill) ⟨s0, [], false⟩

theorem modelX_append (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8)
    (s0 : Model) (ts : List Tran) (t : Tran) :
    modelX xrefs clk tfill s0 (ts ++ [t]) = stepX xrefs clk tfill (modelX xrefs clk tfill s0 ts) t := by
  simp [modelX, List.foldl_append]

theorem foldl_stepX_stop (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8) :
    ∀ (ts : List Tran) (s : MX), s.stop = true → ts.foldl (stepX xrefs clk tfill) s = s
  | [], _, _ => rfl
  | t :: ts, s, h => by
    rw [List.foldl_cons]
    have : stepX xrefs clk tfill s t = s := by simp [stepX, h]
    rw [this]; exact foldl_stepX_stop xrefs clk tfill ts s h

/-- Once stopped, later transactions change nothing. -/
theorem modelX_stop_append (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8)
    (s0 : Model) (ts us : List Tran) (h : (modelX xrefs clk tfill s0 ts).stop = true) :
    modelX xrefs clk tfill s0 (ts ++ us) = modelX xrefs clk tfill s0 ts := by
  simp only [modelX, List.foldl_append]
  exact foldl_stepX_stop xrefs clk tfill us _ h

theorem stepX_not_stop (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8) (s : MX)
    (t : Tran) (h : (stepX xrefs clk tfill s t).stop = false) :
    s.stop = false ∧ (stepX xrefs clk tfill s t).m = step xrefs clk tfill s.m t := by
  unfold stepX at h ⊢
  by_cases hs : s.stop = true
  · simp [hs] at h
  · have hs' : s.stop = false := by simpa using hs
    refine ⟨hs', ?_⟩
    by_cases hp : (step xrefs clk tfill s.m t).posted = s.m.posted + 1
    · by_cases hd : t.id ∈ s.ids
      · simp [hs', hp, hd] at h
      · simp [hs', hp, hd]
    · simp [hs', hp]

theorem foldl_stepX_not_stop (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8) :
    ∀ (ts : List Tran) (s : MX), (ts.foldl (stepX xrefs clk tfill) s).stop = false →
      s.stop = false ∧ (ts.foldl (stepX xrefs clk tfill) s).m = ts.foldl (step xrefs clk tfill) s.m
  | [], s, h => ⟨h, rfl⟩
  | t :: ts, s, h => by
    rw [List.foldl_cons] at h ⊢
    obtain ⟨h1, h2⟩ := foldl_stepX_not_stop xrefs clk tfill ts _ h
    obtain ⟨h3, h4⟩ := stepX_not_stop xrefs clk tfill s t h1
    rw [List.foldl_cons, h2, h4]
    exact ⟨h3, rfl⟩

/-- Without a stop, `modelX` is the posting model. -/
theorem modelX_m (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8) (s0 : Model)
    (ts : List Tran) (h : (modelX xrefs clk tfill s0 ts).stop = false) :
    (modelX xrefs clk tfill s0 ts).m = model xrefs clk tfill s0 ts :=
  (foldl_stepX_not_stop xrefs clk tfill ts _ h).2

/-- The stop: a posted transaction whose id has been written. -/
theorem modelX_dup (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8) (s0 : Model)
    (done rest : List Tran) (t : Tran) (hs : (modelX xrefs clk tfill s0 done).stop = false)
    (hp : (step xrefs clk tfill (model xrefs clk tfill s0 done) t).posted =
      (model xrefs clk tfill s0 done).posted + 1)
    (hd : t.id ∈ (modelX xrefs clk tfill s0 done).ids) :
    modelX xrefs clk tfill s0 (done ++ t :: rest) =
      ⟨{ step xrefs clk tfill (model xrefs clk tfill s0 done) t with
          out := dupEvents ++ (step xrefs clk tfill (model xrefs clk tfill s0 done) t).out.tail },
        (modelX xrefs clk tfill s0 done).ids, true⟩ := by
  have hm := modelX_m xrefs clk tfill s0 done hs
  have e : modelX xrefs clk tfill s0 (done ++ [t]) = ⟨{ step xrefs clk tfill (model xrefs clk tfill s0 done) t with
          out := dupEvents ++ (step xrefs clk tfill (model xrefs clk tfill s0 done) t).out.tail },
        (modelX xrefs clk tfill s0 done).ids, true⟩ := by
    rw [modelX_append]
    unfold stepX
    simp only [hs, Bool.false_eq_true, ↓reduceIte, hm, hp, hd]
  rw [show done ++ t :: rest = (done ++ [t]) ++ rest by simp, modelX_stop_append _ _ _ _ _ _ (by rw [e]),
    e]

/-- A transaction that is not posted (rejected) changes neither the written ids nor the stop. -/
theorem modelX_snoc_reject (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8)
    (s0 : Model) (done : List Tran) (t : Tran) (hs : (modelX xrefs clk tfill s0 done).stop = false)
    (hp : (step xrefs clk tfill (model xrefs clk tfill s0 done) t).posted ≠
      (model xrefs clk tfill s0 done).posted + 1) :
    modelX xrefs clk tfill s0 (done ++ [t]) =
      ⟨step xrefs clk tfill (model xrefs clk tfill s0 done) t, (modelX xrefs clk tfill s0 done).ids,
        false⟩ := by
  have hm := modelX_m xrefs clk tfill s0 done hs
  rw [modelX_append]
  unfold stepX
  simp only [hs, Bool.false_eq_true, ↓reduceIte, hm, hp]

/-- A posted transaction with a new id is written: its id joins the written ids. -/
theorem modelX_snoc_post (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8)
    (s0 : Model) (done : List Tran) (t : Tran) (hs : (modelX xrefs clk tfill s0 done).stop = false)
    (hp : (step xrefs clk tfill (model xrefs clk tfill s0 done) t).posted =
      (model xrefs clk tfill s0 done).posted + 1)
    (hd : t.id ∉ (modelX xrefs clk tfill s0 done).ids) :
    modelX xrefs clk tfill s0 (done ++ [t]) =
      ⟨step xrefs clk tfill (model xrefs clk tfill s0 done) t,
        t.id :: (modelX xrefs clk tfill s0 done).ids, false⟩ := by
  have hm := modelX_m xrefs clk tfill s0 done hs
  rw [modelX_append]
  unfold stepX
  simp only [hs, Bool.false_eq_true, ↓reduceIte, hm, hp, hd]

/-! ## Keyed files: membership -/

theorem findKey_some_of_mem {k : KeyDecl} {v : List UInt8} :
    ∀ {l : List (List UInt8)} {r : List UInt8}, r ∈ l → Sem.keyOf k r = v →
      ∃ i, Sem.findKey k v l = some i
  | [], _, h, _ => by simp at h
  | x :: xs, r, h, hk => by
    simp only [Sem.findKey]
    split
    · exact ⟨0, rfl⟩
    · rename_i hx
      rcases List.mem_cons.1 h with rfl | h
      · simp [hk] at hx
      · obtain ⟨i, hi⟩ := findKey_some_of_mem h hk
        exact ⟨i + 1, by simp [hi]⟩

theorem mem_insertByKey_self (k : KeyDecl) (r : List UInt8) :
    ∀ (l : List (List UInt8)), r ∈ Sem.insertByKey k r l
  | [] => by simp [Sem.insertByKey]
  | y :: ys => by
    simp only [Sem.insertByKey]
    split
    · simp
    · exact List.mem_cons_of_mem _ (mem_insertByKey_self k r ys)

theorem mem_insertByKey_of_mem (k : KeyDecl) (r x : List UInt8) :
    ∀ (l : List (List UInt8)), x ∈ l → x ∈ Sem.insertByKey k r l
  | [], h => by simp at h
  | y :: ys, h => by
    simp only [Sem.insertByKey]
    split
    · exact List.mem_cons_of_mem _ h
    · rcases List.mem_cons.1 h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (mem_insertByKey_of_mem k r x ys h)

/-! ## The loop invariant and the stop -/

/-- Loop invariant: `Inv` of `cbtrn02c_posts`, except that the transaction file holds exactly
records whose keys are the ids `modelX` has written, and no `WRITE` has met a duplicate key. -/
def InvX (m : Mem) (clk : Nat → List UInt8) (xrefs : List Xref) (trans : List Tran) (s0 : Model)
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
      f2.mode = some .output ∧
      ((∀ r ∈ f2.recs, r.take 16 ∈ (modelX xrefs clk (m.read 2212 20) s0 done).ids) ∧
        (∀ i ∈ (modelX xrefs clk (m.read 2212 20) s0 done).ids, ∃ r ∈ f2.recs, r.take 16 = i)) ∧
      f3.mode = some .input ∧ f3.recs = xrefs.map Xref.bytes ∧ f4.mode = some .output ∧
      f5.mode = some .io ∧ f5.recs = (model xrefs clk (m.read 2212 20) s0 done).accts.map Acct.bytes ∧
      f6.mode = some .io ∧ f6.recs = (model xrefs clk (m.read 2212 20) s0 done).cats.map TCat.bytes) ∧
    st.out = (model xrefs clk (m.read 2212 20) s0 done).out ++ [.display startMsg] ∧
    (modelX xrefs clk (m.read 2212 20) s0 done).stop = false

/-- How the loop stops: the abend at a duplicate key, with `modelX`'s events. -/
def ExitX (m : Mem) (clk : Nat → List UInt8) (xrefs : List Xref) (trans : List Tran) (s0 : Model)
    (r : Sem.Res) : Prop :=
  r.1 = .fault (.abend 999) ∧
    r.2.out = (modelX xrefs clk (m.read 2212 20) s0 trans).m.out ++ [.display startMsg] ∧
    (modelX xrefs clk (m.read 2212 20) s0 trans).stop = true ∧
    r.2.mem.read 3250 2 = encodeNum {} RETURN_CODE.fmt 0

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 20000 in
/-- **CBTRN02C on any input**: `cbtrn02c_posts` without distinct transaction ids. If no posted
transaction repeats the id of an earlier posted one, the program ends as `cbtrn02c_posts`
says (`modelX`'s posting model is `model`, `modelX_m`). Otherwise it abends with code 999 at
the first such transaction, and its events are `modelX`'s. -/
theorem cbtrn02c_any (m : Mem) (hm : m.size = 3252) (clk : Nat → List UInt8)
    (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧
      0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post)
    (trans : List Tran) (htv : ∀ t ∈ trans, t.valid) (hlen : trans.length < 1000000000)
    (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid)
    (accts : List Acct) (hav : ∀ a ∈ accts, a.valid)
    (cats : List TCat) (hcv : ∀ c ∈ cats, c.valid) (n : Nat) (hn : trans.length < n) :
    let r := Cbtrn02c.run { clock := clk } (n + 60)
      (Cbtrn02c.initState m [(1, trans.map Tran.bytes), (3, xrefs.map Xref.bytes),
        (5, accts.map Acct.bytes), (6, cats.map TCat.bytes)])
    let sx := modelX xrefs clk (m.read 2212 20) ⟨accts, cats, m.read 2618 22, 0, 0, []⟩ trans
    if sx.stop then
      r.1 = .fault (.abend 999) ∧ r.2.out = sx.m.out ++ [.display startMsg] ∧
        r.2.mem.read 3250 2 = encodeNum {} RETURN_CODE.fmt 0
    else
      r.1 = .stop .goback ∧
        r.2.out = [.display endMsg, .display (rejMsg ++ encodeNum {} WS_REJECT_COUNT.fmt sx.m.rejects),
          .display (procMsg ++ encodeNum {} WS_TRANSACTION_COUNT.fmt trans.length)] ++ sx.m.out ++
          [.display startMsg] ∧
        r.2.mem.read 3250 2 = encodeNum {} RETURN_CODE.fmt (if 0 < sx.m.rejects then 4 else 0) := by
  intro r sx
  simp only [r]
  cobol_auto
  cobol_loop_exit (InvX m clk xrefs trans ⟨accts, cats, m.read 2618 22, 0, 0, []⟩
      [(1, trans.map Tran.bytes), (3, xrefs.map Xref.bytes), (5, accts.map Acct.bytes),
        (6, cats.map TCat.bytes)]) (trans.map some ++ [none])
      (ExitX m clk xrefs trans ⟨accts, cats, m.read 2618 22, 0, 0, []⟩)
  · -- no duplicate: after the loop, six CLOSEs, the counts, RETURN-CODE, GOBACK
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := loopState
    obtain ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, -, hsz, heof, hcnt, hrej, -, -, hrc,
      ⟨f1, f2, f3, f4, f5, f6, rfl, h1m, -, -, -, h2m, -, h3m, -, h4m, h5m, -, h6m, -⟩, hout, hstop⟩ :=
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
      have hxm := modelX_m xrefs clk (m.read 2212 20) _ trans hstop
      simp only [sx, hstop, Bool.false_eq_true, ↓reduceIte, hxm]
      cobol_auto
      refine ⟨⟨by simp [endMsg], by simp [rejMsg], by simp [procMsg], hout⟩, ?_⟩
      split <;> simp_all
    · simp at h
  · -- a duplicate key: the abend ends the run
    obtain ⟨h1, hout, hstop, hmem⟩ := hexitInv
    simp only at h1 hout hmem
    subst h1
    simp only [sx, hstop, ↓reduceIte]
    cobol_auto
    all_goals first | exact hout | exact hmem
  · -- before the loop: nothing read, the counters and flags have their VALUEs
    cobol_inv [model, modelX] with [], trans
  · simp; omega
  · -- the loop ends exactly after the end-of-file READ
    rintro ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨-, -, -, -, -, -, -, -, -, -, heof, -⟩
    simp only [List.isEmpty_nil, ↓reduceIte] at heof
    cobol_auto
  · -- one iteration: READ the next transaction and post or reject it (or abend), or reach the end
    rintro y ys ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, hclk0, hsz, heof, hcnt, hrej, hcf, htf, hrc,
        ⟨f1, f2, f3, f4, f5, f6, rfl, h1m, h1r, h1p, h1e, h2m, ⟨h2r1, h2r2⟩, h3m, h3r, h4m, h5m, h5r,
          h6m, h6r⟩, hout, hstop⟩
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
      left
      cobol_auto
      cobol_inv with trans, []
      all_goals first | exact h2r1 | exact h2r2
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
      rcases hx : Sem.findKey { off := 0, len := 16 } t.card (xrefs.map Xref.bytes) with _ | i
      · -- the card is not in the cross-reference file: rejected (100)
        have hX := modelX_snoc_reject xrefs clk (m.read 2212 20) _ done t hstop
          (by rw [hS]; simp only [step, hx, Model.reject]; omega)
        rw [hS] at hX
        left
        cobol_auto
        cobol_inv [model_append, step, Model.reject, trailer, hout, badCardDesc, hX] with done ++ [t], todo'
        all_goals simp only [hX]
        all_goals first | rfl | exact h2r1 | exact h2r2
      · -- the card's cross-reference record
        have hi := findKey_lt hx
        simp only [List.length_map] at hi
        obtain ⟨x1, x2, x3, x4, x5⟩ := hxv _ (getD_mem hi)
        have hxg := getD_map Xref.bytes xrefs hi
        rcases ha : Sem.findKey { off := 0, len := 11 }
            (encodeNum {} FD_ACCT_ID.fmt (xrefs.getD i default).acct) (S.accts.map Acct.bytes) with _ | j
        · -- the account is not in the account file: rejected (101)
          have hX := modelX_snoc_reject xrefs clk (m.read 2212 20) _ done t hstop
            (by rw [hS]; simp only [step, hx, ha, Model.reject]; omega)
          rw [hS] at hX
          left
          cobol_auto [Xref.bytes]
          cobol_inv [model_append, step, Model.reject, trailer, hout, noAcctDesc, hX] with done ++ [t], todo'
          all_goals simp only [hX]
          all_goals first | rfl | exact h2r1 | exact h2r2
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
            have hX := modelX_snoc_reject xrefs clk (m.read 2212 20) _ done t hstop
              (by rw [hS]; simp only [step, hx, ha, hexp, ↓reduceIte, Model.reject]; omega)
            rw [hS] at hX
            left
            cobol_auto [Xref.bytes, Acct.bytes]
            cobol_inv [model_append, step, Model.reject, trailer, hout, expiredDesc, hX] with done ++ [t], todo'
            all_goals simp only [hX]
            all_goals first | rfl | exact h2r1 | exact h2r2
          by_cases hlim : (S.accts.getD j default).limit < (Sem.fitNum {} WS_TEMP_BAL.fmt
              ((S.accts.getD j default).cc - (S.accts.getD j default).cd + t.amt)).2
          · -- over the credit limit: rejected (102); the program compares with `compare`
            have hcmp : compare (S.accts.getD j default).limit (Sem.fitNum {} WS_TEMP_BAL.fmt
                ((S.accts.getD j default).cc - (S.accts.getD j default).cd + t.amt)).2 = .lt := by
              simp only [compare, compareOfLessAndEq, if_pos hlim]
            have hX := modelX_snoc_reject xrefs clk (m.read 2212 20) _ done t hstop
              (by rw [hS]; simp only [step, hx, ha, hexp, hlim, ↓reduceIte, Model.reject]; omega)
            rw [hS] at hX
            left
            cobol_auto [Xref.bytes, Acct.bytes]
            cobol_inv [model_append, step, Model.reject, trailer, hout, overLimitDesc, hlim, hX] with done ++ [t], todo'
            all_goals simp only [hX]
            all_goals first | rfl | exact h2r1 | exact h2r2
          · -- valid: posted
            have hcmp : compare (S.accts.getD j default).limit (Sem.fitNum {} WS_TEMP_BAL.fmt
                ((S.accts.getD j default).cc - (S.accts.getD j default).cd + t.amt)).2 ≠ .lt := by
              simp only [compare, compareOfLessAndEq, if_neg hlim]
              split <;> simp
            -- the clock reading of this posting
            obtain ⟨pre, mil, post, hpre, hpost, hmil, hmil0, hck⟩ := hclk S.posted
            have hcfl : S.catFill.length = 22 := hsv.fill
            have hp : (step xrefs clk (m.read 2212 20) S t).posted = S.posted + 1 := by
              simp only [step, hx, ha, hexp, hlim, ↓reduceIte, Model.post]
              split <;> rfl
            -- status 22 is numeric (`9910-DISPLAY-IO-STATUS`)
            have hnum : List.all [(242 : UInt8), 242] (fun b => (Config.decDigit {} b).isSome) = true := by
              decide
            by_cases hdup : t.id ∈
                (modelX xrefs clk (m.read 2212 20) ⟨accts, cats, m.read 2618 22, 0, 0, []⟩ done).ids
            · -- the id has been written: the WRITE meets a duplicate key (status 22), the abend
              obtain ⟨r0, hr0, hr0k⟩ := h2r2 _ hdup
              obtain ⟨k0, hf2s⟩ := findKey_some_of_mem (k := { off := 0, len := 16 }) hr0
                (by simpa [Sem.keyOf] using hr0k)
              have hX := modelX_dup xrefs clk (m.read 2212 20) _ done todo' t hstop (by rw [hS]; exact hp) hdup
              rw [hS] at hX
              right
              simp only [ExitX, hX]
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
                  cobol_auto [hclk0, haid, Xref.bytes, Acct.bytes, TCat.bytes, hf2s, hnum]
                  simp only [dupEvents, step, hx, ha, hexp, hlim, ↓reduceIte, Model.post, hk, List.tail_cons, hout]
                  cobol_simp_facts [Acct.bytes, TCat.bytes, noCatMsg, creatingMsg, abendMsg, status22Msg, errWriteMsg, hpos]
                · have hc0 : compare t.amt 0 = .lt := by
                    simp only [compare, compareOfLessAndEq, if_pos (Int.not_le.1 hpos)]
                  cobol_auto [hclk0, haid, Xref.bytes, Acct.bytes, TCat.bytes, hf2s, hnum]
                  simp only [dupEvents, step, hx, ha, hexp, hlim, ↓reduceIte, Model.post, hk, List.tail_cons, hout]
                  cobol_simp_facts [Acct.bytes, TCat.bytes, noCatMsg, creatingMsg, abendMsg, status22Msg, errWriteMsg, hpos]
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
                  cobol_auto [hclk0, haid, hckey, Xref.bytes, Acct.bytes, TCat.bytes, hf2s, hnum]
                  simp only [dupEvents, step, hx, ha, hexp, hlim, ↓reduceIte, Model.post, hk, List.tail_cons, hout]
                  cobol_simp_facts [Acct.bytes, TCat.bytes, noCatMsg, creatingMsg, abendMsg, status22Msg, errWriteMsg, hpos]
                · have hc0 : compare t.amt 0 = .lt := by
                    simp only [compare, compareOfLessAndEq, if_pos (Int.not_le.1 hpos)]
                  cobol_auto [hclk0, haid, hckey, Xref.bytes, Acct.bytes, TCat.bytes, hf2s, hnum]
                  simp only [dupEvents, step, hx, ha, hexp, hlim, ↓reduceIte, Model.post, hk, List.tail_cons, hout]
                  cobol_simp_facts [Acct.bytes, TCat.bytes, noCatMsg, creatingMsg, abendMsg, status22Msg, errWriteMsg, hpos]
            · -- a new id: written, and its id joins the written ids
              have hf2n : Sem.findKey { off := 0, len := 16 } t.id f2.recs = none := by
                apply findKey_eq_none
                intro r hr hkey
                simp only [Sem.keyOf, List.drop_zero] at hkey
                exact hdup (hkey ▸ h2r1 r hr)
              have hX := modelX_snoc_post xrefs clk (m.read 2212 20) _ done t hstop (by rw [hS]; exact hp) hdup
              rw [hS] at hX
              left
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
                  cobol_inv [model_append, step, Model.post, tranRec, db2ts, hout, hlim, noCatMsg, creatingMsg, Acct.bytes, TCat.bytes, hins, hpos, hX] with done ++ [t], todo'
                  · intro r hr
                    simp only [hX]
                    rcases mem_insertByKey _ _ _ _ hr with rfl | hr
                    · simp [List.append_assoc, List.take_append, List.take_of_length_le, t1]
                    · exact List.mem_cons_of_mem _ (h2r1 r hr)
                  · intro i hi
                    simp only [hX] at hi
                    rcases List.mem_cons.1 hi with rfl | hi
                    · exact ⟨_, mem_insertByKey_self _ _ _,
                        by simp [List.append_assoc, List.take_append, List.take_of_length_le, t1]⟩
                    · obtain ⟨r, hr, hrk⟩ := h2r2 i hi
                      exact ⟨r, mem_insertByKey_of_mem _ _ _ _ hr, hrk⟩
                · have hc0 : compare t.amt 0 = .lt := by
                    simp only [compare, compareOfLessAndEq, if_pos (Int.not_le.1 hpos)]
                  cobol_auto [hclk0, haid, Xref.bytes, Acct.bytes, TCat.bytes]
                  cobol_inv [model_append, step, Model.post, tranRec, db2ts, hout, hlim, noCatMsg, creatingMsg, Acct.bytes, TCat.bytes, hins, hpos, hX] with done ++ [t], todo'
                  · intro r hr
                    simp only [hX]
                    rcases mem_insertByKey _ _ _ _ hr with rfl | hr
                    · simp [List.append_assoc, List.take_append, List.take_of_length_le, t1]
                    · exact List.mem_cons_of_mem _ (h2r1 r hr)
                  · intro i hi
                    simp only [hX] at hi
                    rcases List.mem_cons.1 hi with rfl | hi
                    · exact ⟨_, mem_insertByKey_self _ _ _,
                        by simp [List.append_assoc, List.take_append, List.take_of_length_le, t1]⟩
                    · obtain ⟨r, hr, hrk⟩ := h2r2 i hi
                      exact ⟨r, mem_insertByKey_of_mem _ _ _ _ hr, hrk⟩
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
                  cobol_inv [model_append, step, Model.post, tranRec, db2ts, hout, hlim, noCatMsg, creatingMsg, Acct.bytes, TCat.bytes, hpos, hX] with done ++ [t], todo'
                  · intro r hr
                    simp only [hX]
                    rcases mem_insertByKey _ _ _ _ hr with rfl | hr
                    · simp [List.append_assoc, List.take_append, List.take_of_length_le, t1]
                    · exact List.mem_cons_of_mem _ (h2r1 r hr)
                  · intro i hi
                    simp only [hX] at hi
                    rcases List.mem_cons.1 hi with rfl | hi
                    · exact ⟨_, mem_insertByKey_self _ _ _,
                        by simp [List.append_assoc, List.take_append, List.take_of_length_le, t1]⟩
                    · obtain ⟨r, hr, hrk⟩ := h2r2 i hi
                      exact ⟨r, mem_insertByKey_of_mem _ _ _ _ hr, hrk⟩
                · have hc0 : compare t.amt 0 = .lt := by
                    simp only [compare, compareOfLessAndEq, if_pos (Int.not_le.1 hpos)]
                  cobol_auto [hclk0, haid, hckey, Xref.bytes, Acct.bytes, TCat.bytes]
                  cobol_inv [model_append, step, Model.post, tranRec, db2ts, hout, hlim, noCatMsg, creatingMsg, Acct.bytes, TCat.bytes, hpos, hX] with done ++ [t], todo'
                  · intro r hr
                    simp only [hX]
                    rcases mem_insertByKey _ _ _ _ hr with rfl | hr
                    · simp [List.append_assoc, List.take_append, List.take_of_length_le, t1]
                    · exact List.mem_cons_of_mem _ (h2r1 r hr)
                  · intro i hi
                    simp only [hX] at hi
                    rcases List.mem_cons.1 hi with rfl | hi
                    · exact ⟨_, mem_insertByKey_self _ _ _,
                        by simp [List.append_assoc, List.take_append, List.take_of_length_le, t1]⟩
                    · obtain ⟨r, hr, hrk⟩ := h2r2 i hi
                      exact ⟨r, mem_insertByKey_of_mem _ _ _ _ hr, hrk⟩

#print axioms cbtrn02c_any

end Cbtrn02c
end CardDemo
