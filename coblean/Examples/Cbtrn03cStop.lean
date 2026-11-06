/-
# CardDemo CBTRN03C: a transaction outside the date range ends the report

The date check of CBTRN03C's main loop is
`IF TRAN-PROC-TS (1:10) >= WS-START-DATE AND … <= WS-END-DATE CONTINUE ELSE NEXT SENTENCE`,
inside an inline `PERFORM UNTIL … END-PERFORM.`  `NEXT SENTENCE` passes control to the statement
after the next separator period, the one after `END-PERFORM`: the first transaction outside the
range ends the loop. That transaction is neither displayed nor reported, no page, account or
grand total is written, and the program closes its files and ends. `cbtrn03c_stops` states it for
every input: the report of the in-range transactions before it (`report3`, as in
`cbtrn03c_report`), then the end message.
-/
import Examples.Cbtrn03c
import Cobol.Logic.LoopExit

open Cobol

namespace CardDemo
namespace Cbtrn03c

/-- The transaction's processing date (`TRAN-PROC-TS (1:10)`) lies in the date range of the
parameter record (`WS-START-DATE`, `WS-END-DATE`). -/
def inRange (parm : List UInt8) (t : Tran) : Prop :=
  Sem.cmpBytes (t.proc.take 10) (parm.take 10) ≠ .lt ∧
    Sem.cmpBytes (t.proc.take 10) ((parm.drop 11).take 10) ≠ .gt

/-- Loop invariant when the transaction `t0` after the in-range transactions `pre` is out of
range: `Inv` with the end of file never reached (the remaining `READ`s are the rest of `pre`,
then `t0`). -/
def InvS (xrefs : List Xref) (types catgs : List (List UInt8)) (parm : List UInt8)
    (pre : List Tran) (t0 : Tran) (post : List Tran) (inp0 : List (Nat × List (List UInt8)))
    (rest : List (Option Tran)) (st : State) : Prop :=
  ∃ done todo, pre = done ++ todo ∧ rest = todo.map some ++ [some t0] ∧
    st.idx = [] ∧ st.slots = [] ∧ st.active = [] ∧ st.inp = inp0 ∧ st.mem.size = 2309 ∧
    st.mem.read 2300 1 = [213] ∧
    st.mem.read 2272 16 = (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).card ∧
    st.mem.read 2098 1 = (if done = [] then [232] else [213]) ∧
    st.mem.read 2099 5 = encodeNum {} WS_LINE_COUNTER.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).lines ∧
    st.mem.read 2239 11 = encodeNum {} WS_PAGE_TOTAL.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).page ∧
    st.mem.read 2250 11 = encodeNum {} WS_ACCOUNT_TOTAL.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).acct ∧
    st.mem.read 2261 11 = encodeNum {} WS_GRAND_TOTAL.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).grand ∧
    st.mem.read 2077 21 = parm.take 21 ∧
    st.mem.read 2104 2 = encodeNum {} WS_PAGE_SIZE.fmt 20 ∧
    st.mem.read 2106 133 = blankLine ∧ st.mem.read 1490 114 = header1 ∧
    st.mem.read 1604 133 = hdr2Line ∧ st.mem.read 1261 91 = nameHead ∧ st.mem.read 1362 4 = toMsg ∧
    st.mem.read 1737 97 = pageHead ∧ st.mem.read 1849 97 = acctHead ∧
    st.mem.read 1961 97 = grandHead ∧
    st.mem.read 1392 1 = [64] ∧ st.mem.read 1404 1 = [64] ∧ st.mem.read 1407 1 = [96] ∧
    st.mem.read 1423 1 = [64] ∧ st.mem.read 1428 1 = [96] ∧ st.mem.read 1458 1 = [64] ∧
    st.mem.read 1469 4 = [64, 64, 64, 64] ∧ st.mem.read 1488 2 = [64, 64] ∧
    (done = [] ∨
      (st.mem.read 1352 10 = parm.take 10 ∧ st.mem.read 1366 10 = (parm.drop 11).take 10 ∧
        st.mem.read 1110 11 = encodeNum {} XREF_ACCT_ID.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).xacct ∧
        (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).xacct.natAbs < 100000000000 ∧ 0 ≤ (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).xacct ∧
        st.mem.read 733 350 = (done.getLast?.getD default).bytes)) ∧
    (∃ f1 f2 f3 f4 f5 f6 : FileSt,
      st.files = [(1, f1), (5, f5), (2, f2), (3, f3), (4, f4), (6, f6)] ∧
      f1.mode = some .input ∧ f1.recs = (pre ++ t0 :: post).map Tran.bytes ∧
      f1.pos = done.length ∧ f1.eof = false ∧
      f2.mode = some .input ∧ f2.recs = xrefs.map Xref.bytes ∧ f3.mode = some .input ∧
      f3.recs = types ∧ f4.mode = some .input ∧ f4.recs = catgs ∧ f5.mode = some .output ∧
      f6.mode = some .input) ∧
    st.out = (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).out ++
      [.display (reportingMsg ++ parm.take 10 ++ toMsg ++ (parm.drop 11).take 10), .display startMsg]

/-- The state in which `NEXT SENTENCE` leaves the loop: the six files still open, the events of
the report of `pre`. -/
def ExitS (xrefs : List Xref) (types catgs : List (List UInt8)) (parm : List UInt8)
    (pre : List Tran) (inp0 : List (Nat × List (List UInt8))) (st : State) : Prop :=
  st.idx = [] ∧ st.slots = [] ∧ st.active = [] ∧ st.inp = inp0 ∧ st.mem.size = 2309 ∧
    (∃ f1 f2 f3 f4 f5 f6 : FileSt,
      st.files = [(1, f1), (5, f5), (2, f2), (3, f3), (4, f4), (6, f6)] ∧
      f1.mode = some .input ∧ f2.mode = some .input ∧ f3.mode = some .input ∧
      f4.mode = some .input ∧ f5.mode = some .output ∧ f6.mode = some .input) ∧
    st.out = (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) pre).out ++
      [.display (reportingMsg ++ parm.take 10 ++ toMsg ++ (parm.drop 11).take 10), .display startMsg]

set_option maxHeartbeats 60000000 in
set_option maxRecDepth 20000 in
/-- **CBTRN03C stops at the first transaction outside the date range.** For any in-range
transactions `pre`, then a transaction `t0` outside the range, then anything (`post`, never
read), every cross-reference, type and category file, every parameter record and every initial
storage: CBTRN03C ends with `GOBACK`, and its events are the start message, the date range, the
report of `pre` (`report3`, the same fold as in `cbtrn03c_report`), and the end message. No total
is written. Lookups and card numbers are constrained only for `pre`. -/
theorem cbtrn03c_stops (m : Mem) (hm : m.size = 2309)
    (pre : List Tran) (t0 : Tran) (post : List Tran)
    (hpv : ∀ t ∈ pre, t.valid) (ht0v : t0.valid) (hlen : pre.length < 10000000)
    (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid)
    (types catgs : List (List UInt8)) (htyl : ∀ r ∈ types, r.length = 60)
    (hcgl : ∀ r ∈ catgs, r.length = 60)
    (parm : List UInt8) (hpl : parm.length = 80) (prest : List (List UInt8))
    (hpre : ∀ t ∈ pre, inRange parm t) (ht0 : ¬ inRange parm t0)
    (hxf : ∀ t ∈ pre,
      (Sem.findKey { off := 0, len := 16 } t.card (xrefs.map Xref.bytes)).isSome)
    (htf : ∀ t ∈ pre, (Sem.findKey { off := 0, len := 2 } t.ty types).isSome)
    (hcf : ∀ t ∈ pre, (Sem.findKey { off := 0, len := 6 }
      (t.ty ++ encodeNum {} FD_TRAN_CAT_CD.fmt t.cat) catgs).isSome)
    (hcard : ∀ t ∈ pre, t.card ≠ List.replicate 16 64)
    (n : Nat) (hn : pre.length < n) :
    let r := Cbtrn03c.run {} (n + 60) (Cbtrn03c.initState m
      [(1, (pre ++ t0 :: post).map Tran.bytes), (2, xrefs.map Xref.bytes), (3, types), (4, catgs),
        (6, parm :: prest)])
    let s := report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) pre
    r.1 = .stop .goback ∧
      r.2.out = [.display endMsg] ++ s.out ++
        [.display (reportingMsg ++ parm.take 10 ++ toMsg ++ (parm.drop 11).take 10),
          .display startMsg] := by
  intro r s
  simp only [r]
  cobol_auto
  cobol_loop_exit (InvS xrefs types catgs parm pre t0 post
      [(1, (pre ++ t0 :: post).map Tran.bytes), (2, xrefs.map Xref.bytes), (3, types), (4, catgs),
        (6, parm :: prest)]) (pre.map some ++ [some t0])
    (fun (r : Sem.Res) => r.1 = .nextSentence ∧ ExitS xrefs types catgs parm pre
      [(1, (pre ++ t0 :: post).map Tran.bytes), (2, xrefs.map Xref.bytes), (3, types), (4, catgs),
        (6, parm :: prest)] r.2)
  · -- the loop never ends normally: the end of the file is never reached
    obtain ⟨done, todo, -, hrest, -⟩ := hloopInv
    simp at hrest
  · -- `NEXT SENTENCE` left the loop: six CLOSEs, DISPLAY, GOBACK
    obtain ⟨rfl, hx⟩ := hexitInv
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := exitState
    obtain ⟨rfl, rfl, rfl, rfl, hsz, ⟨f1, f2, f3, f4, f5, f6, rfl, h1m, h2m, h3m, h4m, h5m, h6m⟩,
      hout⟩ := hx
    dsimp only at hsz hout
    cobol_auto
    simp only [s] at hout ⊢
    simp [hout, endMsg]
  · -- before the loop: the date range read, nothing else
    cobol_inv [report3_nil, blankLine, hdr2Line, header1, nameHead, toMsg, pageHead, acctHead, grandHead,
      reportingMsg, startMsg, List.drop_take, List.take_take, enc_total_zero, enc_lines_zero] with [], pre
  · simp; omega
  · -- `Inv []` never holds
    rintro st ⟨done, todo, -, hrest, -⟩
    simp at hrest
  · -- one iteration: READ the next transaction; report it, or leave the loop at `t0`
    rintro y ys ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, hsz, heof, hcard', hfirst, hlines, hpage, hacct,
        hgrand, hdp, hps, hbl, hh1, hh2, hnh, hto, hph, hah, hgh, hf1, hf2, hf3, hf4, hf5, hf6,
        hf7, hf8, hphase,
        ⟨f1, f2, f3, f4, f5, f6, rfl, h1m, h1r, h1p, h1e, h2m, h2r, h3m, h3r, h4m, h4r, h5m, h6m⟩,
        hout⟩
    dsimp only at hsz heof hcard' hfirst hlines hpage hacct hgrand hdp hps hbl hh1 hh2 hnh hto hph
    dsimp only at hah hgh hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hphase hout
    refine ⟨by cobol_auto, ?_⟩
    -- the model after `done`
    have hb := report3_bounds xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done
    have hlb := report3_lines xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done
    have hcl := report3_card_length xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done
      (fun t ht => (hpv t (by simp [hd, ht])).2.2.2.2.2.2.2.2.1)
    generalize hS : report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done = S
      at hcard' hlines hpage hacct hgrand hphase hout hb hlb hcl
    obtain ⟨hpb, hab, hgb⟩ := hb
    have hdl : done.length < 10000000 := by
      have := hlen; rw [hd] at this; simp only [List.length_append] at this; omega
    have hl0 : S.lines < 130000000 := by omega
    cases todo with
    | nil =>
      -- `t0`: READ, the date check fails, `NEXT SENTENCE` leaves the loop
      simp only [List.map_nil, List.nil_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      simp only [List.append_nil] at hd
      subst hd
      right
      have hsome : f1.recs[f1.pos]? = some t0.bytes := by rw [h1r, h1p]; simp
      have tb := Tran.length_bytes t0 ht0v
      have tfp := Tran.field_proc10 t0 ht0v
      obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := ht0v
      by_cases hlo : Sem.cmpBytes (t0.proc.take 10) (parm.take 10) = .lt
      · cobol_auto [hlo, List.take_take, List.drop_take]
        cobol_inv [ExitS, hout, hS]
      · have hhi : Sem.cmpBytes (t0.proc.take 10) ((parm.drop 11).take 10) = .gt := by
          exact Classical.byContradiction fun h => ht0 ⟨hlo, h⟩
        cobol_auto [hhi, List.take_take, List.drop_take]
        cobol_inv [ExitS, hout, hS]
    | cons t todo' =>
      -- an in-range transaction: as in `cbtrn03c_report`
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      subst hd
      left
      have htm : t ∈ done ++ t :: todo' := by simp
      obtain ⟨hd1, hd2⟩ := hpre t htm
      have hc0 := hcard t htm
      obtain ⟨ix, hix⟩ := Option.isSome_iff_exists.mp (hxf t htm)
      obtain ⟨it, hit⟩ := Option.isSome_iff_exists.mp (htf t htm)
      obtain ⟨ic, hic⟩ := Option.isSome_iff_exists.mp (hcf t htm)
      have htv' := hpv t htm
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
      -- the type and category records
      have hitl := findKey_lt hit
      have hicl := findKey_lt hic
      have htyr := htyl _ (getD_mem' hitl)
      have hcgr := hcgl _ (getD_mem' hicl)
      -- the cross-reference record (read on a new card)
      have hixl := findKey_lt hix
      simp only [List.length_map] at hixl
      obtain ⟨x1, x2, x3, x4, x5⟩ := hxv _ (getD_mem hixl)
      have hxg := getD_map Xref.bytes xrefs hixl
      by_cases hc : S.card = t.card
      · -- the card of the previous transaction (so not the first one)
        have hdn : done ≠ [] := by
          rintro rfl
          rw [report3_nil] at hS
          exact hc0 (by rw [← hc, ← hS])
        have hSf : S.first = false := by rw [← hS]; exact report3_first _ _ _ _ _ done hdn
        simp only [hdn, ↓reduceIte] at hfirst
        rcases hphase with h0 | ⟨hsd, hed, hxa, hxa1, hxa2, htr⟩
        · exact absurd h0 hdn
        have hnl := name_read mem parm hnh hsd hto hed
        by_cases hb : S.lines % 20 = 0
        · -- a page break before the detail line
          have hm := compare_mod20_eq (x := (S.lines : Int)) (by omega)
          cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length, List.take_take,
            List.drop_take, pageHead_length, nameHead_length, header1_length, toMsg_length,
            hdr2Line_length, blankLine_length, mod20, hm, hc, hit, hic, htyr, hcgr, hnl]
          cobol_inv [report3_append, step3, hS, hout, hSf, hc, hb, headers, hdr1Line, nameLine,
            pageLine, detailLine, typeDesc, catDesc, hit, hic, fitTot, editPlus_length,
            editMinus_length, pageHead_length, nameHead_length, header1_length, toMsg_length,
            hdr2Line_length, blankLine_length, Int.natCast_add,
            Int.add_assoc] with done ++ [t], todo'
        · -- no page break
          have hm := compare_mod20_gt (x := (S.lines : Int)) (by omega)
          cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length, List.take_take,
            List.drop_take, mod20, hm, hc, hit, hic, htyr, hcgr]
          cobol_inv [report3_append, step3, hS, hout, hSf, hc, hb, detailLine, typeDesc, catDesc,
            hit, hic, fitTot, editMinus_length, Int.natCast_add,
            Int.add_assoc] with done ++ [t], todo'
      · by_cases hdn : done = []
        · -- the first transaction: the headers, the cross-reference lookup
          have hS0 : report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done =
              ⟨List.replicate 16 64, true, 0, 0, 0, 0, 0, []⟩ := by rw [hdn]; rfl
          have hSl : S.lines = 0 := by rw [← hS, hS0]
          have hSp : S.page = 0 := by rw [← hS, hS0]
          have hSa : S.acct = 0 := by rw [← hS, hS0]
          have hSg : S.grand = 0 := by rw [← hS, hS0]
          have hSf : S.first = true := by rw [← hS, hS0]
          have hSo : S.out = [] := by rw [← hS, hS0]
          simp [hdn] at hfirst
          have hm : compare ((4 : Int) % 20) 0 = .gt := by decide
          have hm' : compare (4 : Int) 0 = .gt := by decide
          cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length, List.take_take,
            List.drop_take, nameHead_length, header1_length, toMsg_length, hdr2Line_length,
            blankLine_length, mod20, hm, hm', hc, hSl, hSp, hSa, hSg, Xref.bytes, hxg, hix, hit,
            hic, htyr, hcgr]
          cobol_inv [report3_append, step3, hS, hout, hSl, hSp, hSa, hSg, hSf, hSo, hc, headers,
            hdr1Line, nameLine, detailLine, typeDesc, catDesc, xrefOf, hix, hit, hic, fitTot,
            editMinus_length, nameHead_length, header1_length, toMsg_length, hdr2Line_length,
            blankLine_length, Int.natCast_add, Int.add_assoc] with done ++ [t], todo'
        · -- a new card: the account total of the previous card, the cross-reference lookup
          have hSf : S.first = false := by rw [← hS]; exact report3_first _ _ _ _ _ done hdn
          simp only [hdn, ↓reduceIte] at hfirst
          rcases hphase with h0 | ⟨hsd, hed, hxa, hxa1, hxa2, htr⟩
          · exact absurd h0 hdn
          have hnl := name_read mem parm hnh hsd hto hed
          by_cases hb : (S.lines + 2) % 20 = 0
          · have hm := compare_mod20_eq (x := (S.lines : Int) + 1 + 1) (by omega)
            cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length, List.take_take,
              List.drop_take, pageHead_length, acctHead_length, nameHead_length, header1_length,
              toMsg_length, hdr2Line_length, blankLine_length, mod20, hm, hc, Xref.bytes, hxg,
              hix, hit, hic, htyr, hcgr, hnl]
            cobol_inv [report3_append, step3, hS, hout, hSf, hc, hb, headers, hdr1Line, nameLine,
              pageLine, acctLine, detailLine, typeDesc, catDesc, xrefOf, hix, hit, hic, fitTot,
              editPlus_length, editMinus_length, pageHead_length, acctHead_length,
              nameHead_length, header1_length, toMsg_length, hdr2Line_length, blankLine_length,
              Int.natCast_add, Int.add_assoc] with done ++ [t], todo'
          · have hm := compare_mod20_gt (x := (S.lines : Int) + 1 + 1) (by omega)
            cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length, List.take_take,
              List.drop_take, acctHead_length, hdr2Line_length, mod20, hm, hc, Xref.bytes, hxg,
              hix, hit, hic, htyr, hcgr]
            cobol_inv [report3_append, step3, hS, hout, hSf, hc, hb, acctLine, detailLine,
              typeDesc, catDesc, xrefOf, hix, hit, hic, fitTot, editPlus_length,
              editMinus_length, acctHead_length, hdr2Line_length, Int.natCast_add, Int.add_assoc] with done ++ [t], todo'

end Cbtrn03c
end CardDemo

#print axioms CardDemo.Cbtrn03c.cbtrn03c_stops
