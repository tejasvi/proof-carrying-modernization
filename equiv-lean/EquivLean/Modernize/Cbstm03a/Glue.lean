import EquivLean.Modernize.Cbstm03a.StmBridge
import EquivLean.Modernize.Cbstm03a.Domain
import EquivLean.Modernize.Cbstm03a.Model

/-!
# CBSTM03A: Connecting coblean's `CBSTM03AB` theorems (`stm_run_sorted`, `stm_run_abort_cust`,
`stm_run_abort_acct`) to the field-value model `Model.run`

Proves:
* `ofCard_encode`: `ofCard card (trs.map TrnxRecord.encode) = (ofCardF card trs).map TrnxRecord.encode`.
* `stmt_html_of_find`: for a valid `CardXrefRecord` `x` whose customer `c` and account `a` are
  found, `(stmtOfS ... (CardXrefRecord.encode x)).map (·.map cp037Code) = modelStmtOf trs (strOf (x.getD 0 default)) c a`
  and `(htmlOfS ... (CardXrefRecord.encode x)).map (·.map cp037Code) = modelHtmlOf trs (strOf (x.getD 0 default)) c a`.
* `dispL` and `wrL` lemmas on `walkDisplays`, `evsOf`, `custMsg`, and `acctMsg`.
* `cobol_outputs_any`: for any initial storage `m0` with `m0.size = 178495` and
  `m0.read 175623 4 = [0, 0, 0, 0]` (`PSAPTR = 0`), and any valid `trs`, `xrefs`, `custs`, `accts`
  satisfying `Domain trs xrefs custs accts` and `trs.length + xrefs.length ≤ n`, the COBOL run of
  `Stm` at fuel `n + 100` under `{ addrSpace := asp }` ends in `.stop .goback` or
  `.fault (.abend (-1))` matching `Model.run trs xrefs custs accts` on `displays` (after `.drop 11`),
  `writes 1` (`STMT-FILE`), `writes 2` (`HTML-FILE`), and `abended`.
-/

open Cobol Cobol.Stm Cobol.StmCore EquivLean.Cobol.Rec EquivLean.Modernize.GlueKit
open EquivLean.Modernize.Cbstm03a EquivLean.Modernize.Cbstm03a.StmBridge EquivLean.Modernize.Cbstm03a.Model

namespace EquivLean.Modernize.Cbstm03a.Glue

/-! ## 1. `ofCard` on encoded transaction records -/

theorem ofCard_encode {trs : List (List FVal)} (htrs : ∀ r ∈ trs, TrnxRecord.Valid r)
    (card : List UInt8) :
    ofCard card (trs.map TrnxRecord.encode) = (ofCardF card trs).map TrnxRecord.encode := by
  unfold ofCard ofCardF
  induction trs with
  | nil => rfl
  | cons r rs ih =>
    have hr := trnx_fields (htrs r (List.mem_cons_self ..))
    have ih' := ih (fun x hx => htrs x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.filter_cons, hr.1]
    cases (strOf (r.getD 0 default) == card) <;> simp [ih']

theorem foldl_addAmt_encode {ts : List (List FVal)} (hts : ∀ r ∈ ts, TrnxRecord.Valid r) :
    ∀ acc : Int, (ts.map TrnxRecord.encode).foldl addAmt acc = ts.foldl modelAddAmt acc := by
  induction ts with
  | nil => intro acc; rfl
  | cons r rs ih =>
    intro acc
    have htr := (tran_of_valid (hts r (List.mem_cons_self ..)) acc).2.2.2
    simp only [List.map_cons, List.foldl_cons, htr]
    exact ih (fun x hx => hts x (List.mem_cons_of_mem _ hx)) (modelAddAmt acc r)

theorem map_tranStmtR_encode {ts : List (List FVal)} (hts : ∀ r ∈ ts, TrnxRecord.Valid r) :
    ((ts.map TrnxRecord.encode).map tranStmtR).map (·.map cp037Code) = ts.map modelTranStmt := by
  induction ts with
  | nil => rfl
  | cons r rs ih =>
    have htr := (tran_of_valid (hts r (List.mem_cons_self ..)) 0).1
    simp only [List.map_cons, htr, modelTranStmt, ih (fun x hx => hts x (List.mem_cons_of_mem _ hx))]

theorem flatMap_tranHtmlR_encode {ts : List (List FVal)} (hts : ∀ r ∈ ts, TrnxRecord.Valid r) :
    ((ts.map TrnxRecord.encode).flatMap tranHtmlR).map (·.map cp037Code) =
      ts.flatMap modelTranHtml := by
  induction ts with
  | nil => rfl
  | cons r rs ih =>
    have htr := (tran_of_valid (hts r (List.mem_cons_self ..)) 0).2.1
    simp only [List.map_cons, List.flatMap_cons, List.map_append, htr, modelTranHtml,
      ih (fun x hx => hts x (List.mem_cons_of_mem _ hx))]

theorem ofCardF_valid {trs : List (List FVal)} (htrs : ∀ r ∈ trs, TrnxRecord.Valid r)
    (card : List UInt8) : ∀ r ∈ ofCardF card trs, TrnxRecord.Valid r := by
  intro r hr
  unfold ofCardF at hr
  exact htrs r (List.mem_filter.mp hr).1

/-- **`stmtOfS` and `htmlOfS` on encoded records match `modelStmtOf` and `modelHtmlOf`.** -/
theorem stmt_html_of_find {trs custs accts : List (List FVal)}
    (htrs : ∀ r ∈ trs, TrnxRecord.Valid r)
    (hcusts : ∀ c ∈ custs, CustomerRecord.Valid c)
    (haccts : ∀ a ∈ accts, AccountRecord.Valid a)
    {x c a : List FVal} (hx : CardXrefRecord.Valid x)
    (hfc : custs.find? (fun c => numOf (c.getD 0 default) == numOf (x.getD 1 default)) = some c)
    (hfa : accts.find? (fun a => numOf (a.getD 0 default) == numOf (x.getD 2 default)) = some a) :
    (stmtOfS (trs.map TrnxRecord.encode) (custs.map CustomerRecord.encode)
        (accts.map AccountRecord.encode) (CardXrefRecord.encode x)).map (·.map cp037Code) =
      modelStmtOf trs (strOf (x.getD 0 default)) c a ∧
    (htmlOfS (trs.map TrnxRecord.encode) (custs.map CustomerRecord.encode)
        (accts.map AccountRecord.encode) (CardXrefRecord.encode x)).map (·.map cp037Code) =
      modelHtmlOf trs (strOf (x.getD 0 default)) c a := by
  obtain ⟨-, hco, hao, hcv, hav⟩ := xok_of_find hcusts haccts hx hfc hfa
  obtain ⟨hhs, hhh, -⟩ := head_of_valid hcv hav
  have hxc := (xref_fields hx).1
  have hof := ofCard_encode htrs (strOf (x.getD 0 default))
  have hts := ofCardF_valid htrs (strOf (x.getD 0 default))
  constructor
  · unfold stmtOfS modelStmtOf modelHeadStmt modelTailStmt
    rw [hco, hao, hhs, hxc, hof, List.map_append, List.map_append,
      map_tranStmtR_encode hts, foldl_addAmt_encode hts]
  · unfold htmlOfS modelHtmlOf modelHeadHtml modelTailHtml
    rw [hco, hao, hhh, hxc, hof, List.map_append, List.map_append,
      flatMap_tranHtmlR_encode hts]

/-! ## 2. `dispL` and `wrL` on `walkDisplays`, `evsOf`, `evsOfS`, `custMsg`, `acctMsg` -/

theorem dispL_map_write (f : Nat) : ∀ l : List (List UInt8), dispL (l.map (.write f)) = []
  | [] => rfl
  | _ :: ls => by rw [List.map_cons, dispL_write, dispL_map_write f ls]

theorem dispL_headE (c a : List UInt8) : dispL (headE c a) = [] := by
  unfold headE headEvents
  rw [dispL_append, dispL_append, dispL_map_write, dispL_map_write]
  rfl

theorem dispL_tranEvents (r : List UInt8) : dispL (tranEvents r) = [] := by
  unfold tranEvents
  rw [dispL_write, dispL_map_write]

theorem dispL_tailEvents (t : Int) : dispL (tailEvents t) = [] := by
  unfold tailEvents
  rw [dispL_append, dispL_map_write, dispL_map_write]
  rfl

theorem dispL_flatMap_tranEvents : ∀ l : List (List UInt8), dispL (l.flatMap tranEvents) = []
  | [] => rfl
  | r :: rs => by simp [List.flatMap_cons, dispL_append, dispL_tranEvents, dispL_flatMap_tranEvents rs]

theorem dispL_trnxEvents (X : List UInt8) (gs : List (List (List UInt8))) :
    dispL (trnxEvents X gs) = [] := by
  unfold trnxEvents
  rw [dispL_append, dispL_tailEvents, List.append_nil]
  induction (vis X gs) with
  | nil => rfl
  | cons g gs' ih =>
    simp only [List.flatMap_cons, dispL_append, ih, List.append_nil, matchEvents]
    split
    · exact dispL_flatMap_tranEvents g
    · rfl

theorem dispL_evsOf (gs : List (List (List UInt8))) (custs accts : List (List UInt8))
    (x : List UInt8) : dispL (evsOf gs custs accts x) = [] := by
  unfold evsOf
  rw [dispL_append, dispL_headE, dispL_trnxEvents]
  rfl

theorem dispL_flatMap_evsOf (gs : List (List (List UInt8))) (custs accts : List (List UInt8)) :
    ∀ xs : List (List UInt8), dispL (xs.flatMap (evsOf gs custs accts)) = []
  | [] => rfl
  | x :: xs => by
    simp [List.flatMap_cons, dispL_append, dispL_evsOf, dispL_flatMap_evsOf gs custs accts xs]

theorem dispL_evsOfS (trs custs accts : List (List UInt8)) (hs : CardsSorted trs)
    (x : List UInt8) : dispL (evsOfS trs custs accts x) = [] := by
  rw [← evsOf_sorted trs hs custs accts]
  exact dispL_evsOf (grp trs) custs accts x

theorem dispL_flatMap_evsOfS (trs custs accts : List (List UInt8)) (hs : CardsSorted trs) :
    ∀ xs : List (List UInt8), dispL (xs.flatMap (evsOfS trs custs accts)) = []
  | [] => rfl
  | x :: xs => by
    simp [List.flatMap_cons, dispL_append, dispL_evsOfS trs custs accts hs,
      dispL_flatMap_evsOfS trs custs accts hs xs]

theorem length_dispL_walkDisplays : (dispL walkDisplays.reverse).length = 11 := by decide

theorem wrL1_map_write1 : ∀ l : List (List UInt8), wrL 1 (l.map (.write 1)) = l
  | [] => rfl
  | a :: ls => by rw [List.map_cons, wrL_write, wrL1_map_write1 ls]; rfl

theorem wrL1_map_write2 : ∀ l : List (List UInt8), wrL 1 (l.map (.write 2)) = []
  | [] => rfl
  | a :: ls => by rw [List.map_cons, wrL_write]; exact wrL1_map_write2 ls

theorem wrL2_map_write2 : ∀ l : List (List UInt8), wrL 2 (l.map (.write 2)) = l
  | [] => rfl
  | a :: ls => by rw [List.map_cons, wrL_write, wrL2_map_write2 ls]; rfl

theorem wrL2_map_write1 : ∀ l : List (List UInt8), wrL 2 (l.map (.write 1)) = []
  | [] => rfl
  | a :: ls => by rw [List.map_cons, wrL_write]; exact wrL2_map_write1 ls

theorem wrL_walkDisplays (f : Nat) : wrL f walkDisplays.reverse = [] := by
  simp [walkDisplays, wrL]

theorem wrL_custMsg (f : Nat) : wrL f custMsg.reverse = [] := by
  simp [custMsg, wrL]

theorem wrL_acctMsg (f : Nat) : wrL f acctMsg.reverse = [] := by
  simp [acctMsg, wrL]

theorem dispL_custMsg : (dispL custMsg.reverse).map (·.map cp037Code) = modelCustAbortDisp := rfl
theorem dispL_acctMsg : (dispL acctMsg.reverse).map (·.map cp037Code) = modelAcctAbortDisp := rfl

theorem wrL1_headE (c a : List UInt8) : wrL 1 (headE c a) = headS c a := by
  unfold headE headS headEvents stmtHead
  rw [wrL_append, wrL_append, wrL1_map_write2, wrL1_map_write1]
  rfl

theorem wrL2_headE (c a : List UInt8) : wrL 2 (headE c a) = headH c a := by
  unfold headE headH headEvents
  rw [wrL_append, wrL_append, wrL2_map_write2, wrL2_map_write1]
  simp [wrL]

theorem wrL1_tranEvents (r : List UInt8) : wrL 1 (tranEvents r) = [tranStmtR r] := by
  unfold tranEvents
  rw [wrL_write, wrL1_map_write2]
  rfl

theorem wrL2_tranEvents (r : List UInt8) : wrL 2 (tranEvents r) = tranHtmlR r := by
  unfold tranEvents
  rw [wrL_write, wrL2_map_write2]
  rfl

theorem wrL1_flatMap_tranEvents :
    ∀ l : List (List UInt8), wrL 1 (l.flatMap tranEvents) = l.map tranStmtR
  | [] => rfl
  | r :: rs => by
    simp [List.flatMap_cons, wrL_append, wrL1_tranEvents, wrL1_flatMap_tranEvents rs]

theorem wrL2_flatMap_tranEvents :
    ∀ l : List (List UInt8), wrL 2 (l.flatMap tranEvents) = l.flatMap tranHtmlR
  | [] => rfl
  | r :: rs => by
    simp [List.flatMap_cons, wrL_append, wrL2_tranEvents, wrL2_flatMap_tranEvents rs]

theorem wrL1_trnxEvents_sorted (trs : List (List UInt8)) (hs : CardsSorted trs) (X : List UInt8) :
    wrL 1 (trnxEvents X (grp trs)) = trnxStmt X (grp trs) := by
  rw [trnxEvents_sorted trs hs X, trnxStmt_sorted trs hs X]
  unfold tailEvents
  rw [wrL_append, wrL_append, wrL1_flatMap_tranEvents, wrL1_map_write1, wrL1_map_write2,
    List.append_nil]

theorem wrL2_trnxEvents_sorted (trs : List (List UInt8)) (hs : CardsSorted trs) (X : List UInt8) :
    wrL 2 (trnxEvents X (grp trs)) = trnxHtml X (grp trs) := by
  rw [trnxEvents_sorted trs hs X, trnxHtml_sorted trs hs X]
  unfold tailEvents
  rw [wrL_append, wrL_append, wrL2_flatMap_tranEvents, wrL2_map_write1, wrL2_map_write2,
    List.nil_append]

theorem wrL1_evsOf_sorted (trs : List (List UInt8)) (hs : CardsSorted trs)
    (custs accts : List (List UInt8)) (x : List UInt8) :
    wrL 1 (evsOf (grp trs) custs accts x) = stmtOfS trs custs accts x := by
  unfold evsOf stmtOfS
  rw [wrL_append, wrL1_headE, wrL1_trnxEvents_sorted trs hs, trnxStmt_sorted trs hs]

theorem wrL2_evsOf_sorted (trs : List (List UInt8)) (hs : CardsSorted trs)
    (custs accts : List (List UInt8)) (x : List UInt8) :
    wrL 2 (evsOf (grp trs) custs accts x) = htmlOfS trs custs accts x := by
  unfold evsOf htmlOfS
  rw [wrL_append, wrL2_headE, wrL2_trnxEvents_sorted trs hs, trnxHtml_sorted trs hs]

theorem wrL1_flatMap_evsOf (trs : List (List UInt8)) (hs : CardsSorted trs)
    (custs accts : List (List UInt8)) :
    ∀ xs : List (List UInt8),
      wrL 1 (xs.flatMap (evsOf (grp trs) custs accts)) = xs.flatMap (stmtOfS trs custs accts)
  | [] => rfl
  | x :: xs => by
    simp [List.flatMap_cons, wrL_append, wrL1_evsOf_sorted trs hs,
      wrL1_flatMap_evsOf trs hs custs accts xs]

theorem wrL2_flatMap_evsOf (trs : List (List UInt8)) (hs : CardsSorted trs)
    (custs accts : List (List UInt8)) :
    ∀ xs : List (List UInt8),
      wrL 2 (xs.flatMap (evsOf (grp trs) custs accts)) = xs.flatMap (htmlOfS trs custs accts)
  | [] => rfl
  | x :: xs => by
    simp [List.flatMap_cons, wrL_append, wrL2_evsOf_sorted trs hs,
      wrL2_flatMap_evsOf trs hs custs accts xs]

theorem wrL1_evsOfS (trs : List (List UInt8)) (hs : CardsSorted trs)
    (custs accts : List (List UInt8)) (x : List UInt8) :
    wrL 1 (evsOfS trs custs accts x) = stmtOfS trs custs accts x := by
  rw [← evsOf_sorted trs hs custs accts]
  exact wrL1_evsOf_sorted trs hs custs accts x

theorem wrL2_evsOfS (trs : List (List UInt8)) (hs : CardsSorted trs)
    (custs accts : List (List UInt8)) (x : List UInt8) :
    wrL 2 (evsOfS trs custs accts x) = htmlOfS trs custs accts x := by
  rw [← evsOf_sorted trs hs custs accts]
  exact wrL2_evsOf_sorted trs hs custs accts x

theorem wrL1_flatMap_evsOfS (trs : List (List UInt8)) (hs : CardsSorted trs)
    (custs accts : List (List UInt8)) :
    ∀ xs : List (List UInt8),
      wrL 1 (xs.flatMap (evsOfS trs custs accts)) = xs.flatMap (stmtOfS trs custs accts)
  | [] => rfl
  | x :: xs => by
    simp [List.flatMap_cons, wrL_append, wrL1_evsOfS trs hs,
      wrL1_flatMap_evsOfS trs hs custs accts xs]

theorem wrL2_flatMap_evsOfS (trs : List (List UInt8)) (hs : CardsSorted trs)
    (custs accts : List (List UInt8)) :
    ∀ xs : List (List UInt8),
      wrL 2 (xs.flatMap (evsOfS trs custs accts)) = xs.flatMap (htmlOfS trs custs accts)
  | [] => rfl
  | x :: xs => by
    simp [List.flatMap_cons, wrL_append, wrL2_evsOfS trs hs,
      wrL2_flatMap_evsOfS trs hs custs accts xs]

#print axioms stmt_html_of_find
#print axioms wrL1_flatMap_evsOfS
#print axioms wrL2_flatMap_evsOfS

/-! ## 3. Triangulation of `Model.loop` and top-level `cobol_outputs_any` -/

theorem loop_trichotomy {trs custs accts : List (List FVal)}
    (htrs : ∀ r ∈ trs, TrnxRecord.Valid r)
    (hcusts : ∀ c ∈ custs, CustomerRecord.Valid c)
    (haccts : ∀ a ∈ accts, AccountRecord.Valid a) :
    ∀ (xs : List (List FVal)) (_hxs : ∀ x ∈ xs, CardXrefRecord.Valid x)
      (stmts htmls : List (List Nat)),
      (let T := trs.map TrnxRecord.encode
       let C := custs.map CustomerRecord.encode
       let A := accts.map AccountRecord.encode
       (∀ x ∈ xs, XOk C A (CardXrefRecord.encode x)) ∧
       loop trs custs accts xs stmts htmls =
         ⟨[], stmts ++ ((xs.map CardXrefRecord.encode).flatMap (stmtOfS T C A)).map (·.map cp037Code),
              htmls ++ ((xs.map CardXrefRecord.encode).flatMap (htmlOfS T C A)).map (·.map cp037Code),
              false⟩) ∨
      (∃ pre x post,
        let T := trs.map TrnxRecord.encode
        let C := custs.map CustomerRecord.encode
        let A := accts.map AccountRecord.encode
        xs = pre ++ x :: post ∧
        (∀ y ∈ pre, XOk C A (CardXrefRecord.encode y)) ∧
        custs.find? (fun c => numOf (c.getD 0 default) == numOf (x.getD 1 default)) = none ∧
        loop trs custs accts xs stmts htmls =
          ⟨modelCustAbortDisp,
           stmts ++ ((pre.map CardXrefRecord.encode).flatMap (stmtOfS T C A)).map (·.map cp037Code),
           htmls ++ ((pre.map CardXrefRecord.encode).flatMap (htmlOfS T C A)).map (·.map cp037Code),
           true⟩) ∨
      (∃ pre x post c,
        let T := trs.map TrnxRecord.encode
        let C := custs.map CustomerRecord.encode
        let A := accts.map AccountRecord.encode
        xs = pre ++ x :: post ∧
        (∀ y ∈ pre, XOk C A (CardXrefRecord.encode y)) ∧
        custs.find? (fun c => numOf (c.getD 0 default) == numOf (x.getD 1 default)) = some c ∧
        accts.find? (fun a => numOf (a.getD 0 default) == numOf (x.getD 2 default)) = none ∧
        loop trs custs accts xs stmts htmls =
          ⟨modelAcctAbortDisp,
           stmts ++ ((pre.map CardXrefRecord.encode).flatMap (stmtOfS T C A)).map (·.map cp037Code),
           htmls ++ ((pre.map CardXrefRecord.encode).flatMap (htmlOfS T C A)).map (·.map cp037Code),
           true⟩)
  | [], _, stmts, htmls => by
    left
    refine ⟨by simp, ?_⟩
    simp [loop]
  | x :: xs, hxs, stmts, htmls => by
    have hx : CardXrefRecord.Valid x := hxs x (List.mem_cons_self ..)
    have hxs' : ∀ y ∈ xs, CardXrefRecord.Valid y := fun y hy => hxs y (List.mem_cons_of_mem _ hy)
    unfold loop
    dsimp only
    cases hfc : custs.find? (fun c => numOf (c.getD 0 default) == numOf (x.getD 1 default)) with
    | none =>
      right; left
      refine ⟨[], x, xs, rfl, by simp, hfc, ?_⟩
      simp
    | some c =>
      cases hfa : accts.find? (fun a => numOf (a.getD 0 default) == numOf (x.getD 2 default)) with
      | none =>
        right; right
        refine ⟨[], x, xs, c, rfl, by simp, hfc, hfa, ?_⟩
        simp
      | some a =>
        obtain ⟨hxok, -, -, -, -⟩ := xok_of_find hcusts haccts hx hfc hfa
        obtain ⟨hstmt, hhtml⟩ := stmt_html_of_find htrs hcusts haccts hx hfc hfa
        dsimp only
        rcases loop_trichotomy htrs hcusts haccts xs hxs'
            (stmts ++ modelStmtOf trs (strOf (x.getD 0 default)) c a)
            (htmls ++ modelHtmlOf trs (strOf (x.getD 0 default)) c a) with
          ⟨hall, hloop⟩ | ⟨pre, y, post, heq, hpre, hfy, hloop⟩ | ⟨pre, y, post, cy, heq, hpre, hfc', hfa', hloop⟩
        · left
          refine ⟨fun z hz => by rcases List.mem_cons.mp hz with rfl | hz; exact hxok; exact hall z hz, ?_⟩
          rw [hloop, ← hstmt, ← hhtml]
          simp [List.append_assoc]
        · right; left
          refine ⟨x :: pre, y, post, by simp [heq],
            fun z hz => by rcases List.mem_cons.mp hz with rfl | hz; exact hxok; exact hpre z hz,
            hfy, ?_⟩
          rw [hloop, ← hstmt, ← hhtml]
          simp [List.append_assoc]
        · right; right
          refine ⟨x :: pre, y, post, cy, by simp [heq],
            fun z hz => by rcases List.mem_cons.mp hz with rfl | hz; exact hxok; exact hpre z hz,
            hfc', hfa', ?_⟩
          rw [hloop, ← hstmt, ← hhtml]
          simp [List.append_assoc]

/-- **`CBSTM03A`'s COBOL run outputs what `Model.run` says**, for every valid input in `Domain`
and any initial storage `m0` with `m0.size = 178495` and `m0.read 175623 4 = [0, 0, 0, 0]`. -/
theorem cobol_outputs_any (m0 : Mem) (hm0 : m0.size = 178495)
    (hpsa : m0.read 175623 4 = [0, 0, 0, 0])
    (trs xrefs custs accts : List (List FVal))
    (htrs : ∀ r ∈ trs, TrnxRecord.Valid r)
    (hxrefs : ∀ x ∈ xrefs, CardXrefRecord.Valid x)
    (hcusts : ∀ c ∈ custs, CustomerRecord.Valid c)
    (haccts : ∀ a ∈ accts, AccountRecord.Valid a)
    (hD : Domain trs xrefs custs accts)
    (F : Nat) (hF : trs.length + xrefs.length + 100 ≤ F) :
    let res := Stm.run { addrSpace := asp } F (Stm.initState m0
      [(3, trs.map TrnxRecord.encode), (4, xrefs.map CardXrefRecord.encode),
       (5, custs.map CustomerRecord.encode), (6, accts.map AccountRecord.encode)])
    let o := Model.run trs xrefs custs accts
    (res.1 = .stop .goback ∨ res.1 = .fault (.abend (-1))) ∧
    ((displays res.2).drop 11).map (·.map cp037Code) = o.disp ∧
    (writes 1 res.2).map (·.map cp037Code) = o.stmtWrites ∧
    (writes 2 res.2).map (·.map cp037Code) = o.htmlWrites ∧
    abended res.1 = o.abended := by
  dsimp only
  obtain ⟨hne, hs, hG, hT, _⟩ := hD
  have htl : ∀ r ∈ trs.map TrnxRecord.encode, r.length = 350 ∧ AmtOk r := by
    intro r hr
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
    exact ⟨trnx_length (htrs r0 hr0), (trnx_fields (htrs r0 hr0)).2.2.2.2.2.2.2⟩
  have hne' : trs.map TrnxRecord.encode ≠ [] := by simp [hne]
  have hF' : (trs.map TrnxRecord.encode).length + (xrefs.map CardXrefRecord.encode).length + 100 ≤ F := by
    simpa using hF
  unfold Model.run
  rcases loop_trichotomy htrs hcusts haccts xrefs hxrefs [] [] with
    ⟨hall, hloop⟩ | ⟨pre, x, post, heq, hpre, hfc, hloop⟩ | ⟨pre, x, post, c, heq, hpre, hfc, hfa, hloop⟩
  · have hx' : ∀ y ∈ xrefs.map CardXrefRecord.encode,
        XOk (custs.map CustomerRecord.encode) (accts.map AccountRecord.encode) y := by
      intro y hy
      obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hy
      exact hall x0 hx0
    obtain ⟨hsig, hout, -⟩ := stm_run_sorted { addrSpace := asp } rfl (fun _ _ => rfl)
      m0 hm0 hpsa (trs.map TrnxRecord.encode) (xrefs.map CardXrefRecord.encode)
      (custs.map CustomerRecord.encode) (accts.map AccountRecord.encode)
      htl hne' hs hG hT hx' F hF'
    rw [hloop]
    refine ⟨Or.inl hsig, ?_, ?_, ?_, by rw [hsig]; rfl⟩
    · rw [displays_eq, hout, List.reverse_append, List.reverse_reverse, dispL_append,
        dispL_flatMap_evsOfS _ _ _ hs, List.append_nil,
        List.drop_eq_nil_of_le (by rw [length_dispL_walkDisplays]; exact Nat.le_refl 11), List.map_nil]
    · rw [writes_eq, hout, List.reverse_append, List.reverse_reverse, wrL_append,
        wrL_walkDisplays, List.nil_append, wrL1_flatMap_evsOfS _ hs]
      simp
    · rw [writes_eq, hout, List.reverse_append, List.reverse_reverse, wrL_append,
        wrL_walkDisplays, List.nil_append, wrL2_flatMap_evsOfS _ hs]
      simp
  · have hx : CardXrefRecord.Valid x := by
      apply hxrefs x; rw [heq]; simp
    have hxf := xref_fields hx
    have hkc := cust_findKey_none hcusts hx hfc
    have hpre' : ∀ y ∈ pre.map CardXrefRecord.encode,
        XOk (custs.map CustomerRecord.encode) (accts.map AccountRecord.encode) y := by
      intro y hy
      obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hy
      exact hpre x0 hx0
    have hxs' : xrefs.map CardXrefRecord.encode =
        pre.map CardXrefRecord.encode ++ CardXrefRecord.encode x :: post.map CardXrefRecord.encode := by
      simp [heq]
    obtain ⟨hsig, hout, -⟩ := stm_run_abort_cust { addrSpace := asp } rfl (fun _ _ => rfl)
      m0 hm0 hpsa (trs.map TrnxRecord.encode) (xrefs.map CardXrefRecord.encode)
      (custs.map CustomerRecord.encode) (accts.map AccountRecord.encode)
      htl hne' hG hT (pre.map CardXrefRecord.encode) (post.map CardXrefRecord.encode)
      (CardXrefRecord.encode x) hxs' hpre' (xref_length hx)
      (hxf.2.2.1.trans (congrArg some hxf.2.2.2.1.symm)) hkc F hF'
    rw [hloop]
    refine ⟨Or.inr hsig, ?_, ?_, ?_, by rw [hsig]; rfl⟩
    · rw [displays_eq, hout, List.reverse_append, List.reverse_append, List.reverse_reverse,
        dispL_append, dispL_append, dispL_flatMap_evsOf, List.nil_append,
        List.drop_left' length_dispL_walkDisplays, dispL_custMsg]
    · rw [writes_eq, hout, List.reverse_append, List.reverse_append, List.reverse_reverse,
        wrL_append, wrL_append, wrL_walkDisplays, wrL_custMsg, List.nil_append, List.append_nil,
        wrL1_flatMap_evsOf _ hs]
      simp
    · rw [writes_eq, hout, List.reverse_append, List.reverse_append, List.reverse_reverse,
        wrL_append, wrL_append, wrL_walkDisplays, wrL_custMsg, List.nil_append, List.append_nil,
        wrL2_flatMap_evsOf _ hs]
      simp
  · have hx : CardXrefRecord.Valid x := by
      apply hxrefs x; rw [heq]; simp
    have hxf := xref_fields hx
    have hcid_holds : ({ digits := 9 } : NumFmt).Holds {} (numOf (x.getD 1 default)) :=
      (field_num_decode cardXrefRecord_contig hx 1 16 9 { digits := 9 } (by decide) rfl rfl rfl).2.2
    obtain ⟨ic, hfkc, hic, hgetc⟩ := findKey_some
      (fun y hy => cust_key_beq (hcusts y hy) hcid_holds) hfc
    rw [← hxf.2.2.2.1] at hfkc
    have hcv : CustomerRecord.Valid c := hgetc ▸ hcusts _ (getD_mem_of_lt hic)
    have hcl : ((custs.map CustomerRecord.encode).getD ic []).length = 500 := by
      change ((custs.map CustomerRecord.encode).getD ic default).length = 500
      rw [getD_map_lt CustomerRecord.encode hic, hgetc, cust_length hcv]
    have hka := acct_findKey_none haccts hx hfa
    have hpre' : ∀ y ∈ pre.map CardXrefRecord.encode,
        XOk (custs.map CustomerRecord.encode) (accts.map AccountRecord.encode) y := by
      intro y hy
      obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hy
      exact hpre x0 hx0
    have hxs' : xrefs.map CardXrefRecord.encode =
        pre.map CardXrefRecord.encode ++ CardXrefRecord.encode x :: post.map CardXrefRecord.encode := by
      simp [heq]
    obtain ⟨hsig, hout, -⟩ := stm_run_abort_acct { addrSpace := asp } rfl (fun _ _ => rfl)
      m0 hm0 hpsa (trs.map TrnxRecord.encode) (xrefs.map CardXrefRecord.encode)
      (custs.map CustomerRecord.encode) (accts.map AccountRecord.encode)
      htl hne' hG hT (pre.map CardXrefRecord.encode) (post.map CardXrefRecord.encode)
      (CardXrefRecord.encode x) hxs' hpre' (xref_length hx)
      (hxf.2.2.1.trans (congrArg some hxf.2.2.2.1.symm))
      (hxf.2.2.2.2.2.2.1.trans (congrArg some hxf.2.2.2.2.2.2.2.1.symm))
      ic hfkc hcl hka F hF'
    rw [hloop]
    refine ⟨Or.inr hsig, ?_, ?_, ?_, by rw [hsig]; rfl⟩
    · rw [displays_eq, hout, List.reverse_append, List.reverse_append, List.reverse_reverse,
        dispL_append, dispL_append, dispL_flatMap_evsOf, List.nil_append,
        List.drop_left' length_dispL_walkDisplays, dispL_acctMsg]
    · rw [writes_eq, hout, List.reverse_append, List.reverse_append, List.reverse_reverse,
        wrL_append, wrL_append, wrL_walkDisplays, wrL_acctMsg, List.nil_append, List.append_nil,
        wrL1_flatMap_evsOf _ hs]
      simp
    · rw [writes_eq, hout, List.reverse_append, List.reverse_append, List.reverse_reverse,
        wrL_append, wrL_append, wrL_walkDisplays, wrL_acctMsg, List.nil_append, List.append_nil,
        wrL2_flatMap_evsOf _ hs]
      simp

#print axioms cobol_outputs_any

/-! ## 4. Harness initial storage `initMem` and `cobol_outputs` -/

/-- Run-length encoding of `init_mem.hex` (`(count, byte)` pairs). -/
def initMemRuns : List (Nat × UInt8) :=
  [ (214, 64), (4, 240), (110, 64), (10, 240), (1, 192), (9, 240), (198, 64), (20, 240),
    (14, 64), (9, 240), (270, 64), (9, 240), (41, 64), (3, 240), (168, 64), (11, 240),
    (1, 64), (11, 240), (1, 192), (11, 240), (1, 192), (11, 240), (1, 192), (30, 64),
    (11, 240), (1, 192), (11, 240), (1, 192), (198, 64), (13, 0), (1, 12), (8, 64),
    (10, 240), (1, 192), (53, 64), (3, 240), (1, 192), (174051, 64), (118, 0), (536, 64),
    (4, 0), (12, 64), (4, 0), (48, 64), (4, 240), (900, 64), (11, 240), (333, 64),
    (3, 240), (1, 192), (1000, 64) ]

def initMem : Mem := ⟨(initMemRuns.flatMap (fun p => List.replicate p.1 p.2)).toArray⟩

theorem initMem_size : initMem.size = 178495 := by
  have h : ∀ l : List (Nat × UInt8),
      (l.flatMap (fun p => List.replicate p.1 p.2)).length = (l.map Prod.fst).sum := by
    intro l; induction l with
    | nil => rfl
    | cons p ls ih => simp [List.flatMap_cons, List.length_replicate, ih]
  show (initMemRuns.flatMap (fun p => List.replicate p.1 p.2)).length = 178495
  rw [h]
  decide

def rleLookup : List (Nat × UInt8) → Nat → UInt8
  | [], _ => 0
  | (k, b) :: rest, i => if i < k then b else rleLookup rest (i - k)

theorem getD_flatMap_replicate : ∀ (runs : List (Nat × UInt8)) (i : Nat),
    (runs.flatMap (fun p => List.replicate p.1 p.2)).getD i 0 = rleLookup runs i
  | [], _ => rfl
  | (k, b) :: rest, i => by
    simp only [List.flatMap_cons, rleLookup, List.getD_eq_getElem?_getD]
    split <;> rename_i h
    · rw [List.getElem?_append_left (by simp [h]), List.getElem?_replicate, if_pos h]; rfl
    · rw [List.getElem?_append_right (by simp; omega), List.length_replicate,
          ← List.getD_eq_getElem?_getD, getD_flatMap_replicate rest]

theorem mem_get_toArray (l : List UInt8) (i : Nat) : (Mem.mk l.toArray).get i = l.getD i 0 := by
  simp [Mem.get]

theorem mem_read_4 (m : Mem) (o : Nat) :
    m.read o 4 = [m.get o, m.get (o + 1), m.get (o + 2), m.get (o + 3)] := rfl

theorem initMem_get (i : Nat) : initMem.get i = rleLookup initMemRuns i :=
  (mem_get_toArray _ i).trans (getD_flatMap_replicate initMemRuns i)

theorem initMem_psa : initMem.read 175623 4 = [0, 0, 0, 0] := by
  rw [mem_read_4, initMem_get, initMem_get, initMem_get, initMem_get]
  decide

/-- **`CBSTM03A`'s COBOL run from `initMem` outputs what `Model.run` says.** -/
theorem cobol_outputs (trs xrefs custs accts : List (List FVal))
    (htrs : ∀ r ∈ trs, TrnxRecord.Valid r)
    (hxrefs : ∀ x ∈ xrefs, CardXrefRecord.Valid x)
    (hcusts : ∀ c ∈ custs, CustomerRecord.Valid c)
    (haccts : ∀ a ∈ accts, AccountRecord.Valid a)
    (hD : Domain trs xrefs custs accts)
    (n : Nat) (hn : trs.length + xrefs.length < n) :
    let res := Stm.run { addrSpace := asp } (n + 100) (Stm.initState initMem
      [(3, trs.map TrnxRecord.encode), (4, xrefs.map CardXrefRecord.encode),
       (5, custs.map CustomerRecord.encode), (6, accts.map AccountRecord.encode)])
    let o := Model.run trs xrefs custs accts
    (res.1 = .stop .goback ∨ res.1 = .fault (.abend (-1))) ∧
    ((displays res.2).drop 11).map (·.map cp037Code) = o.disp ∧
    (writes 1 res.2).map (·.map cp037Code) = o.stmtWrites ∧
    (writes 2 res.2).map (·.map cp037Code) = o.htmlWrites ∧
    abended res.1 = o.abended :=
  cobol_outputs_any initMem initMem_size initMem_psa trs xrefs custs accts
    htrs hxrefs hcusts haccts hD (n + 100) (by omega)

end EquivLean.Modernize.Cbstm03a.Glue
