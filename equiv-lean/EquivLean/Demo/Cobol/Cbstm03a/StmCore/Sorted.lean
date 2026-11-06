/-
# A transaction file sorted by card: the statement of a card is its transactions

`4000-TRNXFILE-GET` scans the table of consecutive same-card groups (`grp trs`) up to the first
card above the cross-reference card `X` (`vis`) and writes the transactions of the groups with
card `X`.  When the transaction file is sorted by card (`CardsSorted`, byte order), that is
exactly the transactions of card `X` in file order (`ofCard X trs`): `trnxStmt_sorted` and its
companions, and `stm_run_sorted`, the whole run with the statements spelled that way.
-/
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Assembly

open Cobol Cobol.Stm

namespace Cobol.StmCore

/-- The transaction file is sorted by card number (`TRNX-CARD-NUM`, byte order). -/
def CardsSorted (trs : List (List UInt8)) : Prop :=
  trs.Pairwise (fun a b => Sem.cmpBytes (tCard a) (tCard b) ≠ .gt)

/-- The transactions of card `X`, in file order. -/
def ofCard (X : List UInt8) (trs : List (List UInt8)) : List (List UInt8) :=
  trs.filter (fun r => tCard r == X)

theorem cmpBytes_self : ∀ a : List UInt8, Sem.cmpBytes a a = .eq
  | [] => Sem.cmpBytes.eq_2 _ _ (fun _ _ _ _ h _ => by cases h)
  | x :: xs => by
    rw [Sem.cmpBytes.eq_1, if_neg (UInt8.lt_irrefl x), if_neg (UInt8.lt_irrefl x), cmpBytes_self xs]

theorem ne_of_cmpBytes_gt {a b : List UInt8} (h : Sem.cmpBytes a b = .gt) : a ≠ b := by
  rintro rfl
  rw [cmpBytes_self] at h
  cases h

/-! ## The groups of a file -/

theorem getLastD_mem_of_ne_nil {α : Type _} {l : List α} (d : α) (h : l ≠ []) : l.getLastD d ∈ l := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil h
  rw [List.getLastD_cons]
  exact List.getLastD_mem_cons

/-- The groups, in order, are the file; each group is nonempty and its records have its card. -/
theorem grp_props (rs : List (List UInt8)) :
    (grp rs).flatten = rs ∧ (∀ g ∈ grp rs, g ≠ []) ∧ ∀ g ∈ grp rs, ∀ r ∈ g, tCard r = gCard g := by
  induction rs using list_snoc_ind with
  | nil => simp [grp_nil]
  | snoc l a ih =>
    obtain ⟨hf, hn, hc⟩ := ih
    rw [grp_snoc]
    unfold grpSnoc
    split
    · rename_i g0 hlast
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
      rw [hys] at hf hn hc
      split
      · rename_i heq
        rw [hys, List.dropLast_concat]
        refine ⟨?_, ?_, ?_⟩
        · rw [← hf]
          simp
        · intro g hg
          rcases List.mem_append.mp hg with h | h
          · exact hn g (List.mem_append_left _ h)
          · simp only [List.mem_singleton] at h
            subst h
            simp
        · intro g hg r hr
          rcases List.mem_append.mp hg with h | h
          · exact hc g (List.mem_append_left _ h) r hr
          · simp only [List.mem_singleton] at h
            subst h
            have hgc : gCard (g0 ++ [a]) = tCard a := by
              simp [gCard, List.getLastD_eq_getLast?]
            rw [hgc]
            rcases List.mem_append.mp hr with h' | h'
            · rw [hc g0 (by simp) r h', heq]
            · simp only [List.mem_singleton] at h'
              rw [h']
      · refine ⟨?_, ?_, ?_⟩
        · rw [hys, ← hf]
          simp
        · intro g hg
          rcases List.mem_append.mp hg with h | h
          · rw [hys] at h
            exact hn g h
          · simp only [List.mem_singleton] at h
            subst h
            simp
        · intro g hg r hr
          rcases List.mem_append.mp hg with h | h
          · rw [hys] at h
            exact hc g h r hr
          · simp only [List.mem_singleton] at h
            subst h
            simp only [List.mem_singleton] at hr
            subst hr
            simp [gCard]
    · rename_i hnone
      have h0 : grp l = [] := List.getLast?_eq_none_iff.mp hnone
      rw [h0] at hf
      refine ⟨by rw [← hf]; simp, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_singleton] at hg
        subst hg
        simp
      · intro g hg r hr
        simp only [List.mem_singleton] at hg
        subst hg
        simp only [List.mem_singleton] at hr
        subst hr
        simp [gCard]

/-- In a sorted file, the cards of the groups do not decrease. -/
theorem grp_sorted (rs : List (List UInt8)) (hs : CardsSorted rs) :
    (grp rs).Pairwise (fun g h => Sem.cmpBytes (gCard g) (gCard h) ≠ .gt) := by
  obtain ⟨hf, hn, -⟩ := grp_props rs
  unfold CardsSorted at hs
  rw [← hf] at hs
  have hp := (List.pairwise_flatten.mp hs).2
  refine List.Pairwise.imp_of_mem ?_ hp
  intro g h hg hh H
  exact H _ (getLastD_mem_of_ne_nil [] (hn g hg)) _ (getLastD_mem_of_ne_nil [] (hn h hh))

/-! ## The scan for a card -/

theorem flatMap_vis (X : List UInt8) {β : Type _} (F : List (List UInt8) → List β)
    (hF : ∀ g, gCard g ≠ X → F g = []) :
    ∀ gs : List (List (List UInt8)), gs.Pairwise (fun g h => Sem.cmpBytes (gCard g) (gCard h) ≠ .gt) →
      (vis X gs).flatMap F = gs.flatMap F
  | [], _ => rfl
  | g :: gs, hp => by
    rw [List.pairwise_cons] at hp
    unfold vis
    rw [List.takeWhile_cons]
    split
    · rw [List.flatMap_cons, List.flatMap_cons]
      exact congrArg (F g ++ ·) (flatMap_vis X F hF gs hp.2)
    · rename_i hgt
      have hg : Sem.cmpBytes (gCard g) X = .gt := by
        revert hgt
        cases Sem.cmpBytes (gCard g) X <;> simp
      rw [List.flatMap_nil, List.flatMap_cons, hF g (ne_of_cmpBytes_gt hg)]
      symm
      rw [List.nil_append, List.flatMap_eq_nil_iff]
      intro h hh
      apply hF h
      intro he
      exact hp.1 h hh (he ▸ hg)

theorem foldl_skip (X : List UInt8) (hs : List (List (List UInt8))) (h : ∀ g ∈ hs, gCard g ≠ X) :
    ∀ acc, hs.foldl (accStep X) acc = acc := by
  induction hs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [List.foldl_cons, accStep, if_neg (h g (by simp))]
    exact ih (fun g' hg' => h g' (by simp [hg'])) acc

theorem foldl_vis (X : List UInt8) :
    ∀ gs : List (List (List UInt8)), gs.Pairwise (fun g h => Sem.cmpBytes (gCard g) (gCard h) ≠ .gt) →
      ∀ acc, (vis X gs).foldl (accStep X) acc = gs.foldl (accStep X) acc
  | [], _, _ => rfl
  | g :: gs, hp, acc => by
    rw [List.pairwise_cons] at hp
    unfold vis
    rw [List.takeWhile_cons]
    split
    · rw [List.foldl_cons, List.foldl_cons]
      exact foldl_vis X gs hp.2 _
    · rename_i hgt
      have hg : Sem.cmpBytes (gCard g) X = .gt := by
        revert hgt
        cases Sem.cmpBytes (gCard g) X <;> simp
      rw [List.foldl_nil, List.foldl_cons, accStep, if_neg (ne_of_cmpBytes_gt hg)]
      symm
      exact foldl_skip X gs (fun h hh he => hp.1 h hh (he ▸ hg)) acc

theorem flatMap_groups (X : List UInt8) {β : Type _} (f : List UInt8 → List β) :
    ∀ gs : List (List (List UInt8)), (∀ g ∈ gs, ∀ r ∈ g, tCard r = gCard g) →
      gs.flatMap (fun g => if gCard g = X then g.flatMap f else []) =
        (gs.flatten.filter (fun r => tCard r == X)).flatMap f
  | [], _ => rfl
  | g :: gs, hc => by
    rw [List.flatMap_cons, List.flatten_cons, List.filter_append, List.flatMap_append,
      flatMap_groups X f gs (fun g' hg' => hc g' (by simp [hg']))]
    congr 1
    split
    · rename_i he
      rw [List.filter_eq_self.mpr]
      intro r hr
      simp [hc g (by simp) r hr, he]
    · rename_i he
      rw [List.filter_eq_nil_iff.mpr, List.flatMap_nil]
      intro r hr
      simp [hc g (by simp) r hr, he]

theorem foldl_groups (X : List UInt8) :
    ∀ gs : List (List (List UInt8)), (∀ g ∈ gs, ∀ r ∈ g, tCard r = gCard g) →
      ∀ acc, gs.foldl (accStep X) acc = (gs.flatten.filter (fun r => tCard r == X)).foldl addAmt acc
  | [], _, _ => rfl
  | g :: gs, hc, acc => by
    rw [List.foldl_cons, List.flatten_cons, List.filter_append, List.foldl_append,
      foldl_groups X gs (fun g' hg' => hc g' (by simp [hg'])), accStep]
    congr 1
    split
    · rename_i he
      rw [List.filter_eq_self.mpr]
      intro r hr
      simp [hc g (by simp) r hr, he]
    · rename_i he
      rw [List.filter_eq_nil_iff.mpr, List.foldl_nil]
      intro r hr
      simp [hc g (by simp) r hr, he]

/-! ## The statement of a card -/

theorem scan_sorted (trs : List (List UInt8)) (hs : CardsSorted trs) (X : List UInt8) {β : Type _}
    (f : List UInt8 → List β) :
    (vis X (grp trs)).flatMap (fun g => if gCard g = X then g.flatMap f else []) =
      (ofCard X trs).flatMap f := by
  obtain ⟨hf, -, hc⟩ := grp_props trs
  rw [flatMap_vis X _ (fun g hg => if_neg hg) _ (grp_sorted trs hs), flatMap_groups X f _ hc, hf]
  rfl

theorem total_sorted (trs : List (List UInt8)) (hs : CardsSorted trs) (X : List UInt8) :
    (vis X (grp trs)).foldl (accStep X) 0 = (ofCard X trs).foldl addAmt 0 := by
  obtain ⟨hf, -, hc⟩ := grp_props trs
  rw [foldl_vis X _ (grp_sorted trs hs), foldl_groups X _ hc, hf]
  rfl

/-- **The `STMT-FILE` body of card `X`** from a sorted file: one line per transaction of the
card, in file order, then the total of their amounts and the closing lines. -/
theorem trnxStmt_sorted (trs : List (List UInt8)) (hs : CardsSorted trs) (X : List UInt8) :
    trnxStmt X (grp trs) =
      (ofCard X trs).map tranStmtR ++ tailStmt ((ofCard X trs).foldl addAmt 0) := by
  have hm : matchStmt X = fun g => if gCard g = X then g.flatMap (fun r => [tranStmtR r]) else [] := by
    funext g
    unfold matchStmt
    rw [List.map_eq_flatMap]
  unfold trnxStmt
  rw [hm, scan_sorted trs hs X, total_sorted trs hs X, ← List.map_eq_flatMap]

/-- The `HTML-FILE` body of card `X` from a sorted file. -/
theorem trnxHtml_sorted (trs : List (List UInt8)) (hs : CardsSorted trs) (X : List UInt8) :
    trnxHtml X (grp trs) = (ofCard X trs).flatMap tranHtmlR ++ tailHtml := by
  unfold trnxHtml
  rw [← scan_sorted trs hs X tranHtmlR]
  rfl

/-- The output events of card `X` from a sorted file. -/
theorem trnxEvents_sorted (trs : List (List UInt8)) (hs : CardsSorted trs) (X : List UInt8) :
    trnxEvents X (grp trs) =
      (ofCard X trs).flatMap tranEvents ++ tailEvents ((ofCard X trs).foldl addAmt 0) := by
  unfold trnxEvents
  rw [← scan_sorted trs hs X tranEvents, total_sorted trs hs X]
  rfl

/-- The `STMT-FILE` records of cross-reference record `x` from a sorted transaction file: the
statement head of its customer and account, the transactions of its card, their total. -/
def stmtOfS (trs custs accts : List (List UInt8)) (x : List UInt8) : List (List UInt8) :=
  headS (custOf custs x) (acctOf accts x) ++
    ((ofCard (xCard x) trs).map tranStmtR ++ tailStmt ((ofCard (xCard x) trs).foldl addAmt 0))

def htmlOfS (trs custs accts : List (List UInt8)) (x : List UInt8) : List (List UInt8) :=
  headH (custOf custs x) (acctOf accts x) ++ ((ofCard (xCard x) trs).flatMap tranHtmlR ++ tailHtml)

def evsOfS (trs custs accts : List (List UInt8)) (x : List UInt8) : List Event :=
  headE (custOf custs x) (acctOf accts x) ++
    ((ofCard (xCard x) trs).flatMap tranEvents ++ tailEvents ((ofCard (xCard x) trs).foldl addAmt 0))

theorem stmtOf_sorted (trs : List (List UInt8)) (hs : CardsSorted trs) (custs accts : List (List UInt8)) :
    stmtOf (grp trs) custs accts = stmtOfS trs custs accts := by
  funext x
  rw [stmtOf, stmtOfS, trnxStmt_sorted trs hs]

theorem htmlOf_sorted (trs : List (List UInt8)) (hs : CardsSorted trs) (custs accts : List (List UInt8)) :
    htmlOf (grp trs) custs accts = htmlOfS trs custs accts := by
  funext x
  rw [htmlOf, htmlOfS, trnxHtml_sorted trs hs]

theorem evsOf_sorted (trs : List (List UInt8)) (hs : CardsSorted trs) (custs accts : List (List UInt8)) :
    evsOf (grp trs) custs accts = evsOfS trs custs accts := by
  funext x
  rw [evsOf, evsOfS, trnxEvents_sorted trs hs]

/-- **`CBSTM03AB` on a transaction file sorted by card.**  `stm_run` with the statements spelled
out: the run ends with `GOBACK`; the output is, after the 11 walk `DISPLAY`s, for every
cross-reference record in order the events of its statement (`evsOfS`: head, the transactions
of its card in file order, their total); `STMT-FILE` and `HTML-FILE` hold the records
`stmtOfS` / `htmlOfS` of every cross-reference record; all files are closed. -/
theorem stm_run_sorted (env : Env) (hEnv : env.addrSpace = asp)
    (hOpen : ∀ f md, env.openError f md = none)
    (m0 : Mem) (hm0 : m0.size = 178495) (hpsa : m0.read 175623 4 = [0, 0, 0, 0])
    (trs xrefs custs accts : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350 ∧ AmtOk r) (hne : trs ≠ []) (hs : CardsSorted trs)
    (hG : (grp trs).length ≤ 50) (hT : ∀ g ∈ grp trs, g.length ≤ 10)
    (hx : ∀ x ∈ xrefs, XOk custs accts x)
    (F : Nat) (hF : trs.length + xrefs.length + 100 ≤ F) :
    StopAnd (fun st =>
        st.out = (xrefs.flatMap (evsOfS trs custs accts)).reverse ++ walkDisplays ∧
        ∃ q5 e5 q6 e6, st.files =
          [(1, { mode := none, recs := xrefs.flatMap (stmtOfS trs custs accts) }),
           (2, { mode := none, recs := xrefs.flatMap (htmlOfS trs custs accts) }),
           (3, { mode := none, recs := trs, pos := trs.length, eof := true }),
           (4, { mode := none, recs := xrefs, pos := xrefs.length, eof := true }),
           (5, { mode := none, recs := custs, pos := q5, eof := e5 }),
           (6, { mode := none, recs := accts, pos := q6, eof := e6 })])
      (Stm.run env F (Stm.initState m0 [(3, trs), (4, xrefs), (5, custs), (6, accts)])) := by
  obtain ⟨h1, h2, q5, e5, q6, e6, h3⟩ :=
    stm_run env hEnv hOpen m0 hm0 hpsa trs xrefs custs accts htl hne hG hT hx F hF
  refine ⟨h1, ?_, q5, e5, q6, e6, ?_⟩
  · rw [h2, evsOf_sorted trs hs]
  · rw [h3, stmtOf_sorted trs hs, htmlOf_sorted trs hs]
    simp

end Cobol.StmCore
