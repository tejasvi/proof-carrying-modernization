import EquivLean.Modernize.Cbtrn02c.Any.JavaRunWT
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunMS
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunTac
import EquivLean.Modernize.Cbtrn02c.ModelAny

/-!
# CBTRN02C → Java: the outputs after an abend

`WAb σ A s`: the `Result` at `A.r` has abended (return code 0) and its output lists hold the
outputs of the model state `s`.  `W_dup`: after `writeTransaction` found the id of the transaction
already written (it displayed the abend lines and set `abended`), the state holds `WAb` for the
model state with the abend lines displayed.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The `Result` object after an abend: its lists, return code 0, abended. -/
def ResAtAb (σ : State) (A : Addrs) : Prop :=
  ∃ fs, σ.heap A.r = some (.plain "Cbtrn02c$Result" fs) ∧
    Fields.get fs ("Cbtrn02c$Result", "displays") = some (.ref A.lD) ∧
    Fields.get fs ("Cbtrn02c$Result", "transactFileWrites") = some (.ref A.lT) ∧
    Fields.get fs ("Cbtrn02c$Result", "dalyrejsFileWrites") = some (.ref A.lR) ∧
    Fields.get fs ("Cbtrn02c$Result", "tcatbalFileWrites") = some (.ref A.lCW) ∧
    Fields.get fs ("Cbtrn02c$Result", "accountFileRewrites") = some (.ref A.lAR) ∧
    Fields.get fs ("Cbtrn02c$Result", "tcatbalFileRewrites") = some (.ref A.lCR) ∧
    Fields.get fs ("Cbtrn02c$Result", "returnCode") = some (.int 0) ∧
    Fields.get fs ("Cbtrn02c$Result", "abended") = some (.int 1)

/-- **The state of `run` after an abend** holds the outputs of the model state `s`. -/
def WAb (σ : State) (A : Addrs) (s : Model.St) : Prop :=
  ResAtAb σ A ∧ LStr σ A.lD (s.disp.map jline) ∧
  LRec σ A.lT TranRecord "Cbtrn02c$TranRecord" A.ws s.tranW ∧
  LRec σ A.lR RejectRecord "Cbtrn02c$RejectRecord" A.ws s.rejW ∧
  LRec σ A.lCW TranCatBalRecord "Cbtrn02c$TranCatBalRecord" A.ws s.catW ∧
  LRec σ A.lAR AccountRecord "Cbtrn02c$AccountRecord" A.ws s.acctRW ∧
  LRec σ A.lCR TranCatBalRecord "Cbtrn02c$TranCatBalRecord" A.ws s.catRW

/-- The model state of a posted transaction whose id was already written: the category balance
and the account updated, the transaction not written, the abend lines displayed. -/
def dupSt (s : Model.St) (t x a : List EquivLean.Cobol.Rec.FVal) : Model.St :=
  { postAcc (postCat s t x) t a with disp := (postAcc (postCat s t x) t a).disp ++ Model.dupLines }

/-- None of the objects `S` is a record object of class `cls` outside `ws`. -/
def NoRecC (σ : State) (ws : List Addr) (cls : ClassName) (S : List Addr) : Prop :=
  ∀ a ∈ S, a ∈ ws ∨ ∀ fs, σ.heap a ≠ some (.plain cls fs)

theorem LRec.frameC {σ σ' : State} {l : Addr} {s : Schema} {cls : ClassName} {ws S : List Addr}
    {vals : List (List EquivLean.Cobol.Rec.FVal)} (h : LRec σ l s cls ws vals) (hf : FrameS σ σ' S)
    (hS : NoStr σ S) (hR : NoRecC σ ws cls S) (hl : l ∉ S) : LRec σ' l s cls ws vals := by
  obtain ⟨xs, m, hh, hfs, hw, hn⟩ := h
  refine ⟨xs, m, hf.heap hh hl, ?_, hw, hn⟩
  refine forall2_imp_mem (fun v hv val hr => jrecAt_frame hr hf hS ?_) hfs
  rintro x rfl hxS
  rcases hR x hxS with hws | hnp
  · exact hw _ hv x hws rfl
  · obtain ⟨y, fs, hy, hx, _⟩ := hr
    cases hy
    exact hnp _ hx

theorem forall2_app {α β : Type} {R : α → β → Prop} {ys : List α} {ws : List β}
    (h2 : Forall2 R ys ws) : ∀ {xs : List α} {zs : List β}, Forall2 R xs zs →
      Forall2 R (xs ++ ys) (zs ++ ws)
  | _, _, .nil => h2
  | _, _, .cons h hs => .cons h (forall2_app h2 hs)

theorem jline_err : jline (Model.txt "ERROR WRITING TO TRANSACTION FILE") =
    JStr.ofString "ERROR WRITING TO TRANSACTION FILE" := by decide
theorem jline_st22 : jline (Model.txt "FILE STATUS IS: NNNN0022") =
    JStr.ofString "FILE STATUS IS: NNNN0022" := by decide
theorem jline_abend : jline (Model.txt "ABENDING PROGRAM") = JStr.ofString "ABENDING PROGRAM" := by
  decide

/-- The world after `writeTransaction` abended on a written id. -/
theorem W_dup {σ σ' : State} {A : Addrs} {s : Model.St} (hW : W σ A s) {y1 y2 y3 : Addr} {mD' : Nat}
    (hD' : σ'.heap A.lD = some (.list .arrayList (listOf σ A.lD ++ [.ref y1, .ref y2, .ref y3]) mD'))
    (h1 : σ'.heap y1 = some (.str (JStr.ofString "ERROR WRITING TO TRANSACTION FILE")))
    (h2 : σ'.heap y2 = some (.str (JStr.ofString "FILE STATUS IS: NNNN0022")))
    (h3 : σ'.heap y3 = some (.str (JStr.ofString "ABENDING PROGRAM")))
    (hr : σ'.heap A.r = some (.plain "Cbtrn02c$Result"
      (Fields.set (fieldsOf σ A.r) ("Cbtrn02c$Result", "abended") (.int 1))))
    (hf : FrameS σ σ' [A.lD, A.r]) (hlen : s.disp.length + 3 < 2147483648) :
    WAb σ' A { s with disp := s.disp ++ Model.dupLines } := by
  obtain ⟨hR, hD, hT, hRj, hCW, hAR, hCR, -, -, -, -, -, -, -, -, -, hnd⟩ := hW
  obtain ⟨fsR, hr0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := hR
  obtain ⟨xsD, mD, hlD, hfD, hnD⟩ := hD
  have hS : NoStr σ [A.lD, A.r] := by
    intro a ha t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · rw [hlD] at ht; cases ht
    · rw [hr0] at ht; cases ht
  have hN : ∀ cls, cls ≠ "Cbtrn02c$Result" → NoRecC σ A.ws cls [A.lD, A.r] := by
    intro cls hc a ha
    right
    intro fs h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · rw [hlD] at h; cases h
    · rw [hr0] at h
      simp only [Option.some.injEq, Obj.plain.injEq] at h
      exact hc h.1.symm
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨n1, n2, n3, n4, n5, -, -⟩, -⟩ := hnd
  have pr : ∀ {l xs m}, σ.heap l = some (.list .arrayList xs m) → l ≠ A.r := by
    intro l xs m hl h
    rw [h, hr0] at hl
    cases hl
  have nm : ∀ {l xs m}, σ.heap l = some (.list .arrayList xs m) → l ≠ A.lD → l ∉ [A.lD, A.r] :=
    fun hl hD => not_mem_pair hD (pr hl)
  rw [fieldsOf_of hr0] at hr
  refine ⟨⟨_, hr, by fget_simp; exact g1, by fget_simp; exact g2, by fget_simp; exact g3,
    by fget_simp; exact g4, by fget_simp; exact g5, by fget_simp; exact g6, by fget_simp; exact g7,
    by fget_simp⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [listOf_of hlD] at hD'
    refine ⟨xsD ++ [.ref y1, .ref y2, .ref y3], mD', hD', ?_, ?_⟩
    · simp only [List.map_append, Model.dupLines, List.map_cons, List.map_nil, jline_err, jline_st22,
        jline_abend]
      exact forall2_app (.cons ⟨y1, rfl, h1⟩ (.cons ⟨y2, rfl, h2⟩ (.cons ⟨y3, rfl, h3⟩ .nil)))
        (forall2_imp (fun _ _ h => jstrAt_frame h hf hS) hfD)
    · have := forall2_length hfD
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_map] at *
      omega
  · obtain ⟨xs, m, hl, -⟩ := id hT
    exact LRec.frameC hT hf hS (hN _ (by decide)) (nm hl (Ne.symm n1))
  · obtain ⟨xs, m, hl, -⟩ := id hRj
    exact LRec.frameC hRj hf hS (hN _ (by decide)) (nm hl (Ne.symm n2))
  · obtain ⟨xs, m, hl, -⟩ := id hCW
    exact LRec.frameC hCW hf hS (hN _ (by decide)) (nm hl (Ne.symm n3))
  · obtain ⟨xs, m, hl, -⟩ := id hAR
    exact LRec.frameC hAR hf hS (hN _ (by decide)) (nm hl (Ne.symm n4))
  · obtain ⟨xs, m, hl, -⟩ := id hCR
    exact LRec.frameC hCR hf hS (hN _ (by decide)) (nm hl (Ne.symm n5))

end EquivLean.Modernize.Cbtrn02c.Java
