import EquivLean.Modernize.Cbtrn02c.Any.JavaRunB
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunR1

/-!
# CBTRN02C → Java: the state of `run` between two transactions

`W σ A s`: the objects of `run` at the addresses `A` hold the model state `s`: the `Result` and its
output lists (displays, records written and rewritten), the account array and the category list
(the files), the list of transaction ids written, the work-storage records.  The record objects in
the lists are not the work-storage objects (`ws`).  `W` survives allocation (`Grows`) and updates
of objects it does not describe.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The addresses of `run`'s objects. -/
structure Addrs where
  r : Addr
  lD : Addr
  lT : Addr
  lR : Addr
  lCW : Addr
  lAR : Addr
  lCR : Addr
  aD : Addr
  lC : Addr
  lK : Addr
  wX : Addr
  wA : Addr
  wC : Addr
  wT : Addr

/-- The work-storage objects. -/
def Addrs.ws (A : Addrs) : List Addr := [A.wX, A.wA, A.wC, A.wT]

/-- The list object at `l` holds record objects of schema `s` (class `cls`) with the field values
`vals`; none is in `ws`. -/
def LRec (σ : State) (l : Addr) (s : Schema) (cls : ClassName) (ws : List Addr)
    (vals : List (List EquivLean.Cobol.Rec.FVal)) : Prop :=
  ∃ xs m, σ.heap l = some (.list .arrayList xs m) ∧ Forall2 (JRecAt s cls σ) xs vals ∧
    (∀ v ∈ xs, ∀ w ∈ ws, v ≠ .ref w) ∧ xs.length < 2147483648

/-- The array at `a` holds record objects of schema `s` with the field values `vals`. -/
def ARec (σ : State) (a : Addr) (s : Schema) (cls : ClassName) (ws : List Addr)
    (vals : List (List EquivLean.Cobol.Rec.FVal)) : Prop :=
  ∃ et xs, σ.heap a = some (.array et xs) ∧ Forall2 (JRecAt s cls σ) xs vals ∧
    (∀ v ∈ xs, ∀ w ∈ ws, v ≠ .ref w) ∧ xs.length < 2147483648

/-- The list object at `l` holds strings with the texts `strs`. -/
def LStr (σ : State) (l : Addr) (strs : List JStr) : Prop :=
  ∃ xs m, σ.heap l = some (.list .arrayList xs m) ∧ Forall2 (JStrAt σ) xs strs ∧
    xs.length < 2147483648

/-- The `Result` object: its lists, return code 0, not abended. -/
def ResAt (σ : State) (A : Addrs) : Prop :=
  ∃ fs, σ.heap A.r = some (.plain "Cbtrn02c$Result" fs) ∧
    Fields.get fs ("Cbtrn02c$Result", "displays") = some (.ref A.lD) ∧
    Fields.get fs ("Cbtrn02c$Result", "transactFileWrites") = some (.ref A.lT) ∧
    Fields.get fs ("Cbtrn02c$Result", "dalyrejsFileWrites") = some (.ref A.lR) ∧
    Fields.get fs ("Cbtrn02c$Result", "tcatbalFileWrites") = some (.ref A.lCW) ∧
    Fields.get fs ("Cbtrn02c$Result", "accountFileRewrites") = some (.ref A.lAR) ∧
    Fields.get fs ("Cbtrn02c$Result", "tcatbalFileRewrites") = some (.ref A.lCR) ∧
    Fields.get fs ("Cbtrn02c$Result", "returnCode") = some (.int 0) ∧
    Fields.get fs ("Cbtrn02c$Result", "abended") = some (.int 0)

/-- A work-storage object of class `cls` with all the fields `keys`. -/
def WSObj (σ : State) (w : Addr) (cls : ClassName) (keys : List FieldKey) : Prop :=
  ∃ fs, σ.heap w = some (.plain cls fs) ∧ ∀ k ∈ keys, (Fields.get fs k).isSome

/-- The `FILLER` of the work-storage object `w` holds `fill`. -/
def WSFill (σ : State) (w : Addr) (cls : ClassName) (fill : List UInt8) : Prop :=
  ∃ fs sv, σ.heap w = some (.plain cls fs) ∧ Fields.get fs (cls, "filler1") = some sv ∧
    JStrAt σ sv (cp037Str fill)

/-- The text of the id of a written transaction record. -/
def tidJ (r : List EquivLean.Cobol.Rec.FVal) : JStr := cp037Str (Model.strOf (r.getD 0 default))

/-- The field keys of a schema in a class. -/
def keysOf (s : Schema) (cls : ClassName) : List FieldKey := s.fields.map fun f => (cls, f.jname)

/-- **The state of `run` between two transactions** holds the model state `s`. -/
def W (σ : State) (A : Addrs) (s : Model.St) : Prop :=
  ResAt σ A ∧ LStr σ A.lD (s.disp.map jline) ∧
  LRec σ A.lT TranRecord "Cbtrn02c$TranRecord" A.ws s.tranW ∧
  LRec σ A.lR RejectRecord "Cbtrn02c$RejectRecord" A.ws s.rejW ∧
  LRec σ A.lCW TranCatBalRecord "Cbtrn02c$TranCatBalRecord" A.ws s.catW ∧
  LRec σ A.lAR AccountRecord "Cbtrn02c$AccountRecord" A.ws s.acctRW ∧
  LRec σ A.lCR TranCatBalRecord "Cbtrn02c$TranCatBalRecord" A.ws s.catRW ∧
  ARec σ A.aD AccountRecord "Cbtrn02c$AccountRecord" A.ws s.accts ∧
  LRec σ A.lC TranCatBalRecord "Cbtrn02c$TranCatBalRecord" A.ws s.cats ∧
  LStr σ A.lK (s.tranW.map tidJ) ∧
  WSObj σ A.wX "Cbtrn02c$CardXrefRecord" (keysOf CardXrefRecord "Cbtrn02c$CardXrefRecord") ∧
  WSObj σ A.wA "Cbtrn02c$AccountRecord" (keysOf AccountRecord "Cbtrn02c$AccountRecord") ∧
  WSObj σ A.wC "Cbtrn02c$TranCatBalRecord" (keysOf TranCatBalRecord "Cbtrn02c$TranCatBalRecord") ∧
  WSObj σ A.wT "Cbtrn02c$TranRecord" (keysOf TranRecord "Cbtrn02c$TranRecord") ∧
  WSFill σ A.wC "Cbtrn02c$TranCatBalRecord" s.catFill ∧
  WSFill σ A.wT "Cbtrn02c$TranRecord" (Model.sp 20) ∧
  [A.lD, A.lT, A.lR, A.lCW, A.lAR, A.lCR, A.lC, A.lK].Nodup

/-! ## Along `Grows` -/

theorem LRec.grows {σ σ' : State} {l : Addr} {s : Schema} {cls : ClassName} {ws : List Addr}
    {vals : List (List EquivLean.Cobol.Rec.FVal)} (h : LRec σ l s cls ws vals) (hg : Grows σ σ') :
    LRec σ' l s cls ws vals := by
  obtain ⟨xs, m, hl, hf, hw, hn⟩ := h
  exact ⟨xs, m, by rw [hg.2 l (State.lt_next_of_heap hl)]; exact hl,
    forall2_imp (fun _ _ h => jrecAt_grows h hg) hf, hw, hn⟩

theorem ARec.grows {σ σ' : State} {a : Addr} {s : Schema} {cls : ClassName} {ws : List Addr}
    {vals : List (List EquivLean.Cobol.Rec.FVal)} (h : ARec σ a s cls ws vals) (hg : Grows σ σ') :
    ARec σ' a s cls ws vals := by
  obtain ⟨et, xs, hl, hf, hw, hn⟩ := h
  exact ⟨et, xs, by rw [hg.2 a (State.lt_next_of_heap hl)]; exact hl,
    forall2_imp (fun _ _ h => jrecAt_grows h hg) hf, hw, hn⟩

theorem LStr.grows {σ σ' : State} {l : Addr} {strs : List JStr} (h : LStr σ l strs)
    (hg : Grows σ σ') : LStr σ' l strs := by
  obtain ⟨xs, m, hl, hf, hn⟩ := h
  exact ⟨xs, m, by rw [hg.2 l (State.lt_next_of_heap hl)]; exact hl,
    forall2_imp (fun _ _ h => jstrAt_grows h hg) hf, hn⟩

theorem ResAt.grows {σ σ' : State} {A : Addrs} (h : ResAt σ A) (hg : Grows σ σ') : ResAt σ' A := by
  obtain ⟨fs, hr, h1⟩ := h
  exact ⟨fs, by rw [hg.2 _ (State.lt_next_of_heap hr)]; exact hr, h1⟩

theorem WSObj.grows {σ σ' : State} {w : Addr} {cls : ClassName} {keys : List FieldKey}
    (h : WSObj σ w cls keys) (hg : Grows σ σ') : WSObj σ' w cls keys := by
  obtain ⟨fs, hw, hk⟩ := h
  exact ⟨fs, by rw [hg.2 _ (State.lt_next_of_heap hw)]; exact hw, hk⟩

theorem WSFill.grows {σ σ' : State} {w : Addr} {cls : ClassName} {fill : List UInt8}
    (h : WSFill σ w cls fill) (hg : Grows σ σ') : WSFill σ' w cls fill := by
  obtain ⟨fs, sv, hw, hf, hs⟩ := h
  exact ⟨fs, sv, by rw [hg.2 _ (State.lt_next_of_heap hw)]; exact hw, hf, jstrAt_grows hs hg⟩

theorem W.grows {σ σ' : State} {A : Addrs} {s : Model.St} (h : W σ A s) (hg : Grows σ σ') :
    W σ' A s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1.grows hg, h2.grows hg, h3.grows hg, h4.grows hg, h5.grows hg, h6.grows hg, h7.grows hg,
    h8.grows hg, h9.grows hg, h10.grows hg, h11.grows hg, h12.grows hg, h13.grows hg, h14.grows hg,
    h15.grows hg, h16.grows hg, h17⟩

/-! ## Along updates of a few objects -/

/-- The heap grows, and the objects of `σ` outside `S` are unchanged. -/
def FrameS (σ σ' : State) (S : List Addr) : Prop :=
  σ.next ≤ σ'.next ∧ ∀ z, z < σ.next → z ∉ S → σ'.heap z = σ.heap z

/-- The objects at `S` are no strings. -/
def NoStr (σ : State) (S : List Addr) : Prop := ∀ a ∈ S, ∀ t, σ.heap a ≠ some (.str t)

theorem FrameS.of_grows {σ σ' : State} (h : Grows σ σ') (S : List Addr) : FrameS σ σ' S :=
  ⟨h.1, fun z hz _ => h.2 z hz⟩

theorem FrameS.trans {σ1 σ2 σ3 : State} {S : List Addr} (h1 : FrameS σ1 σ2 S) (h2 : FrameS σ2 σ3 S) :
    FrameS σ1 σ3 S :=
  ⟨Nat.le_trans h1.1 h2.1, fun z hz hS => by
    rw [h2.2 z (Nat.lt_of_lt_of_le hz h1.1) hS, h1.2 z hz hS]⟩

theorem FrameS.heap {σ σ' : State} {S : List Addr} {z : Addr} {o : Obj} (h : FrameS σ σ' S)
    (hz : σ.heap z = some o) (hS : z ∉ S) : σ'.heap z = some o := by
  rw [h.2 z (State.lt_next_of_heap hz) hS]; exact hz

theorem jstrAt_frame {σ σ' : State} {S : List Addr} {v : Value} {s : JStr} (h : JStrAt σ v s)
    (hf : FrameS σ σ' S) (hS : NoStr σ S) : JStrAt σ' v s := by
  obtain ⟨x, rfl, hx⟩ := h
  have : x ∉ S := fun hm => hS x hm s hx
  exact ⟨x, rfl, hf.heap hx this⟩

theorem jrecAt_frame {s : Schema} {cls : ClassName} {σ σ' : State} {S : List Addr} {v : Value}
    {vals : List EquivLean.Cobol.Rec.FVal} (h : JRecAt s cls σ v vals) (hf : FrameS σ σ' S)
    (hS : NoStr σ S) (hv : ∀ x, v = .ref x → x ∉ S) : JRecAt s cls σ' v vals := by
  obtain ⟨x, fs, rfl, hx, hfs⟩ := h
  refine ⟨x, fs, rfl, hf.heap hx (hv x rfl), ?_⟩
  exact forall2_imp (fun f val h => jFieldAt_mono (fun v s h' => jstrAt_frame h' hf hS) h) hfs

/-- The objects at `S` are work-storage objects or not records. -/
def NoRec (σ : State) (ws S : List Addr) : Prop :=
  ∀ a ∈ S, a ∈ ws ∨ ∀ c fs, σ.heap a ≠ some (.plain c fs)

theorem LRec.frame {σ σ' : State} {l : Addr} {s : Schema} {cls : ClassName} {ws S : List Addr}
    {vals : List (List EquivLean.Cobol.Rec.FVal)} (h : LRec σ l s cls ws vals) (hf : FrameS σ σ' S)
    (hS : NoStr σ S) (hR : NoRec σ ws S) (hl : l ∉ S) : LRec σ' l s cls ws vals := by
  obtain ⟨xs, m, hh, hfs, hw, hn⟩ := h
  refine ⟨xs, m, hf.heap hh hl, ?_, hw, hn⟩
  refine forall2_imp_mem (fun v hv val hr => jrecAt_frame hr hf hS ?_) hfs
  rintro x rfl hxS
  rcases hR x hxS with hws | hnp
  · exact hw _ hv x hws rfl
  · obtain ⟨y, fs, hy, hx, _⟩ := hr
    cases hy
    exact hnp _ _ hx

theorem ARec.frame {σ σ' : State} {a : Addr} {s : Schema} {cls : ClassName} {ws S : List Addr}
    {vals : List (List EquivLean.Cobol.Rec.FVal)} (h : ARec σ a s cls ws vals) (hf : FrameS σ σ' S)
    (hS : NoStr σ S) (hR : NoRec σ ws S) (ha : a ∉ S) : ARec σ' a s cls ws vals := by
  obtain ⟨et, xs, hh, hfs, hw, hn⟩ := h
  refine ⟨et, xs, hf.heap hh ha, ?_, hw, hn⟩
  refine forall2_imp_mem (fun v hv val hr => jrecAt_frame hr hf hS ?_) hfs
  rintro x rfl hxS
  rcases hR x hxS with hws | hnp
  · exact hw _ hv x hws rfl
  · obtain ⟨y, fs, hy, hx, _⟩ := hr
    cases hy
    exact hnp _ _ hx

theorem LStr.frame {σ σ' : State} {l : Addr} {strs : List JStr} {S : List Addr}
    (h : LStr σ l strs) (hf : FrameS σ σ' S) (hS : NoStr σ S) (hl : l ∉ S) : LStr σ' l strs := by
  obtain ⟨xs, m, hh, hfs, hn⟩ := h
  exact ⟨xs, m, hf.heap hh hl, forall2_imp (fun _ _ h => jstrAt_frame h hf hS) hfs, hn⟩

theorem ResAt.frame {σ σ' : State} {A : Addrs} {S : List Addr} (h : ResAt σ A)
    (hf : FrameS σ σ' S) (hr : A.r ∉ S) : ResAt σ' A := by
  obtain ⟨fs, hh, h1⟩ := h
  exact ⟨fs, hf.heap hh hr, h1⟩

theorem WSObj.frame {σ σ' : State} {w : Addr} {cls : ClassName} {keys : List FieldKey} {S : List Addr}
    (h : WSObj σ w cls keys) (hf : FrameS σ σ' S) (hw : w ∉ S) : WSObj σ' w cls keys := by
  obtain ⟨fs, hh, hk⟩ := h
  exact ⟨fs, hf.heap hh hw, hk⟩

theorem WSFill.frame {σ σ' : State} {w : Addr} {cls : ClassName} {fill : List UInt8} {S : List Addr}
    (h : WSFill σ w cls fill) (hf : FrameS σ σ' S) (hS : NoStr σ S) (hw : w ∉ S) :
    WSFill σ' w cls fill := by
  obtain ⟨fs, sv, hh, h1, h2⟩ := h
  exact ⟨fs, sv, hf.heap hh hw, h1, jstrAt_frame h2 hf hS⟩

end EquivLean.Modernize.Cbtrn02c.Java
