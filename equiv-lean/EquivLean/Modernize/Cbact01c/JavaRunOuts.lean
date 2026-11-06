import EquivLean.Modernize.Cbact01c.JavaRunFrames

/-!
# CBACT01C → Java: the output lists, with their objects above a bound

`OutsB σ B ys1 ys2 ys3 ys4 s`: the four lists of the `Result` hold the outputs of the model state
`s` (`JStrAt`, `JRecAt`, `JRecOccAt` of the contract), every object they reach being above `B`
(newer than the `Result` lists). Such facts survive any step that changes no object above `B`
(`GrowsAbove`): the record methods change only the lists, at `B` and below.
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

/-- No object above `B` changes. -/
def GrowsAbove (B : Addr) (σ σ' : Jimple.State) : Prop :=
  σ.next ≤ σ'.next ∧ ∀ x, B < x → x < σ.next → σ'.heap x = σ.heap x

theorem GrowsAbove.trans {B : Addr} {σ1 σ2 σ3 : Jimple.State} (h1 : GrowsAbove B σ1 σ2)
    (h2 : GrowsAbove B σ2 σ3) : GrowsAbove B σ1 σ3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun x hb hx => by
    rw [h2.2 x hb (Nat.lt_of_lt_of_le hx h1.1), h1.2 x hb hx]⟩

theorem GrowsAbove.heap {B : Addr} {σ σ' : Jimple.State} (h : GrowsAbove B σ σ') {x : Addr}
    {o : Obj} (hb : B < x) (hx : σ.heap x = some o) : σ'.heap x = some o := by
  rw [h.2 x hb (State.lt_next_of_heap hx), hx]

/-- `w` refers to the string `t`, an object above `B`. -/
def JStrB (σ : Jimple.State) (B : Addr) (w : Value) (t : JStr) : Prop :=
  ∃ x, w = .ref x ∧ B < x ∧ σ.heap x = some (.str t)

/-- `jFieldAt` with the string (if any) above `B`. -/
def jFieldB (σ : Jimple.State) (B : Addr) (cls : ClassName) (fs : List (FieldKey × Value))
    (f : Field) : EquivLean.Cobol.Rec.FVal → Prop
  | .num v => Fields.get fs (cls, f.jname) = some (.long (BitVec.ofInt 64 v))
  | .str bs => ∃ s, Fields.get fs (cls, f.jname) = some s ∧ JStrB σ B s (cp037Str bs)

/-- `JRecAt` with the objects above `B`. -/
def JRecB (s : Schema) (cls : ClassName) (σ : Jimple.State) (B : Addr) (v : Value)
    (vals : List EquivLean.Cobol.Rec.FVal) : Prop :=
  ∃ x fs, v = .ref x ∧ B < x ∧ σ.heap x = some (.plain cls fs) ∧
    Forall2 (fun f val => jFieldB σ B cls fs f val) s.fields vals

/-- `jValAt` with the string (if any) above `B`. -/
def jValB (σ : Jimple.State) (B : Addr) (e : Value) : EquivLean.Cobol.Rec.FVal → Prop
  | .num v => e = .long (BitVec.ofInt 64 v)
  | .str bs => JStrB σ B e (cp037Str bs)

/-- `jFieldOccAt` with the objects above `B`. -/
def jFieldOccB (σ : Jimple.State) (B : Addr) (cls : ClassName) (fs : List (FieldKey × Value))
    (f : Field) (val : EquivLean.Cobol.Rec.FVal) : Prop :=
  match f.idx with
  | [] => jFieldB σ B cls fs f val
  | [k] => ∃ a et xs, Fields.get fs (cls, f.jname) = some (.ref a) ∧ B < a ∧
      σ.heap a = some (.array et xs) ∧ jValB σ B (xs.getD k .null) val
  | _ :: _ :: _ => False

/-- `JRecOccAt` with the objects above `B`. -/
def JRecOccB (s : Schema) (cls : ClassName) (σ : Jimple.State) (B : Addr) (v : Value)
    (vals : List EquivLean.Cobol.Rec.FVal) : Prop :=
  ∃ x fs, v = .ref x ∧ B < x ∧ σ.heap x = some (.plain cls fs) ∧
    Forall2 (fun f val => jFieldOccB σ B cls fs f val) s.fields vals

/-- The four lists hold the outputs of `s`, their objects above `B`. -/
def OutsB (σ : Jimple.State) (B : Addr) (ys1 ys2 ys3 ys4 : List Value) (s : Model.St) : Prop :=
  Forall2 (JStrB σ B) ys1 (s.disp.map jline) ∧
  Forall2 (JRecB OutAcctRec outCls σ B) ys2 s.outWrites ∧
  Forall2 (JRecOccB ArrArrayRec arrCls σ B) ys3 s.arryWrites ∧
  Forall2 (JStrB σ B) ys4 (s.vbrcWrites.map jline)

/-! ## Transport -/

theorem forall2_mono' {α β : Type} {R R' : α → β → Prop} (hR : ∀ x y, R x y → R' x y) :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → Forall2 R' xs ys
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (hR _ _ h) (forall2_mono' hR t)

theorem JStrB.grows {B : Addr} {σ σ' : Jimple.State} (hg : GrowsAbove B σ σ') {w : Value}
    {t : JStr} (h : JStrB σ B w t) : JStrB σ' B w t := by
  obtain ⟨x, rfl, hb, hx⟩ := h
  exact ⟨x, rfl, hb, hg.heap hb hx⟩

theorem jFieldB.grows {B : Addr} {σ σ' : Jimple.State} (hg : GrowsAbove B σ σ') {cls : ClassName}
    {fs : List (FieldKey × Value)} {f : Field} {val : EquivLean.Cobol.Rec.FVal}
    (h : jFieldB σ B cls fs f val) : jFieldB σ' B cls fs f val := by
  cases val with
  | num v => exact h
  | str bs => obtain ⟨s, hs, hj⟩ := h; exact ⟨s, hs, hj.grows hg⟩

theorem JRecB.grows {B : Addr} {σ σ' : Jimple.State} (hg : GrowsAbove B σ σ') {s : Schema}
    {cls : ClassName} {v : Value} {vals : List EquivLean.Cobol.Rec.FVal}
    (h : JRecB s cls σ B v vals) : JRecB s cls σ' B v vals := by
  obtain ⟨x, fs, rfl, hb, hx, hf⟩ := h
  exact ⟨x, fs, rfl, hb, hg.heap hb hx, forall2_mono' (fun _ _ h => jFieldB.grows hg h) hf⟩

theorem jValB.grows {B : Addr} {σ σ' : Jimple.State} (hg : GrowsAbove B σ σ') {e : Value}
    {val : EquivLean.Cobol.Rec.FVal} (h : jValB σ B e val) : jValB σ' B e val := by
  cases val with
  | num v => exact h
  | str bs => exact JStrB.grows hg h

theorem jFieldOccB.grows {B : Addr} {σ σ' : Jimple.State} (hg : GrowsAbove B σ σ')
    {cls : ClassName} {fs : List (FieldKey × Value)} {f : Field} {val : EquivLean.Cobol.Rec.FVal}
    (h : jFieldOccB σ B cls fs f val) : jFieldOccB σ' B cls fs f val := by
  unfold jFieldOccB at h ⊢
  split
  · rename_i heq; rw [heq] at h; exact jFieldB.grows hg h
  · rename_i k heq
    rw [heq] at h
    obtain ⟨a, et, xs, ha, hb, hax, hv⟩ := h
    exact ⟨a, et, xs, ha, hb, hg.heap hb hax, jValB.grows hg hv⟩
  · rename_i heq; rw [heq] at h; exact h

theorem JRecOccB.grows {B : Addr} {σ σ' : Jimple.State} (hg : GrowsAbove B σ σ') {s : Schema}
    {cls : ClassName} {v : Value} {vals : List EquivLean.Cobol.Rec.FVal}
    (h : JRecOccB s cls σ B v vals) : JRecOccB s cls σ' B v vals := by
  obtain ⟨x, fs, rfl, hb, hx, hf⟩ := h
  exact ⟨x, fs, rfl, hb, hg.heap hb hx, forall2_mono' (fun _ _ h => jFieldOccB.grows hg h) hf⟩

theorem OutsB.grows {B : Addr} {σ σ' : Jimple.State} (hg : GrowsAbove B σ σ')
    {ys1 ys2 ys3 ys4 : List Value} {s : Model.St} (h : OutsB σ B ys1 ys2 ys3 ys4 s) :
    OutsB σ' B ys1 ys2 ys3 ys4 s :=
  ⟨forall2_mono' (fun _ _ h => JStrB.grows hg h) h.1,
   forall2_mono' (fun _ _ h => JRecB.grows hg h) h.2.1,
   forall2_mono' (fun _ _ h => JRecOccB.grows hg h) h.2.2.1,
   forall2_mono' (fun _ _ h => JStrB.grows hg h) h.2.2.2⟩

/-! ## The contract's relations -/

theorem JStrB.strAt {σ : Jimple.State} {B : Addr} {w : Value} {t : JStr} (h : JStrB σ B w t) :
    JStrAt σ w t := by
  obtain ⟨x, rfl, -, hx⟩ := h; exact ⟨x, rfl, hx⟩

theorem JRecB.recAt {σ : Jimple.State} {B : Addr} {s : Schema} {cls : ClassName} {v : Value}
    {vals : List EquivLean.Cobol.Rec.FVal} (h : JRecB s cls σ B v vals) : JRecAt s cls σ v vals := by
  obtain ⟨x, fs, rfl, -, hx, hf⟩ := h
  refine ⟨x, fs, rfl, hx, forall2_mono' (fun f val h => ?_) hf⟩
  cases val with
  | num v => exact h
  | str bs => obtain ⟨s', hs, hj⟩ := h; exact ⟨s', hs, hj.strAt⟩

theorem JRecOccB.recOccAt {σ : Jimple.State} {B : Addr} {s : Schema} {cls : ClassName} {v : Value}
    {vals : List EquivLean.Cobol.Rec.FVal} (h : JRecOccB s cls σ B v vals) :
    JRecOccAt s cls σ v vals := by
  obtain ⟨x, fs, rfl, -, hx, hf⟩ := h
  refine ⟨x, fs, rfl, hx, forall2_mono' (fun f val h => ?_) hf⟩
  unfold jFieldOccB at h
  unfold jFieldOccAt
  split
  · rename_i heq; rw [heq] at h
    cases val with
    | num v => exact h
    | str bs => obtain ⟨s', hs, hj⟩ := h; exact ⟨s', hs, hj.strAt⟩
  · rename_i k heq; rw [heq] at h
    obtain ⟨a, et, xs, ha, -, hax, hv⟩ := h
    refine ⟨a, et, xs, ha, hax, ?_⟩
    cases val with
    | num v => exact hv
    | str bs => exact JStrB.strAt hv
  · rename_i heq; rw [heq] at h; exact h

end EquivLean.Modernize.Cbact01c.Java
