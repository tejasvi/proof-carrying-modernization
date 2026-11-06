import EquivLean.Modernize.Cbtrn01c.JavaRunRecords

/-!
# CBTRN01C → Java: heap facts carried along `run`

The predicates of the invariants (`CurAt`, `ResAt`, `ListAt`, the input records, `DalOk`,
`dalLine`) survive a callee (`Grows`) and an update of the `displays` list (`setObj` of a list
object), and the lines list grows by one line on `add`.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

/-! ## `Forall2` -/

theorem forall2_mono {α β : Type} {R R' : α → β → Prop} (hR : ∀ x y, R x y → R' x y) :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → Forall2 R' xs ys
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (hR _ _ h) (forall2_mono hR hs)

theorem forall2_append_one {α β : Type} {R : α → β → Prop} {x : α} {y : β} (hxy : R x y) :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → Forall2 R (xs ++ [x]) (ys ++ [y])
  | [], [], .nil => .cons hxy .nil
  | _ :: _, _ :: _, .cons h hs => .cons h (forall2_append_one hxy hs)

theorem forall2_get {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} (h : Forall2 R xs ys) (n : Nat) (hn : n < xs.length),
      R xs[n] (ys[n]'(by rw [← h.length_eq]; exact hn))
  | [], [], .nil, n, hn => by simp at hn
  | _ :: _, _ :: _, .cons h _, 0, _ => by simpa using h
  | _ :: _, _ :: _, .cons _ hs, n + 1, hn => by
      simpa using forall2_get hs n (by simpa using hn)

/-! ## The heap grows -/

theorem jstrAt_of_grows {σ σ' : State} {v : Value} {s : JStr} (hg : Grows σ σ')
    (h : JStrAt σ v s) : JStrAt σ' v s := by
  obtain ⟨x, rfl, hx⟩ := h
  exact ⟨x, rfl, heap_of_grows hg hx⟩

theorem curAt_of_grows {σ σ' : State} {d : Value} {t : List EquivLean.Cobol.Rec.FVal} (hg : Grows σ σ')
    (h : CurAt σ d t) : CurAt σ' d t := by
  obtain ⟨x, fs, c, i, rfl, hx, hc, hcs, hi, his⟩ := h
  exact ⟨x, fs, c, i, rfl, heap_of_grows hg hx, hc, heap_of_grows hg hcs, hi, heap_of_grows hg his⟩

theorem resAt_of_grows {σ σ' : State} {res l : Addr} (hg : Grows σ σ') (h : ResAt σ res l) :
    ResAt σ' res l := by
  obtain ⟨fs, hr, h1, h2⟩ := h
  exact ⟨fs, heap_of_grows hg hr, h1, h2⟩

theorem jFieldAt_of_grows {σ σ' : State} {cls : ClassName} {fs : List (FieldKey × Value)}
    {f : Field} {v : EquivLean.Cobol.Rec.FVal} (hg : Grows σ σ') (h : jFieldAt σ cls fs f v) : jFieldAt σ' cls fs f v := by
  cases v with
  | num n => exact h
  | str bs =>
    obtain ⟨s, hs, hst⟩ := h
    exact ⟨s, hs, jstrAt_of_grows hg hst⟩

theorem jrecAt_of_grows {σ σ' : State} {s : Schema} {cls : ClassName} {v : Value}
    {t : List EquivLean.Cobol.Rec.FVal} (hg : Grows σ σ') (h : JRecAt s cls σ v t) : JRecAt s cls σ' v t := by
  obtain ⟨x, fs, rfl, hx, hf⟩ := h
  exact ⟨x, fs, rfl, heap_of_grows hg hx, forall2_mono (fun _ _ h => jFieldAt_of_grows hg h) hf⟩

theorem strField_of_grows {σ σ' : State} {fs : List (FieldKey × Value)} {f : String}
    (hg : Grows σ σ') (h : StrField σ fs f) : StrField σ' fs f := by
  obtain ⟨x, s, h1, h2⟩ := h
  exact ⟨x, s, h1, heap_of_grows hg h2⟩

theorem dalOk_of_grows {σ σ' : State} {c : Addr} (hg : Grows σ σ') (h : DalOk σ c) :
    DalOk σ' c := by
  obtain ⟨fs, hc, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨fs, heap_of_grows hg hc, strField_of_grows hg h0, strField_of_grows hg h1, h2,
    strField_of_grows hg h3, strField_of_grows hg h4, h5, h6, strField_of_grows hg h7,
    strField_of_grows hg h8, strField_of_grows hg h9, strField_of_grows hg h10,
    strField_of_grows hg h11, strField_of_grows hg h12, strField_of_grows hg h13⟩

theorem argText_of_grows {σ σ' : State} {fs : List (FieldKey × Value)} {f : String}
    (hg : Grows σ σ') (h : StrField σ fs f) :
    argText σ' ((Fields.get fs (dalCls, f)).getD .null) =
      argText σ ((Fields.get fs (dalCls, f)).getD .null) := by
  obtain ⟨x, s, h1, h2⟩ := h
  simp [argText, strOf, h1, h2, heap_of_grows hg h2]

theorem dalLine_of_grows {σ σ' : State} {c : Addr} (hg : Grows σ σ') (h : DalOk σ c) :
    dalLine σ' c = dalLine σ c := by
  obtain ⟨fs, hc, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have hc' := heap_of_grows hg hc
  simp only [dalLine, fieldOf, fieldLong, hc, hc', argText_of_grows hg h0, argText_of_grows hg h1,
    argText_of_grows hg h3, argText_of_grows hg h4, argText_of_grows hg h7,
    argText_of_grows hg h8, argText_of_grows hg h9, argText_of_grows hg h10,
    argText_of_grows hg h11, argText_of_grows hg h12, argText_of_grows hg h13]

/-! ## The `displays` list changes -/

theorem jstrAt_setObj_list {σ : State} {l : Addr} {k : ListKind} {ys : List Value} {m : Nat}
    {o : Obj} {v : Value} {s : JStr} (hl : σ.heap l = some (.list k ys m)) (h : JStrAt σ v s) :
    JStrAt (σ.setObj l o) v s := by
  obtain ⟨x, rfl, hx⟩ := h
  have hxl : x ≠ l := by intro h; subst h; rw [hl] at hx; cases hx
  exact ⟨x, rfl, by rw [State.heap_setObj, ite_eq_right hxl, hx]⟩

theorem heap_setObj_ne {σ : State} {l x : Addr} {o : Obj} (hxl : x ≠ l) :
    (σ.setObj l o).heap x = σ.heap x := by
  rw [State.heap_setObj, ite_eq_right hxl]

theorem curAt_setObj_list {σ : State} {l : Addr} {k : ListKind} {ys : List Value} {m : Nat}
    {o : Obj} {d : Value} {t : List EquivLean.Cobol.Rec.FVal} (hl : σ.heap l = some (.list k ys m))
    (h : CurAt σ d t) : CurAt (σ.setObj l o) d t := by
  obtain ⟨x, fs, c, i, rfl, hx, hc, hcs, hi, his⟩ := h
  have hxl : x ≠ l := by intro h; subst h; rw [hl] at hx; cases hx
  have hcl : c ≠ l := by intro h; subst h; rw [hl] at hcs; cases hcs
  have hil : i ≠ l := by intro h; subst h; rw [hl] at his; cases his
  exact ⟨x, fs, c, i, rfl, by rw [heap_setObj_ne hxl, hx], hc, by rw [heap_setObj_ne hcl, hcs], hi,
    by rw [heap_setObj_ne hil, his]⟩

theorem resAt_setObj_list {σ : State} {res l : Addr} {k : ListKind} {ys : List Value} {m : Nat}
    {o : Obj} (hrl : res ≠ l) (h : ResAt σ res l) : ResAt (σ.setObj l o) res l := by
  obtain ⟨fs, hr, h1, h2⟩ := h
  exact ⟨fs, by rw [heap_setObj_ne hrl, hr], h1, h2⟩

/-- `displays.add(s)`: one more line. -/
theorem listAt_add {σ : State} {l x : Addr} {ys : List Value} {m : Nat} {D : List (List Nat)}
    {a : List Nat} (hl : σ.heap l = some (.list .arrayList ys m))
    (hD : Forall2 (JStrAt σ) ys (D.map jline)) (hx : σ.heap x = some (.str (jline a))) :
    ListAt (σ.setObj l (.list .arrayList (ys ++ [.ref x]) (m + 1))) l (D ++ [a]) := by
  have hlt := State.lt_next_of_heap hl
  refine ⟨ys ++ [.ref x], m + 1, by rw [State.heap_setObj, ite_eq_left rfl, ite_eq_left hlt], Hide.intro ?_⟩
  rw [List.map_append, List.map_singleton]
  exact forall2_append_one (jstrAt_setObj_list hl ⟨x, rfl, hx⟩)
    (forall2_mono (fun _ _ h => jstrAt_setObj_list hl h) hD)

theorem listAt_of_grows {σ σ' : State} {l : Addr} {D : List (List Nat)} (hg : Grows σ σ')
    (h : ListAt σ l D) : ListAt σ' l D := by
  obtain ⟨ys, m, hl, hD⟩ := h
  exact ⟨ys, m, heap_of_grows hg hl,
    Hide.intro (forall2_mono (fun _ _ h => jstrAt_of_grows hg h) (Hide.elim hD))⟩

theorem spAt_intro {σ : State} {fr : Frame} {j n : Nat} {s : Addr}
    (h1 : fr.get j = some (.ref s)) (h2 : σ.heap s = some (.str (spJ n))) : SpAt σ fr j n :=
  ⟨s, h1, h2⟩

theorem fval_default : (default : EquivLean.Cobol.Rec.FVal) = .num 0 := rfl

theorem ofNat32_succ (i : Nat) : BitVec.ofNat 32 i + 1#32 = BitVec.ofNat 32 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

theorem addr_eq_false {a b : Nat} (h : a ≠ b) : (a = b) = False := eq_false h
theorem addr_lt_true {a b : Nat} (h : a < b) : (a < b) = True := eq_true h

/-- A heap read through the states of the calls: the frame conditions of the callees
(hypotheses `∀ x, x < σ.next → σ'.heap x = σ.heap x`), allocations and updates; address
(dis)equalities by `jomega`. -/
macro "trn_chain" : tactic => `(tactic| (
  try simp only [State.next_alloc, State.next_setObj] at *
  simp (config := { decide := true }) (disch := jomega) only [State.heap_alloc, State.heap_setObj,
    State.next_alloc, State.next_setObj, ite_true, ite_false, reduceIte, addr_eq_false, addr_lt_true,
    jstrLitT, dalCls, State.initOf_alloc, State.initOf_setObj, List.cons_append, List.nil_append,
    List.append_assoc, List.getD_eq_getElem?_getD, fval_default, *]
  try rfl))

/-- A frame fact after `setLocal`s (`trn_frame_simp`), closing numeral forms by `rfl`. -/
macro "trn_frame" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp (config := { decide := true }) only [Frame.get_setLocal, ite_true, ite_false,
    reduceIte, $hs,*] <;> rfl))

/-- `fr'.get k = some v` for a frame built by `setLocal`s, from facts about the old frame. -/
macro "trn_frame_simp" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (config := { decide := true }) only [Frame.get_setLocal, ite_true, ite_false,
    reduceIte, $hs,*])

/-! ## The display lines as Java strings -/

theorem line_invalid_card :
    jline (Model.txt "INVALID CARD NUMBER FOR XREF") = JStr.ofString "INVALID CARD NUMBER FOR XREF" := by
  decide

theorem line_skip (T I : List UInt8) :
    jline (Model.txt "CARD NUMBER " ++ T.map cp037Code ++
      Model.txt " COULD NOT BE VERIFIED. SKIPPING TRANSACTION ID-" ++ I.map cp037Code) =
    JStr.ofString "CARD NUMBER " ++ (cp037Str T ++
      (JStr.ofString " COULD NOT BE VERIFIED. SKIPPING TRANSACTION ID-" ++ cp037Str I)) := by
  have h1 : jline (Model.txt "CARD NUMBER ") = JStr.ofString "CARD NUMBER " := by decide
  have h2 : jline (Model.txt " COULD NOT BE VERIFIED. SKIPPING TRANSACTION ID-") =
      JStr.ofString " COULD NOT BE VERIFIED. SKIPPING TRANSACTION ID-" := by decide
  simp only [jline_append, jline_cp037, h1, h2, List.append_assoc]

theorem line_ok_xref :
    jline (Model.txt "SUCCESSFUL READ OF XREF") = JStr.ofString "SUCCESSFUL READ OF XREF" := by
  decide

theorem line_card_num (X : List UInt8) :
    jline (Model.txt "CARD NUMBER: " ++ X.map cp037Code) =
      JStr.ofString "CARD NUMBER: " ++ cp037Str X := by
  have h1 : jline (Model.txt "CARD NUMBER: ") = JStr.ofString "CARD NUMBER: " := by decide
  simp only [jline_append, jline_cp037, h1]

theorem line_acct_id (c : Nat) :
    jline (Model.txt "ACCOUNT ID : " ++ zpad 11 c) = JStr.ofString "ACCOUNT ID : " ++ zpadJ c 11 := by
  have h1 : jline (Model.txt "ACCOUNT ID : ") = JStr.ofString "ACCOUNT ID : " := by decide
  simp only [jline_append, jline_zpad, h1]

theorem line_cust_id (c : Nat) :
    jline (Model.txt "CUSTOMER ID: " ++ zpad 9 c) = JStr.ofString "CUSTOMER ID: " ++ zpadJ c 9 := by
  have h1 : jline (Model.txt "CUSTOMER ID: ") = JStr.ofString "CUSTOMER ID: " := by decide
  simp only [jline_append, jline_zpad, h1]

theorem line_invalid_acct :
    jline (Model.txt "INVALID ACCOUNT NUMBER FOUND") = JStr.ofString "INVALID ACCOUNT NUMBER FOUND" := by
  decide

theorem line_acct_not_found (c : Nat) :
    jline (Model.txt "ACCOUNT " ++ zpad 11 c ++ Model.txt " NOT FOUND") =
      JStr.ofString "ACCOUNT " ++ (zpadJ c 11 ++ JStr.ofString " NOT FOUND") := by
  have h1 : jline (Model.txt "ACCOUNT ") = JStr.ofString "ACCOUNT " := by decide
  have h2 : jline (Model.txt " NOT FOUND") = JStr.ofString " NOT FOUND" := by decide
  simp only [jline_append, jline_zpad, h1, h2, List.append_assoc]

theorem line_ok_acct :
    jline (Model.txt "SUCCESSFUL READ OF ACCOUNT FILE") =
      JStr.ofString "SUCCESSFUL READ OF ACCOUNT FILE" := by
  decide

theorem forall2_append_two {α β : Type} {R : α → β → Prop} {x1 x2 : α} {y1 y2 : β}
    (h1 : R x1 y1) (h2 : R x2 y2) {xs : List α} {ys : List β} (h : Forall2 R xs ys) :
    Forall2 R (xs ++ [x1, x2]) (ys ++ [y1, y2]) := by
  have := forall2_append_one h2 (forall2_append_one h1 h)
  simpa [List.append_assoc] using this

theorem forall2_append {α β : Type} {R : α → β → Prop} :
    ∀ {xs xs' : List α} {ys ys' : List β}, Forall2 R xs ys → Forall2 R xs' ys' →
      Forall2 R (xs ++ xs') (ys ++ ys')
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons h hs, h' => .cons h (forall2_append hs h')

/-- The `displays` list right after an update (`add`): its lines from the updated contents. -/
theorem listAt_setObj {S : State} {l : Addr} {k : ListKind} {zs : List Value} {n : Nat}
    {D : List (List Nat)} (hlt : l < S.next) (hk : k = .arrayList)
    (hD : Forall2 (JStrAt (S.setObj l (.list k zs n))) zs (D.map jline)) :
    ListAt (S.setObj l (.list k zs n)) l D := by
  subst hk
  exact ⟨zs, n, by rw [State.heap_setObj, ite_eq_left rfl, ite_eq_left hlt], Hide.intro hD⟩

/-! ## Building the invariants -/

theorem Base.intro {a1 a3 a5 : Addr} {vals1 : List (List EquivLean.Cobol.Rec.FVal)} {σ0 : State}
    {fr : Frame} {σ : State} {k : Nat} {e : Bool} {d : Value} {res l : Addr}
    (f10 : fr.get 10 = some (.ref a1)) (f35 : fr.get 35 = some (.ref a3))
    (f4 : fr.get 4 = some (.ref a5)) (f9 : fr.get 9 = some (.ref res))
    (f11 : fr.get 11 = some (.ref l)) (f17 : fr.get 17 = some (.int (BitVec.ofNat 32 k)))
    (hk : k ≤ vals1.length) (f7 : fr.get 7 = some (.int (JInt.ofBool e)))
    (f8 : fr.get 8 = some (.int (JInt.ofBool e))) (f5 : fr.get 5 = some (.int (JInt.ofBool e)))
    (he : e = true → k = vals1.length) (f1 : fr.get 1 = some d) (hcur : CurAt σ d (curT vals1 k))
    (hres : ResAt σ res l) (hres0 : σ0.next ≤ res) (hl0 : σ0.next ≤ l) (hrl : res ≠ l)
    (hg : Grows σ0 σ) (hinit : σ.initOf "Cbtrn01c" = .done) :
    Base a1 a3 a5 vals1 σ0 fr σ k e d res l :=
  ⟨f10, f35, f4, f9, f11, f17, hk, f7, f8, f5, he, f1, Hide.intro hcur, hres, hres0, hl0, hrl, hg,
    hinit⟩

theorem J29.intro {a1 a3 a5 : Addr} {vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)}
    {args : List Value} {σ0 : State} {fr : Frame} {σ : State} (k : Nat) (e : Bool) (d : Value)
    (res l : Addr) (base : Base a1 a3 a5 vals1 σ0 fr σ k e d res l)
    (hlist : ListAt σ l (headL vals1 vals3 vals5 k e)) :
    J29 a1 a3 a5 vals1 vals3 vals5 args σ0 fr σ :=
  ⟨k, e, d, res, l, base, hlist⟩

theorem J60.intro {a1 a3 a5 : Addr} {vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)}
    {args : List Value} {σ0 : State} {fr : Frame} {σ : State} (k : Nat) (e : Bool) (d : Value)
    (res l : Addr) (i : Nat) (cs : Addr) (base : Base a1 a3 a5 vals1 σ0 fr σ k e d res l)
    (hek : e = false → 1 ≤ k) (hlist : ListAt σ l (befL vals1 vals3 vals5 k e))
    (f16 : fr.get 16 = some (.int (BitVec.ofNat 32 i))) (hi : i ≤ vals3.length)
    (f20 : fr.get 20 = some (.ref cs))
    (hcs : σ.heap cs = some (.str (cp037Str (Model.strOf ((curT vals1 k).getD 10 default)))))
    (f34 : fr.get 34 = some .null) (f12 : fr.get 12 = some (.long 0))
    (hno : NoCard vals3 i (curT vals1 k)) :
    J60 a1 a3 a5 vals1 vals3 vals5 args σ0 fr σ :=
  ⟨k, e, d, res, l, i, cs, base, hek, hlist, f16, hi, f20, hcs, f34, f12, hno⟩

theorem J92.intro {a1 a3 a5 : Addr} {vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)}
    {args : List Value} {σ0 : State} {fr : Frame} {σ : State} (k : Nat) (e : Bool) (d : Value)
    (res l : Addr) (j : Nat) (x : List EquivLean.Cobol.Rec.FVal)
    (base : Base a1 a3 a5 vals1 σ0 fr σ k e d res l) (hek : e = false → 1 ≤ k)
    (hx : vals3.find? (cardMatch (curT vals1 k)) = some x)
    (hlist : ListAt σ l (befL vals1 vals3 vals5 k e ++ xrefL x))
    (f18 : fr.get 18 = some (.int (BitVec.ofNat 32 j))) (hj : j ≤ vals5.length)
    (f13 : fr.get 13 = some (.long (BitVec.ofInt 64 (Model.numOf (x.getD 2 default)))))
    (f15 : fr.get 15 = some (.long (BitVec.ofInt 64 (Model.numOf (x.getD 2 default)))))
    (f14 : fr.get 14 = some (.long 0)) (f32 : fr.get 32 = some .null) (hno : NoAcct vals5 j x) :
    J92 a1 a3 a5 vals1 vals3 vals5 args σ0 fr σ :=
  ⟨k, e, d, res, l, j, x, base, hek, hx, hlist, f18, hj, f13, f15, f14, f32, hno⟩

end EquivLean.Modernize.Cbtrn01c.Java
