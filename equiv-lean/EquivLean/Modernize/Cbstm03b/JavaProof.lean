import EquivLean.Modernize.Cbstm03b.JavaStatement
import EquivLean.Modernize.Cbstm03b.Glue
import EquivLean.Modernize.Cbstm03b.Domain

/-!
# CBSTM03B → Java: from the contract of `call` to the generated statement

* the Java side: `runSpec`, the contract of `Cbstm03b.call(Integer[], State, LkM03bArea)`: on a heap holding the
  model's values (`StateAtM`, `EnvAtM`, the area's field values), for valid values and the key `cbstm03b_call`
  assumes, the call returns normally and the heap holds the model's call (`Model.call`);
* the COBOL side and the glue: `Glue.call_run`, the model's call against coblean's interpreter;
* the transfer: a heap related by the generated relations holds model values related by the glue's relations,
  and back (`stateAt_to_model`, `model_to_stateAt`).

The translation updates the FD record objects of CUSTFILE and ACCTFILE in place (`fdCustId`, `fdAcctId`), so the
contract also assumes, and keeps, that these objects are not record objects of their files (`SepM`, the separation
conjuncts of the generated `StateAt`); the key of a keyed READ of ACCTFILE is a digit string (the statements'
domain, `Domain.lean`).

`statement_of_sat`: the contract implies the generated `Statement`.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (st0)

namespace EquivLean.Modernize.Cbstm03b.Java

/-! ## The model's values in the heap -/

/-- The file object `x` (class `cls`, records of class `rcls`) holds the model's file `f`. -/
def FileAtM (cls rcls : ClassName) (S : Schema) (σ : Jimple.State) (x : Jimple.Value) (f : Model.FileM) : Prop :=
  ∃ o fs l et xs, x = .ref o ∧ σ.heap o = some (.plain cls fs) ∧
    Fields.get fs (cls, "open") = some (.ofBool f.isOpen) ∧
    Fields.get fs (cls, "recs") = some (.ref l) ∧ σ.heap l = some (.array et xs) ∧ xs.length < 2147483648 ∧
    Forall2 (fun x vals => JRecAt S rcls σ x vals) xs f.recs ∧
    f.pos < 2147483648 ∧ Fields.get fs (cls, "pos") = some (.int (BitVec.ofNat 32 f.pos)) ∧
    Fields.get fs (cls, "eof") = some (.ofBool f.eof)

/-- The state object `st` holds the model's state `s`; a status is the CP037 text of its EBCDIC bytes. -/
def StateAtM (σ : Jimple.State) (st : Addr) (s : Model.StM) : Prop :=
  ∃ fs, σ.heap st = some (.plain "Cbstm03b$State" fs) ∧
    (∃ x, Fields.get fs ("Cbstm03b$State", "trnxFile") = some x ∧
      FileAtM "Cbstm03b$TrnxFile" "Cbstm03b$FdTrnxfileRec" FdTrnxfileRec σ x s.trnx) ∧
    (∃ x, Fields.get fs ("Cbstm03b$State", "xrefFile") = some x ∧
      FileAtM "Cbstm03b$XrefFile" "Cbstm03b$FdXreffileRec" FdXreffileRec σ x s.xref) ∧
    (∃ x, Fields.get fs ("Cbstm03b$State", "custFile") = some x ∧
      FileAtM "Cbstm03b$CustFile" "Cbstm03b$FdCustfileRec" FdCustfileRec σ x s.cust) ∧
    (∃ x, Fields.get fs ("Cbstm03b$State", "acctFile") = some x ∧
      FileAtM "Cbstm03b$AcctFile" "Cbstm03b$FdAcctfileRec" FdAcctfileRec σ x s.acct) ∧
    (∃ x, Fields.get fs ("Cbstm03b$State", "fdTrnxfileRec") = some x ∧
      JRecAt FdTrnxfileRec "Cbstm03b$FdTrnxfileRec" σ x s.trnxRec) ∧
    (∃ x, Fields.get fs ("Cbstm03b$State", "fdXreffileRec") = some x ∧
      JRecAt FdXreffileRec "Cbstm03b$FdXreffileRec" σ x s.xrefRec) ∧
    (∃ x, Fields.get fs ("Cbstm03b$State", "fdCustfileRec") = some x ∧
      JRecAt FdCustfileRec "Cbstm03b$FdCustfileRec" σ x s.custRec) ∧
    (∃ x, Fields.get fs ("Cbstm03b$State", "fdAcctfileRec") = some x ∧
      JRecAt FdAcctfileRec "Cbstm03b$FdAcctfileRec" σ x s.acctRec) ∧
    (∃ x, Fields.get fs ("Cbstm03b$State", "trnxfileStatus") = some x ∧
      JStrAt σ x (cp037Str (s.trnxSt.map ebcdicOfLatin1))) ∧
    (∃ x, Fields.get fs ("Cbstm03b$State", "xreffileStatus") = some x ∧
      JStrAt σ x (cp037Str (s.xrefSt.map ebcdicOfLatin1))) ∧
    (∃ x, Fields.get fs ("Cbstm03b$State", "custfileStatus") = some x ∧
      JStrAt σ x (cp037Str (s.custSt.map ebcdicOfLatin1))) ∧
    (∃ x, Fields.get fs ("Cbstm03b$State", "acctfileStatus") = some x ∧
      JStrAt σ x (cp037Str (s.acctSt.map ebcdicOfLatin1)))

/-- The FD record objects of CUSTFILE and ACCTFILE are not record objects of their files (the separation
conjuncts of the generated `StateAt`). -/
def SepM (σ : Jimple.State) (st : Addr) : Prop :=
  ∃ fs, σ.heap st = some (.plain "Cbstm03b$State" fs) ∧
    (∀ x y, Fields.get fs ("Cbstm03b$State", "fdCustfileRec") = some x →
      Fields.get fs ("Cbstm03b$State", "custFile") = some y → NotRecOf σ "Cbstm03b$CustFile" x y) ∧
    (∀ x y, Fields.get fs ("Cbstm03b$State", "fdAcctfileRec") = some x →
      Fields.get fs ("Cbstm03b$State", "acctFile") = some y → NotRecOf σ "Cbstm03b$AcctFile" x y)

/-- The OPEN outcomes array `oe` holds the model's `oeM`: element `i` is null when `oeM (i + 1)` is `none`, else
an `Integer` below 100. -/
def EnvAtM (σ : Jimple.State) (oe : Addr) (oeM : Model.OpenErrs) : Prop :=
  ∃ et xs, σ.heap oe = some (.array et xs) ∧ xs.length = 4 ∧ ∀ i, i < 4 →
    (xs.getD i .null = .null ∧ oeM (i + 1) = none) ∨
    (∃ o c, xs.getD i .null = .ref o ∧ σ.heap o = some (.boxed "java.lang.Integer" (.int (BitVec.ofNat 32 c))) ∧
      c < 100 ∧ oeM (i + 1) = some c)

/-- The classes the call uses are initialized. -/
def InitsDone (σ : Jimple.State) : Prop :=
  σ.initOf "Cbstm03b" = .done ∧ σ.initOf "Cbstm03b$State" = .done ∧ σ.initOf "Cbstm03b$TrnxFile" = .done ∧
    σ.initOf "Cbstm03b$XrefFile" = .done ∧ σ.initOf "Cbstm03b$CustFile" = .done ∧
    σ.initOf "Cbstm03b$AcctFile" = .done ∧ σ.initOf "Cbstm03b$FdAcctfileRec" = .done ∧
    σ.initOf "Cbstm03b$FdCustfileRec" = .done ∧ σ.initOf "Cbstm03b$FdTrnxfileRec" = .done ∧
    σ.initOf "Cbstm03b$FdXreffileRec" = .done ∧ σ.initOf "Cbstm03b$LkM03bArea" = .done

/-- `Cbstm03b.call(Integer[], State, LkM03bArea)`. -/
abbrev callRef : MethodRef := Gen.Cbstm03b.«call(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea)».ref

/-- **The Java side**: the contract of `call` (partial correctness) over the model's call. -/
def runSpec : Spec := Spec.of
  (fun args σ => ∃ oe st q oeM s a, args = [.ref oe, .ref st, .ref q] ∧ EnvAtM σ oe oeM ∧ StateAtM σ st s ∧
     SepM σ st ∧ JRecAt LkM03bArea "Cbstm03b$LkM03bArea" σ (.ref q) a ∧ Glue.ValidSt s ∧ LkM03bArea.Valid a ∧
     Glue.KeyOk a ∧ InitsDone σ)
  (fun args σ r σ' => ∀ oe st q oeM s a, args = [.ref oe, .ref st, .ref q] → EnvAtM σ oe oeM →
     StateAtM σ st s → SepM σ st → JRecAt LkM03bArea "Cbstm03b$LkM03bArea" σ (.ref q) a → Glue.ValidSt s →
     LkM03bArea.Valid a → Glue.KeyOk a → InitsDone σ →
     r = none ∧ StateAtM σ' st (Model.call oeM s a).1 ∧ SepM σ' st ∧
       JRecAt LkM03bArea "Cbstm03b$LkM03bArea" σ' (.ref q) (Model.call oeM s a).2)

/-! ## The generated relations and the model's values -/

theorem latin_rt_fin : ∀ n : Fin 256,
    ebcdicOfLatin1 (latin1OfEbcdic (UInt8.ofNat n.val)) = UInt8.ofNat n.val := by
  decide +kernel

theorem latin_rt (b : UInt8) : ebcdicOfLatin1 (latin1OfEbcdic b) = b := by
  have h := latin_rt_fin ⟨b.toNat, b.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at h
  exact h

theorem map_latin (bs : List UInt8) : (bs.map latin1OfEbcdic).map ebcdicOfLatin1 = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [List.map_cons, List.map_cons, latin_rt, ih]

/-- The shape of the generated file relations. -/
def GenFileAt (cls rcls : ClassName) (S : Schema) (σ : Jimple.State) (x : Jimple.Value) (s : FileSt) : Prop :=
  ∃ o fs b l et xs, x = .ref o ∧ σ.heap o = some (.plain cls fs) ∧
    Fields.get fs (cls, "open") = some (.ofBool b) ∧ s.mode = (if b then some .input else none) ∧
    Fields.get fs (cls, "recs") = some (.ref l) ∧ σ.heap l = some (.array et xs) ∧
    xs.length < 2147483648 ∧
    Forall2 (fun x r => ∃ vals, JRecAt S rcls σ x vals ∧ S.Valid vals ∧
      r = S.encode vals) xs s.recs ∧
    s.pos < 2147483648 ∧ Fields.get fs (cls, "pos") = some (.int (BitVec.ofNat 32 s.pos)) ∧
    Fields.get fs (cls, "eof") = some (.ofBool s.eof)

theorem trnxFileAt_eq (σ : Jimple.State) (x : Jimple.Value) (s : FileSt) :
    TrnxFileAt σ x s = GenFileAt "Cbstm03b$TrnxFile" "Cbstm03b$FdTrnxfileRec" FdTrnxfileRec σ x s := rfl
theorem xrefFileAt_eq (σ : Jimple.State) (x : Jimple.Value) (s : FileSt) :
    XrefFileAt σ x s = GenFileAt "Cbstm03b$XrefFile" "Cbstm03b$FdXreffileRec" FdXreffileRec σ x s := rfl
theorem custFileAt_eq (σ : Jimple.State) (x : Jimple.Value) (s : FileSt) :
    CustFileAt σ x s = GenFileAt "Cbstm03b$CustFile" "Cbstm03b$FdCustfileRec" FdCustfileRec σ x s := rfl
theorem acctFileAt_eq (σ : Jimple.State) (x : Jimple.Value) (s : FileSt) :
    AcctFileAt σ x s = GenFileAt "Cbstm03b$AcctFile" "Cbstm03b$FdAcctfileRec" FdAcctfileRec σ x s := rfl

theorem forall2_vals {σ : Jimple.State} {S : Schema} {rcls : ClassName} :
    ∀ {xs : List Jimple.Value} {rs : List (List UInt8)},
      Forall2 (fun x r => ∃ vals, JRecAt S rcls σ x vals ∧ S.Valid vals ∧ r = S.encode vals) xs rs →
      ∃ vs, Forall2 (fun x vals => JRecAt S rcls σ x vals) xs vs ∧ (∀ v ∈ vs, S.Valid v) ∧ rs = vs.map S.encode
  | [], [], .nil => ⟨[], .nil, fun _ h => absurd h (List.not_mem_nil), rfl⟩
  | _ :: _, _ :: _, .cons ⟨v, hj, hv, he⟩ hrest => by
    obtain ⟨vs, hj', hv', he'⟩ := forall2_vals hrest
    refine ⟨v :: vs, .cons hj hj', fun w hw => ?_, by rw [he, he']; rfl⟩
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hv
    · exact hv' w hw

theorem forall2_encode {σ : Jimple.State} {S : Schema} {rcls : ClassName} :
    ∀ {xs : List Jimple.Value} {vs : List (List EquivLean.Cobol.Rec.FVal)},
      Forall2 (fun x vals => JRecAt S rcls σ x vals) xs vs → (∀ v ∈ vs, S.Valid v) →
      Forall2 (fun x r => ∃ vals, JRecAt S rcls σ x vals ∧ S.Valid vals ∧ r = S.encode vals) xs (vs.map S.encode)
  | [], [], .nil, _ => .nil
  | _ :: _, v :: _, .cons hj hrest, hv =>
    .cons ⟨v, hj, hv v List.mem_cons_self, rfl⟩ (forall2_encode hrest fun w hw => hv w (List.mem_cons_of_mem _ hw))

theorem gen_to_model {cls rcls : ClassName} {S : Schema} {σ : Jimple.State} {x : Jimple.Value} {s : FileSt}
    (h : GenFileAt cls rcls S σ x s) : ∃ f, FileAtM cls rcls S σ x f ∧ Glue.FileRel S f s := by
  obtain ⟨o, fs, b, l, et, xs, hx, ho, hb, hmode, hl, hlh, hlen, hrecs, hpos, hp, he⟩ := h
  obtain ⟨vs, hj, hv, he'⟩ := forall2_vals hrecs
  exact ⟨{ isOpen := b, recs := vs, pos := s.pos, eof := s.eof },
    ⟨o, fs, l, et, xs, hx, ho, hb, hl, hlh, hlen, hj, hpos, hp, he⟩, ⟨hmode, hv, he', rfl, rfl⟩⟩

theorem model_to_gen {cls rcls : ClassName} {S : Schema} {σ : Jimple.State} {x : Jimple.Value} {f : Model.FileM}
    {s : FileSt} (h : FileAtM cls rcls S σ x f) (hr : Glue.FileRel S f s) : GenFileAt cls rcls S σ x s := by
  obtain ⟨o, fs, l, et, xs, hx, ho, hb, hl, hlh, hlen, hj, hpos, hp, he⟩ := h
  obtain ⟨hmode, hv, hrecs, hpos', heof⟩ := hr
  refine ⟨o, fs, f.isOpen, l, et, xs, hx, ho, hb, hmode, hl, hlh, hlen, ?_, by rw [hpos']; exact hpos,
    by rw [hpos']; exact hp, by rw [heof]; exact he⟩
  rw [hrecs]
  exact forall2_encode hj hv

/-- A heap related by the generated `StateAt` holds model values related by the glue's `StateRel`. -/
theorem stateAt_to_model {σ : Jimple.State} {st : Addr} {cs : Cobol.State} (h : StateAt σ st cs) :
    ∃ s, StateAtM σ st s ∧ Glue.StateRel s cs := by
  obtain ⟨fs, hst, ⟨x1, s1, g1, l1, h1⟩, ⟨x2, s2, g2, l2, h2⟩, ⟨x3, s3, g3, l3, h3⟩, ⟨x4, s4, g4, l4, h4⟩,
    ⟨y1, v1, k1, j1, w1, a1⟩, ⟨y2, v2, k2, j2, w2, a2⟩, ⟨y3, v3, k3, j3, w3, a3⟩, ⟨y4, v4, k4, j4, w4, a4⟩,
    ⟨z1, b1, n1, t1, u1⟩, ⟨z2, b2, n2, t2, u2⟩, ⟨z3, b3, n3, t3, u3⟩, ⟨z4, b4, n4, t4, u4⟩, -, -⟩ := h
  rw [trnxFileAt_eq] at h1
  rw [xrefFileAt_eq] at h2
  rw [custFileAt_eq] at h3
  rw [acctFileAt_eq] at h4
  obtain ⟨f1, m1, r1⟩ := gen_to_model h1
  obtain ⟨f2, m2, r2⟩ := gen_to_model h2
  obtain ⟨f3, m3, r3⟩ := gen_to_model h3
  obtain ⟨f4, m4, r4⟩ := gen_to_model h4
  let s : Model.StM :=
    { trnx := f1, xref := f2, cust := f3, acct := f4
      trnxRec := v1, xrefRec := v2, custRec := v3, acctRec := v4
      trnxSt := b1.map latin1OfEbcdic, xrefSt := b2.map latin1OfEbcdic
      custSt := b3.map latin1OfEbcdic, acctSt := b4.map latin1OfEbcdic }
  refine ⟨s,
    ⟨fs, hst, ⟨x1, g1, m1⟩, ⟨x2, g2, m2⟩, ⟨x3, g3, m3⟩, ⟨x4, g4, m4⟩, ⟨y1, k1, j1⟩, ⟨y2, k2, j2⟩, ⟨y3, k3, j3⟩,
      ⟨y4, k4, j4⟩, ⟨z1, n1, ?_⟩, ⟨z2, n2, ?_⟩, ⟨z3, n3, ?_⟩, ⟨z4, n4, ?_⟩⟩,
    ⟨⟨s1, l1, r1⟩, ⟨s2, l2, r2⟩, ⟨s3, l3, r3⟩, ⟨s4, l4, r4⟩, w1, a1, w2, a2, w3, a3, w4, a4, ?_, ?_, ?_, ?_⟩⟩
  all_goals simp only [s, map_latin]
  all_goals assumption

/-- The generated `StateAt`'s separation conjuncts. -/
theorem stateAt_sep {σ : Jimple.State} {st : Addr} {cs : Cobol.State} (h : StateAt σ st cs) : SepM σ st := by
  obtain ⟨fs, hst, -, -, -, -, -, -, -, -, -, -, -, -, c1, c2⟩ := h
  exact ⟨fs, hst, c1, c2⟩

/-- Model values related by the glue's `StateRel`, held by a heap with `SepM`, make the generated `StateAt`. -/
theorem model_to_stateAt {σ : Jimple.State} {st : Addr} {s : Model.StM} {cs : Cobol.State}
    (h : StateAtM σ st s) (hsep : SepM σ st) (hr : Glue.StateRel s cs) : StateAt σ st cs := by
  obtain ⟨fs, hst, ⟨x1, g1, m1⟩, ⟨x2, g2, m2⟩, ⟨x3, g3, m3⟩, ⟨x4, g4, m4⟩, ⟨y1, k1, j1⟩, ⟨y2, k2, j2⟩,
    ⟨y3, k3, j3⟩, ⟨y4, k4, j4⟩, ⟨z1, n1, t1⟩, ⟨z2, n2, t2⟩, ⟨z3, n3, t3⟩, ⟨z4, n4, t4⟩⟩ := h
  obtain ⟨fs', hst', c1, c2⟩ := hsep
  rw [hst] at hst'
  cases hst'
  obtain ⟨⟨s1, l1, r1⟩, ⟨s2, l2, r2⟩, ⟨s3, l3, r3⟩, ⟨s4, l4, r4⟩, v1, a1, v2, a2, v3, a3, v4, a4, b1, b2, b3, b4⟩ :=
    hr
  refine ⟨fs, hst, ⟨x1, s1, g1, l1, ?_⟩, ⟨x2, s2, g2, l2, ?_⟩, ⟨x3, s3, g3, l3, ?_⟩, ⟨x4, s4, g4, l4, ?_⟩,
    ⟨y1, _, k1, j1, v1, a1⟩, ⟨y2, _, k2, j2, v2, a2⟩, ⟨y3, _, k3, j3, v3, a3⟩, ⟨y4, _, k4, j4, v4, a4⟩,
    ⟨z1, _, n1, t1, b1⟩, ⟨z2, _, n2, t2, b2⟩, ⟨z3, _, n3, t3, b3⟩, ⟨z4, _, n4, t4, b4⟩, c1, c2⟩
  · rw [trnxFileAt_eq]; exact model_to_gen m1 r1
  · rw [xrefFileAt_eq]; exact model_to_gen m2 r2
  · rw [custFileAt_eq]; exact model_to_gen m3 r3
  · rw [acctFileAt_eq]; exact model_to_gen m4 r4

theorem envAt_model {σ : Jimple.State} {oe : Addr} {env : Env} (h : EnvAt σ oe env) :
    EnvAtM σ oe (fun id => env.openError id .input) := h

/-! ## The statement -/

/-- **The contract of `call` implies the generated statement.** -/
theorem statement_of_sat (hrun : Sat Gen.prog callRef runSpec) : Statement := by
  intro env m hm fs k v _ _ _ _ hK hA hD σ oe st q1 hE hS hR i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11
  obtain ⟨s, hsm, hsr⟩ := stateAt_to_model hS
  have hsep := stateAt_sep hS
  obtain ⟨a, haj, hav, haa⟩ := hR
  have hR' : Glue.LkM03bAreaRel a m := ⟨hav, haa⟩
  have hE' : Glue.EnvRel (fun id => env.openError id .input) env := fun _ _ => rfl
  have hval := Glue.validSt_of_stateRel hsr
  have hkey := Glue.keyOk_of hR' hK hA hD
  have hinit : InitsDone σ := ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩
  obtain ⟨hgo, hS2, hR2⟩ := Glue.call_run env m hm fs k v hK hA _ s a hE' hsr hR'
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbstm03b.run env 50 (st0 m fs)) := by
    rw [EquivLean.Cobol.Ok, hgo]; rfl
  rw [EquivLean.Cobol.run]
  refine sim_of_sat ((EquivLean.Cobol.safe_exec_iff _).2 hok) ((EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩)
    hrun ⟨oe, st, q1, fun id => env.openError id .input, s, a, rfl, envAt_model hE, hsm, hsep, haj, hval, hav,
      hkey, hinit⟩ ?_
  intro o ho
  cases o with
  | normal r σ' =>
    obtain ⟨hr, hsm', hsep', haj'⟩ :=
      ho oe st q1 (fun id => env.openError id .input) s a rfl (envAt_model hE) hsm hsep haj hval hav hkey hinit
    exact ⟨σ', by rw [hr], hgo, model_to_stateAt hsm' hsep' hS2, ⟨_, haj', hR2.1, hR2.2⟩⟩
  | exc e σ' => simp [runSpec, Spec.of] at ho
  | wrong msg => simp [runSpec, Spec.of] at ho

end EquivLean.Modernize.Cbstm03b.Java
