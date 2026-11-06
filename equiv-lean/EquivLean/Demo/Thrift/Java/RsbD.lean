import EquivLean.Demo.Thrift.Java.RlbP

/-!
# Thrift → Java (T4): the compact set header reader `readSetBegin()`, definitions

`readSetBegin()` is `new TSet(readListBegin())`; `readListBegin()` is used through its proved
contract, the `TSet` constructors are executed inline.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev rsbRef : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«readSetBegin()».ref

def rlbSig : MethodSig := ⟨cpCls, .cls "org.apache.thrift.protocol.TList", "readListBegin", []⟩

theorem instanceFields_ts {P : Program} (hns : NoShadow P)
    (h1 : P.findClass "org.apache.thrift.protocol.TSet" = some tsC) :
    P.instanceFields "org.apache.thrift.protocol.TSet" =
      [(("org.apache.thrift.protocol.TSet", "elemType"), .prim .byte),
       (("org.apache.thrift.protocol.TSet", "size"), .prim .int)] := by
  have h5 : P.findClass "java.lang.Object" = none := findClass_of_noShadow hns (by decide)
  have p5 : preludeFind "java.lang.Object" = some { name := "java.lang.Object", isInterface := false, isAbstract := false, super := none, interfaces := [], fields := [] } := rfl
  rw [show P.instanceFields "org.apache.thrift.protocol.TSet" =
      P.instanceFieldsN (4094 + 1 + 1) "org.apache.thrift.protocol.TSet" from rfl,
    ifN_step (lookup_prog h1) rfl, ifN_last (lookup_lib h5 p5) rfl]
  rfl

/-- The new `TSet` object (before its constructor). -/
def tsNew : Obj := .plain "org.apache.thrift.protocol.TSet"
  [(("org.apache.thrift.protocol.TSet", "elemType"), .int 0#32),
   (("org.apache.thrift.protocol.TSet", "size"), .int 0#32)]

/-- `readListBegin()` for the callers. -/
def rlbSpecA (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (lim : I64), args = [.ref p] ∧ CPAt P R σ p t tmp ∧
     LimitAt σ p lim ∧ σ.initOf tpeCls = .done ∧ σ.initOf tlCls = .done ∧
     σ.initOf ttExcCls = .done ∧ NibbleOKL (R.src σ t))
  (rlbN P R) (rlbE P R)

/-- What `readSetBegin()` returns: a new `TSet` with the TType of the type nibble and the size. -/
def rsbN (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (lim : I64), args = [.ref p] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim) →
    ∃ u rest size rest' tt k s sfs, R.src σ t = u :: rest ∧ listSizeJ u rest = some (size, rest') ∧
      0 ≤ size.toInt ∧ InLimit lim size ∧ Spec.ttypeOfCompact (u.toNat % 16) = some tt ∧
      minSize tt = some k ∧ R.src σ' t = rest' ∧ R.sink σ' t = R.sink σ t ∧ CPAt P R σ' p t tmp ∧
      r = some (.ref s) ∧ σ'.heap s = some (.plain tsCls sfs) ∧
      Fields.get sfs (tsCls, "elemType") = some (.int (BitVec.ofNat 32 tt)) ∧
      Fields.get sfs (tsCls, "size") = some (.int size)

attribute [irreducible] rsbN

def rsbSpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (lim : I64), args = [.ref p] ∧ CPAt P R σ p t tmp ∧
     CPAtH P R σ p t tmp ∧ LimitAt σ p lim ∧ σ.initOf tpeCls = .done ∧ σ.initOf tlCls = .done ∧
     σ.initOf ttExcCls = .done ∧ σ.initOf tsCls = .done ∧ NibbleOKL (R.src σ t))
  (rsbN P R) (rlbE P R)

/-- The cut points (locals `$r1` 0, `this` 1, `$r0` 2): statement 2, the call `readListBegin()`
after `new TSet`; statement 3, the call of the constructor `TSet(list)`. -/
def rsbInv (P : Program) (R : TRep) : Invariants :=
  [(2, fun args σ0 fr σ =>
    ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (lim : I64), args = [.ref p] →
    σ0.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim) →
    fr.get 1 = some (.ref p) ∧ fr.get 2 = some (.ref σ0.next) ∧ σ.heap σ0.next = some tsNew ∧
      σ0.next < σ.next ∧ σ.heap p = some (.plain cpCls fs) ∧ CPAtH P R σ p t tmp ∧
      R.src σ t = R.src σ0 t ∧ R.sink σ t = R.sink σ0 t ∧ σ.inits = σ0.inits ∧
      σ0.next ≠ t ∧ σ0.next ≠ tmp ∧ σ0.next ≠ p ∧ ¬ R.owns σ t σ0.next),
   (3, fun args σ0 fr σ =>
    ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (lim : I64), args = [.ref p] →
    σ0.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim) →
    ∃ (u : UInt8) (rest : Bytes) (size : I32) (tt k : Nat) (l : Addr) (lfs : List (FieldKey × Value)),
      R.src σ0 t = u :: rest ∧ listSizeJ u rest = some (size, R.src σ t) ∧ 0 ≤ size.toInt ∧
      InLimit lim size ∧ Spec.ttypeOfCompact (u.toNat % 16) = some tt ∧ minSize tt = some k ∧
      fr.get 2 = some (.ref σ0.next) ∧ fr.get 0 = some (.ref l) ∧ σ.heap σ0.next = some tsNew ∧
      σ.heap l = some (.plain tlCls lfs) ∧
      Fields.get lfs (tlCls, "elemType") = some (.int (BitVec.ofNat 32 tt)) ∧
      Fields.get lfs (tlCls, "size") = some (.int size) ∧ CPAtH P R σ p t tmp ∧
      R.sink σ t = R.sink σ0 t ∧ σ0.next ≠ t ∧ σ0.next ≠ tmp ∧ σ0.next ≠ p ∧
      ¬ R.owns σ t σ0.next ∧ σ0.next < σ.next)]

/-- The contracts `readSetBegin()` uses: `readListBegin()`. -/
def Γ7 (P : Program) (R : TRep) : SpecEnv := fun sig =>
  if sig = rlbSig then some (rlbSpecA P R) else (tContracts R).env sig

/-! ## The closers of the verification conditions -/

theorem alloc_cpAtH {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} (o : Obj)
    (h : CPAtH P R σ p t tmp) : CPAtH P R (σ.alloc o).2 p t tmp :=
  CPAtH.intro (cpAt_alloc o (CPAtH.elim h)).1

theorem alloc_src {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} (o : Obj)
    (h : CPAtH P R σ p t tmp) : R.src (σ.alloc o).2 t = R.src σ t :=
  (cpAt_alloc o (CPAtH.elim h)).2.2.2.2.2.1

theorem alloc_sink {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} (o : Obj)
    (h : CPAtH P R σ p t tmp) : R.sink (σ.alloc o).2 t = R.sink σ t :=
  (cpAt_alloc o (CPAtH.elim h)).2.2.2.2.2.2.1

theorem alloc_notown {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} (o : Obj)
    (h : CPAtH P R σ p t tmp) : ¬ R.owns (σ.alloc o).2 t σ.next := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hinv, -⟩ := CPAtH.elim h
  rw [(cpAt_alloc o (CPAtH.elim h)).2.2.2.2.2.2.2]
  exact fun hown => Nat.lt_irrefl _ (R.inv_owns σ t σ.next hinv hown).1

theorem ts_get_elemType (L : List (FieldKey × Value)) (v1 v2 : Value) :
    Fields.get (Fields.set (Fields.set L (tsCls, "elemType") v1) (tsCls, "size") v2) (tsCls, "elemType") =
      some v1 := by
  rw [Fields.get_set, if_neg (show ¬ ((tsCls, "elemType") : FieldKey) = (tsCls, "size") by decide),
    Fields.get_set, if_pos rfl]

theorem ts_get_size (L : List (FieldKey × Value)) (v1 v2 : Value) :
    Fields.get (Fields.set (Fields.set L (tsCls, "elemType") v1) (tsCls, "size") v2) (tsCls, "size") =
      some v2 := by
  rw [Fields.get_set, if_pos rfl]

/-- `readListBegin()`'s precondition at the call (after `new TSet`). -/
theorem rsb_rlb_pre {P : Program} {R : TRep} {σ0 σ : State} {p t tmp : Addr}
    (hH : CPAtH P R σ p t tmp) (hsrc : R.src σ t = R.src σ0 t) (hnib : NibbleOKL (R.src σ0 t)) :
    ∃ x, (∃ x_1, CPAt P R σ p x x_1) ∧ NibbleOKL (R.src σ x) :=
  ⟨t, ⟨tmp, CPAtH.elim hH⟩, by rw [hsrc]; exact hnib⟩

/-- The cut at statement 3, from `readListBegin()`'s result. -/
theorem rsb_cut3 {P : Program} {R : TRep} {σ0 σc σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {lim : I64} {v : Option Value}
    (hN : rlbN P R [.ref p] σc v σ)
    (htr : Fields.get fs (tpCls, "trans_") = some (.ref t))
    (hte : Fields.get fs (cpCls, "temp") = some (.ref tmp))
    (hlim : Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim))
    (hpc : σc.heap p = some (.plain cpCls fs)) (hsrc : R.src σc t = R.src σ0 t)
    (hsink : R.sink σc t = R.sink σ0 t) (hs : σc.heap σ0.next = some tsNew)
    (hlt : σ0.next < σc.next) (hst : σ0.next ≠ t) (hstm : σ0.next ≠ tmp)
    (hown : ¬ R.owns σc t σ0.next) :
    ∃ u rest, R.src σ0 t = u :: rest ∧ ∃ x, listSizeJ u rest = some (x, R.src σ t) ∧ 0 ≤ x.toInt ∧
      InLimit lim x ∧ ∃ x_1, Spec.ttypeOfCompact (u.toNat % 16) = some x_1 ∧
        (∃ x, minSize x_1 = some x) ∧ ∃ x_2, v.getD Value.null = Value.ref x_2 ∧
          σ.heap σ0.next = some tsNew ∧ ∃ x_3, σ.heap x_2 = some (Obj.plain tlCls x_3) ∧
            Fields.get x_3 (tlCls, "elemType") = some (.int (BitVec.ofNat 32 x_1)) ∧
            Fields.get x_3 (tlCls, "size") = some (.int x) ∧ CPAtH P R σ p t tmp ∧
            R.sink σ t = R.sink σ0 t ∧ ¬ R.owns σ t σ0.next ∧ σ0.next < σ.next := by
  unfold rlbN at hN
  obtain ⟨u, rest, size, rest', tt, k, l, lfs, hs1, hsz, h0, hin, htt, hk, hsr, hsk, hC, hr, hl, hft, hfs,
    -, -, -, -, -, hPF, hOM⟩ := hN p t tmp fs lim rfl hpc htr hte hlim
  rw [hsrc] at hs1
  refine ⟨u, rest, hs1, size, by rw [hsz, hsr], h0, hin, tt, htt, ⟨k, hk⟩, l, by rw [hr]; rfl,
    by rw [hPF.2.2.2 σ0.next hlt hst hstm hown]; exact hs, lfs, hl, hft, hfs, CPAtH.intro hC,
    hsk.trans hsink, hOM σ0.next hlt hown, Nat.lt_of_lt_of_le hlt hPF.1⟩

/-- `readListBegin()` threw: the exception object is on the heap. -/
theorem rsb_exc_none {P : Program} {R : TRep} {σc σ' : State} {p t tmp e : Addr}
    {fs : List (FieldKey × Value)} {lim : I64}
    (hE : rlbE P R [.ref p] σc e σ') (hpc : σc.heap p = some (.plain cpCls fs))
    (htr : Fields.get fs (tpCls, "trans_") = some (.ref t))
    (hte : Fields.get fs (cpCls, "temp") = some (.ref tmp))
    (hlim : Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim))
    (hd : σ'.heap e = none) : False := by
  unfold rlbE at hE
  rcases hE p t tmp fs lim rfl hpc htr hte hlim with ⟨_, w, hw⟩ | ⟨_, _, _, _, ⟨_, w, hw⟩ | ⟨_, w, hw⟩⟩ |
    ⟨_, _, _, _, _, _, _, w, hw⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, w, hw⟩ <;> rw [hd] at hw <;> cases hw

/-- `readListBegin()` threw: so does `readSetBegin()` (the source is the one at the call). -/
theorem rlbE_shift {P : Program} {R : TRep} {σ0 σc σ' : State} {p t tmp e : Addr}
    {fs : List (FieldKey × Value)}
    (hE : rlbE P R [.ref p] σc e σ') (hH0 : CPAtH P R σ0 p t tmp)
    (hp0 : σ0.heap p = some (.plain cpCls fs)) (hpc : σc.heap p = some (.plain cpCls fs))
    (hsrc : R.src σc t = R.src σ0 t) : rlbE P R [.ref p] σ0 e σ' := by
  unfold rlbE at hE ⊢
  intro p' t' tmp' fs' lim hargs hp htr hte hlim
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  rw [hp0] at hp
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp
  subst hp
  obtain ⟨h1, h2⟩ := cpAt_fields (CPAtH.elim hH0) hp0 htr hte
  subst t' tmp'
  have h := hE p t tmp fs lim rfl hpc htr hte hlim
  rw [hsrc] at h
  exact h

/-- The return: the new `TSet`. -/
theorem rsb_post {P : Program} {R : TRep} {σ0 σ : State} {p t tmp : Addr}
    {fs F : List (FieldKey × Value)} {lim : I64} {u : UInt8} {rest : Bytes} {size : I32} {tt k : Nat}
    {o1 : Obj}
    (hH0 : CPAtH P R σ0 p t tmp) (hp0 : σ0.heap p = some (.plain cpCls fs))
    (hlim0 : Fields.get fs (cpCls, "containerLengthLimit_") = some (.long lim))
    (hsrc0 : R.src σ0 t = u :: rest) (hsz : listSizeJ u rest = some (size, R.src σ t))
    (h0 : 0 ≤ size.toInt) (hin : InLimit lim size)
    (htt : Spec.ttypeOfCompact (u.toNat % 16) = some tt) (hk : minSize tt = some k)
    (hH : CPAtH P R σ p t tmp) (hsink : R.sink σ t = R.sink σ0 t)
    (hst : σ0.next ≠ t) (hstm : σ0.next ≠ tmp) (hsp : σ0.next ≠ p) (hown : ¬ R.owns σ t σ0.next)
    (hlt : σ0.next < σ.next)
    (hFt : Fields.get F (tsCls, "elemType") = some (.int (JInt.toByte (BitVec.ofNat 32 tt))))
    (hFs : Fields.get F (tsCls, "size") = some (.int size)) :
    rsbN P R [.ref p] σ0 (some (.ref σ0.next)) ((σ.setObj σ0.next o1).setObj σ0.next (.plain tsCls F)) := by
  obtain ⟨hC1, hsrc1, hsink1, how1⟩ := cpAt_setOther o1 (CPAtH.elim hH) hsp hst hstm hown
  have hown1 : ¬ R.owns (σ.setObj σ0.next o1) t σ0.next := by rw [how1]; exact hown
  obtain ⟨hC2, hsrc2, hsink2, -⟩ := cpAt_setOther (.plain tsCls F) hC1 hsp hst hstm hown1
  have hle : tt ≤ 16 := ttypeOfCompact_le htt
  unfold rsbN
  intro p' t' tmp' fs' lim' hargs hp htr hte hlim
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  subst hargs
  rw [hp0] at hp
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp
  subst hp
  obtain ⟨h1, h2⟩ := cpAt_fields (CPAtH.elim hH0) hp0 htr hte
  subst t' tmp'
  rw [hlim0] at hlim
  simp only [Option.some.injEq, Value.long.injEq] at hlim
  subst hlim
  refine ⟨u, rest, size, R.src σ t, tt, k, σ0.next, F, hsrc0, hsz, h0, hin, htt, hk,
    by rw [hsrc2, hsrc1], by rw [hsink2, hsink1, hsink], hC2, rfl,
    setObj_heap_self (by rw [State.next_setObj]; exact hlt), by rw [hFt, toByte_ofNat_lt (by omega)], hFs⟩

end EquivLean.Demo.Thrift.Java
