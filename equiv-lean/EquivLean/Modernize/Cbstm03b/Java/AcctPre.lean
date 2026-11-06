import EquivLean.Modernize.Cbstm03b.Java.AcctInv

/-!
# CBSTM03B → Java, `acctProc`: the precondition, object by object

`pre_dest`: the objects the paths read (the State object, its ACCTFILE object with the record array, its FD record
object and status, the area with its six fields, the operation string) and the facts the final states need.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.AcctP

open EquivLean.Modernize.Cbstm03b.Java

/-- The facts of the precondition the final states need, kept out of `jvc`'s sight (it unpacks the hypotheses it
can read and renames their variables). -/
@[irreducible] def FinCtx (oe st q : Addr) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (σ0 : State) (fs fsr fsq : List (FieldKey × Value)) (o4 fdr xop : Addr)
    (sv : Value) (dd rc key fldt : List UInt8) (b : UInt8) (kl : Int) (sdd src skey sfl : Value) : Prop :=
  StateAtM σ0 st s ∧ SepM σ0 st ∧ EnvAtM σ0 oe oeM ∧ Glue.ValidSt s ∧ Glue.KeyOk a ∧ Model.aDd a = ddAcct ∧
  InitsDone σ0 ∧ JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ0 (.ref q) a ∧ Model.LkM03bArea.Valid a ∧
  FileAtM "Cbstm03b$AcctFile" "Cbstm03b$FdAcctfileRec" Model.FdAcctfileRec σ0 (.ref o4) s.acct ∧
  σ0.heap fdr = some (.plain "Cbstm03b$FdAcctfileRec" fsr) ∧
  JRecAt Model.FdAcctfileRec "Cbstm03b$FdAcctfileRec" σ0 (.ref fdr) s.acctRec ∧
  NotRecOf σ0 "Cbstm03b$AcctFile" (.ref fdr) (.ref o4) ∧
  Fields.get fs ("Cbstm03b$State", "fdAcctfileRec") = some (.ref fdr) ∧
  JStrAt σ0 sv (cp037Str (s.acctSt.map ebcdicOfLatin1)) ∧
  a = [.str dd, .str [b], .str rc, .str key, .num kl, .str fldt] ∧
  dd.length = 8 ∧ rc.length = 2 ∧ key.length = 25 ∧ -10000 < kl ∧ kl < 10000 ∧ fldt.length = 1000 ∧
  Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bDd") = some sdd ∧ JStrAt σ0 sdd (cp037Str dd) ∧
  Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bOper") = some (.ref xop) ∧ JStrAt σ0 (.ref xop) (cp037Str [b]) ∧
  JStrAt σ0 src (cp037Str rc) ∧
  Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bKey") = some skey ∧ JStrAt σ0 skey (cp037Str key) ∧
  Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bKeyLn") = some (.long (BitVec.ofInt 64 kl)) ∧
  Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bFldt") = some sfl ∧ JStrAt σ0 sfl (cp037Str fldt) ∧
  fdr ≠ st ∧ fdr ≠ o4 ∧ fdr ≠ q ∧ st < σ0.next ∧ o4 < σ0.next ∧ q < σ0.next ∧ fdr < σ0.next ∧
  Away (AccA st o4 q fdr) σ0 [] ∧ Away (AccA st o4 q fdr) σ0 restCls

theorem pre_dest {oe st q : Addr} {opv : Value} {oeM : Model.OpenErrs} {s : Model.StM}
    {a : List EquivLean.Cobol.Rec.FVal} {σ0 : State}
    (hpre : (procSpecG ddAcct oe st q opv oeM s a).pre [.ref oe, .ref st, .ref q, opv] σ0) :
    ∃ (fs fs4 fsr fsq : List (FieldKey × Value)) (o4 fdr xop l : Addr) (sv : Value) (et : JType)
      (xs : List Value) (dd rc key fldt : List UInt8) (b : UInt8) (kl : Int) (sdd src skey sfl : Value),
      σ0.heap st = some (.plain "Cbstm03b$State" fs) ∧
      Fields.get fs ("Cbstm03b$State", "acctFile") = some (.ref o4) ∧
      σ0.heap o4 = some (.plain "Cbstm03b$AcctFile" fs4) ∧
      FileAtM "Cbstm03b$AcctFile" "Cbstm03b$FdAcctfileRec" Model.FdAcctfileRec σ0 (.ref o4) s.acct ∧
      Fields.get fs4 ("Cbstm03b$AcctFile", "open") = some (.ofBool s.acct.isOpen) ∧
      Fields.get fs4 ("Cbstm03b$AcctFile", "recs") = some (.ref l) ∧ σ0.heap l = some (.array et xs) ∧
      xs.length < 2147483648 ∧
      Forall2 (fun x vals => JRecAt Model.FdAcctfileRec "Cbstm03b$FdAcctfileRec" σ0 x vals) xs s.acct.recs ∧
      Fields.get fs ("Cbstm03b$State", "fdAcctfileRec") = some (.ref fdr) ∧
      σ0.heap fdr = some (.plain "Cbstm03b$FdAcctfileRec" fsr) ∧
      JRecAt Model.FdAcctfileRec "Cbstm03b$FdAcctfileRec" σ0 (.ref fdr) s.acctRec ∧
      NotRecOf σ0 "Cbstm03b$AcctFile" (.ref fdr) (.ref o4) ∧
      Fields.get fs ("Cbstm03b$State", "acctfileStatus") = some sv ∧
      JStrAt σ0 sv (cp037Str (s.acctSt.map ebcdicOfLatin1)) ∧
      σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq) ∧
      a = [.str dd, .str [b], .str rc, .str key, .num kl, .str fldt] ∧
      dd.length = 8 ∧ rc.length = 2 ∧ key.length = 25 ∧ -10000 < kl ∧ kl < 10000 ∧ fldt.length = 1000 ∧
      Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bDd") = some sdd ∧ JStrAt σ0 sdd (cp037Str dd) ∧
      Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bOper") = some (.ref xop) ∧
      σ0.heap xop = some (.str (cp037Str [b])) ∧ opv = .ref xop ∧
      Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bRc") = some src ∧ JStrAt σ0 src (cp037Str rc) ∧
      Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bKey") = some skey ∧ JStrAt σ0 skey (cp037Str key) ∧
      Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bKeyLn") = some (.long (BitVec.ofInt 64 kl)) ∧
      Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bFldt") = some sfl ∧ JStrAt σ0 sfl (cp037Str fldt) ∧
      st ≠ o4 ∧ st ≠ q ∧ o4 ≠ q ∧ fdr ≠ st ∧ fdr ≠ o4 ∧ fdr ≠ q ∧
      st < σ0.next ∧ o4 < σ0.next ∧ q < σ0.next ∧ fdr < σ0.next ∧ xop < σ0.next ∧ l < σ0.next ∧
      Keeps (AccA st o4 q fdr) σ0 σ0 ∧ Away (AccA st o4 q fdr) σ0 [] ∧ Away (AccA st o4 q fdr) σ0 restCls := by
  obtain ⟨-, -, hS, hSep, hA, -, hVa, -, -, hOp, -⟩ := hpre
  obtain ⟨fs, hst, -, -, -, ⟨⟨x4, g4, m4⟩, ⟨xr, gr, mr⟩, ⟨sv, gs, js⟩⟩⟩ := stateAtM_iff.1 hS
  obtain ⟨o4, fs4, l, et, xs, e4, ho4, hop4, hrec4, hl, hlen, hrs, -⟩ := id m4
  subst e4
  obtain ⟨fdr, fsr, er, hr, -⟩ := id mr
  subst er
  obtain ⟨fs0, hst0, -, c2⟩ := hSep
  rw [hst] at hst0
  cases hst0
  obtain ⟨q', fsq, dd, op, rc, key, kl, fldt, sdd, sop, src, skey, sfl, eq, hq, ha, ldd, lop, lrc, lkey, hkl1,
    hkl2, lfl, g1, j1, g2, j2, g3, j3, g4', j4, g5, g6, j6⟩ := areaAt_of hA hVa
  cases eq
  obtain ⟨fsq', hq', gop⟩ := hOp
  rw [hq] at hq'
  cases hq'
  rw [g2] at gop
  cases gop
  obtain ⟨xop, exop, hxop⟩ := j2
  subst exop
  obtain ⟨b, rfl⟩ : ∃ b, op = [b] := by
    match op, lop with
    | [b], _ => exact ⟨b, rfl⟩
  have n1 : st ≠ o4 := ne_of_cls hst ho4 (by decide)
  have n2 : st ≠ q := ne_of_cls hst hq (by decide)
  have n3 : o4 ≠ q := ne_of_cls ho4 hq (by decide)
  have n4 : fdr ≠ st := ne_of_cls hr hst (by decide)
  have n5 : fdr ≠ o4 := ne_of_cls hr ho4 (by decide)
  have n6 : fdr ≠ q := ne_of_cls hr hq (by decide)
  exact ⟨fs, fs4, fsr, fsq, o4, fdr, xop, l, sv, et, xs, dd, rc, key, fldt, b, kl, sdd, src, skey, sfl,
    hst, g4, ho4, m4, hop4, hrec4, hl, hlen, hrs, gr, hr, mr, c2 _ _ gr g4, gs, js, hq, ha, ldd, lrc, lkey, hkl1,
    hkl2, lfl, g1, j1, g2, hxop, rfl, g3, j3, g4', j4, g5, g6, j6, n1, n2, n3, n4, n5, n6,
    State.lt_next_of_heap hst, State.lt_next_of_heap ho4, State.lt_next_of_heap hq, State.lt_next_of_heap hr,
    State.lt_next_of_heap hxop, State.lt_next_of_heap hl, keeps_refl _ _,
    accA_away hst ho4 hq hr [] (by simp), accA_away hst ho4 hq hr _ (by decide)⟩

/-- Any facts kept out of `jvc`'s sight. -/
@[irreducible] def Hid (P : Prop) : Prop := P

theorem hid_intro {P : Prop} (h : P) : Hid P := by unfold Hid; exact h

theorem hid_elim {P : Prop} (h : Hid P) : P := by unfold Hid at h; exact h

/-- The key value: `acctVal` of the area is the key loop's value (on a keyed read of ACCTFILE). -/
theorem acctVal_keyVal {a : List EquivLean.Cobol.Rec.FVal} {dd op rc key fldt : List UInt8} {kl : Int}
    (hK : Glue.KeyOk a) (hop : Model.aOp a = opReadK) (hdd : Model.aDd a = ddAcct)
    (ha : a = [.str dd, .str op, .str rc, .str key, .num kl, .str fldt]) (lkey : key.length = 25) :
    Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat = (keyVal a : Int) := by
  obtain ⟨k1, k2⟩ := hK
  obtain ⟨hk1, hk2⟩ := k1 hop (Or.inr hdd)
  obtain ⟨-, hdig⟩ := k2 hop hdd
  have hkey : Model.aKey a = key := by subst ha; rfl
  have hlen : ((Model.aKey a).take (Model.aKeyLn a).toNat).length = (Model.aKeyLn a).toNat := by
    rw [List.length_take, hkey, lkey]; omega
  exact jkey_eq_acctVal _ _ (by omega) hlen hdig

theorem FinCtx.dd {oe st q : Addr} {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal}
    {σ0 : State} {fs fsr fsq : List (FieldKey × Value)} {o4 fdr xop : Addr} {sv : Value}
    {dd rc key fldt : List UInt8} {b : UInt8} {kl : Int} {sdd src skey sfl : Value}
    (h : FinCtx oe st q oeM s a σ0 fs fsr fsq o4 fdr xop sv dd rc key fldt b kl sdd src skey sfl) :
    Model.aDd a = ddAcct := by
  unfold FinCtx at h; exact h.2.2.2.2.2.1

theorem FinCtx.js {oe st q : Addr} {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal}
    {σ0 : State} {fs fsr fsq : List (FieldKey × Value)} {o4 fdr xop : Addr} {sv : Value}
    {dd rc key fldt : List UInt8} {b : UInt8} {kl : Int} {sdd src skey sfl : Value}
    (h : FinCtx oe st q oeM s a σ0 fs fsr fsq o4 fdr xop sv dd rc key fldt b kl sdd src skey sfl) :
    JStrAt σ0 sv (cp037Str (s.acctSt.map ebcdicOfLatin1)) := by
  unfold FinCtx at h; exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The precondition as the paths use it: the objects `jvc` reads, and `FinCtx` for the final states. -/
theorem pre_fin {oe st q : Addr} {opv : Value} {oeM : Model.OpenErrs} {s : Model.StM}
    {a : List EquivLean.Cobol.Rec.FVal} {σ0 : State}
    (hpre : (procSpecG ddAcct oe st q opv oeM s a).pre [.ref oe, .ref st, .ref q, opv] σ0) :
    ∃ (fs fs4 fsr fsq : List (FieldKey × Value)) (o4 fdr xop l : Addr) (sv : Value) (et : JType)
      (xs : List Value) (dd rc key fldt : List UInt8) (b : UInt8) (kl : Int) (sdd src skey sfl : Value),
      σ0.heap st = some (.plain "Cbstm03b$State" fs) ∧
      Fields.get fs ("Cbstm03b$State", "acctFile") = some (.ref o4) ∧
      σ0.heap o4 = some (.plain "Cbstm03b$AcctFile" fs4) ∧
      Fields.get fs4 ("Cbstm03b$AcctFile", "open") = some (.ofBool s.acct.isOpen) ∧
      Fields.get fs4 ("Cbstm03b$AcctFile", "recs") = some (.ref l) ∧ σ0.heap l = some (.array et xs) ∧
      xs.length < 2147483648 ∧
      Forall2 (fun x vals => JRecAt Model.FdAcctfileRec "Cbstm03b$FdAcctfileRec" σ0 x vals) xs s.acct.recs ∧
      s.acct.pos < 2147483648 ∧
      Fields.get fs4 ("Cbstm03b$AcctFile", "pos") = some (.int (BitVec.ofNat 32 s.acct.pos)) ∧
      Fields.get fs4 ("Cbstm03b$AcctFile", "eof") = some (.ofBool s.acct.eof) ∧
      Fields.get fs ("Cbstm03b$State", "fdAcctfileRec") = some (.ref fdr) ∧
      σ0.heap fdr = some (.plain "Cbstm03b$FdAcctfileRec" fsr) ∧
      Fields.get fs ("Cbstm03b$State", "acctfileStatus") = some sv ∧
      σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq) ∧
      σ0.heap xop = some (.str (cp037Str [b])) ∧ opv = .ref xop ∧ Model.aOp a = b ∧
      Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bOper") = some (.ref xop) ∧
      Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bRc") = some src ∧
      Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bKey") = some skey ∧
      Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bKeyLn") = some (.long (BitVec.ofInt 64 kl)) ∧
      Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bFldt") = some sfl ∧
      st ≠ o4 ∧ st ≠ q ∧ o4 ≠ q ∧ σ0.initOf "Cbstm03b" = .done ∧
      FinCtx oe st q oeM s a σ0 fs fsr fsq o4 fdr xop sv dd rc key fldt b kl sdd src skey sfl := by
  obtain ⟨-, hE, hS, hSep, hA, hV, hVa, hK, hdd, hOp, hI⟩ := id hpre
  obtain ⟨fs, fs4, fsr, fsq, o4, fdr, xop, l, sv, et, xs, dd, rc, key, fldt, b, kl, sdd, src, skey, sfl,
    hst, g4, ho4, m4, hop4, hrec4, hl, hlen, hrs, gr, hr, mr, hnr, gs, js, hq, ha, ldd, lrc, lkey, hkl1,
    hkl2, lfl, g1, j1, g2, hxop, hopv, g3, j3, g4', j4, g5, g6, j6, n1, n2, n3, n4, n5, n6,
    lst, lo4, lq, lfdr, lxop, ll, hk0, haw0, hawr⟩ := pre_dest hpre
  obtain ⟨o', fs', l', et', xs', e', ho', -, -, -, -, -, hp, hpos, heof⟩ := id m4
  cases e'
  rw [ho4] at ho'
  cases ho'
  have hb : Model.aOp a = b := by rw [ha]; rfl
  refine ⟨fs, fs4, fsr, fsq, o4, fdr, xop, l, sv, et, xs, dd, rc, key, fldt, b, kl, sdd, src, skey, sfl,
    hst, g4, ho4, hop4, hrec4, hl, hlen, hrs, hp, hpos, heof, gr, hr, gs, hq, hxop, hopv, hb, g2, g3, g4', g5, g6,
    n1, n2, n3, hI.1, ?_⟩
  unfold FinCtx
  exact ⟨hS, hSep, hE, hV, hK, hdd, hI, hA, hVa, m4, hr, mr, hnr, gr, js, ha, ldd, lrc, lkey, hkl1, hkl2, lfl,
    g1, j1, g2, ⟨xop, rfl, hxop⟩, j3, g4', j4, g5, g6, j6, n4, n5, n6, lst, lo4, lq, lfdr, haw0, hawr⟩

end EquivLean.Modernize.Cbstm03b.Java.AcctP
