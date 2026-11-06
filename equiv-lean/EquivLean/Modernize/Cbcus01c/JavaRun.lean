import EquivLean.Modernize.Cbcus01c.JavaProof
import EquivLean.Modernize.GlueKit
import EquivLean.Modernize.JLBridge
import EquivLean.Modernize.JL.Cbcus01cLink

/-!
# CBCUS01C → Java: the translation side

JimpleLean's session proved the contract of `Cbcus01c.run` (`cu_run_sat : Sat Gen.prog runRef
cuRunSpecJ`, in `Modernize/JL/`, copied from its snapshot by `tools/modernize/import_jl.py`),
stated with the texts that `fmtRecord` builds.  `sat_runSpec_of_J`: that contract implies ours
(`runSpec`, stated with the field values of the records), so `statement_of_sat` gives the generated
statement.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbcus01c.Java

open EquivLean.Modernize.JL EquivLean.Modernize.JLBridge

/-! ## The records: what JimpleLean's contract reads, and their lines -/

/-- A valid customer record's values, by kind. -/
theorem cust_shape {v : List EquivLean.Cobol.Rec.FVal} (hv : CustomerRecord.Valid v) :
    ∃ cid fn mn ln a1 a2 a3 st cc zp p1 p2 ssn gid dob eft pci fico fill,
      v = [.num cid, .str fn, .str mn, .str ln, .str a1, .str a2, .str a3, .str st, .str cc,
        .str zp, .str p1, .str p2, .num ssn, .str gid, .str dob, .str eft, .str pci, .num fico,
        .str fill] ∧
      cid.natAbs < 1000000000 ∧ 0 ≤ cid ∧ ssn.natAbs < 1000000000 ∧ 0 ≤ ssn ∧
      fico.natAbs < 1000 ∧ 0 ≤ fico ∧ fn.length = 25 ∧ mn.length = 25 ∧ ln.length = 25 ∧
      a1.length = 50 ∧ a2.length = 50 ∧ a3.length = 50 ∧ st.length = 2 ∧ cc.length = 3 ∧
      zp.length = 10 ∧ p1.length = 15 ∧ p2.length = 15 ∧ gid.length = 20 ∧ dob.length = 10 ∧
      eft.length = 10 ∧ pci.length = 1 ∧ fill.length = 168 := by
  have hl : v.length = 19 := hv.length_eq.symm
  match v, hl, hv with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18], _,
      .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8
        (.cons h9 (.cons h10 (.cons h11 (.cons h12 (.cons h13 (.cons h14 (.cons h15 (.cons h16
        (.cons h17 (.cons h18 .nil)))))))))))))))))) =>
    obtain ⟨cid, rfl, hcid⟩ := GlueKit.num_of_valid rfl h0
    obtain ⟨fn, rfl, hfn⟩ := GlueKit.str_of_valid rfl h1
    obtain ⟨mn, rfl, hmn⟩ := GlueKit.str_of_valid rfl h2
    obtain ⟨ln, rfl, hln⟩ := GlueKit.str_of_valid rfl h3
    obtain ⟨a1, rfl, ha1⟩ := GlueKit.str_of_valid rfl h4
    obtain ⟨a2, rfl, ha2⟩ := GlueKit.str_of_valid rfl h5
    obtain ⟨a3, rfl, ha3⟩ := GlueKit.str_of_valid rfl h6
    obtain ⟨st, rfl, hst⟩ := GlueKit.str_of_valid rfl h7
    obtain ⟨cc, rfl, hcc⟩ := GlueKit.str_of_valid rfl h8
    obtain ⟨zp, rfl, hzp⟩ := GlueKit.str_of_valid rfl h9
    obtain ⟨p1, rfl, hp1⟩ := GlueKit.str_of_valid rfl h10
    obtain ⟨p2, rfl, hp2⟩ := GlueKit.str_of_valid rfl h11
    obtain ⟨ssn, rfl, hssn⟩ := GlueKit.num_of_valid rfl h12
    obtain ⟨gid, rfl, hgid⟩ := GlueKit.str_of_valid rfl h13
    obtain ⟨dob, rfl, hdob⟩ := GlueKit.str_of_valid rfl h14
    obtain ⟨eft, rfl, heft⟩ := GlueKit.str_of_valid rfl h15
    obtain ⟨pci, rfl, hpci⟩ := GlueKit.str_of_valid rfl h16
    obtain ⟨fico, rfl, hfico⟩ := GlueKit.num_of_valid rfl h17
    obtain ⟨fill, rfl, hfill⟩ := GlueKit.str_of_valid rfl h18
    obtain ⟨_, k0, -, -, n0, -⟩ := hcid
    obtain ⟨_, k12, -, -, n12, -⟩ := hssn
    obtain ⟨_, k17, -, -, n17, -⟩ := hfico
    cases k0; cases k12; cases k17
    rw [GlueKit.holds_display rfl] at n0 n12 n17
    exact ⟨cid, fn, mn, ln, a1, a2, a3, st, cc, zp, p1, p2, ssn, gid, dob, eft, pci, fico, fill,
      rfl, n0.1, n0.2 rfl, n12.1, n12.2 rfl, n17.1, n17.2 rfl, hfn, hmn, hln, ha1, ha2, ha3, hst,
      hcc, hzp, hp1, hp2, hgid, hdob, heft, hpci, hfill⟩

/-- A string field holding the CP037 text of `bs` is one `fmtRecord` reads, and that text cut or
padded to its length is the text itself. -/
theorem cstr_field {σ : Jimple.State} {c : Addr} {fs : List (FieldKey × Jimple.Value)}
    {f : EquivLean.Cobol.Rec.Field} {bs : List UInt8} {k : String} {n : Nat}
    (hc : σ.heap c = some (.plain custCls fs))
    (h : jFieldAt σ "Cbcus01c$CustomerRecord" fs f (.str bs)) (hk : f.jname = k)
    (hn : bs.length = n) (hn' : n < 2147483648) :
    CStrField σ fs k ∧ ctext σ c k n = cp037Str bs := by
  subst hk hn
  obtain ⟨s, hs, x, rfl, hx⟩ := h
  have hs' : Fields.get fs (custCls, f.jname) = some (.ref x) := hs
  refine ⟨⟨x, _, hs', hx, by rw [cp037Str_length]; exact hn'⟩, ?_⟩
  have e : cfieldOf σ c f.jname = .ref x := by simp [cfieldOf, hc, hs']
  unfold ctext
  rw [e]
  exact fixStr_argText hx

/-- A `long` field holding `0 ≤ v < 2 ^ 63` is one `fmtRecord` reads, and its digits are `v`'s. -/
theorem clong_field {σ : Jimple.State} {c : Addr} {fs : List (FieldKey × Jimple.Value)}
    {f : EquivLean.Cobol.Rec.Field} {v : Int} {k : String} {d : Nat}
    (hc : σ.heap c = some (.plain custCls fs))
    (h : jFieldAt σ "Cbcus01c$CustomerRecord" fs f (.num v)) (hk : f.jname = k) (h0 : 0 ≤ v)
    (h1 : v < 2 ^ 63) :
    CLongField fs k ∧ zpadStr (cfieldLong σ c k).toNat d = (zpad d v.natAbs).map (BitVec.ofNat 16) := by
  subst hk
  have hf : Fields.get fs (custCls, f.jname) = some (.long (BitVec.ofInt 64 v)) := h
  refine ⟨⟨_, hf, by rw [toInt_ofInt64 h0 h1]; exact h0⟩, ?_⟩
  have e : cfieldLong σ c f.jname = BitVec.ofInt 64 v := by simp [cfieldLong, cfieldOf, hc, hf]
  rw [e]
  exact zpadStr_ofInt64 d h0 h1

set_option maxHeartbeats 1000000 in
/-- A record object holding valid field values is what JimpleLean's contract reads, and its line
is ours. -/
theorem jrec_cust {σ : Jimple.State} {x : Jimple.Value} {v : List EquivLean.Cobol.Rec.FVal}
    (hx : JRecAt CustomerRecord "Cbcus01c$CustomerRecord" σ x v) (hv : CustomerRecord.Valid v) :
    ∃ c, x = .ref c ∧ CustOk σ c ∧ crecLineV σ x = recLine v := by
  obtain ⟨cid, fn, mn, ln, a1, a2, a3, st, cc, zp, p1, p2, ssn, gid, dob, eft, pci, fico, fill,
    rfl, hcid, hcid0, hssn, hssn0, hfico, hfico0, hfn, hmn, hln, ha1, ha2, ha3, hst, hcc, hzp, hp1,
    hp2, hgid, hdob, heft, hpci, hfill⟩ := cust_shape hv
  obtain ⟨c, fs, rfl, hc, hf⟩ := hx
  match hf with
  | .cons f0 (.cons f1 (.cons f2 (.cons f3 (.cons f4 (.cons f5 (.cons f6 (.cons f7 (.cons f8
      (.cons f9 (.cons f10 (.cons f11 (.cons f12 (.cons f13 (.cons f14 (.cons f15 (.cons f16
      (.cons f17 (.cons f18 .nil)))))))))))))))))) =>
    have e0 := clong_field (k := "custId") (d := 9) hc f0 rfl hcid0 (by omega)
    have e1 := cstr_field (k := "custFirstName") hc f1 rfl hfn (by decide)
    have e2 := cstr_field (k := "custMiddleName") hc f2 rfl hmn (by decide)
    have e3 := cstr_field (k := "custLastName") hc f3 rfl hln (by decide)
    have e4 := cstr_field (k := "custAddrLine1") hc f4 rfl ha1 (by decide)
    have e5 := cstr_field (k := "custAddrLine2") hc f5 rfl ha2 (by decide)
    have e6 := cstr_field (k := "custAddrLine3") hc f6 rfl ha3 (by decide)
    have e7 := cstr_field (k := "custAddrStateCd") hc f7 rfl hst (by decide)
    have e8 := cstr_field (k := "custAddrCountryCd") hc f8 rfl hcc (by decide)
    have e9 := cstr_field (k := "custAddrZip") hc f9 rfl hzp (by decide)
    have e10 := cstr_field (k := "custPhoneNum1") hc f10 rfl hp1 (by decide)
    have e11 := cstr_field (k := "custPhoneNum2") hc f11 rfl hp2 (by decide)
    have e12 := clong_field (k := "custSsn") (d := 9) hc f12 rfl hssn0 (by omega)
    have e13 := cstr_field (k := "custGovtIssuedId") hc f13 rfl hgid (by decide)
    have e14 := cstr_field (k := "custDobYyyyMmDd") hc f14 rfl hdob (by decide)
    have e15 := cstr_field (k := "custEftAccountId") hc f15 rfl heft (by decide)
    have e16 := cstr_field (k := "custPriCardHolderInd") hc f16 rfl hpci (by decide)
    have e17 := clong_field (k := "custFicoCreditScore") (d := 3) hc f17 rfl hfico0 (by omega)
    have e18 := cstr_field (k := "filler1") hc f18 rfl hfill (by decide)
    refine ⟨c, rfl, ?_, ?_⟩
    · unfold CustOk
      exact ⟨fs, hc, e0.1, e1.1, e2.1, e3.1, e4.1, e5.1, e6.1, e7.1, e8.1, e9.1, e10.1, e11.1,
        e12.1, e13.1, e14.1, e15.1, e16.1, e17.1, e18.1⟩
    · have erl : recLine [.num cid, .str fn, .str mn, .str ln, .str a1, .str a2, .str a3, .str st,
          .str cc, .str zp, .str p1, .str p2, .num ssn, .str gid, .str dob, .str eft, .str pci,
          .num fico, .str fill] =
          (zpad 9 cid.natAbs).map (BitVec.ofNat 16) ++ (cp037Str fn ++ (cp037Str mn ++
          (cp037Str ln ++ (cp037Str a1 ++ (cp037Str a2 ++ (cp037Str a3 ++ (cp037Str st ++
          (cp037Str cc ++ (cp037Str zp ++ (cp037Str p1 ++ (cp037Str p2 ++
          ((zpad 9 ssn.natAbs).map (BitVec.ofNat 16) ++ (cp037Str gid ++ (cp037Str dob ++
          (cp037Str eft ++ (cp037Str pci ++ ((zpad 3 fico.natAbs).map (BitVec.ofNat 16) ++
          (cp037Str fill ++ [])))))))))))))))))) := rfl
      rw [erl]
      show custLine σ c = _
      unfold custLine
      rw [e0.2, e1.2, e2.2, e3.2, e4.2, e5.2, e6.2, e7.2, e8.2, e9.2, e10.2, e11.2, e12.2, e13.2,
        e14.2, e15.2, e16.2, e17.2, e18.2]
      simp only [List.append_assoc, List.append_nil]

theorem cuStartText_eq : cuStartText = startLine := by decide +kernel
theorem cuEndText_eq : cuEndText = endLine := by decide +kernel

/-- **JimpleLean's contract of `run` implies ours.** -/
theorem sat_runSpec_of_J (h : Sat Gen.prog runRef cuRunSpecJ) : Sat Gen.prog runRef runSpec := by
  intro args σ o hpre hexec
  obtain ⟨a, vals, rfl, ⟨et, xs, hheap, hlen, hrec⟩, hv, hi1, hi2, hi3⟩ := hpre
  have hok : ∀ x ∈ xs, ∃ c, x = .ref c ∧ CustOk σ c := by
    intro x hx
    obtain ⟨v, hvm, hxv⟩ := forall2_mem hrec x hx
    obtain ⟨c, rfl, hc, -⟩ := jrec_cust hxv (hv v hvm)
    exact ⟨c, rfl, hc⟩
  have hpost := h [.ref a] σ o ⟨a, et, xs, rfl, hheap, hlen, hok, hi1, hi2, hi3⟩ hexec
  cases o with
  | normal r σ' =>
    intro a' vals' heq hfile' hv'
    simp only [List.cons.injEq, Jimple.Value.ref.injEq, and_true] at heq
    subst heq
    obtain ⟨et', xs', hheap', -, hrec'⟩ := hfile'
    rw [hheap] at hheap'
    simp only [Option.some.injEq, Jimple.Obj.array.injEq] at hheap'
    obtain ⟨rfl, rfl⟩ := hheap'
    obtain ⟨res, fs, l, k, ys, m, hr, hres, hl, hlist, hstrs, hab⟩ := hpost a et xs rfl hheap
    refine ⟨res, fs, l, k, ys, m, hr, hres, hl, hlist, ?_, hab⟩
    have hmap : xs.flatMap (fun v => [crecLineV σ v, crecLineV σ v]) =
        vals'.flatMap (fun v => [recLine v, recLine v]) :=
      forall2_flatMap_eq (forall2_imp (fun x v hxv => by
        obtain ⟨c, rfl, -, e⟩ := jrec_cust hxv.1 hxv.2
        exact congrArg (fun s => [s, s]) e) (forall2_and_mem hrec' hv'))
    rw [custLines_length, hmap, cuStartText_eq, cuEndText_eq] at hstrs
    exact strsAt_forall2 hstrs
  | exc e σ' => simp [cuRunSpecJ, Spec.of] at hpost
  | wrong msg => simp [cuRunSpecJ, Spec.of] at hpost

/-- **CBCUS01C → Java, every input**: the generated statement (`JavaStatement.lean`). -/
theorem java : Statement := statement_of_sat (sat_runSpec_of_J cu_run_sat)

end EquivLean.Modernize.Cbcus01c.Java

#print axioms EquivLean.Modernize.Cbcus01c.Java.java
