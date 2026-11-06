import EquivLean.Modernize.Cbact03c.JavaProof
import EquivLean.Modernize.GlueKit
import EquivLean.Modernize.JLBridge
import EquivLean.Modernize.JL.Cbact03cLink

/-!
# CBACT03C → Java: the translation side

JimpleLean's session proved the contract of `Cbact03c.run` (`c3_run_sat : Sat Gen.prog runRef
c3RunSpecJ`, in `Modernize/JL/`, copied from its snapshot by `tools/modernize/import_jl.py`),
stated with the texts that `recordText` builds.  `sat_runSpec_of_J`: that contract implies ours
(`runSpec`, stated with the field values of the records), so `statement_of_sat` gives the generated
statement.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbact03c.Java

open EquivLean.Modernize.JL EquivLean.Modernize.JLBridge

/-! ## The records: what JimpleLean's contract reads, and their lines -/

/-- A valid cross-reference record's values, by kind. -/
theorem xref_shape {v : List EquivLean.Cobol.Rec.FVal} (hv : CardXrefRecord.Valid v) :
    ∃ card cust acct fill, v = [.str card, .num cust, .num acct, .str fill] ∧
      cust.natAbs < 1000000000 ∧ 0 ≤ cust ∧ acct.natAbs < 100000000000 ∧ 0 ≤ acct ∧
      card.length = 16 ∧ fill.length = 14 := by
  have hl : v.length = 4 := hv.length_eq.symm
  match v, hl, hv with
  | [x0, x1, x2, x3], _, .cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))) =>
    obtain ⟨card, rfl, hcard⟩ := GlueKit.str_of_valid rfl h0
    obtain ⟨cust, rfl, hcust⟩ := GlueKit.num_of_valid rfl h1
    obtain ⟨acct, rfl, hacct⟩ := GlueKit.num_of_valid rfl h2
    obtain ⟨fill, rfl, hfill⟩ := GlueKit.str_of_valid rfl h3
    obtain ⟨_, k1, -, -, n1, -⟩ := hcust
    obtain ⟨_, k2, -, -, n2, -⟩ := hacct
    cases k1; cases k2
    rw [GlueKit.holds_display rfl] at n1 n2
    exact ⟨card, cust, acct, fill, rfl, n1.1, n1.2 rfl, n2.1, n2.2 rfl, hcard, hfill⟩

/-- A string field holding the CP037 text of `bs` is one the program reads, and that text cut or
padded to its length is the text itself. -/
theorem xstr_field {σ : Jimple.State} {c : Addr} {fs : List (FieldKey × Jimple.Value)}
    {f : EquivLean.Cobol.Rec.Field} {bs : List UInt8} {k : String} {n : Nat}
    (hc : σ.heap c = some (.plain xrefCls fs))
    (h : jFieldAt σ "Cbact03c$CardXrefRecord" fs f (.str bs)) (hk : f.jname = k)
    (hn : bs.length = n) (hn' : n < 2147483648) :
    XStrField σ fs k ∧ fixStr (argText σ (xfieldOf σ c k)) n = cp037Str bs := by
  subst hk hn
  obtain ⟨s, hs, x, rfl, hx⟩ := h
  have hs' : Fields.get fs (xrefCls, f.jname) = some (.ref x) := hs
  refine ⟨⟨x, _, hs', hx, by rw [cp037Str_length]; exact hn'⟩, ?_⟩
  have e : xfieldOf σ c f.jname = .ref x := by simp [xfieldOf, hc, hs']
  rw [e]
  exact fixStr_argText hx

/-- A `long` field holding `0 ≤ v < 2 ^ 63` is one the program reads, and its digits are `v`'s. -/
theorem xlong_field {σ : Jimple.State} {c : Addr} {fs : List (FieldKey × Jimple.Value)}
    {f : EquivLean.Cobol.Rec.Field} {v : Int} {k : String} {d : Nat}
    (hc : σ.heap c = some (.plain xrefCls fs))
    (h : jFieldAt σ "Cbact03c$CardXrefRecord" fs f (.num v)) (hk : f.jname = k) (h0 : 0 ≤ v)
    (h1 : v < 2 ^ 63) :
    XLongField fs k ∧ zpadStr (xfieldLong σ c k).toNat d = (zpad d v.natAbs).map (BitVec.ofNat 16) := by
  subst hk
  have hf : Fields.get fs (xrefCls, f.jname) = some (.long (BitVec.ofInt 64 v)) := h
  refine ⟨⟨_, hf, by rw [toInt_ofInt64 h0 h1]; exact h0⟩, ?_⟩
  have e : xfieldLong σ c f.jname = BitVec.ofInt 64 v := by simp [xfieldLong, xfieldOf, hc, hf]
  rw [e]
  exact zpadStr_ofInt64 d h0 h1

/-- A record object holding valid field values is what JimpleLean's contract reads, and its line
is ours. -/
theorem jrec_xref {σ : Jimple.State} {x : Jimple.Value} {v : List EquivLean.Cobol.Rec.FVal}
    (hx : JRecAt CardXrefRecord "Cbact03c$CardXrefRecord" σ x v) (hv : CardXrefRecord.Valid v) :
    ∃ c, x = .ref c ∧ XrefOk σ c ∧ xrecLineV σ x = recLine v := by
  obtain ⟨card, cust, acct, fill, rfl, hcust, hcust0, hacct, hacct0, hcard, hfill⟩ := xref_shape hv
  obtain ⟨c, fs, rfl, hc, hf⟩ := hx
  match hf with
  | .cons f0 (.cons f1 (.cons f2 (.cons f3 .nil))) =>
    have e0 := xstr_field (k := "xrefCardNum") hc f0 rfl hcard (by decide)
    have e1 := xlong_field (k := "xrefCustId") (d := 9) hc f1 rfl hcust0 (by omega)
    have e2 := xlong_field (k := "xrefAcctId") (d := 11) hc f2 rfl hacct0 (by omega)
    have e3 := xstr_field (k := "filler1") hc f3 rfl hfill (by decide)
    refine ⟨c, rfl, ⟨fs, hc, e0.1, e1.1, e2.1, e3.1⟩, ?_⟩
    have erl : recLine [.str card, .num cust, .num acct, .str fill] =
        cp037Str card ++ ((zpad 9 cust.natAbs).map (BitVec.ofNat 16) ++
          ((zpad 11 acct.natAbs).map (BitVec.ofNat 16) ++ (cp037Str fill ++ []))) := rfl
    rw [erl]
    show xrefLine σ c = _
    unfold xrefLine
    rw [e0.2, e1.2, e2.2, e3.2]
    simp only [List.append_assoc, List.append_nil]

theorem c3StartText_eq : c3StartText = startLine := by decide +kernel
theorem c3EndText_eq : c3EndText = endLine := by decide +kernel

/-- **JimpleLean's contract of `run` implies ours.** -/
theorem sat_runSpec_of_J (h : Sat Gen.prog runRef c3RunSpecJ) : Sat Gen.prog runRef runSpec := by
  intro args σ o hpre hexec
  obtain ⟨a, vals, rfl, ⟨et, xs, hheap, hlen, hrec⟩, hv, hi1, hi2, hi3, hi4⟩ := hpre
  have hok : ∀ x ∈ xs, ∃ c, x = .ref c ∧ XrefOk σ c := by
    intro x hx
    obtain ⟨v, hvm, hxv⟩ := forall2_mem hrec x hx
    obtain ⟨c, rfl, hc, -⟩ := jrec_xref hxv (hv v hvm)
    exact ⟨c, rfl, hc⟩
  have hpost := h [.ref a] σ o ⟨a, et, xs, rfl, hheap, hlen, hok, hi1, hi2, hi3, hi4⟩ hexec
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
    have hmap : xs.flatMap (fun v => [xrecLineV σ v, xrecLineV σ v]) =
        vals'.flatMap (fun v => [recLine v, recLine v]) :=
      forall2_flatMap_eq (forall2_imp (fun x v hxv => by
        obtain ⟨c, rfl, -, e⟩ := jrec_xref hxv.1 hxv.2
        exact congrArg (fun s => [s, s]) e) (forall2_and_mem hrec' hv'))
    rw [xrefLines_length, hmap, c3StartText_eq, c3EndText_eq] at hstrs
    exact strsAt_forall2 hstrs
  | exc e σ' => simp [c3RunSpecJ, Spec.of] at hpost
  | wrong msg => simp [c3RunSpecJ, Spec.of] at hpost

/-- **CBACT03C → Java, every input**: the generated statement (`JavaStatement.lean`). -/
theorem java : Statement := statement_of_sat (sat_runSpec_of_J c3_run_sat)

end EquivLean.Modernize.Cbact03c.Java

#print axioms EquivLean.Modernize.Cbact03c.Java.java
