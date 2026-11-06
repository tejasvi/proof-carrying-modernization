import EquivLean.Modernize.Cbact02c.JavaProof
import EquivLean.Modernize.Cbact04c.Glue
import EquivLean.Modernize.JLBridge
import EquivLean.Modernize.JL.Cbact02cLink
import EquivLean.Modernize.JL.Cbact02cLemmas

/-!
# CBACT02C → Java: the translation side

JimpleLean's session proved the contract of `Cbact02c.run` (`run_sat : Sat Gen.prog runRef
runSpecJ`, in `Modernize/JL/`, copied from its snapshot by `tools/modernize/import_jl.py`), stated
with the texts that `formatCard` builds.  `sat_runSpec_of_J`: that contract implies ours (`runSpec`,
stated with the field values of the records), so `statement_of_sat` gives the generated statement.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbact02c.Java

open EquivLean.Modernize.JL EquivLean.Modernize.JLBridge

/-! ## The records: what JimpleLean's contract reads, and their lines -/

/-- A valid card record's values, by kind. -/
theorem card_shape {v : List EquivLean.Cobol.Rec.FVal} (hv : CardRecord.Valid v) :
    ∃ num acct cvv name exp st fill, v = [.str num, .num acct, .num cvv, .str name, .str exp,
      .str st, .str fill] ∧ num.length = 16 ∧ acct.natAbs < 100000000000 ∧ 0 ≤ acct ∧
      cvv.natAbs < 1000 ∧ 0 ≤ cvv ∧ name.length = 50 ∧ exp.length = 10 ∧ st.length = 1 ∧
      fill.length = 59 := by
  have hl : v.length = 7 := hv.length_eq.symm
  match v, hl, hv with
  | [x0, x1, x2, x3, x4, x5, x6], _,
      .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 .nil)))))) =>
    obtain ⟨num, rfl, hn⟩ := Cbact04c.Glue.str_of_valid rfl h0
    obtain ⟨acct, rfl, ha⟩ := Cbact04c.Glue.num_of_valid rfl h1
    obtain ⟨cvv, rfl, hc⟩ := Cbact04c.Glue.num_of_valid rfl h2
    obtain ⟨name, rfl, hna⟩ := Cbact04c.Glue.str_of_valid rfl h3
    obtain ⟨exp, rfl, he⟩ := Cbact04c.Glue.str_of_valid rfl h4
    obtain ⟨st, rfl, hs⟩ := Cbact04c.Glue.str_of_valid rfl h5
    obtain ⟨fill, rfl, hf⟩ := Cbact04c.Glue.str_of_valid rfl h6
    obtain ⟨_, k1, -, -, n1, -⟩ := ha
    obtain ⟨_, k2, -, -, n2, -⟩ := hc
    cases k1; cases k2
    rw [Cbact04c.Glue.holds_display rfl] at n1 n2
    exact ⟨num, acct, cvv, name, exp, st, fill, rfl, hn, n1.1, n1.2 rfl, n2.1, n2.2 rfl, hna, he, hs, hf⟩

set_option maxHeartbeats 1000000 in
/-- A record object holding valid field values is what JimpleLean's contract reads, and its line
is ours. -/
theorem jrec_card {σ : Jimple.State} {x : Jimple.Value} {v : List EquivLean.Cobol.Rec.FVal}
    (hx : JRecAt CardRecord "Cbact02c$CardRecord" σ x v) (hv : CardRecord.Valid v) :
    ∃ c, x = .ref c ∧ CardOk σ c ∧ recLineV σ x = recLine v := by
  obtain ⟨num, acct, cvv, name, exp, st, fill, rfl, hnum, hacct, hacct0, hcvv, hcvv0, hname,
    hexp, hst, hfill⟩ := card_shape hv
  obtain ⟨c, fs, rfl, hc, hf⟩ := hx
  match hf with
  | .cons f0 (.cons f1 (.cons f2 (.cons f3 (.cons f4 (.cons f5 (.cons f6 .nil)))))) =>
    obtain ⟨s0, g0, x0, rfl, h0⟩ := f0
    obtain ⟨s3, g3, x3, rfl, h3⟩ := f3
    obtain ⟨s4, g4, x4, rfl, h4⟩ := f4
    obtain ⟨s5, g5, x5, rfl, h5⟩ := f5
    obtain ⟨s6, g6, x6, rfl, h6⟩ := f6
    change Fields.get fs (cardCls, "cardNum") = some (.ref x0) at g0
    change Fields.get fs (cardCls, "cardEmbossedName") = some (.ref x3) at g3
    change Fields.get fs (cardCls, "cardExpiraionDate") = some (.ref x4) at g4
    change Fields.get fs (cardCls, "cardActiveStatus") = some (.ref x5) at g5
    change Fields.get fs (cardCls, "filler1") = some (.ref x6) at g6
    change Fields.get fs (cardCls, "cardAcctId") = some (.long (BitVec.ofInt 64 acct)) at f1
    change Fields.get fs (cardCls, "cardCvvCd") = some (.long (BitVec.ofInt 64 cvv)) at f2
    have hlen : ∀ bs : List UInt8, (cp037Str bs).length = bs.length := fun bs => by simp [cp037Str]
    refine ⟨c, rfl, ⟨fs, hc, ⟨x0, _, g0, h0, by rw [hlen, hnum]; decide⟩,
      ⟨_, f1, by rw [toInt_ofInt64 hacct0 (by omega)]; exact hacct0⟩,
      ⟨_, f2, by rw [toInt_ofInt64 hcvv0 (by omega)]; exact hcvv0⟩,
      ⟨x3, _, g3, h3, by rw [hlen, hname]; decide⟩, ⟨x4, _, g4, h4, by rw [hlen, hexp]; decide⟩,
      ⟨x5, _, g5, h5, by rw [hlen, hst]; decide⟩, ⟨x6, _, g6, h6, by rw [hlen, hfill]; decide⟩⟩, ?_⟩
    have fo : ∀ (k : String) (w : Jimple.Value), Fields.get fs (cardCls, k) = some w →
        fieldOf σ c k = w := by
      intro k w hk; simp [fieldOf, hc, hk]
    have at_ : ∀ (k : String) (y : Addr) (t : List UInt8), Fields.get fs (cardCls, k) = some (.ref y) →
        σ.heap y = some (.str (cp037Str t)) → argText σ (fieldOf σ c k) = cp037Str t := by
      intro k y t hk hy; rw [fo k _ hk]; simp [argText, strOf, hy]
    have erl : recLine [.str num, .num acct, .num cvv, .str name, .str exp, .str st, .str fill] =
        cp037Str num ++ ((zpad 11 acct.natAbs).map (BitVec.ofNat 16) ++
          ((zpad 3 cvv.natAbs).map (BitVec.ofNat 16) ++ (cp037Str name ++ (cp037Str exp ++
          (cp037Str st ++ (cp037Str fill ++ [])))))) := rfl
    rw [erl]
    simp only [recLineV, cardLine]
    rw [at_ _ _ _ g0 h0, at_ _ _ _ g3 h3, at_ _ _ _ g4 h4, at_ _ _ _ g5 h5, at_ _ _ _ g6 h6,
      fixStr_eq_self (by rw [hlen, hnum]), fixStr_eq_self (by rw [hlen, hname]),
      fixStr_eq_self (by rw [hlen, hexp]), fixStr_eq_self (by rw [hlen, hst]),
      fixStr_eq_self (by rw [hlen, hfill])]
    have l1 : fieldLong σ c "cardAcctId" = BitVec.ofInt 64 acct := by simp [fieldLong, fo _ _ f1]
    have l2 : fieldLong σ c "cardCvvCd" = BitVec.ofInt 64 cvv := by simp [fieldLong, fo _ _ f2]
    rw [l1, l2, ofInt64_toNat hacct0 (by omega), ofInt64_toNat hcvv0 (by omega), zpadStr_eq,
      zpadStr_eq]
    have e1 : acct.toNat = acct.natAbs := by omega
    have e2 : cvv.toNat = cvv.natAbs := by omega
    rw [e1, e2]
    simp only [List.append_assoc, List.append_nil]

theorem startText_eq : startText = startLine := by decide +kernel
theorem endText_eq : endText = endLine := by decide +kernel

/-- **JimpleLean's contract of `run` implies ours.** -/
theorem sat_runSpec_of_J (h : Sat Gen.prog runRef runSpecJ) : Sat Gen.prog runRef runSpec := by
  intro args σ o hpre hexec
  obtain ⟨a, vals, rfl, ⟨et, xs, hheap, hlen, hrec⟩, hv, hi1, hi2, hi3⟩ := hpre
  have hok : ∀ x ∈ xs, ∃ c, x = .ref c ∧ CardOk σ c := by
    intro x hx
    obtain ⟨v, hvm, hxv⟩ := forall2_mem hrec x hx
    obtain ⟨c, rfl, hc, -⟩ := jrec_card hxv (hv v hvm)
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
    have hmap : xs.map (recLineV σ) = vals'.map recLine :=
      forall2_map_eq (forall2_imp (fun x v hxv => by
        obtain ⟨c, rfl, -, e⟩ := jrec_card hxv.1 hxv.2; exact e) (forall2_and_mem hrec' hv'))
    rw [cardLines_length, hmap, startText_eq, endText_eq] at hstrs
    exact strsAt_forall2 hstrs
  | exc e σ' => simp [runSpecJ, Spec.of] at hpost
  | wrong msg => simp [runSpecJ, Spec.of] at hpost

/-- **CBACT02C → Java, every input**: the generated statement (`JavaStatement.lean`). -/
theorem java : Statement := statement_of_sat (sat_runSpec_of_J run_sat)

end EquivLean.Modernize.Cbact02c.Java

#print axioms EquivLean.Modernize.Cbact02c.Java.java
