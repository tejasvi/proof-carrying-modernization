import EquivLean.Modernize.Cbstm03b.Java.AcctClose
import EquivLean.Modernize.Cbstm03b.Java.AcctOpen
import EquivLean.Modernize.Cbstm03b.Java.AcctOther
import EquivLean.Modernize.Cbstm03b.Java.AcctKEntry
import EquivLean.Modernize.Cbstm03b.Java.AcctLoop
import EquivLean.Modernize.Cbstm03b.Java.AcctFound

/-!
# CBSTM03B → Java: `acctProc`

`acct_vc`: for every choice of ghost values, `acctProc`'s verification conditions against `procSpecG ddAcct`
(the file procedure contract `procSpec ddAcct` of `Iface.lean` with its ghost values fixed; `procSpec_of_ghost`
gives `procSpec ddAcct` from it), with the invariants `acctInv` (`AcctInv.lean`) and fuel 200, callees answered by
`acctCallees` (depth 1: `FdAcctfileRec.<init>` inlined).

The paths: `OPEN` (`AcctOpen`), `CLOSE` (`AcctClose`), another operation (`AcctOther`), keyed `READ` up to the key
loop (`AcctKEntry`), the key loop (`AcctLoop`), the search (`AcctSearch`, `AcctSearch2`, `AcctFound`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.AcctP

open EquivLean.Modernize.Cbstm03b.Java

theorem ofNat32_eq {i j : Nat} (hj : j < 4294967296) (h : BitVec.ofNat 32 i = BitVec.ofNat 32 j) :
    i % 4294967296 = j := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  omega

/-- The entry paths. -/
theorem acct_entry {oe st q : Addr} {opv : Value} {oeM : Model.OpenErrs} {s : Model.StM}
    {a : List EquivLean.Cobol.Rec.FVal} {σ0 : State}
    (hpre : (procSpecG ddAcct oe st q opv oeM s a).pre [.ref oe, .ref st, .ref q, opv] σ0) :
    acctWP oe st q opv oeM s a σ0 0 (Frame.init true [.ref oe, .ref st, .ref q, opv]) σ0 := by
  by_cases h1 : Model.aOp a = opOpen
  · cases ho : s.acct.isOpen
    · obtain ⟨-, hE, -⟩ := id hpre
      obtain ⟨et, xs, hoe, hlen, hx⟩ := hE
      match xs, hlen with
      | [x0, x1, x2, x3], _ =>
        rcases hx 3 (by decide) with ⟨h3, hc⟩ | ⟨o, c, h3, ho3, hc, hc4⟩
        · simp only [List.getD_cons_succ, List.getD_cons_zero] at h3
          subst h3
          exact acct_open_ok hpre h1 ho et x0 x1 x2 hoe hc
        · simp only [List.getD_cons_succ, List.getD_cons_zero] at h3
          subst h3
          exact acct_open_err hpre h1 ho et x0 x1 x2 o c hoe ho3 hc hc4
    · exact acct_open_open hpre h1 ho
  by_cases h2 : Model.aOp a = opReadK
  · exact acct_key_entry hpre h2
  by_cases h3 : Model.aOp a = opClose
  · cases ho : s.acct.isOpen
    · exact acct_close_shut hpre h3 ho
    · exact acct_close_open hpre h3 ho
  · exact acct_other hpre h1 h2 h3

/-- The search head (statement 65). -/
theorem acct_search {oe st q : Addr} {opv : Value} {oeM : Model.OpenErrs} {s : Model.StM}
    {a : List EquivLean.Cobol.Rec.FVal} {σ0 : State}
    (hpre : (procSpecG ddAcct oe st q opv oeM s a).pre [.ref oe, .ref st, .ref q, opv] σ0)
    (fr : Frame) (σ : State) (hJ : J65 oe st q s a σ0 fr σ) :
    acctWP oe st q opv oeM s a σ0 65 fr σ := by
  obtain ⟨fs, fs4, fsr, fsq, o4, fdr, xop, l, sv, et, xs, dd, rc, key, fldt, b, kl, sdd, src, skey, sfl,
    hst, g4, ho4, hop4, hrec4, hl, hlen, hrs, -⟩ := pre_fin hpre
  have hxl := forall2_length hrs
  obtain ⟨-, -, -, j, -, f10, hj, -⟩ := id hJ
  have hj32 : j < 4294967296 := by omega
  by_cases hjl : j < s.acct.recs.length
  · by_cases hm : Model.numOf ((s.acct.recs.getD j []).getD 0 default) = (keyVal a : Int)
    · refine acct_search_found hpre fr σ hJ fun j' f10' hj' => ?_
      rw [f10] at f10'
      have e := ofNat32_eq hj32 (Value.int.inj (Option.some.inj f10')).symm
      have e' : j' = j := by rw [← e]; exact (Nat.mod_eq_of_lt (by omega)).symm
      subst e'
      exact ⟨hjl, hm⟩
    · refine acct_search_next hpre fr σ hJ fun j' f10' hj' => ?_
      rw [f10] at f10'
      have e := ofNat32_eq hj32 (Value.int.inj (Option.some.inj f10')).symm
      have e' : j' = j := by rw [← e]; exact (Nat.mod_eq_of_lt (by omega)).symm
      subst e'
      exact ⟨hjl, hm⟩
  · refine acct_search_none hpre fr σ hJ fun j' f10' => ?_
    rw [f10] at f10'
    have e := ofNat32_eq hj32 (Value.int.inj (Option.some.inj f10')).symm
    have : j' % 4294967296 ≤ j' := Nat.mod_le _ _
    omega

/-- **`acctProc`'s verification conditions**, for every choice of ghost values. -/
theorem acct_vc (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) :
    MethodVC Gen.prog acctCallees.env 1 acctProcRef (procSpecG ddAcct oe st q opv oeM s a)
      (acctInv oe st q s a) 200 := by
  refine ⟨Gen.Cbstm03b.«acctProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)»,
    rfl, fun args σ0 hpre => ?_⟩
  have hargs : args = [.ref oe, .ref st, .ref q, opv] := hpre.1
  subst hargs
  refine ⟨?_, ?_⟩
  · have h := acct_entry hpre
    unfold acctWP at h
    have hs : acctProcRef.decl.mods.isStatic = true := rfl
    simp only [hs, acctInv, Invariants.inst, List.map_cons, List.map_nil, List.lookup_cons, List.lookup_nil,
      Nat.reduceBEq, Bool.false_eq_true, ite_false, cond_false] at h ⊢
    -- `exact h` would compare the two (equal) terms by unfolding the method's statements
    exact (by assumption)
  · intro p hp fr σ hI
    simp only [acctInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · have h := acct_loop hpre fr σ hI
      unfold acctWP at h
      exact h
    · have h := acct_search hpre fr σ hI
      unfold acctWP at h
      exact h

/-- `procSpec ddAcct` (`Iface.lean`) for `acctProc`, given its callees' contracts. -/
theorem acct_sat (hV : Valid Gen.prog acctCallees.env) : Sat Gen.prog acctProcRef (procSpec ddAcct) :=
  procSpec_of_ghost fun oe st q opv oeM s a => MethodVC.sat_of_valid hV (acct_vc oe st q opv oeM s a)

end EquivLean.Modernize.Cbstm03b.Java.AcctP

#print axioms EquivLean.Modernize.Cbstm03b.Java.AcctP.acct_vc
#print axioms EquivLean.Modernize.Cbstm03b.Java.AcctP.acct_sat
