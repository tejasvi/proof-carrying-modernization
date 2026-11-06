import EquivLean.Modernize.Cbstm03b.Java.AcctSearch2

/-!
# CBSTM03B → Java, `acctProc`: the found record's text and the model of a keyed read that finds it
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.AcctP

open EquivLean.Modernize.Cbstm03b.Java

theorem zpad_map (c : Nat) : ∀ m, (EquivLean.Cobol.Rec.zpad m c).map (BitVec.ofNat 16) = zpadStr c m
  | 0 => rfl
  | m + 1 => by
    rw [EquivLean.Cobol.Rec.zpad, EquivLean.Cobol.Rec.toDigits_succ, List.map_append, List.map_append,
      List.map_singleton, List.map_singleton, zpadStr, ← zpad_map (c / 10) m]
    rfl

/-- The text of an ACCTFILE record: its id's 11 digits, then its data. -/
theorem acct_text (n : Int) (d : List UInt8) (hv : Model.FdAcctfileRec.Valid [.num n, .str d]) :
    cp037Str (Model.FdAcctfileRec.encode [.num n, .str d]) = zpadStr n.natAbs 11 ++ cp037Str d := by
  have h := Schema.text_eq (s := Model.FdAcctfileRec) (by decide) hv
  have e : cp037Str (Model.FdAcctfileRec.encode [.num n, .str d]) =
      ((Model.FdAcctfileRec.encode [.num n, .str d]).map cp037Code).map (BitVec.ofNat 16) := by
    simp only [cp037Str, List.map_map]; rfl
  rw [e, ← h]
  have e2 : Model.FdAcctfileRec.text [.num n, .str d] =
      EquivLean.Cobol.Rec.zpad 11 n.natAbs ++ (d.map cp037Code ++ []) := by
    rfl
  rw [e2, List.append_nil, List.map_append, zpad_map]
  simp only [cp037Str, List.map_map]
  rfl

/-- `LK-M03B-FLDT` after a keyed read finds record `[n, d]`. -/
theorem fldt_text (n : Nat) (d : List UInt8) (hv : Model.FdAcctfileRec.Valid [.num (n : Int), .str d])
    (hd : d.length = 289) :
    cp037Str (intoBuf (Model.FdAcctfileRec.encode [.num (n : Int), .str d])) =
      fixStr (zpadStr n 11 ++ fixStr (cp037Str d) 289) 1000 := by
  have hl : (Model.FdAcctfileRec.encode [.num (n : Int), .str d]).length ≤ 1000 := by
    have := congrArg List.length (acct_text n d hv)
    rw [cp037Str_length, List.length_append, zpadStr_length, cp037Str_length, hd] at this
    omega
  rw [intoBuf_text hl, acct_text n d hv, fixStr_eq_self (s := cp037Str d) (by rw [cp037Str_length, hd])]
  rfl

theorem call_key_found {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal} {j : Nat}
    (hdd : Model.aDd a = ddAcct) (hop : Model.aOp a = opReadK) (ho : s.acct.isOpen = true)
    (hj : j < s.acct.recs.length)
    (hm : Model.numOf ((s.acct.recs.getD j []).getD 0 default) =
      Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat)
    (hnm : ∀ i, i < j → Model.numOf ((s.acct.recs.getD i []).getD 0 default) ≠
      Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat) :
    Model.call oeM s a =
      ({ s with
          acct := { s.acct with pos := j + 1, eof := false }
          acctRec := s.acct.recs.getD j []
          acctSt := Model.stCp 0 },
        Model.setFldt (Model.setRc a (stBytes 0)) (Model.FdAcctfileRec.encode (s.acct.recs.getD j []))) := by
  have hf : s.acct.recs.findIdx? (fun x => Model.numOf (x.getD 0 default) ==
      Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat) = some j := by
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hj, ?_, fun i hi => ?_⟩
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hm
      simp only [beq_iff_eq]
      exact hm
    · have := hnm i hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.lt_trans hi hj),
        Option.getD_some] at this
      simp only [beq_iff_eq]
      exact this
  rw [call_acct hdd, hop]
  simp only [Model.keyStep, Model.keyReadM]
  rw [hf]
  simp [ho, show opReadK ≠ opOpen by decide]

end EquivLean.Modernize.Cbstm03b.Java.AcctP
