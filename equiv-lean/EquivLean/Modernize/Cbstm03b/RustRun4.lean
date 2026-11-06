import EquivLean.Modernize.Cbstm03b.RustRun3

/-!
# CBSTM03B → Rust: the file procedures

`trnx_proc`, `xref_proc` (sequential files) and `cust_proc`, `acct_proc` (keyed files) against the model's
`seqStep` / `keyStep`, on the translation's values (`absSt`, `LkM03bArea.vals`): each leaf of the procedure is
the model's result for the operation byte (`aOp_vals`, `op_iff`), the file's flags, the OPEN outcome and, for a
read, the record (`*_image_rel`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Rust

/-- Closes a leaf of a file procedure: the translation's state and area against the model's. -/
macro "slot_close" : tactic => `(tactic|
  simp only [absSt, absTrnx, absXref, absCust, absAcct, LkM03bArea.vals, FdCustfileRec.vals, FdAcctfileRec.vals,
    Model.setRc, Model.setFldt,
    List.set_cons_succ, List.set_cons_zero, Prod.mk.injEq, Model.StM.mk.injEq, Model.FileM.mk.injEq,
    FVal.str.injEq, FVal.num.injEq, List.cons.injEq, st00, st10, st23, st41, st42, st46, st47,
    st_ebc st00, st_ebc st10, st_ebc st23, st_ebc st41, st_ebc st42, st_ebc st46, st_ebc st47,
    uscalar_ofNat_val, UScalar.ofNatCore_val_eq, and_true, true_and, and_self])

theorem no_err_val : cbstm03b.NO_ERR.val = 255 := by simp [cbstm03b.NO_ERR]

/-- `trnx_proc` is the model's step of TRNXFILE. -/
theorem trnx_proc_spec (c : U8) (oc : Option Nat)
    (hc : (c.val = 255 ∧ oc = none) ∨ (c.val < 100 ∧ oc = some c.val))
    (st : cbstm03b.State) (q : cbstm03b.LkM03bArea) :
    ∃ v, cbstm03b.trnx_proc c st q = .ok v ∧
      (absSt v.1, LkM03bArea.vals v.2) =
        (let r := Model.seqStep oc Model.FdTrnxfileRec (Model.aOp (LkM03bArea.vals q)) (absSt st).trnx
            (absSt st).trnxRec (absSt st).trnxSt (LkM03bArea.vals q)
         ({ absSt st with trnx := r.1, trnxRec := r.2.1, trnxSt := r.2.2.1 }, r.2.2.2)) := by
  have hop1 : q.lk_m03b_oper.val.length = 1 := q.lk_m03b_oper.property
  have hidx : Array.index_usize q.lk_m03b_oper 0#usize = .ok (q.lk_m03b_oper.val.getD 0 default) :=
    index_usize_getD _ _ (by simp [hop1])
  rw [aOp_vals]
  generalize q.lk_m03b_oper.val.getD 0 default = op at hidx ⊢
  refine exists_ok_of_wp ?_
  simp only [cbstm03b.trnx_proc, hidx, bind_ok, Model.seqStep, absSt, absTrnx]
  by_cases hO : op = 79#u8
  · -- OPEN
    subst hO
    simp only [ebc_O, ↓reduceIte, Model.openM]
    by_cases hopen : st.trnx_file.open = true
    · simp only [hopen, ↓reduceIte]
      aeneas_wp []
      refine ⟨_, rfl, ?_⟩
      slot_close
      exact hopen
    · have hopen' : st.trnx_file.open = false := by simpa using hopen
      simp only [hopen', Bool.false_eq_true, ↓reduceIte]
      rcases hc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
      · have hne : c = cbstm03b.NO_ERR := by rw [UScalar.eq_equiv, no_err_val, hc]
        simp only [hne, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        aeneas_wp []
        refine ⟨_, rfl, ?_⟩
        slot_close
      · have hne : (c != cbstm03b.NO_ERR) = true := by
          rw [bne_iff_ne, ne_eq, UScalar.eq_equiv, no_err_val]; omega
        obtain ⟨s, hs, hsv⟩ := fmt_status_eq c
        have hsv' : s.val.map (·.val) = Model.stCp c.val := hsv
        simp only [hne, ↓reduceIte]
        aeneas_wp [hs]
        refine ⟨_, rfl, ?_⟩
        slot_close
        simp only [hsv', st_ebc hsv', hopen', and_self]
  · have hO' : ebcdicOfLatin1 op.val ≠ opOpen := fun h => hO ((op_iff ebc_O).1 h)
    simp only [hO, hO', ↓reduceIte]
    by_cases hR : op = 82#u8
    · -- READ
      subst hR
      simp only [ebc_R, ↓reduceIte, Model.seqReadM]
      by_cases hopen : st.trnx_file.open = true
      · simp only [hopen, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        by_cases heof : st.trnx_file.eof = true
        · simp only [heof, ↓reduceIte]
          aeneas_wp []
          refine ⟨_, rfl, ?_⟩
          slot_close
          exact ⟨hopen, heof⟩
        · have heof' : st.trnx_file.eof = false := by simpa using heof
          simp only [heof', Bool.false_eq_true, ↓reduceIte]
          by_cases hge : st.trnx_file.recs.val.length ≤ st.trnx_file.pos.val
          · simp only [List.getElem?_map, List.getElem?_eq_none hge, Option.map_none]
            aeneas_wp [hge]
            refine ⟨_, rfl, ?_⟩
            slot_close
          · have hlt : st.trnx_file.pos.val < st.trnx_file.recs.val.length := by omega
            have hmax : st.trnx_file.pos.val + 1 ≤ Usize.max := by
              have := st.trnx_file.recs.property; omega
            obtain ⟨img, himg, himgv⟩ := trnx_image_eq (st.trnx_file.recs.val[st.trnx_file.pos.val])
            simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, Option.map_some]
            aeneas_wp [hge, hlt, hmax, himg]
            refine ⟨_, rfl, ?_⟩
            slot_close
            simp only [trnx_image_rel _ _ himgv]
      · have hopen' : st.trnx_file.open = false := by simpa using hopen
        simp only [hopen', Bool.not_false, Bool.false_eq_true, ↓reduceIte]
        aeneas_wp []
        refine ⟨_, rfl, ?_⟩
        slot_close
        exact hopen'
    · have hR' : ebcdicOfLatin1 op.val ≠ opRead := fun h => hR ((op_iff ebc_R).1 h)
      simp only [hR, hR', ↓reduceIte]
      by_cases hC : op = 67#u8
      · -- CLOSE
        subst hC
        simp only [ebc_C, ↓reduceIte, Model.closeM]
        by_cases hopen : st.trnx_file.open = true
        · simp only [hopen, ↓reduceIte]
          aeneas_wp []
          refine ⟨_, rfl, ?_⟩
          slot_close
        · have hopen' : st.trnx_file.open = false := by simpa using hopen
          simp only [hopen', Bool.false_eq_true, ↓reduceIte]
          aeneas_wp []
          refine ⟨_, rfl, ?_⟩
          slot_close
          exact hopen'
      · -- any other operation: the status item into the return code
        have hC' : ebcdicOfLatin1 op.val ≠ opClose := fun h => hC ((op_iff ebc_C).1 h)
        simp only [hC, hC', ↓reduceIte]
        aeneas_wp []
        refine ⟨_, rfl, ?_⟩
        slot_close
        simp only [List.map_map]
        rfl

/-- `xref_proc` is the model's step of XREFFILE. -/
theorem xref_proc_spec (c : U8) (oc : Option Nat)
    (hc : (c.val = 255 ∧ oc = none) ∨ (c.val < 100 ∧ oc = some c.val))
    (st : cbstm03b.State) (q : cbstm03b.LkM03bArea) :
    ∃ v, cbstm03b.xref_proc c st q = .ok v ∧
      (absSt v.1, LkM03bArea.vals v.2) =
        (let r := Model.seqStep oc Model.FdXreffileRec (Model.aOp (LkM03bArea.vals q)) (absSt st).xref
            (absSt st).xrefRec (absSt st).xrefSt (LkM03bArea.vals q)
         ({ absSt st with xref := r.1, xrefRec := r.2.1, xrefSt := r.2.2.1 }, r.2.2.2)) := by
  have hop1 : q.lk_m03b_oper.val.length = 1 := q.lk_m03b_oper.property
  have hidx : Array.index_usize q.lk_m03b_oper 0#usize = .ok (q.lk_m03b_oper.val.getD 0 default) :=
    index_usize_getD _ _ (by simp [hop1])
  rw [aOp_vals]
  generalize q.lk_m03b_oper.val.getD 0 default = op at hidx ⊢
  refine exists_ok_of_wp ?_
  simp only [cbstm03b.xref_proc, hidx, bind_ok, Model.seqStep, absSt, absXref]
  by_cases hO : op = 79#u8
  · -- OPEN
    subst hO
    simp only [ebc_O, ↓reduceIte, Model.openM]
    by_cases hopen : st.xref_file.open = true
    · simp only [hopen, ↓reduceIte]
      aeneas_wp []
      refine ⟨_, rfl, ?_⟩
      slot_close
      exact hopen
    · have hopen' : st.xref_file.open = false := by simpa using hopen
      simp only [hopen', Bool.false_eq_true, ↓reduceIte]
      rcases hc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
      · have hne : c = cbstm03b.NO_ERR := by rw [UScalar.eq_equiv, no_err_val, hc]
        simp only [hne, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        aeneas_wp []
        refine ⟨_, rfl, ?_⟩
        slot_close
      · have hne : (c != cbstm03b.NO_ERR) = true := by
          rw [bne_iff_ne, ne_eq, UScalar.eq_equiv, no_err_val]; omega
        obtain ⟨s, hs, hsv⟩ := fmt_status_eq c
        have hsv' : s.val.map (·.val) = Model.stCp c.val := hsv
        simp only [hne, ↓reduceIte]
        aeneas_wp [hs]
        refine ⟨_, rfl, ?_⟩
        slot_close
        simp only [hsv', st_ebc hsv', hopen', and_self]
  · have hO' : ebcdicOfLatin1 op.val ≠ opOpen := fun h => hO ((op_iff ebc_O).1 h)
    simp only [hO, hO', ↓reduceIte]
    by_cases hR : op = 82#u8
    · -- READ
      subst hR
      simp only [ebc_R, ↓reduceIte, Model.seqReadM]
      by_cases hopen : st.xref_file.open = true
      · simp only [hopen, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        by_cases heof : st.xref_file.eof = true
        · simp only [heof, ↓reduceIte]
          aeneas_wp []
          refine ⟨_, rfl, ?_⟩
          slot_close
          exact ⟨hopen, heof⟩
        · have heof' : st.xref_file.eof = false := by simpa using heof
          simp only [heof', Bool.false_eq_true, ↓reduceIte]
          by_cases hge : st.xref_file.recs.val.length ≤ st.xref_file.pos.val
          · simp only [List.getElem?_map, List.getElem?_eq_none hge, Option.map_none]
            aeneas_wp [hge]
            refine ⟨_, rfl, ?_⟩
            slot_close
          · have hlt : st.xref_file.pos.val < st.xref_file.recs.val.length := by omega
            have hmax : st.xref_file.pos.val + 1 ≤ Usize.max := by
              have := st.xref_file.recs.property; omega
            obtain ⟨img, himg, himgv⟩ := xref_image_eq (st.xref_file.recs.val[st.xref_file.pos.val])
            simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, Option.map_some]
            aeneas_wp [hge, hlt, hmax, himg]
            refine ⟨_, rfl, ?_⟩
            slot_close
            simp only [xref_image_rel _ _ himgv]
      · have hopen' : st.xref_file.open = false := by simpa using hopen
        simp only [hopen', Bool.not_false, Bool.false_eq_true, ↓reduceIte]
        aeneas_wp []
        refine ⟨_, rfl, ?_⟩
        slot_close
        exact hopen'
    · have hR' : ebcdicOfLatin1 op.val ≠ opRead := fun h => hR ((op_iff ebc_R).1 h)
      simp only [hR, hR', ↓reduceIte]
      by_cases hC : op = 67#u8
      · -- CLOSE
        subst hC
        simp only [ebc_C, ↓reduceIte, Model.closeM]
        by_cases hopen : st.xref_file.open = true
        · simp only [hopen, ↓reduceIte]
          aeneas_wp []
          refine ⟨_, rfl, ?_⟩
          slot_close
        · have hopen' : st.xref_file.open = false := by simpa using hopen
          simp only [hopen', Bool.false_eq_true, ↓reduceIte]
          aeneas_wp []
          refine ⟨_, rfl, ?_⟩
          slot_close
          exact hopen'
      · -- any other operation: the status item into the return code
        have hC' : ebcdicOfLatin1 op.val ≠ opClose := fun h => hC ((op_iff ebc_C).1 h)
        simp only [hC, hC', ↓reduceIte]
        aeneas_wp []
        refine ⟨_, rfl, ?_⟩
        slot_close
        simp only [List.map_map]
        rfl

/-! ## The keyed files -/

/-- CUSTFILE's search: the model's predicate on field values is the translation's on structs. -/
theorem cust_find_map (recs : List cbstm03b.FdCustfileRec) (id : List U8) :
    (recs.map FdCustfileRec.vals).findIdx?
        (fun x => Model.strOf (x.getD 0 default) == id.map (fun u => ebcdicOfLatin1 u.val)) =
      recs.findIdx? (fun x => decide (x.fd_cust_id.val = id)) := by
  rw [List.findIdx?_map]
  congr 1
  funext x
  simp only [Function.comp_apply, FdCustfileRec.vals, List.getD_cons_zero, Model.strOf]
  by_cases h : x.fd_cust_id.val = id
  · simp [h]
  · have h' : x.fd_cust_id.val.map (fun u => ebcdicOfLatin1 u.val) ≠ id.map (fun u => ebcdicOfLatin1 u.val) :=
      fun e => h (ebc_map_inj e)
    simp [h, h']

/-- ACCTFILE's search: the model's predicate on field values is the translation's on structs. -/
theorem acct_find_map (recs : List cbstm03b.FdAcctfileRec) (v : Int) :
    (recs.map FdAcctfileRec.vals).findIdx? (fun x => Model.numOf (x.getD 0 default) == v) =
      recs.findIdx? (fun x => decide (x.fd_acct_id.val = v)) := by
  rw [List.findIdx?_map]
  congr 1

/-- `cust_proc` is the model's step of CUSTFILE, for a key length in `0 ..= 25` on a keyed READ. -/
theorem cust_proc_spec (c : U8) (oc : Option Nat)
    (hc : (c.val = 255 ∧ oc = none) ∨ (c.val < 100 ∧ oc = some c.val))
    (st : cbstm03b.State) (q : cbstm03b.LkM03bArea)
    (hkl : Model.aOp (LkM03bArea.vals q) = opReadK → 0 ≤ q.lk_m03b_key_ln.val ∧ q.lk_m03b_key_ln.val ≤ 25) :
    ∃ v, cbstm03b.cust_proc c st q = .ok v ∧
      (absSt v.1, LkM03bArea.vals v.2) =
        (let key := Model.custKey (Model.aKey (LkM03bArea.vals q)) (Model.aKeyLn (LkM03bArea.vals q)).toNat
         let r := Model.keyStep oc Model.FdCustfileRec (fun rec => rec.set 0 (.str key))
           (fun x => Model.strOf (x.getD 0 default) == key) (Model.aOp (LkM03bArea.vals q)) (absSt st).cust
           (absSt st).custRec (absSt st).custSt (LkM03bArea.vals q)
         ({ absSt st with cust := r.1, custRec := r.2.1, custSt := r.2.2.1 }, r.2.2.2)) := by
  have hop1 : q.lk_m03b_oper.val.length = 1 := q.lk_m03b_oper.property
  have hidx : Array.index_usize q.lk_m03b_oper 0#usize = .ok (q.lk_m03b_oper.val.getD 0 default) :=
    index_usize_getD _ _ (by simp [hop1])
  rw [aOp_vals] at hkl ⊢
  rw [aKey_vals, aKeyLn_vals]
  generalize q.lk_m03b_oper.val.getD 0 default = op at hidx hkl ⊢
  refine exists_ok_of_wp ?_
  simp only [cbstm03b.cust_proc, hidx, bind_ok, Model.keyStep, absSt, absCust]
  by_cases hO : op = 79#u8
  · -- OPEN
    subst hO
    simp only [ebc_O, ↓reduceIte, Model.openM]
    by_cases hopen : st.cust_file.open = true
    · simp only [hopen, ↓reduceIte]
      aeneas_wp []
      refine ⟨_, rfl, ?_⟩
      slot_close
      exact hopen
    · have hopen' : st.cust_file.open = false := by simpa using hopen
      simp only [hopen', Bool.false_eq_true, ↓reduceIte]
      rcases hc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
      · have hne : c = cbstm03b.NO_ERR := by rw [UScalar.eq_equiv, no_err_val, hc]
        simp only [hne, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        aeneas_wp []
        refine ⟨_, rfl, ?_⟩
        slot_close
      · have hne : (c != cbstm03b.NO_ERR) = true := by
          rw [bne_iff_ne, ne_eq, UScalar.eq_equiv, no_err_val]; omega
        obtain ⟨s, hs, hsv⟩ := fmt_status_eq c
        have hsv' : s.val.map (·.val) = Model.stCp c.val := hsv
        simp only [hne, ↓reduceIte]
        aeneas_wp [hs]
        refine ⟨_, rfl, ?_⟩
        slot_close
        simp only [hsv', st_ebc hsv', hopen', and_self]
  · have hO' : ebcdicOfLatin1 op.val ≠ opOpen := fun h => hO ((op_iff ebc_O).1 h)
    simp only [hO, hO', ↓reduceIte]
    by_cases hK : op = 75#u8
    · -- keyed READ
      subst hK
      obtain ⟨h0, h25⟩ := hkl ebc_K
      obtain ⟨id, hid, hidv⟩ := cust_key_eq q h0 h25
      have hkey : Model.custKey (q.lk_m03b_key.val.map (fun u => ebcdicOfLatin1 u.val))
          q.lk_m03b_key_ln.val.toNat = id.val.map (fun u => ebcdicOfLatin1 u.val) := by
        rw [hidv, custKey_ebc _ q.lk_m03b_key.property _ (by omega)]
      simp only [ebc_K, ↓reduceIte, Model.keyReadM, hkey]
      by_cases hopen : st.cust_file.open = true
      · simp only [hopen, Bool.not_true, Bool.false_eq_true, ↓reduceIte, cust_find_map]
        obtain ⟨idx, hfind, hidxv⟩ := find_cust_eq st.cust_file.recs id
        cases hJ : st.cust_file.recs.val.findIdx? (fun x => decide (x.fd_cust_id.val = id.val)) with
        | none =>
          have hge : st.cust_file.recs.val.length ≤ idx.val := by rw [hidxv, hJ]; simp
          aeneas_wp [hid, hfind, hge]
          refine ⟨_, rfl, ?_⟩
          slot_close
          exact hopen
        | some j =>
          have hj : j < st.cust_file.recs.val.length := findIdx?_lt hJ
          have hidxj : idx.val = j := by rw [hidxv, hJ]; rfl
          subst hidxj
          have hnge : ¬ st.cust_file.recs.val.length ≤ idx.val := by omega
          have hmax : idx.val + 1 ≤ Usize.max := by have := st.cust_file.recs.property; omega
          obtain ⟨img, himg, himgv⟩ := cust_image_eq (st.cust_file.recs.val[idx.val])
          simp only [List.getD_eq_getElem (st.cust_file.recs.val.map FdCustfileRec.vals) []
            (by simpa using hj), List.getElem_map]
          aeneas_wp [hid, hfind, hnge, hj, hmax, himg]
          refine ⟨_, rfl, ?_⟩
          slot_close
          simp only [cust_image_rel _ _ himgv, FdCustfileRec.vals]
      · have hopen' : st.cust_file.open = false := by simpa using hopen
        simp only [hopen', Bool.not_false, Bool.false_eq_true, ↓reduceIte]
        aeneas_wp [hid]
        refine ⟨_, rfl, ?_⟩
        slot_close
        exact hopen'
    · have hK' : ebcdicOfLatin1 op.val ≠ opReadK := fun h => hK ((op_iff ebc_K).1 h)
      simp only [hK, hK', ↓reduceIte]
      by_cases hC : op = 67#u8
      · -- CLOSE
        subst hC
        simp only [ebc_C, ↓reduceIte, Model.closeM]
        by_cases hopen : st.cust_file.open = true
        · simp only [hopen, ↓reduceIte]
          aeneas_wp []
          refine ⟨_, rfl, ?_⟩
          slot_close
        · have hopen' : st.cust_file.open = false := by simpa using hopen
          simp only [hopen', Bool.false_eq_true, ↓reduceIte]
          aeneas_wp []
          refine ⟨_, rfl, ?_⟩
          slot_close
          exact hopen'
      · -- any other operation: the status item into the return code
        have hC' : ebcdicOfLatin1 op.val ≠ opClose := fun h => hC ((op_iff ebc_C).1 h)
        simp only [hC, hC', ↓reduceIte]
        aeneas_wp []
        refine ⟨_, rfl, ?_⟩
        slot_close
        simp only [List.map_map]
        rfl

/-- `acct_proc` is the model's step of ACCTFILE, for valid records and, on a keyed READ, a key that
`acct_key` reads as the model's value. -/
theorem acct_proc_spec (c : U8) (oc : Option Nat)
    (hc : (c.val = 255 ∧ oc = none) ∨ (c.val < 100 ∧ oc = some c.val))
    (st : cbstm03b.State) (q : cbstm03b.LkM03bArea)
    (hrecs : ∀ r ∈ st.acct_file.recs.val, FdAcctfileRec.Valid (FdAcctfileRec.vals r))
    (hkv : Model.aOp (LkM03bArea.vals q) = opReadK → ∃ key, cbstm03b.acct_key q = .ok key ∧
      key.val = Model.acctVal (Model.aKey (LkM03bArea.vals q)) (Model.aKeyLn (LkM03bArea.vals q)).toNat) :
    ∃ v, cbstm03b.acct_proc c st q = .ok v ∧
      (absSt v.1, LkM03bArea.vals v.2) =
        (let v := Model.acctVal (Model.aKey (LkM03bArea.vals q)) (Model.aKeyLn (LkM03bArea.vals q)).toNat
         let r := Model.keyStep oc Model.FdAcctfileRec (fun rec => rec.set 0 (.num v))
           (fun x => Model.numOf (x.getD 0 default) == v) (Model.aOp (LkM03bArea.vals q)) (absSt st).acct
           (absSt st).acctRec (absSt st).acctSt (LkM03bArea.vals q)
         ({ absSt st with acct := r.1, acctRec := r.2.1, acctSt := r.2.2.1 }, r.2.2.2)) := by
  have hop1 : q.lk_m03b_oper.val.length = 1 := q.lk_m03b_oper.property
  have hidx : Array.index_usize q.lk_m03b_oper 0#usize = .ok (q.lk_m03b_oper.val.getD 0 default) :=
    index_usize_getD _ _ (by simp [hop1])
  rw [aOp_vals, aKey_vals, aKeyLn_vals] at hkv
  rw [aOp_vals, aKey_vals, aKeyLn_vals]
  generalize q.lk_m03b_oper.val.getD 0 default = op at hidx hkv ⊢
  refine exists_ok_of_wp ?_
  simp only [cbstm03b.acct_proc, hidx, bind_ok, Model.keyStep, absSt, absAcct]
  by_cases hO : op = 79#u8
  · -- OPEN
    subst hO
    simp only [ebc_O, ↓reduceIte, Model.openM]
    by_cases hopen : st.acct_file.open = true
    · simp only [hopen, ↓reduceIte]
      aeneas_wp []
      refine ⟨_, rfl, ?_⟩
      slot_close
      exact hopen
    · have hopen' : st.acct_file.open = false := by simpa using hopen
      simp only [hopen', Bool.false_eq_true, ↓reduceIte]
      rcases hc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
      · have hne : c = cbstm03b.NO_ERR := by rw [UScalar.eq_equiv, no_err_val, hc]
        simp only [hne, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        aeneas_wp []
        refine ⟨_, rfl, ?_⟩
        slot_close
      · have hne : (c != cbstm03b.NO_ERR) = true := by
          rw [bne_iff_ne, ne_eq, UScalar.eq_equiv, no_err_val]; omega
        obtain ⟨s, hs, hsv⟩ := fmt_status_eq c
        have hsv' : s.val.map (·.val) = Model.stCp c.val := hsv
        simp only [hne, ↓reduceIte]
        aeneas_wp [hs]
        refine ⟨_, rfl, ?_⟩
        slot_close
        simp only [hsv', st_ebc hsv', hopen', and_self]
  · have hO' : ebcdicOfLatin1 op.val ≠ opOpen := fun h => hO ((op_iff ebc_O).1 h)
    simp only [hO, hO', ↓reduceIte]
    by_cases hK : op = 75#u8
    · -- keyed READ
      subst hK
      obtain ⟨key, hkey, hkeyv⟩ := hkv ebc_K
      rw [← hkeyv]
      simp only [ebc_K, ↓reduceIte, Model.keyReadM]
      by_cases hopen : st.acct_file.open = true
      · simp only [hopen, Bool.not_true, Bool.false_eq_true, ↓reduceIte, acct_find_map]
        obtain ⟨idx, hfind, hidxv⟩ := find_acct_eq st.acct_file.recs key
        cases hJ : st.acct_file.recs.val.findIdx? (fun x => decide (x.fd_acct_id.val = key.val)) with
        | none =>
          have hge : st.acct_file.recs.val.length ≤ idx.val := by rw [hidxv, hJ]; simp
          aeneas_wp [hkey, hfind, hge]
          refine ⟨_, rfl, ?_⟩
          slot_close
          exact hopen
        | some j =>
          have hj : j < st.acct_file.recs.val.length := findIdx?_lt hJ
          have hidxj : idx.val = j := by rw [hidxv, hJ]; rfl
          subst hidxj
          have hnge : ¬ st.acct_file.recs.val.length ≤ idx.val := by omega
          have hmax : idx.val + 1 ≤ Usize.max := by have := st.acct_file.recs.property; omega
          have hv := acct_id_range _ (hrecs _ (List.getElem_mem hj))
          obtain ⟨img, himg, himgv⟩ := acct_image_eq (st.acct_file.recs.val[idx.val]) hv.1 hv.2
          simp only [List.getD_eq_getElem (st.acct_file.recs.val.map FdAcctfileRec.vals) []
            (by simpa using hj), List.getElem_map]
          aeneas_wp [hkey, hfind, hnge, hj, hmax, himg]
          refine ⟨_, rfl, ?_⟩
          slot_close
          simp only [acct_image_rel _ _ hv.1 himgv, FdAcctfileRec.vals]
      · have hopen' : st.acct_file.open = false := by simpa using hopen
        simp only [hopen', Bool.not_false, Bool.false_eq_true, ↓reduceIte]
        aeneas_wp [hkey]
        refine ⟨_, rfl, ?_⟩
        slot_close
        exact hopen'
    · have hK' : ebcdicOfLatin1 op.val ≠ opReadK := fun h => hK ((op_iff ebc_K).1 h)
      simp only [hK, hK', ↓reduceIte]
      by_cases hC : op = 67#u8
      · -- CLOSE
        subst hC
        simp only [ebc_C, ↓reduceIte, Model.closeM]
        by_cases hopen : st.acct_file.open = true
        · simp only [hopen, ↓reduceIte]
          aeneas_wp []
          refine ⟨_, rfl, ?_⟩
          slot_close
        · have hopen' : st.acct_file.open = false := by simpa using hopen
          simp only [hopen', Bool.false_eq_true, ↓reduceIte]
          aeneas_wp []
          refine ⟨_, rfl, ?_⟩
          slot_close
          exact hopen'
      · -- any other operation: the status item into the return code
        have hC' : ebcdicOfLatin1 op.val ≠ opClose := fun h => hC ((op_iff ebc_C).1 h)
        simp only [hC, hC', ↓reduceIte]
        aeneas_wp []
        refine ⟨_, rfl, ?_⟩
        slot_close
        simp only [List.map_map]
        rfl

end EquivLean.Modernize.Cbstm03b.Rust
