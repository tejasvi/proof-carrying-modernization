import EquivLean.Modernize.Cbact01c.RustRun1

/-!
# CBACT01C → Rust: what `run` outputs per record, in bytes, and its loop body in pieces

`rstep`/`rfold`: the outputs of `run` after some account records (Latin-1 lines, the structs
written, the cycle debit of the last copy).  The loop body is long; `chunkA1` … `chunkE` state
its pieces (copied from the translation) in continuation form, each proven by symbolic
execution (`cwp_c01`: `aeneas_wp` whose conditional lemmas have their length side conditions
discharged by `omega`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec
open Aeneas.Std.Result ControlFlow Error

set_option maxRecDepth 20000

namespace EquivLean.Modernize.Cbact01c.Rust
open cbact01c

/-- `ACCT-ID                 :` as `run` builds it. -/
def lblId : List U8 :=
  [65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 73#u8, 68#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8,
    32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8]
/-- `ACCT-ACTIVE-STATUS      :` as `run` builds it. -/
def lblStatus : List U8 :=
  [65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 65#u8, 67#u8, 84#u8, 73#u8, 86#u8, 69#u8, 45#u8, 83#u8,
    84#u8, 65#u8, 84#u8, 85#u8, 83#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8]
/-- `ACCT-CURR-BAL           :` as `run` builds it. -/
def lblBal : List U8 :=
  [65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 67#u8, 85#u8, 82#u8, 82#u8, 45#u8, 66#u8, 65#u8, 76#u8,
    32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8]
/-- `ACCT-CREDIT-LIMIT       :` as `run` builds it. -/
def lblLimit : List U8 :=
  [65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 67#u8, 82#u8, 69#u8, 68#u8, 73#u8, 84#u8, 45#u8, 76#u8,
    73#u8, 77#u8, 73#u8, 84#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8]
/-- `ACCT-CASH-CREDIT-LIMIT  :` as `run` builds it. -/
def lblCash : List U8 :=
  [65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 67#u8, 65#u8, 83#u8, 72#u8, 45#u8, 67#u8, 82#u8, 69#u8,
    68#u8, 73#u8, 84#u8, 45#u8, 76#u8, 73#u8, 77#u8, 73#u8, 84#u8, 32#u8, 32#u8, 58#u8]
/-- `ACCT-OPEN-DATE          :` as `run` builds it. -/
def lblOpen : List U8 :=
  [65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 79#u8, 80#u8, 69#u8, 78#u8, 45#u8, 68#u8, 65#u8, 84#u8,
    69#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8]
/-- `ACCT-EXPIRAION-DATE     :` as `run` builds it. -/
def lblExp : List U8 :=
  [65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 69#u8, 88#u8, 80#u8, 73#u8, 82#u8, 65#u8, 73#u8, 79#u8,
    78#u8, 45#u8, 68#u8, 65#u8, 84#u8, 69#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8]
/-- `ACCT-REISSUE-DATE       :` as `run` builds it. -/
def lblReis : List U8 :=
  [65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 82#u8, 69#u8, 73#u8, 83#u8, 83#u8, 85#u8, 69#u8, 45#u8,
    68#u8, 65#u8, 84#u8, 69#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8]
/-- `ACCT-CURR-CYC-CREDIT    :` as `run` builds it. -/
def lblCc : List U8 :=
  [65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 67#u8, 85#u8, 82#u8, 82#u8, 45#u8, 67#u8, 89#u8, 67#u8,
    45#u8, 67#u8, 82#u8, 69#u8, 68#u8, 73#u8, 84#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8]
/-- `ACCT-CURR-CYC-DEBIT     :` as `run` builds it. -/
def lblCd : List U8 :=
  [65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 67#u8, 85#u8, 82#u8, 82#u8, 45#u8, 67#u8, 89#u8, 67#u8,
    45#u8, 68#u8, 69#u8, 66#u8, 73#u8, 84#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8]
/-- `ACCT-GROUP-ID           :` as `run` builds it. -/
def lblGrp : List U8 :=
  [65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 71#u8, 82#u8, 79#u8, 85#u8, 80#u8, 45#u8, 73#u8, 68#u8,
    32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8]
/-- `-------------------------------------------------` as `run` builds it. -/
def dashes : List U8 :=
  [45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8,
    45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8,
    45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8,
    45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8]
/-- `VBRC-REC1:` as `run` builds it. -/
def vb1Lbl : List U8 :=
  [86#u8, 66#u8, 82#u8, 67#u8, 45#u8, 82#u8, 69#u8, 67#u8, 49#u8, 58#u8]
/-- `VBRC-REC2:` as `run` builds it. -/
def vb2Lbl : List U8 :=
  [86#u8, 66#u8, 82#u8, 67#u8, 45#u8, 82#u8, 69#u8, 67#u8, 50#u8, 58#u8]
/-- `START OF EXECUTION OF PROGRAM CBACT01C` as `run` builds it. -/
def startLine : List U8 :=
  [83#u8, 84#u8, 65#u8, 82#u8, 84#u8, 32#u8, 79#u8, 70#u8, 32#u8, 69#u8, 88#u8, 69#u8, 67#u8,
    85#u8, 84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 79#u8, 70#u8, 32#u8, 80#u8, 82#u8, 79#u8, 71#u8,
    82#u8, 65#u8, 77#u8, 32#u8, 67#u8, 66#u8, 65#u8, 67#u8, 84#u8, 48#u8, 49#u8, 67#u8]
/-- `END OF EXECUTION OF PROGRAM CBACT01C` as `run` builds it. -/
def endLine : List U8 :=
  [69#u8, 78#u8, 68#u8, 32#u8, 79#u8, 70#u8, 32#u8, 69#u8, 88#u8, 69#u8, 67#u8, 85#u8, 84#u8,
    73#u8, 79#u8, 78#u8, 32#u8, 79#u8, 70#u8, 32#u8, 80#u8, 82#u8, 79#u8, 71#u8, 82#u8, 65#u8,
    77#u8, 32#u8, 67#u8, 66#u8, 65#u8, 67#u8, 84#u8, 48#u8, 49#u8, 67#u8]

/-! ## The outputs of one account record, in bytes -/

/-- VBRC-REC1 and VBRC-REC2 of an account (Latin-1). -/
def vbrc1 (a : AccountRecord) : List U8 :=
  zonedText a.acct_id.val 11 false ++ a.acct_active_status.val
def vbrc2 (a : AccountRecord) : List U8 :=
  zonedText a.acct_id.val 11 false ++ zonedText a.acct_curr_bal.val 12 true ++
    zonedText a.acct_credit_limit.val 12 true ++ a.acct_reissue_date.val.take 4

/-- The account record as DISPLAY shows it (Latin-1). -/
def recText (a : AccountRecord) : List U8 :=
  zonedText a.acct_id.val 11 false ++ a.acct_active_status.val ++
    zonedText a.acct_curr_bal.val 12 true ++ zonedText a.acct_credit_limit.val 12 true ++
    zonedText a.acct_cash_credit_limit.val 12 true ++ a.acct_open_date.val ++
    a.acct_expiraion_date.val ++ a.acct_reissue_date.val ++
    zonedText a.acct_curr_cyc_credit.val 12 true ++ zonedText a.acct_curr_cyc_debit.val 12 true ++
    a.acct_addr_zip.val ++ a.acct_group_id.val ++ a.filler1.val

/-- The lines displayed for an account (Latin-1). -/
def recLines (a : AccountRecord) : List (List U8) :=
  [lblId ++ zonedText a.acct_id.val 11 false,
    lblStatus ++ a.acct_active_status.val,
    lblBal ++ zonedText a.acct_curr_bal.val 12 true,
    lblLimit ++ zonedText a.acct_credit_limit.val 12 true,
    lblCash ++ zonedText a.acct_cash_credit_limit.val 12 true,
    lblOpen ++ a.acct_open_date.val,
    lblExp ++ a.acct_expiraion_date.val,
    lblReis ++ a.acct_reissue_date.val,
    lblCc ++ zonedText a.acct_curr_cyc_credit.val 12 true,
    lblCd ++ zonedText a.acct_curr_cyc_debit.val 12 true,
    lblGrp ++ a.acct_group_id.val,
    dashes,
    vb1Lbl ++ vbrc1 a,
    vb2Lbl ++ vbrc2 a,
    recText a]

theorem reis_length (a : AccountRecord) :
    (picks a.acct_reissue_date.val ++ [32#u8, 32#u8]).length = 10 := by
  have h : a.acct_reissue_date.val.length = 10 := by rw [Array.length_eq]; rfl
  simp only [picks, List.length_append, List.length_take, List.length_drop, List.length_cons,
    List.length_nil, h]
  omega

/-- The copy written to OUT-FILE, with cycle debit `cd`. -/
def outRec (a : AccountRecord) (cd : I64) : OutAcctRec :=
  { out_acct_id := a.acct_id, out_acct_active_status := a.acct_active_status,
    out_acct_curr_bal := a.acct_curr_bal, out_acct_credit_limit := a.acct_credit_limit,
    out_acct_cash_credit_limit := a.acct_cash_credit_limit,
    out_acct_open_date := a.acct_open_date, out_acct_expiraion_date := a.acct_expiraion_date,
    out_acct_reissue_date := Array.from (picks a.acct_reissue_date.val ++ [32#u8, 32#u8])
      (reis_length a),
    out_acct_curr_cyc_credit := a.acct_curr_cyc_credit, out_acct_curr_cyc_debit := cd,
    out_acct_group_id := a.acct_group_id }

/-- The array record written to ARRY-FILE. -/
def arrRec (a : AccountRecord) : ArrArrayRec :=
  { arr_acct_id := a.acct_id,
    arr_acct_curr_bal := Array.from [a.acct_curr_bal, a.acct_curr_bal, (-102500)#i64, 0#i64, 0#i64]
      rfl,
    arr_acct_curr_cyc_debit := Array.from [100500#i64, 152500#i64, (-250000)#i64, 0#i64, 0#i64] rfl,
    arr_filler := Array.from [32#u8, 32#u8, 32#u8, 32#u8] rfl }

/-- What `run` has output after some records, and the cycle debit of the last copy. -/
structure RSt where
  cd : I64
  disp : List (List U8)
  outs : List OutAcctRec
  arrs : List ArrArrayRec
  vbrcs : List (List U8)

def rstep (s : RSt) (a : AccountRecord) : RSt :=
  let cd := if a.acct_curr_cyc_debit = 0#i64 then 252500#i64 else s.cd
  { cd, disp := s.disp ++ recLines a, outs := s.outs ++ [outRec a cd], arrs := s.arrs ++ [arrRec a],
    vbrcs := s.vbrcs ++ [vbrc1 a, vbrc2 a] }

def rinit : RSt := { cd := 0#i64, disp := [startLine], outs := [], arrs := [], vbrcs := [] }

def rfold (l : List AccountRecord) : RSt := l.foldl rstep rinit

theorem rfold_lengths (l : List AccountRecord) :
    (rfold l).disp.length = 1 + 15 * l.length ∧ (rfold l).outs.length = l.length ∧
      (rfold l).arrs.length = l.length ∧ (rfold l).vbrcs.length = 2 * l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [rfold, rinit]
  | append_singleton l a ih =>
    simp only [rfold, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
    simp only [rstep, recLines, List.length_append, List.length_cons, List.length_nil]
    omega

/-- The state of `run`'s loop. -/
abbrev LSt := alloc.vec.Vec (alloc.vec.Vec U8) × alloc.vec.Vec OutAcctRec ×
  alloc.vec.Vec ArrArrayRec × alloc.vec.Vec (alloc.vec.Vec U8) × I64 × Array U8 1#usize × I64 ×
  I64 × I64 × Array U8 10#usize × Array U8 10#usize × Array U8 10#usize × I64 × I64 ×
  Array U8 10#usize × Array U8 80#usize × Bool × Usize

theorem rep5 : List.replicate 5 (0#i64) = [0#i64, 0#i64, 0#i64, 0#i64, 0#i64] := rfl
theorem rep4 : List.replicate 4 (32#u8) = [32#u8, 32#u8, 32#u8, 32#u8] := rfl



theorem zonedText_length11 (v : Int) (s : Bool) : (zonedText v 11 s).length = 11 :=
  zonedText_length _ _ _ (by decide)
theorem zonedText_length12 (v : Int) (s : Bool) : (zonedText v 12 s).length = 12 :=
  zonedText_length _ _ _ (by decide)

theorem dite_pos' {c : Prop} [Decidable c] {α : Sort _} {t : c → α} {e : ¬c → α} (h : c) :
    dite c t e = t h := by simp [h]

theorem one_elem (a : Array U8 1#usize) (h : 0 < a.val.length) : [a.val[0]'h] = a.val := by
  have hl : a.val.length = 1 := by rw [Array.length_eq]; rfl
  match a.val, hl, h with
  | [x], _, _ => rfl

/-- `aeneas_wp` whose conditional lemmas have their side conditions (lengths) discharged by a
small simp and `omega`. -/
syntax "cwp_c01" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic

macro_rules
  | `(tactic| cwp_c01 [$args,*]) => do
    let args : EquivLean.Aeneas.SimpArgs := args.getElems.map (⟨·.raw⟩)
    `(tactic| simp (config := { maxSteps := 2000000 })
        (disch := first
          | omega
          | (simp only [alloc.vec.Vec.from_val, Slice.from_val, List.length_append,
              List.length_cons, List.length_nil, List.length_take, Array.val_to_slice,
              Array.length_eq, uscalar_ofNat_val, UScalar.ofNatCore_val_eq, $args,*]; omega)
          | decide)
        only [wp_bind, wp_bind_tc, wp_ok, wp_fail, wp_div, wp_pure, wp_lift, wp_ite,
        wp_dite, wp_massert, wp_ofOption, wp_Slice_index_usize, wp_Vec_index_usize, wp_Vec_push,
        alloc.vec.Vec.index_slice_index, alloc.vec.Vec.len_val, alloc.vec.Vec.length,
        alloc.vec.Vec.from_val, Slice.from_val,
        wp_UScalar_add_val, wp_UScalar_sub_val, wp_UScalar_mul_val, wp_UScalar_div_val,
        wp_UScalar_rem_val, wp_IScalar_add_val, wp_IScalar_sub_val, wp_IScalar_mul_val,
        wp_IScalar_neg_val, wp_IScalar_div_val, wp_IScalar_rem, wp_UScalar_shl, wp_UScalar_shr,
        UScalar.cast_val_mod_pow_greater_numBits_eq, IScalar.val_mod_pow_greater_numBits,
        UScalar.hcast_val_of_numBits_lt,
        UScalar.lt_equiv, UScalar.le_equiv, IScalar.lt_equiv, IScalar.le_equiv,
        UScalar.eq_equiv, IScalar.eq_equiv, bne_iff_ne, ne_eq, decide_eq_true_eq,
        Slice.len_val, Slice.length, UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq,
        UScalarTy.U8_numBits_eq, UScalarTy.U16_numBits_eq, UScalarTy.U32_numBits_eq,
        UScalarTy.U64_numBits_eq, UScalarTy.U128_numBits_eq, IScalarTy.I8_numBits_eq,
        IScalarTy.I16_numBits_eq, IScalarTy.I32_numBits_eq, IScalarTy.I64_numBits_eq,
        IScalarTy.I128_numBits_eq, Nat.reduceLeDiff, Nat.reduceLT,
        UScalar.max_USize_eq, UScalar.max_UScalarTy_U8_eq, UScalar.max_UScalarTy_U16_eq,
        UScalar.max_UScalarTy_U32_eq, UScalar.max_UScalarTy_U64_eq,
        UScalar.max_UScalarTy_U128_eq, U8.max_eq, U16.max_eq, U32.max_eq, U64.max_eq,
        U128.max_eq, IScalar.min_IScalarTy_I8_eq, IScalar.max_IScalarTy_I8_eq,
        IScalar.min_IScalarTy_I16_eq, IScalar.max_IScalarTy_I16_eq,
        IScalar.min_IScalarTy_I32_eq, IScalar.max_IScalarTy_I32_eq,
        IScalar.min_IScalarTy_I64_eq, IScalar.max_IScalarTy_I64_eq,
        IScalar.min_IScalarTy_I128_eq, IScalar.max_IScalarTy_I128_eq, I8.min_eq, I8.max_eq,
        I16.min_eq, I16.max_eq, I32.min_eq, I32.max_eq, I64.min_eq, I64.max_eq, I128.min_eq,
        I128.max_eq, Prod.mk.injEq, Aeneas.Std.uncurry_apply_pair, _root_.dite_true,
        _root_.dite_false, _root_.ite_true, _root_.ite_false, and_self, and_true, true_and,
        $args,*])

set_option maxHeartbeats 8000000 in
/-- Chunk A1 of the loop body: the first six lines of 1100-DISPLAY-ACCT-RECORD. -/
theorem chunkA1 {β : Type} (acct : AccountRecord) (displays : alloc.vec.Vec (alloc.vec.Vec U8))
    (Q : Except Error β → Prop) (f : alloc.vec.Vec (alloc.vec.Vec U8) → Result β)
    (hU : 4294967295 ≤ Usize.max) (hb : displays.val.length + 6 < Usize.max)
    (hf : ∀ d6 : alloc.vec.Vec (alloc.vec.Vec U8),
      d6.val.map (·.val) = displays.val.map (·.val) ++ (recLines acct).take 6 →
      wp (f d6) Q) :
    wp (do
      let s ←
        lift (Array.to_slice
          (Array.make 25#usize [
            65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 73#u8, 68#u8, 32#u8, 32#u8,
            32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8,
            32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8
            ]))
      let v ← labeled_num s acct.acct_id 11#usize false
      let displays1 ← alloc.vec.Vec.push displays v
      let s1 ←
        lift (Array.to_slice
          (Array.make 25#usize [
            65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 65#u8, 67#u8, 84#u8, 73#u8,
            86#u8, 69#u8, 45#u8, 83#u8, 84#u8, 65#u8, 84#u8, 85#u8, 83#u8,
            32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8
            ]))
      let s2 ← lift (Array.to_slice acct.acct_active_status)
      let v1 ← labeled_x s1 s2
      let displays2 ← alloc.vec.Vec.push displays1 v1
      let s3 ←
        lift (Array.to_slice
          (Array.make 25#usize [
            65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 67#u8, 85#u8, 82#u8, 82#u8,
            45#u8, 66#u8, 65#u8, 76#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8,
            32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8
            ]))
      let v2 ← labeled_num s3 acct.acct_curr_bal 12#usize true
      let displays3 ← alloc.vec.Vec.push displays2 v2
      let s4 ←
        lift (Array.to_slice
          (Array.make 25#usize [
            65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 67#u8, 82#u8, 69#u8, 68#u8,
            73#u8, 84#u8, 45#u8, 76#u8, 73#u8, 77#u8, 73#u8, 84#u8, 32#u8,
            32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8
            ]))
      let v3 ← labeled_num s4 acct.acct_credit_limit 12#usize true
      let displays4 ← alloc.vec.Vec.push displays3 v3
      let s5 ←
        lift (Array.to_slice
          (Array.make 25#usize [
            65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 67#u8, 65#u8, 83#u8, 72#u8,
            45#u8, 67#u8, 82#u8, 69#u8, 68#u8, 73#u8, 84#u8, 45#u8, 76#u8,
            73#u8, 77#u8, 73#u8, 84#u8, 32#u8, 32#u8, 58#u8
            ]))
      let v4 ← labeled_num s5 acct.acct_cash_credit_limit 12#usize true
      let displays5 ← alloc.vec.Vec.push displays4 v4
      let s6 ←
        lift (Array.to_slice
          (Array.make 25#usize [
            65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 79#u8, 80#u8, 69#u8, 78#u8,
            45#u8, 68#u8, 65#u8, 84#u8, 69#u8, 32#u8, 32#u8, 32#u8, 32#u8,
            32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8
            ]))
      let s7 ← lift (Array.to_slice acct.acct_open_date)
      let v5 ← labeled_x s6 s7
      let displays6 ← alloc.vec.Vec.push displays5 v5
      f displays6) Q := by
  cwp_c01 [labeled_num_eq, labeled_x_eq, lit_eq, zonedText_length11, zonedText_length12, dite_pos',
    Array.make_val, Array.val_to_slice]
  apply hf
  simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, recLines,
    List.take_succ_cons, List.take_zero, List.append_assoc,
    List.cons_append, List.nil_append, lblId, lblStatus, lblBal, lblLimit,
    lblCash, lblOpen, lblExp, lblReis, lblCc, lblCd, lblGrp, dashes]

set_option maxHeartbeats 8000000 in
/-- Chunk A2: the next six lines (through the dashes). -/
theorem chunkA2 {β : Type} (acct : AccountRecord) (displays6 : alloc.vec.Vec (alloc.vec.Vec U8))
    (Q : Except Error β → Prop) (f : alloc.vec.Vec (alloc.vec.Vec U8) → Result β)
    (hU : 4294967295 ≤ Usize.max) (hb : displays6.val.length + 6 < Usize.max)
    (hf : ∀ d12 : alloc.vec.Vec (alloc.vec.Vec U8),
      d12.val.map (·.val) = displays6.val.map (·.val) ++ ((recLines acct).drop 6).take 6 →
      wp (f d12) Q) :
    wp (do
      let s8 ←
        lift (Array.to_slice
          (Array.make 25#usize [
            65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 69#u8, 88#u8, 80#u8, 73#u8,
            82#u8, 65#u8, 73#u8, 79#u8, 78#u8, 45#u8, 68#u8, 65#u8, 84#u8,
            69#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8
            ]))
      let s9 ← lift (Array.to_slice acct.acct_expiraion_date)
      let v6 ← labeled_x s8 s9
      let displays7 ← alloc.vec.Vec.push displays6 v6
      let s10 ←
        lift (Array.to_slice
          (Array.make 25#usize [
            65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 82#u8, 69#u8, 73#u8, 83#u8,
            83#u8, 85#u8, 69#u8, 45#u8, 68#u8, 65#u8, 84#u8, 69#u8, 32#u8,
            32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8
            ]))
      let s11 ← lift (Array.to_slice acct.acct_reissue_date)
      let v7 ← labeled_x s10 s11
      let displays8 ← alloc.vec.Vec.push displays7 v7
      let s12 ←
        lift (Array.to_slice
          (Array.make 25#usize [
            65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 67#u8, 85#u8, 82#u8, 82#u8,
            45#u8, 67#u8, 89#u8, 67#u8, 45#u8, 67#u8, 82#u8, 69#u8, 68#u8,
            73#u8, 84#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8
            ]))
      let v8 ← labeled_num s12 acct.acct_curr_cyc_credit 12#usize true
      let displays9 ← alloc.vec.Vec.push displays8 v8
      let s13 ←
        lift (Array.to_slice
          (Array.make 25#usize [
            65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 67#u8, 85#u8, 82#u8, 82#u8,
            45#u8, 67#u8, 89#u8, 67#u8, 45#u8, 68#u8, 69#u8, 66#u8, 73#u8,
            84#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8
            ]))
      let v9 ← labeled_num s13 acct.acct_curr_cyc_debit 12#usize true
      let displays10 ← alloc.vec.Vec.push displays9 v9
      let s14 ←
        lift (Array.to_slice
          (Array.make 25#usize [
            65#u8, 67#u8, 67#u8, 84#u8, 45#u8, 71#u8, 82#u8, 79#u8, 85#u8,
            80#u8, 45#u8, 73#u8, 68#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8,
            32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 32#u8, 58#u8
            ]))
      let s15 ← lift (Array.to_slice acct.acct_group_id)
      let v10 ← labeled_x s14 s15
      let displays11 ← alloc.vec.Vec.push displays10 v10
      let s16 ←
        lift (Array.to_slice
          (Array.make 49#usize [
            45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8,
            45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8,
            45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8,
            45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8,
            45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8, 45#u8,
            45#u8, 45#u8, 45#u8, 45#u8
            ]))
      let v11 ← lit s16
      let displays12 ← alloc.vec.Vec.push displays11 v11
      f displays12) Q := by
  cwp_c01 [labeled_num_eq, labeled_x_eq, lit_eq, zonedText_length11, zonedText_length12, dite_pos',
    Array.make_val, Array.val_to_slice]
  apply hf
  simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, recLines,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.append_assoc,
    List.cons_append, List.nil_append, lblId, lblStatus, lblBal, lblLimit,
    lblCash, lblOpen, lblExp, lblReis, lblCc, lblCd, lblGrp, dashes]

set_option maxHeartbeats 4000000 in
/-- Chunk C: the OUT-FILE and ARRY-FILE records. -/
theorem chunkC {β : Type} (acct : AccountRecord) (i5 : I64) (a5 : Array U8 10#usize)
    (out_file_writes : alloc.vec.Vec OutAcctRec) (arry_file_writes : alloc.vec.Vec ArrArrayRec)
    (Q : Except Error β → Prop)
    (f : I64 → alloc.vec.Vec OutAcctRec → alloc.vec.Vec ArrArrayRec → Result β)
    (ho : out_file_writes.val.length < Usize.max) (ha : arry_file_writes.val.length < Usize.max)
    (hf : ∀ o1 a1, o1.val = out_file_writes.val ++
        [{ out_acct_id := acct.acct_id, out_acct_active_status := acct.acct_active_status,
           out_acct_curr_bal := acct.acct_curr_bal, out_acct_credit_limit := acct.acct_credit_limit,
           out_acct_cash_credit_limit := acct.acct_cash_credit_limit,
           out_acct_open_date := acct.acct_open_date,
           out_acct_expiraion_date := acct.acct_expiraion_date, out_acct_reissue_date := a5,
           out_acct_curr_cyc_credit := acct.acct_curr_cyc_credit,
           out_acct_curr_cyc_debit := if acct.acct_curr_cyc_debit = 0#i64 then 252500#i64 else i5,
           out_acct_group_id := acct.acct_group_id }] →
      a1.val = arry_file_writes.val ++ [arrRec acct] →
      wp (f (if acct.acct_curr_cyc_debit = 0#i64 then 252500#i64 else i5) o1 a1) Q) :
    wp (do
      let i7 ← (if acct.acct_curr_cyc_debit = 0#i64 then ok 252500#i64 else ok i5)
      let out_file_writes1 ←
        alloc.vec.Vec.push out_file_writes
          ({
             out_acct_id := acct.acct_id,
             out_acct_active_status := acct.acct_active_status,
             out_acct_curr_bal := acct.acct_curr_bal,
             out_acct_credit_limit := acct.acct_credit_limit,
             out_acct_cash_credit_limit := acct.acct_cash_credit_limit,
             out_acct_open_date := acct.acct_open_date,
             out_acct_expiraion_date := acct.acct_expiraion_date,
             out_acct_reissue_date := a5,
             out_acct_curr_cyc_credit := acct.acct_curr_cyc_credit,
             out_acct_curr_cyc_debit := i7,
             out_acct_group_id := acct.acct_group_id
           } : OutAcctRec)
      let bal1 ← Array.update (Array.repeat 5#usize 0#i64) 0#usize acct.acct_curr_bal
      let deb1 ← Array.update (Array.repeat 5#usize 0#i64) 0#usize 100500#i64
      let bal2 ← Array.update bal1 1#usize acct.acct_curr_bal
      let deb2 ← Array.update deb1 1#usize 152500#i64
      let bal3 ← Array.update bal2 2#usize (-102500)#i64
      let deb3 ← Array.update deb2 2#usize (-250000)#i64
      let arry_file_writes1 ←
        alloc.vec.Vec.push arry_file_writes
          ({
             arr_acct_id := acct.acct_id,
             arr_acct_curr_bal := bal3,
             arr_acct_curr_cyc_debit := deb3,
             arr_filler := (Array.repeat 4#usize 32#u8)
           } : ArrArrayRec)
      f i7 out_file_writes1 arry_file_writes1) Q := by
  by_cases hc : acct.acct_curr_cyc_debit = 0#i64
  · have hc' : acct.acct_curr_cyc_debit.val = 0 := by rw [hc]; rfl
    simp only [hc, _root_.ite_true]
    simp only [hc, _root_.ite_true] at hf
    cwp_c01 [array_update_eq, Array.repeat_val, Array.length_eq, dite_pos', hc']
    apply hf
    · simp only [alloc.vec.Vec.from_val]
    · simp only [alloc.vec.Vec.from_val, arrRec, List.append_cancel_left_eq, List.cons.injEq,
        ArrArrayRec.mk.injEq, Aeneas.Std.Array.eq_iff, Array.from_val,
        Array.repeat_val, uscalar_ofNat_val, List.replicate_succ, List.replicate_zero,
        List.set_cons_succ, List.set_cons_zero, and_self]
  · have hc' : acct.acct_curr_cyc_debit.val ≠ 0 := fun h => hc (IScalar.eq_of_val_eq (by simp [h]))
    simp only [hc, _root_.ite_false]
    simp only [hc, _root_.ite_false] at hf
    cwp_c01 [array_update_eq, Array.repeat_val, Array.length_eq, dite_pos', hc']
    apply hf
    · simp only [alloc.vec.Vec.from_val]
    · simp only [alloc.vec.Vec.from_val, arrRec, List.append_cancel_left_eq, List.cons.injEq,
        ArrArrayRec.mk.injEq, Aeneas.Std.Array.eq_iff, Array.from_val,
        Array.repeat_val, uscalar_ofNat_val, List.replicate_succ, List.replicate_zero,
        List.set_cons_succ, List.set_cons_zero, and_self]

set_option maxHeartbeats 4000000 in
/-- Chunk D: the variable-length records, displayed and written. -/
theorem chunkD {β : Type} (acct : AccountRecord) (displays12 : alloc.vec.Vec (alloc.vec.Vec U8))
    (vbrc_file_writes : alloc.vec.Vec (alloc.vec.Vec U8)) (Q : Except Error β → Prop)
    (f : alloc.vec.Vec U8 → alloc.vec.Vec (alloc.vec.Vec U8) → alloc.vec.Vec (alloc.vec.Vec U8) →
      Result β)
    (hU : 4294967295 ≤ Usize.max) (hd : displays12.val.length + 2 < Usize.max)
    (hv : vbrc_file_writes.val.length + 2 < Usize.max)
    (hf : ∀ v1 d14 vw2, v1.val = zonedText acct.acct_id.val 11 false →
      d14.val.map (·.val) = displays12.val.map (·.val) ++ [vb1Lbl ++ vbrc1 acct, vb2Lbl ++ vbrc2 acct] →
      vw2.val.map (·.val) = vbrc_file_writes.val.map (·.val) ++ [vbrc1 acct, vbrc2 acct] →
      wp (f v1 d14 vw2) Q) :
    wp (do
      let vbrc1 ←
        push_zoned (alloc.vec.Vec.new Std.U8) acct.acct_id 11#usize false
      let i8 ← Array.index_usize acct.acct_active_status 0#usize
      let vbrc11 ← alloc.vec.Vec.push vbrc1 i8
      let vbrc2 ← push_zoned vbrc1 acct.acct_curr_bal 12#usize true
      let vbrc21 ← push_zoned vbrc2 acct.acct_credit_limit 12#usize true
      let vbrc22 ← push_first4 vbrc21 acct.acct_reissue_date
      let s17 ←
        lift (Array.to_slice
          (Array.make 10#usize [
            86#u8, 66#u8, 82#u8, 67#u8, 45#u8, 82#u8, 69#u8, 67#u8, 49#u8,
            58#u8
            ]))
      let d1 ← lit s17
      let d11 ← push_bytes d1 (alloc.vec.Vec.deref vbrc11)
      let displays13 ← alloc.vec.Vec.push displays12 d11
      let s19 ←
        lift (Array.to_slice
          (Array.make 10#usize [
            86#u8, 66#u8, 82#u8, 67#u8, 45#u8, 82#u8, 69#u8, 67#u8, 50#u8,
            58#u8
            ]))
      let d2 ← lit s19
      let d21 ← push_bytes d2 (alloc.vec.Vec.deref vbrc22)
      let displays14 ← alloc.vec.Vec.push displays13 d21
      let vbrc_file_writes1 ← alloc.vec.Vec.push vbrc_file_writes vbrc11
      let vbrc_file_writes2 ← alloc.vec.Vec.push vbrc_file_writes1 vbrc22
      f vbrc1 displays14 vbrc_file_writes2) Q := by
  cwp_c01 [push_zoned_eq, push_bytes_eq, push_first4_eq, lit_eq, array_index_usize_eq,
    alloc.vec.Vec.new, alloc.vec.Vec.deref, zonedText_length11, zonedText_length12, dite_pos']
  apply hf
  · simp only [alloc.vec.Vec.from_val, List.nil_append]
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, vbrc1, vbrc2,
      List.nil_append, List.append_assoc, one_elem, vb1Lbl, vb2Lbl, Array.val_to_slice,
      Array.make_val, List.cons_append]
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, vbrc1, vbrc2,
      List.nil_append, List.append_assoc, one_elem, List.cons_append]

set_option maxHeartbeats 4000000 in
/-- Chunk E: the account record's line. -/
theorem chunkE {β : Type} (acct : AccountRecord) (vbrc1 : alloc.vec.Vec U8)
    (displays14 : alloc.vec.Vec (alloc.vec.Vec U8)) (Q : Except Error β → Prop)
    (f : alloc.vec.Vec (alloc.vec.Vec U8) → Result β)
    (hU : 4294967295 ≤ Usize.max) (hv1 : vbrc1.val = zonedText acct.acct_id.val 11 false)
    (hd : displays14.val.length < Usize.max)
    (hf : ∀ d15, d15.val.map (·.val) = displays14.val.map (·.val) ++ [recText acct] →
      wp (f d15) Q) :
    wp (do
      let s21 ← lift (Array.to_slice acct.acct_active_status)
      let d ← push_bytes vbrc1 s21
      let d3 ← push_zoned d acct.acct_curr_bal 12#usize true
      let d4 ← push_zoned d3 acct.acct_credit_limit 12#usize true
      let d5 ← push_zoned d4 acct.acct_cash_credit_limit 12#usize true
      let s22 ← lift (Array.to_slice acct.acct_open_date)
      let d6 ← push_bytes d5 s22
      let s23 ← lift (Array.to_slice acct.acct_expiraion_date)
      let d7 ← push_bytes d6 s23
      let s24 ← lift (Array.to_slice acct.acct_reissue_date)
      let d8 ← push_bytes d7 s24
      let d9 ← push_zoned d8 acct.acct_curr_cyc_credit 12#usize true
      let d10 ← push_zoned d9 acct.acct_curr_cyc_debit 12#usize true
      let s25 ← lift (Array.to_slice acct.acct_addr_zip)
      let d12 ← push_bytes d10 s25
      let s26 ← lift (Array.to_slice acct.acct_group_id)
      let d13 ← push_bytes d12 s26
      let s27 ← lift (Array.to_slice acct.filler1)
      let d14 ← push_bytes d13 s27
      let displays15 ← alloc.vec.Vec.push displays14 d14
      f displays15) Q := by
  have l1 : vbrc1.val.length = 11 := by rw [hv1]; exact zonedText_length _ _ _ (by decide)
  cwp_c01 [push_bytes_eq, push_zoned_eq, zonedText_length11, zonedText_length12, l1, dite_pos']
  apply hf
  simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, recText, hv1,
    Array.val_to_slice, List.append_assoc]

end EquivLean.Modernize.Cbact01c.Rust
