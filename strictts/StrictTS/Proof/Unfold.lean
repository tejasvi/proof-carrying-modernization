/-
StrictTS proof layer: interpreter equations in the `ts_sym` simp set.

Every IR construct unfolds by one equation, except loops (`evalLoop`, `evalDo`,
`evalForOf…`), which are handled by the loop theorems of `StrictTS.Proof.Loops`, and calls of
top-level functions (`callFun`), which are unfolded explicitly (`rw [f_call]`) or replaced by a
specification lemma, so that recursion never makes `simp` loop.
-/
import StrictTS.Proof.EqnsS

set_option maxHeartbeats 0

namespace StrictTS

attribute [ts_sym] evalE
attribute [ts_sym] evalArgs evalB
attribute [ts_sym] applyFn applyLam
attribute [ts_sym] Builtin.hasCallback evalBuiltinBasic.eq_def
attribute [ts_sym] PrimOp.eval.eq_def
attribute [ts_sym] JS.finishSync JS.finishAsync defaultRet Alts.select AltsS.select
attribute [ts_sym] OVals.get? OVals.set OVals.empty normKey
attribute [ts_sym] JS.index? JS.toInt JS.num JS.materialize JS.materializeList
attribute [simp, ts_sym] Ty.eqable Tys.eqable
attribute [ts_sym] Prim.ofErr Prim.intToJSStr BigOps.bin BigOps.cmp Except.map
attribute [ts_sym] Prim.numBin Prim.numUn Prim.numCmp Prim.numPred Prim.strCmp
attribute [ts_sym] Val.toNum_num Val.toBig_bigint Val.toBool_bool Val.toStr_str Val.toErr_err
attribute [ts_sym] Val.arrAddr_arr Val.mapAddr_map Val.setAddr_set Val.objAddr_obj Val.promAddr_promise
attribute [ts_sym] Val.boxAddr_box Val.tarrAddr_tarr Val.unfold_fold Val.extId_ext Val.dictAddr_dict
attribute [ts_sym] Val.toNum Val.toBig Val.toBool Val.toStr Val.toErr Val.arrAddr Val.tarrAddr Val.mapAddr
attribute [ts_sym] Val.setAddr Val.objAddr Val.promAddr Val.boxAddr Val.extId Val.dictAddr Val.tupVals Val.recVals Val.unfold Val.enumIdx
attribute [ts_sym] Vals.head_cons Vals.tail_cons Vals.get_here Vals.get_there Vals.a0_cons Vals.a1_cons
attribute [ts_sym] Vals.a2_cons Vals.a3_cons Vals.toEnv_nil Vals.toEnv_cons
attribute [ts_sym] Env.head_cons Env.tail_cons Env.get_here Env.get_there Env.set_here Env.set_there
attribute [ts_sym] Env.getC_here Env.getC_there Env.append_nil Env.append_cons
attribute [ts_sym] Caps.capture_nil Caps.capture_cons
attribute [ts_sym] ite_true ite_false dite_true dite_false Bool.false_eq_true Bool.true_eq_false
attribute [ts_sym] Lit.val_num Lit.val_bigint Lit.val_bool Lit.val_str Lit.val_undef Lit.val_null


namespace JS
variable {TT : TypeTable}

/-! Heap helpers keep their own execution lemmas (unfolding them would expose the dependent
cell type `HKind.Cell`, which `simp` cannot match against). -/

@[simp, ts_sym] theorem exec_readArr (t : Ty) (a : Nat) (w : World TT) :
    exec (readArr t a) w = (match w.heap.get? (.arr t, a) with
      | some c => some (.ok c, w)
      | none => some (.error (.panic "dangling reference"), w)) := by
  unfold readArr; rw [exec_read]; cases w.heap.get? (.arr t, a) <;> rfl
@[simp, ts_sym] theorem exec_writeArr (t : Ty) (a : Nat) (c : Array (Val TT t)) (w : World TT) :
    exec (writeArr t a c) w = some (.ok ⟨⟩, { w with heap := w.heap.insert (.arr t, a) c }) := rfl
@[simp, ts_sym] theorem exec_allocArr (t : Ty) (c : Array (Val TT t)) (w : World TT) :
    exec (allocArr t c) w =
      some (.ok (.arr w.next), { w with heap := w.heap.insert (.arr t, w.next) c, next := w.next + 1 }) := rfl
@[simp, ts_sym] theorem exec_readTA (k : TAKind) (a : Nat) (w : World TT) :
    exec (readTA k a) w = (match w.heap.get? (.tarr k, a) with
      | some c => some (.ok c, w)
      | none => some (.error (.panic "dangling reference"), w)) := by
  unfold readTA; rw [exec_read]; cases w.heap.get? (.tarr k, a) <;> rfl
@[simp, ts_sym] theorem exec_writeTA (k : TAKind) (a : Nat) (c : Array (BitVec k.width)) (w : World TT) :
    exec (writeTA k a c) w = some (.ok ⟨⟩, { w with heap := w.heap.insert (.tarr k, a) c }) := rfl
@[simp, ts_sym] theorem exec_readMap (k v : Ty) (a : Nat) (w : World TT) :
    exec (readMap k v a) w = (match w.heap.get? (.map k v, a) with
      | some c => some (.ok c, w)
      | none => some (.error (.panic "dangling reference"), w)) := by
  unfold readMap; rw [exec_read]; cases w.heap.get? (.map k v, a) <;> rfl
@[simp, ts_sym] theorem exec_writeMap (k v : Ty) (a : Nat) (m : JSMap (Val TT k) (Val TT v)) (w : World TT) :
    exec (writeMap k v a m) w = some (.ok ⟨⟩, { w with heap := w.heap.insert (.map k v, a) m }) := rfl
@[simp, ts_sym] theorem exec_readSet (t : Ty) (a : Nat) (w : World TT) :
    exec (readSet t a) w = (match w.heap.get? (.set t, a) with
      | some c => some (.ok c, w)
      | none => some (.error (.panic "dangling reference"), w)) := by
  unfold readSet; rw [exec_read]; cases w.heap.get? (.set t, a) <;> rfl
@[simp, ts_sym] theorem exec_writeSet (t : Ty) (a : Nat) (m : JSMap (Val TT t) Unit) (w : World TT) :
    exec (writeSet t a m) w = some (.ok ⟨⟩, { w with heap := w.heap.insert (.set t, a) m }) := rfl
@[simp, ts_sym] theorem exec_readDict (t : Ty) (a : Nat) (w : World TT) :
    exec (readDict t a) w = (match w.heap.get? (.dict t, a) with
      | some c => some (.ok c, w)
      | none => some (.error (.panic "dangling reference"), w)) := by
  unfold readDict; rw [exec_read]; cases w.heap.get? (.dict t, a) <;> rfl
@[simp, ts_sym] theorem exec_writeDict (t : Ty) (a : Nat) (m : JSMap JSStr (Val TT t)) (w : World TT) :
    exec (writeDict t a m) w = some (.ok ⟨⟩, { w with heap := w.heap.insert (.dict t, a) m }) := rfl
@[simp, ts_sym] theorem exec_readPromise (t : Ty) (p : Nat) (w : World TT) :
    exec (readPromise t p) w = (match w.heap.get? (.promise t, p) with
      | some c => some (.ok c, w)
      | none => some (.error (.panic "dangling reference"), w)) := by
  unfold readPromise; rw [exec_read]; cases w.heap.get? (.promise t, p) <;> rfl
@[simp, ts_sym] theorem exec_readBoxOpt (t : Ty) (a : Nat) (w : World TT) :
    exec (readBoxOpt t a) w = (match w.heap.get? (.box t, a) with
      | some c => some (.ok c, w)
      | none => some (.error (.panic "dangling reference"), w)) := by
  unfold readBoxOpt; rw [exec_read]; cases w.heap.get? (.box t, a) <;> rfl
@[simp, ts_sym] theorem exec_readBox (t : Ty) (a : Nat) (w : World TT) :
    exec (readBox t a) w = (match w.heap.get? (.box t, a) with
      | some (some v) => some (.ok v, w)
      | some none => some (.error (.thrown (mkErr .referenceError
          (JSStr.ofString "Cannot access variable before initialization"))), w)
      | none => some (.error (.panic "dangling reference"), w)) := by
  unfold readBox
  rw [exec_bind, exec_read]
  rcases w.heap.get? (.box t, a) with _ | (_ | v) <;> rfl

@[simp, ts_sym] theorem exec_readObj (c : String) (fs : List Ty) (a : Nat) (w : World TT) :
    exec (readObj c fs a) w = (match w.heap.get? (.obj c fs, a) with
      | some cell => some (.ok cell, w)
      | none => some (.error (.panic "dangling reference"), w)) := by
  unfold readObj; rw [exec_read]; cases w.heap.get? (.obj c fs, a) <;> rfl
@[simp, ts_sym] theorem exec_writeObj (c : String) (fs : List Ty) (a : Nat) (cell : OVals TT fs) (w : World TT) :
    exec (writeObj c fs a cell) w = some (.ok ⟨⟩, { w with heap := w.heap.insert (.obj c fs, a) cell }) := rfl

@[simp, ts_sym] theorem exec_materialize_val {t : Ty} (v : Val TT t) (w : World TT) :
    exec (materialize (.val v)) w = some (.ok v, w) := rfl

/-- External calls: the oracle answers, and the call counter advances. -/
@[simp, ts_sym] theorem exec_extAnswer (name : String) (args : List Ty) (ret : Ty) (vs : Vals TT args)
    (w : World TT) :
    exec (extAnswer name args ret vs) w =
      some (.ok (w.ext name args ret vs w.extIdx), { w with extIdx := w.extIdx + 1 }) := rfl

end JS
/-! `===` on each type (the equation compiler cannot generate `strictEq`'s equations). -/
section strictEq
variable {TT : TypeTable}
@[simp, ts_sym] theorem Conv.strictEq_num (x y : Val TT .num) : Conv.strictEq .num x y = Conv.numEq x.toNum y.toNum := rfl
@[simp, ts_sym] theorem Conv.strictEq_str (x y : Val TT .str) : Conv.strictEq .str x y = (x.toStr == y.toStr) := rfl
@[simp, ts_sym] theorem Conv.strictEq_bool (x y : Val TT .bool) : Conv.strictEq .bool x y = (x.toBool == y.toBool) := rfl
@[simp, ts_sym] theorem Conv.strictEq_bigint (x y : Val TT .bigint) : Conv.strictEq .bigint x y = (x.toBig == y.toBig) := rfl
@[simp, ts_sym] theorem Conv.strictEq_arr {t : Ty} (x y : Val TT (.arr t)) :
    Conv.strictEq (.arr t) x y = (x.arrAddr == y.arrAddr) := rfl
@[simp, ts_sym] theorem Conv.strictEq_map {k v : Ty} (x y : Val TT (.map k v)) :
    Conv.strictEq (.map k v) x y = (x.mapAddr == y.mapAddr) := rfl
@[simp, ts_sym] theorem Conv.strictEq_set {t : Ty} (x y : Val TT (.set t)) :
    Conv.strictEq (.set t) x y = (x.setAddr == y.setAddr) := rfl
@[simp, ts_sym] theorem Conv.strictEq_obj {c : String} (x y : Val TT (.obj c)) :
    Conv.strictEq (.obj c) x y = (x.objAddr == y.objAddr) := rfl
@[simp, ts_sym] theorem Conv.strictEq_ext {n : String} (x y : Val TT (.ext n)) :
    Conv.strictEq (.ext n) x y = (x.extId == y.extId) := rfl
@[simp, ts_sym] theorem Conv.strictEq_enum {cs : List String} (x y : Val TT (.enum cs)) :
    Conv.strictEq (.enum cs) x y = (x.enumIdx == y.enumIdx) := rfl
@[simp, ts_sym] theorem Conv.strictEq_undef (x y : Val TT .undef) : Conv.strictEq .undef x y = true := rfl
@[simp, ts_sym] theorem Conv.strictEq_null (x y : Val TT .null) : Conv.strictEq .null x y = true := rfl
@[simp, ts_sym] theorem Conv.strictEq_none_none {t : Ty} :
    Conv.strictEq (TT := TT) (.opt t) .none .none = true := rfl
@[simp, ts_sym] theorem Conv.strictEq_some_some {t : Ty} (x y : Val TT t) :
    Conv.strictEq (.opt t) (.some x) (.some y) = Conv.strictEq t x y := rfl
@[simp, ts_sym] theorem Conv.strictEq_none_some {t : Ty} (y : Val TT t) :
    Conv.strictEq (.opt t) .none (.some y) = false := rfl
@[simp, ts_sym] theorem Conv.strictEq_some_none {t : Ty} (x : Val TT t) :
    Conv.strictEq (.opt t) (.some x) .none = false := rfl
end strictEq

end StrictTS
