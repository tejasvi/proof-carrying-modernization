import EquivLean.Modernize.Cbact01c.JavaRunClose

/-!
# CBACT01C → Java: `run`, a record read

From the head of the read loop with a record left (`endOfFile` not set, `pos <` the length): the
record is displayed, copied to the three output files and displayed whole; back at the loop head
with one record more.
-/

-- JimpleLean 2006Z took `ite_nat_ne` out of `jsimp`: these proofs decide address
-- (dis)equalities with it.
attribute [local jsimp high] Jimple.ite_nat_ne

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

set_option jimple.dischFailFast true in
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_seg10_read (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal))
    (fr : Frame) (σ : Jimple.State) (et : JType) (xs : List Value) (i : I32) (cd : I64) (d : Addr)
    (s : JStr) (fs : List (FieldKey × Value)) (ys1 ys2 ys3 ys4 : List Value) (m1 m2 m3 m4 : Nat)
    (c : Addr) (fsc : List (FieldKey × Value)) (x7 : Addr) (s7 : JStr) (dbt : I64)
    (ha : σ0.heap a = some (.array et xs)) (ha0 : a < σ0.next) (hlen : xs.length < 2147483648)
    (f0 : fr.get 0 = some (.ref σ0.next)) (f1 : fr.get 1 = some (.ref a))
    (f7 : fr.get 7 = some (.int i)) (f12 : fr.get 12 = some (.int 0#32))
    (f11 : fr.get 11 = some (.int 0#32)) (f3 : fr.get 3 = some (.long cd))
    (f9 : fr.get 9 = some (.ref d)) (hd : σ.heap d = some (.str s))
    (hR : σ.heap σ0.next = some (.plain resCls fs))
    (hl1 : σ.heap (σ0.next + 1) = some (.list .arrayList ys1 m1))
    (hl2 : σ.heap (σ0.next + 2) = some (.list .arrayList ys2 m2))
    (hl3 : σ.heap (σ0.next + 3) = some (.list .arrayList ys3 m3))
    (hl4 : σ.heap (σ0.next + 4) = some (.list .arrayList ys4 m4))
    (hi0 : 0 ≤ i.toInt) (hin : i.toInt < xs.length)
    (hdB1 : d ≠ σ0.next + 1) (hdB2 : d ≠ σ0.next + 2) (hdB3 : d ≠ σ0.next + 3)
    (hdB4 : d ≠ σ0.next + 4)
    (hR1 : Fields.get fs (resCls, "displays") = some (.ref (σ0.next + 1)))
    (hR2 : Fields.get fs (resCls, "outFileWrites") = some (.ref (σ0.next + 2)))
    (hR3 : Fields.get fs (resCls, "arryFileWrites") = some (.ref (σ0.next + 3)))
    (hR4 : Fields.get fs (resCls, "vbrcFileWrites") = some (.ref (σ0.next + 4)))
    (hR5 : Fields.get fs (resCls, "abended") = some (.int 0))
    (hD : Hide (RunData σ0 vals σ i.toNat cd s ys1 ys2 ys3 ys4))
    (hg1 : σ0.next ≤ σ.next) (hg2 : ∀ x, x < σ0.next → σ.heap x = σ0.heap x)
    (hinits : σ.inits = σ0.inits) (hstatics : σ.statics = σ0.statics)
    (hxk : xs[i.toNat]? = some (.ref c)) (hk : (BitVec.toInt i).toNat < xs.length)
    (hxk2 : xs[(BitVec.toInt i).toNat]'hk = .ref c) (hs20 : s.length = 20) (hc0 : c < σ0.next)
    (hc : σ0.heap c = some (.plain acctCls fsc))
    (hf7 : Fields.get fsc (acctCls, "acctReissueDate") = some (.ref x7))
    (hx70 : x7 < σ0.next) (hx7 : σ0.heap x7 = some (.str s7)) (hs7 : s7.length < 2147483648)
    (hf9 : Fields.get fsc (acctCls, "acctCurrCycDebit") = some (.long dbt))
    (hok : Hide (AcctOk σ0 c)) (v : List EquivLean.Cobol.Rec.FVal) (hv : Hide (vals[i.toNat]? = some v))
    (hA : Hide (AcctAt σ0 c v)) (hd0 : d < σ.next) (hl40 : σ0.next + 4 < σ.next)
    (i1 : σ0.initOf "Cbact01c" = .done) (i2 : σ0.initOf "Cbact01c$Result" = .done)
    (i3 : σ0.initOf "Cbact01c$AccountRecord" = .done) (i4 : σ0.initOf "Cbact01c$ArrArrayRec" = .done)
    (i5 : σ0.initOf "Cbact01c$OutAcctRec" = .done) :
    RunWP σ0 a vals 10 fr σ := by
  unfold RunWP
  jvc [runEnv_listAdd, runEnv_strEquals, runEnv_displayIoStatus, runEnv_pad, runEnv_cobdatft,
    runEnv_displayAcctRecord, runEnv_writeOutRecord, runEnv_writeArrayRecord, runEnv_writeVbrcRecords,
    runEnv_accountRecordText, padSpec, cobdatftSpec, padSpecR, cobdatftSpecR, displayAcctRecordSpecR,
    writeOutRecordSpecR, writeArrayRecordSpecR, writeVbrcRecordsSpecR, accountRecordTextSpecR, runSpecG,
    runInv, runInv10, Grows, StrOk, argText, lElems, lMods, resCls, acctCls, inlineFuel, fixStr_length,
    jstrLit, exists_and_left, exists_and_right, and_assoc, exists_eq_left, exists_eq_left',
    exists_eq_right, exists_eq_right', cobOut_length, cobOut_fixStr_length, List.filter_cons,
    List.filter_nil, List.foldl_cons, List.foldl_nil]
  all_goals
    apply read_close hD hv hA hc hf7 hx7 hf9 hi0
    all_goals try first
      | exact cd_neg ‹_›
      | exact cd_zero ‹_›
      | exact cd_pos ‹_›
      | exact ⟨by simp only [State.next_setObj]; jomega, fun x hb hx => by rchain⟩
      | jomega
      | (rchain; done)
      | (apply outRecJ_of_parts; all_goals first | assumption | jomega | (rchain; done))
      | (apply arrRecJ_of_parts; all_goals first | assumption | jomega | (rchain; done))

end EquivLean.Modernize.Cbact01c.Java
