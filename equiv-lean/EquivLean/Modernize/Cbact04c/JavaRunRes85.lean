import EquivLean.Modernize.Cbact04c.JavaRunRunHeap
import EquivLean.Modernize.Cbact04c.JavaRunCallSpecs

/-!
# CBACT04C → Java, `run`: the cut point after statement 85's read (the residual of `jvc`)
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-- Record `i` copied into a fresh object (`copyTcb`'s contract): the cut point 90. -/
theorem j89_of_copy {g : G} {σ0 σ σ1 : State} {fr : Frame} {i : I32} {hp : Hp}
    {acctV xrefV lastV : Value} {y : Addr} {fsy : List (FieldKey × Value)} {v : Option Value}
    (hn' : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr)
    (f12 : fr.get 12 = some (.long (BitVec.ofInt 64 (g.st i.toInt.toNat).total)))
    (f3 : fr.get 3 = some (.int (if (g.st i.toInt.toNat).lastId.isSome then 0#32 else 1#32)))
    (f14 : fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)))
    (f25 : fr.get 25 = some lastV) (f16 : fr.get 16 = some acctV) (f17 : fr.get 17 = some xrefV)
    (f4 : fr.get 4 = some (.int 0#32)) (f5 : fr.get 5 = some (.int 0#32))
    (hheap : Hide (LoopHeap g σ0 σ hp (g.st i.toInt.toNat) acctV xrefV lastV))
    (hrec : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ0 (.ref y)
      (g.trec i.toInt.toNat)))
    (hyh : σ.heap y = some (.plain "Cbact04c$TranCatBalRecord" fsy))
    (hpost : ∀ (x : Addr) (fs : List (FieldKey × Value)), y = x →
      σ.heap x = some (.plain "Cbact04c$TranCatBalRecord" fs) →
      ∃ y', v = some (.ref y') ∧ σ.next ≤ y' ∧ ∃ fs',
        σ1.heap y' = some (.plain "Cbact04c$TranCatBalRecord" fs') ∧
        (∀ k ∈ keysTC, Fields.get fs' ("Cbact04c$TranCatBalRecord", k) =
          Fields.get fs ("Cbact04c$TranCatBalRecord", k)) ∧
        Grows σ σ1 ∧ σ1.inits = σ.inits ∧ σ1.statics = σ.statics) :
    J89 g g.args σ0 (((fr.setLocal 6 (.ref y)).setLocal 6 (v.getD .null)).setLocal 22
      (.int (i + 1#32))) σ1 := by
  obtain ⟨y', rfl, -, fs', hy1, hkeys, hg, hi, -⟩ := hpost y fsy rfl hyh
  have hL := Hide.elim hheap
  have hg0 : Grows σ0 σ := hL.1.1
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hrec' := Hide.elim hrec
  have hy0 : σ0.heap y = some (.plain "Cbact04c$TranCatBalRecord" fsy) := by
    obtain ⟨x, fs, hx, hxh, -⟩ := jrec_obj hrec'
    cases hx
    rw [← hg0.2 y (State.lt_next_of_heap hxh), hyh]
  refine ⟨i, hp, .ref y', acctV, xrefV, lastV, ⟨hn', hi0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (frame_simp [f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24, f12, f3, f14, f25,
        f16, f17, f4, f5, Option.getD_some]; done)
    | skip
  · exact Hide.intro (jrecAt_copy hrec' hy0 hy1 (same_keys tranCatBalRecord_jnames hkeys)
      (strKeep_of_grows (grows_trans hg0 hg)))
  · exact Hide.intro (loopHeap_grows hL hg hi)

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

/-- Record `i` copied into a fresh object (`copyTcb`'s functional contract): the cut point 90. -/
theorem j89_of_copyF {g : G} {σ0 σ σ1 : State} {fr : Frame} {i : I32} {hp : Hp}
    {acctV xrefV lastV : Value} {y w : Addr} {fsy fs' : List (FieldKey × Value)}
    (hn' : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr)
    (f12 : fr.get 12 = some (.long (BitVec.ofInt 64 (g.st i.toInt.toNat).total)))
    (f3 : fr.get 3 = some (.int (if (g.st i.toInt.toNat).lastId.isSome then 0#32 else 1#32)))
    (f14 : fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)))
    (f25 : fr.get 25 = some lastV) (f16 : fr.get 16 = some acctV) (f17 : fr.get 17 = some xrefV)
    (f4 : fr.get 4 = some (.int 0#32)) (f5 : fr.get 5 = some (.int 0#32))
    (hheap : Hide (LoopHeap g σ0 σ hp (g.st i.toInt.toNat) acctV xrefV lastV))
    (hrec : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ0 (.ref y)
      (g.trec i.toInt.toNat)))
    (hyh : σ.heap y = some (.plain "Cbact04c$TranCatBalRecord" fsy))
    (hw : σ1.heap w = some (.plain "Cbact04c$TranCatBalRecord" fs'))
    (hk : ∀ k ∈ keysTC, Fields.get fs' ("Cbact04c$TranCatBalRecord", k) =
      Fields.get (fieldsOf σ y) ("Cbact04c$TranCatBalRecord", k))
    (hg : Grows σ σ1) (hi : σ1.inits = σ.inits) :
    J89 g g.args σ0 (((fr.setLocal 6 (.ref y)).setLocal 6 (.ref w)).setLocal 22
      (.int (i + 1#32))) σ1 := by
  have hL := Hide.elim hheap
  have hg0 : Grows σ0 σ := hL.1.1
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hrec' := Hide.elim hrec
  have hy0 : σ0.heap y = some (.plain "Cbact04c$TranCatBalRecord" fsy) := by
    obtain ⟨x, fs, hx, hxh, -⟩ := jrec_obj hrec'
    cases hx
    rw [← hg0.2 y (State.lt_next_of_heap hxh), hyh]
  rw [fieldsOf_eq hyh] at hk
  refine ⟨i, hp, .ref w, acctV, xrefV, lastV, ⟨hn', hi0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (frame_simp [f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24, f12, f3, f14, f25,
        f16, f17, f4, f5]; done)
    | skip
  · exact Hide.intro (jrecAt_copy hrec' hy0 hw (same_keys tranCatBalRecord_jnames hk)
      (strKeep_of_grows (grows_trans hg0 hg)))
  · exact Hide.intro (loopHeap_grows hL hg hi)

end EquivLean.Modernize.Cbact04c.Java
