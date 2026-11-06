import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH5
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH4a
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH4b
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunS2
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunS1
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunR2b

/-!
# CBTRN02C → Java: the helper contracts as functions of the call state

For symbolic execution of a caller, a callee's postcondition is best a function of the state at
the call (`argText σ s`, `arrOf σ f`, `fieldsOf σ a`): it is then instantiated by the arguments
alone, whatever heap updates came before the call.  Each contract here follows from the proved
one (`sat_weaken`).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem sat_weaken {P : Program} {m : MethodRef} {S S' : Spec} (h : Sat P m S)
    (hpre : ∀ args σ, S'.pre args σ → S.pre args σ)
    (hpost : ∀ args σ o, S'.pre args σ → S.post args σ o → S'.post args σ o) : Sat P m S' :=
  fun args σ o hp hm => hpost args σ o hp (h args σ o (hpre args σ hp) hm)

theorem findIdx?_congr_mem {α : Type} {p q : α → Bool} :
    ∀ {xs : List α}, (∀ a ∈ xs, p a = q a) → xs.findIdx? p = xs.findIdx? q
  | [], _ => rfl
  | a :: xs, h => by
    rw [List.findIdx?_cons, List.findIdx?_cons, h a List.mem_cons_self,
      findIdx?_congr_mem (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem firstIdx_congr' {α : Type} {p q : α → Bool} {xs : List α} (h : ∀ a ∈ xs, p a = q a) :
    firstIdx p xs = firstIdx q xs := by
  unfold firstIdx; rw [findIdx?_congr_mem h]

theorem firstIdx_lt {α : Type} (p : α → Bool) (l : List α) : firstIdx p l < l.length := by
  unfold firstIdx
  cases h : l.findIdx? p with
  | none => simp only; omega
  | some i =>
    rw [List.findIdx?_eq_some_iff_getElem] at h
    obtain ⟨hi, -⟩ := h
    simp only; omega

theorem firstIdx_ge {α : Type} (p : α → Bool) (l : List α) : -1 ≤ firstIdx p l := by
  unfold firstIdx
  cases l.findIdx? p <;> simp <;> omega

/-- An index result as an `int`: its value is the index. -/
theorem toInt_ofInt_idx {j : Int} (h1 : -1 ≤ j) (h2 : j < 2147483648) :
    (BitVec.ofInt 32 j).toInt = j := by
  rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le] <;> omega

theorem longFieldOf_setObj {σ : State} {w x : Addr} {o : Obj} {k : FieldKey} (h : x ≠ w) :
    longFieldOf (σ.setObj w o) k (.ref x) = longFieldOf σ k (.ref x) := by
  simp only [longFieldOf, State.heap_setObj, if_neg h]

theorem firstIdx_longField_setObj {σ : State} {w : Addr} {o : Obj} {k : FieldKey} {key : I64}
    {xs : List Value} (h : ∀ v ∈ xs, v ≠ .ref w) :
    firstIdx (fun v => longFieldOf (σ.setObj w o) k v == some key) xs =
      firstIdx (fun v => longFieldOf σ k v == some key) xs := by
  apply firstIdx_congr' 
  intro v hv
  cases v with
  | ref x => rw [longFieldOf_setObj (fun e => h _ hv (by rw [e]))]
  | _ => rfl

/-- The text of a string value (`[]` otherwise). -/
def argText (σ : State) (v : Value) : JStr := (strOfV σ v).getD []

/-- The elements of the array at `a` (`[]` otherwise). -/
def arrOf (σ : State) (a : Addr) : List Value :=
  match σ.heap a with
  | some (.array _ xs) => xs
  | _ => []

/-- The elements of the list object at `l` (`[]` otherwise). -/
def listOf (σ : State) (l : Addr) : List Value :=
  match σ.heap l with
  | some (.list _ xs _) => xs
  | _ => []

/-- The fields of the object at `a` (`[]` otherwise). -/
def fieldsOf (σ : State) (a : Addr) : List (FieldKey × Value) :=
  match σ.heap a with
  | some (.plain _ fs) => fs
  | _ => []

/-- The address in the reference field `k` of the object at `a` (`0` otherwise). -/
def refField (σ : State) (a : Addr) (k : FieldKey) : Addr :=
  match Fields.get (fieldsOf σ a) k with
  | some (.ref x) => x
  | _ => 0

theorem refField_of {σ : State} {a x : Addr} {c : ClassName} {fs : List (FieldKey × Value)}
    {k : FieldKey} (h : σ.heap a = some (.plain c fs)) (hk : Fields.get fs k = some (.ref x)) :
    refField σ a k = x := by simp [refField, fieldsOf, h, hk]

theorem argText_of {σ : State} {s : Addr} {cs : JStr} (h : σ.heap s = some (.str cs)) :
    argText σ (.ref s) = cs := by simp [argText, strOfV, h]
theorem arrOf_of {σ : State} {a : Addr} {et : JType} {xs : List Value}
    (h : σ.heap a = some (.array et xs)) : arrOf σ a = xs := by simp [arrOf, h]
theorem listOf_of {σ : State} {l : Addr} {lk : ListKind} {xs : List Value} {m : Nat}
    (h : σ.heap l = some (.list lk xs m)) : listOf σ l = xs := by simp [listOf, h]
theorem fieldsOf_of {σ : State} {a : Addr} {c : ClassName} {fs : List (FieldKey × Value)}
    (h : σ.heap a = some (.plain c fs)) : fieldsOf σ a = fs := by simp [fieldsOf, h]

/-! ### `fit` -/

def fitSpecF : Spec := Spec.of
  (fun args σ => ∃ (s : Addr) (cs : JStr) (n : I32), args = [.ref s, .int n] ∧
     σ.heap s = some (.str cs) ∧ cs.length < 2147483648 ∧ 0 ≤ n.toInt ∧ n.toInt < 2147483647)
  (fun args σ r σ' => ∀ (s : Addr) (n : I32), args = [.ref s, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (fitJ (argText σ (.ref s)) n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

theorem fitF_sat : Sat Gen.prog fitRef fitSpecF := by
  refine sat_weaken fit_vc.sat (fun args σ h => h) ?_
  intro args σ o hp hpost
  obtain ⟨s0, cs, n0, hargs, hs, -⟩ := hp
  cases o with
  | normal v σ' =>
    intro s n he
    rw [hargs] at he
    simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨x, h1, h2, h3⟩ := hpost s0 cs n0 hargs hs
    exact ⟨x, h1, by rw [argText_of hs]; exact h2, h3⟩
  | exc e σ' => exact hpost
  | wrong m => exact hpost

/-! ### `db2Timestamp` -/

def db2TimestampSpecF : Spec := Spec.of
  db2TimestampSpec.pre
  (fun args σ r σ' => ∀ c : Addr, args = [.ref c] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (db2J (argText σ (.ref c)))) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧ σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

theorem db2TimestampF_sat : Sat Gen.prog db2TimestampRef db2TimestampSpecF := by
  refine sat_weaken (db2Timestamp_vc.sat) (fun args σ h => h) ?_
  intro args σ o hp hpost
  obtain ⟨c0, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18,
    x19, x20, hargs, hs⟩ := hp
  cases o with
  | normal v σ' =>
    intro c he
    rw [hargs] at he
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at he
    subst he
    obtain ⟨x, h1, h2, h3⟩ := hpost c0 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
      x17 x18 x19 x20 hargs hs
    exact ⟨x, h1, by rw [argText_of hs]; exact h2, h3⟩
  | exc e σ' => exact hpost
  | wrong m => exact hpost

/-! ### The searches -/

def findXrefSpecF : Spec := Spec.of
  findXrefSpec.pre
  (fun args σ r σ' => ∀ (f k : Addr), args = [.ref f, .ref k] →
     ∃ c : I32, r = some (.int c) ∧ c.toInt = firstIdx (fun v => strFieldOf σ xrefCardKey v == some (argText σ (.ref k))) (arrOf σ f) ∧
       firstIdx (fun v => strFieldOf σ xrefCardKey v == some (argText σ (.ref k))) (arrOf σ f) < (arrOf σ f).length ∧ σ' = σ)

theorem findXrefF_sat : Sat Gen.prog findXrefRef findXrefSpecF := by
  refine sat_weaken findXref_vc.sat (fun args σ h => h) ?_
  intro args σ o hp hpost
  obtain ⟨f0, k0, et, xs, kcs, hargs, hf, hlen, hk, -⟩ := hp
  cases o with
  | normal v σ' =>
    intro f k he
    rw [hargs] at he
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [arrOf_of hf, argText_of hk]
    obtain ⟨h1, h2⟩ := hpost f0 k0 et xs kcs hargs hf hk
    exact ⟨_, h1, toInt_ofInt_idx (firstIdx_ge _ _) (Int.lt_of_lt_of_le (firstIdx_lt _ _) (by omega)),
      firstIdx_lt _ _, h2⟩
  | exc e σ' => exact hpost
  | wrong m => exact hpost

def findAccountSpecF : Spec := Spec.of
  findAccountSpec.pre
  (fun args σ r σ' => ∀ (f : Addr) (key : I64), args = [.ref f, .long key] →
     ∃ c : I32, r = some (.int c) ∧ c.toInt = firstIdx (fun v => longFieldOf σ acctIdKey v == some key) (arrOf σ f) ∧
       firstIdx (fun v => longFieldOf σ acctIdKey v == some key) (arrOf σ f) < (arrOf σ f).length ∧ σ' = σ)

theorem findAccountF_sat : Sat Gen.prog findAccountRef findAccountSpecF := by
  refine sat_weaken findAccount_vc.sat (fun args σ h => h) ?_
  intro args σ o hp hpost
  obtain ⟨f0, k0, et, xs, hargs, hf, hlen, -⟩ := hp
  cases o with
  | normal v σ' =>
    intro f key he
    rw [hargs] at he
    simp only [List.cons.injEq, Value.ref.injEq, Value.long.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [arrOf_of hf]
    obtain ⟨h1, h2⟩ := hpost f0 k0 et xs hargs hf
    exact ⟨_, h1, toInt_ofInt_idx (firstIdx_ge _ _) (Int.lt_of_lt_of_le (firstIdx_lt _ _) (by omega)),
      firstIdx_lt _ _, h2⟩
  | exc e σ' => exact hpost
  | wrong m => exact hpost

def findTcatbalSpecF : Spec := Spec.of
  findTcatbalSpec.pre
  (fun args σ r σ' => ∀ (f : Addr) (acct : I64) (ty : Addr) (cd : I64), args = [.ref f, .long acct, .ref ty, .long cd] →
     ∃ c : I32, r = some (.int c) ∧ c.toInt = firstIdx (tcMatch σ acct (argText σ (.ref ty)) cd) (listOf σ f) ∧
       firstIdx (tcMatch σ acct (argText σ (.ref ty)) cd) (listOf σ f) < (listOf σ f).length ∧ σ' = σ)

theorem findTcatbalF_sat : Sat Gen.prog findTcatbalRef findTcatbalSpecF := by
  refine sat_weaken findTcatbal_vc.sat (fun args σ h => h) ?_
  intro args σ o hp hpost
  obtain ⟨f0, a0, t0, c0, lk, xs, m, tcs, hargs, hf, hlen, ht, -⟩ := hp
  cases o with
  | normal v σ' =>
    intro f acct ty cd he
    rw [hargs] at he
    simp only [List.cons.injEq, Value.ref.injEq, Value.long.injEq, and_true] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [listOf_of hf, argText_of ht]
    obtain ⟨h1, h2⟩ := hpost f0 a0 t0 c0 lk xs m tcs hargs hf ht
    exact ⟨_, h1, toInt_ofInt_idx (firstIdx_ge _ _) (Int.lt_of_lt_of_le (firstIdx_lt _ _) (by omega)),
      firstIdx_lt _ _, h2⟩
  | exc e σ' => exact hpost
  | wrong m => exact hpost

def findKeySpecF : Spec := Spec.of
  findKeySpec.pre
  (fun args σ r σ' => ∀ (f k : Addr), args = [.ref f, .ref k] →
     ∃ c : I32, r = some (.int c) ∧ c.toInt = firstIdx (fun v => strOfV σ v == some (argText σ (.ref k))) (listOf σ f) ∧
       firstIdx (fun v => strOfV σ v == some (argText σ (.ref k))) (listOf σ f) < (listOf σ f).length ∧ σ' = σ)

theorem findKeyF_sat : Sat Gen.prog findKeyRef findKeySpecF := by
  refine sat_weaken findKey_vc.sat (fun args σ h => h) ?_
  intro args σ o hp hpost
  obtain ⟨f0, k0, lk, xs, m, kcs, hargs, hf, hlen, hk, -⟩ := hp
  cases o with
  | normal v σ' =>
    intro f k he
    rw [hargs] at he
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [listOf_of hf, argText_of hk]
    obtain ⟨h1, h2⟩ := hpost f0 k0 lk xs m kcs hargs hf hk
    exact ⟨_, h1, toInt_ofInt_idx (firstIdx_ge _ _) (Int.lt_of_lt_of_le (firstIdx_lt _ _) (by omega)),
      firstIdx_lt _ _, h2⟩
  | exc e σ' => exact hpost
  | wrong m => exact hpost


/-! ### Copies -/

def copyTcatSpecF : Spec := Spec.of
  (fun args σ => ∃ (a : Addr) (fs : List (FieldKey × Value)), args = [.ref a] ∧
     σ.heap a = some (.plain "Cbtrn02c$TranCatBalRecord" fs) ∧ AllSome tcKeys fs ∧
     σ.initOf "Cbtrn02c$TranCatBalRecord" = .done)
  (fun args σ r σ' => ∀ a : Addr, args = [.ref a] →
     ∃ x fs', r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.plain "Cbtrn02c$TranCatBalRecord" fs') ∧
       SameFields tcKeys fs' (fieldsOf σ a) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧ σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

theorem copyTcatF_sat : Sat Gen.prog copyTcatRef copyTcatSpecF := by
  refine sat_weaken (MethodVC.sat_of_valid (fun _ _ h => by cases h) copyTcat_vc) (fun args σ h => h) ?_
  intro args σ o hp hpost
  obtain ⟨a0, fs, hargs, ha, -⟩ := hp
  cases o with
  | normal v σ' =>
    intro a he
    rw [hargs] at he
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at he
    subst he
    rw [fieldsOf_of ha]
    exact hpost a0 fs hargs ha
  | exc e σ' => exact hpost
  | wrong m => exact hpost

def copyAccountSpecF : Spec := Spec.of
  (fun args σ => ∃ (a : Addr) (fs : List (FieldKey × Value)), args = [.ref a] ∧
     σ.heap a = some (.plain "Cbtrn02c$AccountRecord" fs) ∧ AllSome acKeys fs ∧
     σ.initOf "Cbtrn02c$AccountRecord" = .done)
  (fun args σ r σ' => ∀ a : Addr, args = [.ref a] →
     ∃ x fs', r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.plain "Cbtrn02c$AccountRecord" fs') ∧
       SameFields acKeys fs' (fieldsOf σ a) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧ σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

theorem copyAccountF_sat : Sat Gen.prog copyAccountRef copyAccountSpecF := by
  refine sat_weaken (MethodVC.sat_of_valid copyAccountC_valid copyAccount_vc) (fun args σ h => h) ?_
  intro args σ o hp hpost
  obtain ⟨a0, fs, hargs, ha, -⟩ := hp
  cases o with
  | normal v σ' =>
    intro a he
    rw [hargs] at he
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at he
    subst he
    rw [fieldsOf_of ha]
    exact hpost a0 fs hargs ha
  | exc e σ' => exact hpost
  | wrong m => exact hpost

def copyTranSpecF : Spec := Spec.of
  (fun args σ => ∃ (a : Addr) (fs : List (FieldKey × Value)), args = [.ref a] ∧
     σ.heap a = some (.plain "Cbtrn02c$TranRecord" fs) ∧ AllSome trKeys fs ∧
     σ.initOf "Cbtrn02c$TranRecord" = .done)
  (fun args σ r σ' => ∀ a : Addr, args = [.ref a] →
     ∃ x fs', r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.plain "Cbtrn02c$TranRecord" fs') ∧
       SameFields trKeys fs' (fieldsOf σ a) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧ σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

theorem copyTranF_sat : Sat Gen.prog copyTranRef copyTranSpecF := by
  refine sat_weaken (MethodVC.sat_of_valid copyTranC_valid copyTran_vc) (fun args σ h => h) ?_
  intro args σ o hp hpost
  obtain ⟨a0, fs, hargs, ha, -⟩ := hp
  cases o with
  | normal v σ' =>
    intro a he
    rw [hargs] at he
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at he
    subst he
    rw [fieldsOf_of ha]
    exact hpost a0 fs hargs ha
  | exc e σ' => exact hpost
  | wrong m => exact hpost

def assignTcatSpecF : Spec := Spec.of
  (fun args σ => ∃ (d s : Addr) (fsd fss : List (FieldKey × Value)), args = [.ref d, .ref s] ∧
     d ≠ s ∧ σ.heap d = some (.plain "Cbtrn02c$TranCatBalRecord" fsd) ∧ σ.heap s = some (.plain "Cbtrn02c$TranCatBalRecord" fss) ∧
     AllSome tcKeys fsd ∧ AllSome tcKeys fss)
  (fun args σ r σ' => ∀ d s : Addr, args = [.ref d, .ref s] →
     ∃ fs', σ' = σ.setObj d (.plain "Cbtrn02c$TranCatBalRecord" fs') ∧
       ∀ k ∈ tcKeys, Fields.get fs' k = Fields.get (fieldsOf σ s) k)

theorem assignTcatF_sat : Sat Gen.prog assignTcatRef assignTcatSpecF := by
  refine sat_weaken assignTcat_vc.sat (fun args σ h => h) ?_
  intro args σ o hp hpost
  obtain ⟨d0, s0, fsd, fss, hargs, -, hd, hs, -⟩ := hp
  cases o with
  | normal v σ' =>
    intro d s he
    rw [hargs] at he
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [fieldsOf_of hs]
    exact hpost d0 s0 fsd fss hargs hd hs
  | exc e σ' => exact hpost
  | wrong m => exact hpost

def assignAccountSpecF : Spec := Spec.of
  (fun args σ => ∃ (d s : Addr) (fsd fss : List (FieldKey × Value)), args = [.ref d, .ref s] ∧
     d ≠ s ∧ σ.heap d = some (.plain "Cbtrn02c$AccountRecord" fsd) ∧ σ.heap s = some (.plain "Cbtrn02c$AccountRecord" fss) ∧
     AllSome acKeys fsd ∧ AllSome acKeys fss)
  (fun args σ r σ' => ∀ d s : Addr, args = [.ref d, .ref s] →
     ∃ fs', σ' = σ.setObj d (.plain "Cbtrn02c$AccountRecord" fs') ∧
       ∀ k ∈ acKeys, Fields.get fs' k = Fields.get (fieldsOf σ s) k)

theorem assignAccountF_sat : Sat Gen.prog assignAccountRef assignAccountSpecF := by
  refine sat_weaken assignAccount_vc.sat (fun args σ h => h) ?_
  intro args σ o hp hpost
  obtain ⟨d0, s0, fsd, fss, hargs, -, hd, hs, -⟩ := hp
  cases o with
  | normal v σ' =>
    intro d s he
    rw [hargs] at he
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [fieldsOf_of hs]
    exact hpost d0 s0 fsd fss hargs hd hs
  | exc e σ' => exact hpost
  | wrong m => exact hpost

def assignXrefSpecF : Spec := Spec.of
  (fun args σ => ∃ (d s : Addr) (fsd fss : List (FieldKey × Value)), args = [.ref d, .ref s] ∧
     d ≠ s ∧ σ.heap d = some (.plain "Cbtrn02c$CardXrefRecord" fsd) ∧ σ.heap s = some (.plain "Cbtrn02c$CardXrefRecord" fss) ∧
     AllSome xrKeys fsd ∧ AllSome xrKeys fss)
  (fun args σ r σ' => ∀ d s : Addr, args = [.ref d, .ref s] →
     ∃ fs', σ' = σ.setObj d (.plain "Cbtrn02c$CardXrefRecord" fs') ∧
       ∀ k ∈ xrKeys, Fields.get fs' k = Fields.get (fieldsOf σ s) k)

theorem assignXrefF_sat : Sat Gen.prog assignXrefRef assignXrefSpecF := by
  refine sat_weaken assignXref_vc.sat (fun args σ h => h) ?_
  intro args σ o hp hpost
  obtain ⟨d0, s0, fsd, fss, hargs, -, hd, hs, -⟩ := hp
  cases o with
  | normal v σ' =>
    intro d s he
    rw [hargs] at he
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [fieldsOf_of hs]
    exact hpost d0 s0 fsd fss hargs hd hs
  | exc e σ' => exact hpost
  | wrong m => exact hpost

/-! ### `compareEbcdic` -/

/-- The CP037 table as UTF-16 units. -/
def cp037Tab : JStr := (List.range 256).map fun k => cp037Unit (UInt8.ofNat k)

/-- The EBCDIC bytes of a CP037 text. -/
def decJ (cs : JStr) : List UInt8 := cs.map fun u => UInt8.ofNat (cp037Tab.idxOf u)

set_option maxRecDepth 100000 in
theorem decJ_unit_nat : ∀ k, k < 256 →
    UInt8.ofNat (cp037Tab.idxOf (cp037Unit (UInt8.ofNat k))) = UInt8.ofNat k := by decide

theorem decJ_unit (b : UInt8) : UInt8.ofNat (cp037Tab.idxOf (cp037Unit b)) = b := by
  have h := decJ_unit_nat b.toNat b.toNat_lt
  rwa [UInt8.ofNat_toNat] at h

theorem decJ_cp037 (bs : List UInt8) : decJ (cp037Str bs) = bs := by
  simp only [decJ, cp037Str, List.map_map]
  conv => rhs; rw [← List.map_id bs]
  apply List.map_congr_left
  intro b _
  exact decJ_unit b

def compareEbcdicSpecF : Spec := Spec.of
  compareEbcdicSpec.pre
  (fun args σ r σ' => Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
     σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c" ∧ ∀ a b : Addr, args = [.ref a, .ref b] →
     r = some (.int (cmpJ (Cobol.Sem.cmpBytes (decJ (argText σ (.ref a))) (decJ (argText σ (.ref b)))))))

theorem compareEbcdicF_sat (h : Sat Gen.prog compareEbcdicRef compareEbcdicSpec) :
    Sat Gen.prog compareEbcdicRef compareEbcdicSpecF := by
  refine sat_weaken h (fun args σ h => h) ?_
  intro args σ o hp hpost
  obtain ⟨a0, b0, xs, ys, hargs, ha, hb, -⟩ := hp
  cases o with
  | normal v σ' =>
    obtain ⟨h1, h2, h3, h4, c, hc, hpc⟩ := hpost
    refine ⟨h1, h2, h3, h4, ?_⟩
    intro a b he
    rw [hargs] at he
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [argText_of ha, argText_of hb, decJ_cp037, decJ_cp037, hc, hpc a0 b0 xs ys hargs ha hb]
  | exc e σ' => exact hpost
  | wrong m => exact hpost

end EquivLean.Modernize.Cbtrn02c.Java
