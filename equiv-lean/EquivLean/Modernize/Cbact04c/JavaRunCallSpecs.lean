import EquivLean.Modernize.Cbact04c.JavaRunHelpers3
import EquivLean.Modernize.Cbact04c.JavaRunHelpers4
import EquivLean.Modernize.Cbact04c.JavaRunCopySpecs

/-!
# CBACT04C → Java: the callee contracts as `run` uses them

At a call, `jvc` instantiates a postcondition whose universals are fixed by the arguments
(`∀ x, args = [.ref x] → …`) and whose results are functions of the entry state. These contracts
follow from the ones proved in `Helpers*`/`CopyProofs` by the consequence rule `sat_conseq`:
* `copyF cls keys`: the copy holds, in `keys`, the field values of the object at `x`
  (`fieldsOf σ x`);
* `displayTcbF`: the line is `tcbLineOf σ x`, read from the record object at `x`.
-/

open Jimple

namespace EquivLean.Modernize.Cbact04c.Java

/-- The consequence rule for contracts. -/
theorem sat_conseq {P : Program} {m : MethodRef} {S S' : Spec} (h : Sat P m S)
    (hpre : ∀ args σ, S'.pre args σ → S.pre args σ)
    (hpost : ∀ args σ o, S'.pre args σ → S.post args σ o → S'.post args σ o) : Sat P m S' :=
  fun args σ o hp hm => hpost args σ o hp (h args σ o (hpre args σ hp) hm)

/-- The fields of the object at `x`. -/
def fieldsOf (σ : State) (x : Addr) : List (FieldKey × Value) :=
  match σ.heap x with
  | some (.plain _ fs) => fs
  | _ => []

theorem fieldsOf_eq {σ : State} {x : Addr} {cls : ClassName} {fs : List (FieldKey × Value)}
    (h : σ.heap x = some (.plain cls fs)) : fieldsOf σ x = fs := by
  simp [fieldsOf, h]

/-! ## Copies -/

/-- A copy of the object at `x` (class `cls`, fields `keys`). -/
def copyF (cls : ClassName) (keys : List String) : Spec := Spec.of
  (fun args σ => ∃ x fs, args = [.ref x] ∧ σ.heap x = some (.plain cls fs) ∧
     (∀ k ∈ keys, ∃ v, Fields.get fs (cls, k) = some v) ∧ σ.initOf cls = .done)
  (fun args σ r σ' => ∀ x, args = [.ref x] →
     ∃ y fs', r = some (.ref y) ∧ σ.next ≤ y ∧ σ'.heap y = some (.plain cls fs') ∧
       (∀ k ∈ keys, Fields.get fs' (cls, k) = Fields.get (fieldsOf σ x) (cls, k)) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

theorem copyF_of_sat {m : MethodRef} {cls : ClassName} {keys : List String}
    (h : Sat Gen.prog m (copySpec cls keys)) : Sat Gen.prog m (copyF cls keys) := by
  refine sat_conseq h (fun args σ hp => hp) ?_
  intro args σ o hp hpost
  obtain ⟨x, fs, rfl, hx, -⟩ := hp
  cases o with
  | normal r σ' =>
    intro x' hx'
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hx'
    subst hx'
    obtain ⟨y, fs', h1, h2, h3, h4, h5⟩ := hpost x fs rfl hx
    exact ⟨y, fs', h1, h2, h3, by rw [fieldsOf_eq hx]; exact h4, h5⟩
  | exc e σ' => exact hpost
  | wrong msg => exact hpost

/-! ## `displayTcb` -/

/-- The line `displayTcb` builds for the record object at `x`. -/
def tcbLineOf (σ : State) (x : Addr) : JStr :=
  match Fields.get (fieldsOf σ x) ("Cbact04c$TranCatBalRecord", "trancatAcctId"),
    Fields.get (fieldsOf σ x) ("Cbact04c$TranCatBalRecord", "trancatTypeCd"),
    Fields.get (fieldsOf σ x) ("Cbact04c$TranCatBalRecord", "trancatCd"),
    Fields.get (fieldsOf σ x) ("Cbact04c$TranCatBalRecord", "tranCatBal"),
    Fields.get (fieldsOf σ x) ("Cbact04c$TranCatBalRecord", "filler1") with
  | some (.long a), some (.ref tv), some (.long c), some (.long b), some (.ref fv) =>
    match σ.heap tv, σ.heap fv with
    | some (.str ty), some (.str f) => tcbLine a ty c b f
    | _, _ => []
  | _, _, _, _, _ => []

theorem tcbLineOf_eq {σ : State} {x : Addr} {fs : List (FieldKey × Value)} {a c b : I64}
    {tv fv : Addr} {ty f : JStr} (hx : σ.heap x = some (.plain "Cbact04c$TranCatBalRecord" fs))
    (ha : Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatAcctId") = some (.long a))
    (htv : Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatTypeCd") = some (.ref tv))
    (hty : σ.heap tv = some (.str ty))
    (hc : Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatCd") = some (.long c))
    (hb : Fields.get fs ("Cbact04c$TranCatBalRecord", "tranCatBal") = some (.long b))
    (hfv : Fields.get fs ("Cbact04c$TranCatBalRecord", "filler1") = some (.ref fv))
    (hf : σ.heap fv = some (.str f)) : tcbLineOf σ x = tcbLine a ty c b f := by
  simp only [tcbLineOf, fieldsOf_eq hx, ha, htv, hc, hb, hfv, hty, hf]

/-- `displayTcb`'s contract as `run` uses it. -/
def displayTcbF : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (fs : List (FieldKey × Value)) (a c b : I64) (tv fv : Addr)
       (ty f : JStr), args = [.ref x] ∧
     σ.heap x = some (.plain "Cbact04c$TranCatBalRecord" fs) ∧
     Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatAcctId") = some (.long a) ∧
     Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatTypeCd") = some (.ref tv) ∧
     σ.heap tv = some (.str ty) ∧
     Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatCd") = some (.long c) ∧
     Fields.get fs ("Cbact04c$TranCatBalRecord", "tranCatBal") = some (.long b) ∧
     Fields.get fs ("Cbact04c$TranCatBalRecord", "filler1") = some (.ref fv) ∧
     σ.heap fv = some (.str f) ∧
     -9223372036854775808 < a.toInt ∧ -9223372036854775808 < c.toInt ∧
     -9223372036854775808 < b.toInt ∧ σ.initOf "Cbact04c" = .done)
  (fun args σ r σ' => ∀ x, args = [.ref x] →
     ∃ y, r = some (.ref y) ∧ σ'.heap y = some (.str (tcbLineOf σ x)) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

theorem displayTcbF_of_sat (h : Sat Gen.prog displayTcbRef displayTcbSpec) :
    Sat Gen.prog displayTcbRef displayTcbF := by
  refine sat_conseq h (fun args σ hp => hp) ?_
  intro args σ o hp hpost
  obtain ⟨x, fs, a, c, b, tv, fv, ty, f, rfl, hx, ha, htv, hty, hc, hb, hfv, hf, -⟩ := hp
  cases o with
  | normal r σ' =>
    intro x' hx'
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hx'
    subst hx'
    obtain ⟨y, h1, h2, h3⟩ := hpost x fs a c b tv fv ty f rfl hx ha htv hty hc hb hfv hf
    exact ⟨y, h1, by rw [tcbLineOf_eq hx ha htv hty hc hb hfv hf]; exact h2, h3⟩
  | exc e σ' => exact hpost
  | wrong msg => exact hpost

/-! ## The searches -/

/-- The index `findAcct` returns: the first account object in the array at `a` with id `key`. -/
def acctIdx (σ : State) (a : Addr) (key : I64) : I32 :=
  match σ.heap a with
  | some (.array _ xs) =>
    match xs.findIdx? (fun x => decide (acctIdOf σ x = some key)) with
    | some i => BitVec.ofNat 32 i
    | none => -1
  | _ => -1

/-- `findAcct`'s contract as `run` uses it. -/
def findAcctF : Spec := Spec.of
  (fun args σ => ∃ a key et xs, findAcctPreG a key et xs args σ)
  (fun args σ r σ' => ∀ a key, args = [.ref a, .long key] →
     r = some (.int (acctIdx σ a key)) ∧ σ' = σ)

/-- A first match found by a search loop is `findIdx?`. -/
theorem findIdx?_of_first {α : Type} {p : α → Bool} {xs : List α} {i : Nat} (hi : i < xs.length)
    (hp : p xs[i] = true) (hprev : ∀ x ∈ xs.take i, p x = false) : xs.findIdx? p = some i := by
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hi, hp, fun j hj => ?_⟩
  have hm : xs[j] ∈ xs.take i := by
    rw [List.mem_iff_getElem]
    exact ⟨j, by simp; omega, by simp⟩
  simp [hprev _ hm]

theorem findAcctF_of_sat (h : Sat Gen.prog findAcctRef findAcctSpec) :
    Sat Gen.prog findAcctRef findAcctF := by
  refine sat_conseq h (fun args σ hp => hp) ?_
  intro args σ o hp hpost
  obtain ⟨a, key, et, xs, rfl, hx, -, -, -⟩ := hp
  cases o with
  | normal r σ' =>
    intro a' key' hargs
    simp only [List.cons.injEq, Value.ref.injEq, Value.long.injEq, and_true] at hargs
    obtain ⟨rfl, rfl⟩ := hargs
    obtain ⟨i, rfl, hi0, hilen, hfound, hprev, rfl⟩ := hpost a key et xs rfl hx
    refine ⟨?_, rfl⟩
    have hit : i.toNat < xs.length := by
      rw [i32_toNat_eq i hi0]; omega
    have hfi : xs.findIdx? (fun x => decide (acctIdOf σ' x = some key)) = some i.toNat := by
      refine findIdx?_of_first hit ?_ ?_
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hit, Option.getD_some] at hfound
        simp [hfound]
      · intro x hxm
        simp [hprev x hxm]
    simp only [acctIdx, hx, hfi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  | exc e σ' => exact hpost
  | wrong msg => exact hpost

/-- The index `findDisc` returns: the first disclosure-group object in the array at `a` with the
key (group at `gs`, type at `ts`, category `cat`). -/
def discIdx (σ : State) (a gs ts : Addr) (cat : I64) : I32 :=
  match σ.heap a, σ.heap gs, σ.heap ts with
  | some (.array _ xs), some (.str g), some (.str t) =>
    match xs.findIdx? (fun x => decide (discKeyOf σ x = some (g, t, cat))) with
    | some i => BitVec.ofNat 32 i
    | none => -1
  | _, _, _ => -1

/-- `findDisc`'s contract as `run` uses it. -/
def findDiscF : Spec := Spec.of
  (fun args σ => ∃ a len gs ts g t cat et xs, findDiscPreG a len gs ts g t cat et xs args σ)
  (fun args σ r σ' => ∀ a len gs ts cat, args = [.ref a, .int len, .ref gs, .ref ts, .long cat] →
     r = some (.int (discIdx σ a gs ts cat)) ∧ σ' = σ)

theorem findDiscF_of_sat (h : Sat Gen.prog findDiscRef findDiscSpec) :
    Sat Gen.prog findDiscRef findDiscF := by
  refine sat_conseq h (fun args σ hp => hp) ?_
  intro args σ o hp hpost
  obtain ⟨a, len, gs, ts, g, t, cat, et, xs, rfl, hx, -, -, hgs, hts, -, -⟩ := hp
  cases o with
  | normal r σ' =>
    intro a' len' gs' ts' cat' hargs
    simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, Value.long.injEq,
      and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
    obtain ⟨i, rfl, hi0, hilen, hfound, hprev, rfl⟩ := hpost a len gs ts g t cat et xs rfl hx hgs hts
    refine ⟨?_, rfl⟩
    have hit : i.toNat < xs.length := by
      rw [i32_toNat_eq i hi0]; omega
    have hfi : xs.findIdx? (fun x => decide (discKeyOf σ' x = some (g, t, cat))) = some i.toNat := by
      refine findIdx?_of_first hit ?_ ?_
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hit, Option.getD_some] at hfound
        simp [hfound]
      · intro x hxm
        simp [hprev x hxm]
    simp only [discIdx, hx, hgs, hts, hfi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  | exc e σ' => exact hpost
  | wrong msg => exact hpost

/-! ### `fixLen`: the result is the argument string -/

/-- The address an argument list starts with (its first reference). -/
def argAddr : List Value → Addr
  | .ref x :: _ => x
  | _ => 0

/-- `fixLen`'s contract as `run` uses it: the result string is the (fixed-length) argument. -/
def fixLenF : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (n : I32) (s : JStr), args = [.ref x, .int n] ∧
     σ.heap x = some (.str s) ∧ s.length = n.toInt.toNat ∧ 0 ≤ n.toInt ∧ n.toInt ≤ 1000)
  (fun args σ r σ' => ∃ y, r = some (.ref y) ∧ σ'.heap y = σ.heap (argAddr args) ∧ Grows σ σ' ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

theorem fixLenF_of_sat {m : MethodRef} (h : Sat Gen.prog m fixLenSpec) : Sat Gen.prog m fixLenF := by
  refine sat_conseq h (fun args σ hp => hp) ?_
  intro args σ o hp hpost
  obtain ⟨x, n, s, rfl, hx, -⟩ := hp
  cases o with
  | normal r σ' =>
    obtain ⟨y, h1, h2, h3, h4, h5⟩ := hpost x n s rfl hx
    exact ⟨y, h1, by rw [h2]; exact hx.symm, h3, h4, h5⟩
  | exc e σ' => exact hpost
  | wrong msg => exact hpost

end EquivLean.Modernize.Cbact04c.Java
