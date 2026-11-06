import EquivLean.Modernize.Cbact04c.Every.JavaRunHelpers2

/-!
# CBACT04C → Java: the searches `findAcct`, `findDisc` and the record copies
-/

open Jimple

-- (JimpleLean 1546Z) key comparisons (`lcmp`) split two ways, by `jlong_cmp_eq_zero_iff`, not three
attribute [-jsimp] JLong.cmp_eq

namespace EquivLean.Modernize.Cbact04c.Java


theorem jlong_cmp_eq_zero_iff (a b : I64) : JLong.cmp a b = 0#32 ↔ a = b := by
  unfold JLong.cmp
  by_cases h1 : a.slt b
  · have hne : a ≠ b := by
      intro h; subst h; simp [BitVec.slt, Int.lt_irrefl] at h1
    simp only [h1, ite_true, hne, iff_false]
    decide
  · simp only [h1]
    by_cases h2 : a = b
    · simp [h2]
    · simp only [h2, ite_false, iff_false]; decide

theorem mem_take_succ {α : Type} {xs : List α} {n : Nat} (hn : n < xs.length) {x : α}
    (h : x ∈ xs.take (n + 1)) : x ∈ xs.take n ∨ x = xs[n] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hn] at h
  rcases List.mem_append.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa using h)

theorem i32_toInt_add_one (i : I32) (h0 : 0 ≤ i.toInt) (h1 : i.toInt < 2147483647) :
    (i + 1#32).toInt = i.toInt + 1 := by
  rw [BitVec.toInt_add]
  have : (1#32).toInt = 1 := by decide
  rw [this]
  rw [Int.bmod_def]; split <;> omega

theorem i32_toNat_eq (i : I32) (h0 : 0 ≤ i.toInt) : i.toNat = i.toInt.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at *
  split at h0 <;> omega

theorem i32_toNat_add_one (i : I32) (h0 : 0 ≤ i.toInt) (h1 : i.toInt < 2147483647) :
    (i + 1#32).toNat = i.toNat + 1 := by
  have h2 := i32_toInt_add_one i h0 h1
  rw [i32_toNat_eq i h0, i32_toNat_eq (i + 1#32) (by omega), h2]
  omega

/-! ## `findAcct` -/

/-- The `acctId` of the account object `v`. -/
def acctIdOf (σ : State) (v : Value) : Option I64 :=
  match v with
  | .ref a => match σ.heap a with
    | some (.plain _ fs) => match Fields.get fs ("Cbact04c$AccountRecord", "acctId") with
      | some (.long n) => some n
      | _ => none
    | _ => none
  | _ => none

abbrev findAcctRef : MethodRef := Gen.Cbact04c.«findAcct(Cbact04c$AccountRecord[],long)».ref

theorem acctIdOf_ref {σ : State} {x : Addr} {fs : List (FieldKey × Value)} {n : I64}
    (h1 : σ.heap x = some (.plain "Cbact04c$AccountRecord" fs)) (h2 : Fields.get fs ("Cbact04c$AccountRecord", "acctId") = some (.long n)) :
    acctIdOf σ (.ref x) = some n := by
  simp [acctIdOf, h1, h2]

/-- The accounts array as `findAcct` reads it. -/
def AcctArr (σ : State) (xs : List Value) : Prop :=
  ∀ x ∈ xs, ∃ y fs n, x = .ref y ∧ σ.heap y = some (.plain "Cbact04c$AccountRecord" fs) ∧
    Fields.get fs ("Cbact04c$AccountRecord", "acctId") = some (.long n)

def findAcctPreG (a : Addr) (key : I64) (et : JType) (xs : List Value) (args : List Value)
    (σ : State) : Prop :=
  args = [.ref a, .long key] ∧ σ.heap a = some (.array et xs) ∧ xs.length < 2147483648 ∧
  AcctArr σ xs

def findAcctPostG (key : I64) (xs : List Value) (σ : State) (r : Option Value) (σ' : State) : Prop :=
  (∃ i : I32, r = some (.int i) ∧ 0 ≤ i.toInt ∧ i.toInt < xs.length ∧
    acctIdOf σ (xs.getD i.toNat .null) = some key ∧
    (∀ x ∈ xs.take i.toNat, acctIdOf σ x ≠ some key) ∧ σ' = σ) ∨
  (r = some (.int (-1#32)) ∧ (∀ x ∈ xs, acctIdOf σ x ≠ some key) ∧ σ' = σ)

def findAcctSpecG (a : Addr) (key : I64) (et : JType) (xs : List Value) : Spec :=
  Spec.of (findAcctPreG a key et xs) (fun _ σ r σ' => findAcctPostG key xs σ r σ')

def findAcctInv3 (a : Addr) (key : I64) (xs : List Value) (_args : List Value) (σ0 : State)
    (fr : Frame) (σ : State) : Prop :=
  ∃ i : I32, fr.get 6 = some (.ref a) ∧ fr.get 3 = some (.long key) ∧ fr.get 2 = some (.int i) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧ (∀ x ∈ xs.take i.toNat, acctIdOf σ0 x ≠ some key) ∧
    σ = σ0

def findAcctInv (a : Addr) (key : I64) (xs : List Value) : Invariants :=
  [(3, findAcctInv3 a key xs)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem findAcct_vc (a : Addr) (key : I64) (et : JType) (xs : List Value) :
    MethodVC Gen.prog (fun _ => none) 0 findAcctRef (findAcctSpecG a key et xs)
      (findAcctInv a key xs) 20 := by
  refine ⟨_, rfl, ?_⟩
  intro args σ0 hpre
  simp only [findAcctInv, Invariants.inst, List.map_cons, List.map_nil, List.lookup,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [findAcctSpecG, Spec.of, findAcctPreG] at hpre
  obtain ⟨rfl, hheap, hlen, hall⟩ := hpre
  refine ⟨?_, ?_⟩
  · jvc [findAcctSpecG, findAcctPostG]
    refine ⟨0#32, ?_⟩
    simp [Frame.get_setLocal]
  · intro fr σ h
    obtain ⟨i, h6, h3, h2, hi0, hilen, htake, rfl⟩ := h
    by_cases hc : (xs.length : Int) ≤ i.toInt
    · have hi : i.toNat = xs.length := by rw [i32_toNat_eq i hi0]; omega
      rw [hi, List.take_length] at htake
      jvc [findAcctSpecG, findAcctPostG, jlong_cmp_eq_zero_iff]
    · have hn : i.toInt.toNat < xs.length := by omega
      obtain ⟨y, fs, n, hyeq, hyheap, hfid⟩ := hall xs[i.toInt.toNat] (List.getElem_mem hn)
      have hget : xs[i.toInt.toNat]? = some (.ref y) := by rw [List.getElem?_eq_getElem hn, hyeq]
      have hyid : acctIdOf σ (.ref y) = some n := acctIdOf_ref hyheap hfid
      clear hall
      jvc [findAcctSpecG, findAcctPostG, jlong_cmp_eq_zero_iff]
      -- the next iteration (the found case is closed by `jvc`)
      have hlt : i.toInt < 2147483647 := by omega
      refine ⟨i + 1#32, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
      · simp [Frame.get_setLocal, h6]
      · simp [Frame.get_setLocal, h3]
      · simp [Frame.get_setLocal]
      · rw [i32_toInt_add_one i hi0 hlt]; omega
      · rw [i32_toInt_add_one i hi0 hlt]; omega
      · rw [i32_toNat_add_one i hi0 hlt]
        intro z hz
        simp only [i32_toNat_eq i hi0] at htake hz
        rcases mem_take_succ hn hz with hz | hz
        · exact htake z hz
        · rw [hz, hyeq, hyid]; simpa using hcond

/-! ## `findDisc` -/

/-- The key (group, type, category) of the disclosure-group object `v`. -/
def discKeyOf (σ : State) (v : Value) : Option (JStr × JStr × I64) :=
  match v with
  | .ref a => match σ.heap a with
    | some (.plain _ fs) =>
      match Fields.get fs ("Cbact04c$DisGroupRecord", "disAcctGroupId"),
        Fields.get fs ("Cbact04c$DisGroupRecord", "disTranTypeCd"),
        Fields.get fs ("Cbact04c$DisGroupRecord", "disTranCatCd") with
      | some gv, some tv, some (.long c) =>
        match strOf σ gv, strOf σ tv with
        | some g, some t => some (g, t, c)
        | _, _ => none
      | _, _, _ => none
    | _ => none
  | _ => none

/-- The disclosure-group array as `findDisc` reads it. -/
def DiscArr (σ : State) (xs : List Value) : Prop :=
  ∀ x ∈ xs, ∃ y fs gv tv g t c, x = .ref y ∧ σ.heap y = some (.plain "Cbact04c$DisGroupRecord" fs) ∧
    Fields.get fs ("Cbact04c$DisGroupRecord", "disAcctGroupId") = some (.ref gv) ∧
    σ.heap gv = some (.str g) ∧
    Fields.get fs ("Cbact04c$DisGroupRecord", "disTranTypeCd") = some (.ref tv) ∧
    σ.heap tv = some (.str t) ∧
    Fields.get fs ("Cbact04c$DisGroupRecord", "disTranCatCd") = some (.long c)

theorem discKeyOf_ref {σ : State} {y gv tv : Addr} {fs : List (FieldKey × Value)} {g t : JStr}
    {c : I64} (h1 : σ.heap y = some (.plain "Cbact04c$DisGroupRecord" fs))
    (h2 : Fields.get fs ("Cbact04c$DisGroupRecord", "disAcctGroupId") = some (.ref gv))
    (h3 : σ.heap gv = some (.str g))
    (h4 : Fields.get fs ("Cbact04c$DisGroupRecord", "disTranTypeCd") = some (.ref tv))
    (h5 : σ.heap tv = some (.str t))
    (h6 : Fields.get fs ("Cbact04c$DisGroupRecord", "disTranCatCd") = some (.long c)) :
    discKeyOf σ (.ref y) = some (g, t, c) := by
  simp [discKeyOf, h1, h2, h3, h4, h5, h6, strOf]

abbrev findDiscRef : MethodRef :=
  Gen.Cbact04c.«findDisc(Cbact04c$DisGroupRecord[],int,java.lang.String,java.lang.String,long)».ref

def findDiscPreG (a : Addr) (len : I32) (gs ts : Addr) (g t : JStr) (cat : I64) (et : JType)
    (xs : List Value) (args : List Value) (σ : State) : Prop :=
  args = [.ref a, .int len, .ref gs, .ref ts, .long cat] ∧ σ.heap a = some (.array et xs) ∧
  len.toInt = xs.length ∧ xs.length < 2147483648 ∧ σ.heap gs = some (.str g) ∧
  σ.heap ts = some (.str t) ∧ DiscArr σ xs

def findDiscPostG (g t : JStr) (cat : I64) (xs : List Value) (σ : State) (r : Option Value)
    (σ' : State) : Prop :=
  (∃ i : I32, r = some (.int i) ∧ 0 ≤ i.toInt ∧ i.toInt < xs.length ∧
    discKeyOf σ (xs.getD i.toNat .null) = some (g, t, cat) ∧
    (∀ x ∈ xs.take i.toNat, discKeyOf σ x ≠ some (g, t, cat)) ∧ σ' = σ) ∨
  (r = some (.int (-1#32)) ∧ (∀ x ∈ xs, discKeyOf σ x ≠ some (g, t, cat)) ∧ σ' = σ)

def findDiscSpecG (a : Addr) (len : I32) (gs ts : Addr) (g t : JStr) (cat : I64) (et : JType)
    (xs : List Value) : Spec :=
  Spec.of (findDiscPreG a len gs ts g t cat et xs) (fun _ σ r σ' => findDiscPostG g t cat xs σ r σ')

def findDiscInv6 (a : Addr) (len : I32) (gs ts : Addr) (g t : JStr) (cat : I64) (xs : List Value)
    (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ i : I32, fr.get 3 = some (.ref a) ∧ fr.get 5 = some (.int len) ∧ fr.get 7 = some (.ref gs) ∧
    fr.get 8 = some (.ref ts) ∧ fr.get 1 = some (.long cat) ∧ fr.get 6 = some (.int i) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧ (∀ x ∈ xs.take i.toNat, discKeyOf σ0 x ≠ some (g, t, cat)) ∧
    σ = σ0

def findDiscInv (a : Addr) (len : I32) (gs ts : Addr) (g t : JStr) (cat : I64) (xs : List Value) :
    Invariants :=
  [(6, findDiscInv6 a len gs ts g t cat xs)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem findDisc_vc (a : Addr) (len : I32) (gs ts : Addr) (g t : JStr) (cat : I64) (et : JType)
    (xs : List Value) :
    MethodVC Gen.prog (fun _ => none) 0 findDiscRef (findDiscSpecG a len gs ts g t cat et xs)
      (findDiscInv a len gs ts g t cat xs) 30 := by
  refine ⟨_, rfl, ?_⟩
  intro args σ0 hpre
  simp only [findDiscInv, Invariants.inst, List.map_cons, List.map_nil, List.lookup,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [findDiscSpecG, Spec.of, findDiscPreG] at hpre
  obtain ⟨rfl, hheap, hlenx, hlen, hgs, hts, hall⟩ := hpre
  refine ⟨?_, ?_⟩
  · jvc [findDiscSpecG, findDiscPostG]
    refine ⟨0#32, ?_⟩
    simp [Frame.get_setLocal]
  · intro fr σ h
    obtain ⟨i, h3, h5, h7, h8, h1, h6, hi0, hilen, htake, rfl⟩ := h
    by_cases hc : (xs.length : Int) ≤ i.toInt
    · have hi : i.toNat = xs.length := by rw [i32_toNat_eq i hi0]; omega
      rw [hi, List.take_length] at htake
      jvc [findDiscSpecG, findDiscPostG]
    · have hn : i.toInt.toNat < xs.length := by omega
      obtain ⟨y, fs, gv, tv, g', t', c', hyeq, hyheap, hfg, hgv, hft, htv, hfc⟩ :=
        hall xs[i.toInt.toNat] (List.getElem_mem hn)
      have hget : xs[i.toInt.toNat]? = some (.ref y) := by rw [List.getElem?_eq_getElem hn, hyeq]
      have hykey : discKeyOf σ (.ref y) = some (g', t', c') :=
        discKeyOf_ref hyheap hfg hgv hft htv hfc
      clear hall
      jvc [findDiscSpecG, findDiscPostG, jlong_cmp_eq_zero_iff]
      all_goals
        have hlt : i.toInt < 2147483647 := by omega
        refine ⟨i + 1#32, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
        · simp [Frame.get_setLocal, h3]
        · simp [Frame.get_setLocal, h5]
        · simp [Frame.get_setLocal, h7]
        · simp [Frame.get_setLocal, h8]
        · simp [Frame.get_setLocal, h1]
        · simp [Frame.get_setLocal]
        · rw [i32_toInt_add_one i hi0 hlt]; omega
        · rw [i32_toInt_add_one i hi0 hlt]; omega
        · rw [i32_toNat_add_one i hi0 hlt]
          intro z hz
          simp only [i32_toNat_eq i hi0] at htake hz
          rcases mem_take_succ hn hz with hz | hz
          · exact htake z hz
          · rw [hz, hyeq, hykey]
            intro he
            simp only [Option.some.injEq, Prod.mk.injEq] at he
            simp_all

/-! ## The contracts with existential ghosts -/

def findAcctSpec : Spec := Spec.of
  (fun args σ => ∃ a key et xs, findAcctPreG a key et xs args σ)
  (fun args σ r σ' => ∀ (a : Addr) (key : I64) (et : JType) (xs : List Value),
     args = [.ref a, .long key] → σ.heap a = some (.array et xs) → findAcctPostG key xs σ r σ')

theorem findAcct_sat : Sat Gen.prog findAcctRef findAcctSpec := by
  intro args σ o hpre hm
  obtain ⟨a, key, et, xs, hp⟩ := hpre
  have h0 := MethodVC.sat (findAcct_vc a key et xs) args σ o hp hm
  have hargs := hp.1
  subst hargs
  cases o with
  | normal r σ' =>
    intro a' key' et' xs' hargs hheap'
    simp only [List.cons.injEq, Value.ref.injEq, Value.long.injEq, and_true] at hargs
    obtain ⟨rfl, rfl⟩ := hargs
    rw [hp.2.1] at hheap'
    simp only [Option.some.injEq, Obj.array.injEq] at hheap'
    obtain ⟨rfl, rfl⟩ := hheap'
    exact h0
  | exc e σ' => exact h0
  | wrong msg => exact h0

def findDiscSpec : Spec := Spec.of
  (fun args σ => ∃ a len gs ts g t cat et xs, findDiscPreG a len gs ts g t cat et xs args σ)
  (fun args σ r σ' => ∀ (a : Addr) (len : I32) (gs ts : Addr) (g t : JStr) (cat : I64) (et : JType)
     (xs : List Value), args = [.ref a, .int len, .ref gs, .ref ts, .long cat] →
     σ.heap a = some (.array et xs) → σ.heap gs = some (.str g) → σ.heap ts = some (.str t) →
     findDiscPostG g t cat xs σ r σ')

theorem findDisc_sat : Sat Gen.prog findDiscRef findDiscSpec := by
  intro args σ o hpre hm
  obtain ⟨a, len, gs, ts, g, t, cat, et, xs, hp⟩ := hpre
  have h0 := MethodVC.sat (findDisc_vc a len gs ts g t cat et xs) args σ o hp hm
  have hargs := hp.1
  subst hargs
  cases o with
  | normal r σ' =>
    intro a' len' gs' ts' g' t' cat' et' xs' hargs hheap' hgs' hts'
    simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, Value.long.injEq,
      and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
    rw [hp.2.1] at hheap'
    rw [hp.2.2.2.2.1] at hgs'
    rw [hp.2.2.2.2.2.1] at hts'
    simp only [Option.some.injEq, Obj.array.injEq, Obj.str.injEq] at hheap' hgs' hts'
    obtain ⟨rfl, rfl⟩ := hheap'
    subst hgs'
    subst hts'
    exact h0
  | exc e σ' => exact h0
  | wrong msg => exact h0

end EquivLean.Modernize.Cbact04c.Java
