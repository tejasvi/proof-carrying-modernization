import EquivLean.Demo.Jimple.Cbact04c.JavaLib

/-!
# CBACT04C in Java: the callees `readAccount`, `readRate`, `post`

Each method is verified with JimpleLean's VC generator against a contract whose ghost values
(the arrays, the key, the expected record) are parameters (`raSpecG`, `rrSpecG`, `postSpecG`);
the contracts of `Cbact04c/Model.lean` (`readAccountSpec`, `readRateSpec`, `postSpec`) follow, and
`callees_valid` collects them as the contract table used for `run`.
-/

open Jimple

-- these proofs split each key comparison (`lcmp`) two ways, by `jlong_cmp_eq_zero`, not three
attribute [-jsimp] JLong.cmp_eq

namespace EquivLean.Demo.Cbact04c.Java

/-! ## `readAccount` -/

abbrev raRef := Gen.Cbact04c.«readAccount(Cbact04c$Account[],long)».ref

def raPre (aa : Addr) (id : I64) (et : JType) (xs : List Value) (a : JAcct)
    (args : List Value) (σ : State) : Prop :=
  args = [.ref aa, .long id] ∧ σ.heap aa = some (.array et xs) ∧ xs.length < 2147483647 ∧
  (∀ x ∈ xs, ∃ b, AcctAt σ x b) ∧ (∃ x ∈ xs, AcctAt σ x a) ∧ a.id = id ∧
  ∀ x ∈ xs, idOf σ x = some id → AcctAt σ x a

def raPost (a : JAcct) (σ : State) (r : Option Value) (σ' : State) : Prop :=
  ∃ v, r = some v ∧ AcctAt σ v a ∧ σ' = σ

def raSpecG (aa : Addr) (id : I64) (et : JType) (xs : List Value) (a : JAcct) : Spec :=
  Spec.of (raPre aa id et xs a) (fun _ σ r σ' => raPost a σ r σ')

def raInv3 (aa : Addr) (id : I64) (xs : List Value) (_args : List Value) (σ0 : State) (fr : Frame)
    (σ : State) : Prop :=
  ∃ i : I32, fr.get 0 = some (.ref aa) ∧ fr.get 4 = some (.long id) ∧ fr.get 3 = some (.int i) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧ (∀ x ∈ xs.take i.toNat, idOf σ0 x ≠ some id) ∧ σ = σ0

def raInv (aa : Addr) (id : I64) (xs : List Value) : Invariants := [(3, raInv3 aa id xs)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem ra_vc (aa : Addr) (id : I64) (et : JType) (xs : List Value) (a : JAcct) :
    MethodVC Gen.prog (fun _ => none) 0 raRef (raSpecG aa id et xs a) (raInv aa id xs) 20 := by
  refine ⟨_, rfl, ?_⟩
  intro args σ0 hpre
  simp only [raInv, Invariants.inst, List.map_cons, List.map_nil, List.lookup,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [raSpecG, Spec.of] at hpre
  obtain ⟨rfl, hheap, hlen, hall, ⟨x0, hx0mem, hx0⟩, rfl, hkey⟩ := hpre
  have hx0id := idOf_of_acctAt hx0
  clear hx0
  refine ⟨?_, ?_⟩
  · jvc [raSpecG]
    refine ⟨0#32, ?_⟩
    simp [Frame.get_setLocal]
  · intro fr σ h
    obtain ⟨i, h0, h4, h3, hi0, hilen, htake, rfl⟩ := h
    by_cases hc : (xs.length : Int) ≤ i.toInt
    · jvc [raSpecG, jlong_cmp_eq_zero']
      exfalso
      have hi : i.toNat = xs.length := by rw [i32_toNat_eq i hi0]; omega
      rw [hi, List.take_length] at htake
      exact htake _ hx0mem hx0id
    · have hn : i.toInt.toNat < xs.length := by omega
      obtain ⟨b, x, fs, g, hxeq, hxheap, hfid, hfbal, hfcc, hfcd, hfg, hstr⟩ :=
        hall xs[i.toInt.toNat] (List.getElem_mem hn)
      have hget : xs[i.toInt.toNat]? = some (.ref x) := by rw [List.getElem?_eq_getElem hn, hxeq]
      have hxid : idOf σ (.ref x) = some b.id := idOf_ref hxheap hfid
      have hfound : Hide (b.id = a.id → AcctAt σ (.ref x) a) := Hide.intro fun hb => by
        have := hkey _ (List.getElem_mem hn) (by rw [hxeq, hxid, hb])
        rwa [hxeq] at this
      clear hall hkey
      jvc [raSpecG, jlong_cmp_eq_zero']
      · -- found
        exact ⟨_, rfl, (Hide.elim hfound) hcond, rfl⟩
      · -- next iteration
        have hlt : i.toInt < 2147483647 := by omega
        refine ⟨i + 1#32, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
        · simp [Frame.get_setLocal, h0]
        · simp [Frame.get_setLocal, h4]
        · simp [Frame.get_setLocal]
        · rw [i32_toInt_add_one i hi0 hlt]; omega
        · rw [i32_toInt_add_one i hi0 hlt]; omega
        · rw [i32_toNat_add_one i hi0 hlt]
          intro y hy
          simp only [i32_toNat_eq i hi0] at htake hy
          rcases mem_take_succ hn hy with hy | hy
          · exact htake y hy
          · rw [hy, hxeq, hxid]; simpa using hcond

/-! ## `readRate` -/

abbrev rrRef := Gen.Cbact04c.«readRate(Cbact04c$Disc[],java.lang.String,java.lang.String,int)».ref

def rrPre (da gs ts : Addr) (g t : JStr) (cat : I32) (rate : I64) (et : JType) (xs : List Value)
    (args : List Value) (σ : State) : Prop :=
  args = [.ref da, .ref gs, .ref ts, .int cat] ∧ σ.heap gs = some (.str g) ∧
  σ.heap ts = some (.str t) ∧ σ.heap da = some (.array et xs) ∧ xs.length < 2147483647 ∧
  (∀ x ∈ xs, ∃ d, DiscAt σ x d) ∧ (∃ x ∈ xs, DiscAt σ x ⟨g, t, cat, rate⟩) ∧
  ∀ x ∈ xs, ∀ d, DiscAt σ x d → d.grp = g → d.ty = t → d.cat = cat → d.rate = rate

def rrPost (rate : I64) (σ : State) (r : Option Value) (σ' : State) : Prop :=
  r = some (.long rate) ∧ σ' = σ

def rrSpecG (da gs ts : Addr) (g t : JStr) (cat : I32) (rate : I64) (et : JType)
    (xs : List Value) : Spec :=
  Spec.of (rrPre da gs ts g t cat rate et xs) (fun _ σ r σ' => rrPost rate σ r σ')

def rrInv5 (da gs ts : Addr) (g t : JStr) (cat : I32) (xs : List Value) (_args : List Value)
    (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ i : I32, fr.get 9 = some (.ref da) ∧ fr.get 6 = some (.ref gs) ∧ fr.get 7 = some (.ref ts) ∧
    fr.get 3 = some (.int cat) ∧ fr.get 5 = some (.int i) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧ NoKey σ0 g t cat (xs.take i.toNat) ∧ σ = σ0

def rrInv21 (_args : List Value) (_σ0 : State) (_fr : Frame) (_σ : State) : Prop := False

def rrInv (da gs ts : Addr) (g t : JStr) (cat : I32) (xs : List Value) : Invariants :=
  [(5, rrInv5 da gs ts g t cat xs), (21, rrInv21)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem rr_vc (da gs ts : Addr) (g t : JStr) (cat : I32) (rate : I64) (et : JType)
    (xs : List Value) :
    MethodVC Gen.prog (fun _ => none) 0 rrRef (rrSpecG da gs ts g t cat rate et xs)
      (rrInv da gs ts g t cat xs) 30 := by
  refine ⟨_, rfl, ?_⟩
  intro args σ0 hpre
  simp only [rrInv, Invariants.inst, List.map_cons, List.map_nil, List.lookup,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [rrSpecG, Spec.of] at hpre
  obtain ⟨rfl, hgs, hts, hheap, hlen, hall, hex, hkey⟩ := hpre
  have hex' := Hide.intro hex
  clear hex
  refine ⟨?_, ?_, ?_⟩
  · jvc [rrSpecG]
    refine ⟨0#32, ?_⟩
    simp [Frame.get_setLocal, NoKey]
  · intro fr σ h
    obtain ⟨i, h9, h6, h7, h3, h5, hi0, hilen, htake, rfl⟩ := h
    have htake' := Hide.intro htake
    clear htake
    by_cases hc : (xs.length : Int) ≤ i.toInt
    · jvc [rrSpecG]
      have hi : i.toNat = xs.length := by rw [i32_toNat_eq i hi0]; omega
      have h1 := Hide.elim htake'
      rw [hi, List.take_length] at h1
      exact noKey_absurd h1 (Hide.elim hex')
    · have hn : i.toInt.toNat < xs.length := by omega
      obtain ⟨d, x, fs, _, _, hxeq, hxheap, hfg, ⟨gy, rfl, hgy⟩, hft, ⟨ty, rfl, hty⟩, hfc, hfr⟩ :=
        hall xs[i.toInt.toNat] (List.getElem_mem hn)
      have hget : xs[i.toInt.toNat]? = some (.ref x) := by rw [List.getElem?_eq_getElem hn, hxeq]
      have hd : DiscAt σ (.ref x) d :=
        ⟨x, fs, _, _, rfl, hxheap, hfg, ⟨gy, rfl, hgy⟩, hft, ⟨ty, rfl, hty⟩, hfc, hfr⟩
      have hrate : Hide (d.grp = g → d.ty = t → d.cat = cat → d.rate = rate) :=
        Hide.intro (hkey _ (List.getElem_mem hn) d (by rw [hxeq]; exact hd))
      have hd' := Hide.intro hd
      clear hall hkey hd
      have hlt : i.toInt < 2147483647 := by omega
      jvc [rrSpecG]
      · -- found
        have e : d.rate = rate := Hide.elim hrate
        exact ⟨by rw [e], rfl⟩
      all_goals
        refine ⟨i + 1#32, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
        · simp [Frame.get_setLocal, h9]
        · simp [Frame.get_setLocal, h6]
        · simp [Frame.get_setLocal, h7]
        · simp [Frame.get_setLocal, h3]
        · simp [Frame.get_setLocal]
        · rw [i32_toInt_add_one i hi0 hlt]; omega
        · rw [i32_toInt_add_one i hi0 hlt]; omega
        · rw [i32_toNat_add_one i hi0 hlt]
          have h1 := Hide.elim htake'
          simp only [i32_toNat_eq i hi0] at h1 ⊢
          refine noKey_step hn hxeq (Hide.elim hd') ?_ h1
          intro ⟨e1, e2, e3⟩
          apply hcond
          first | exact e1.symm | exact e2.symm | exact e3 | exact e1 | exact e2 | exact e3.symm
  · intro fr σ h
    exact h.elim

/-! ## `post` -/

abbrev postRef := Gen.Cbact04c.«post(Cbact04c$Account,long)».ref

def postPreG (v : Value) (t : I64) (a : JAcct) (args : List Value) (σ : State) : Prop :=
  args = [v, .long t] ∧ AcctAt σ v a ∧ σ.initOf "Cbact04c$Account" = .done

def postPostG (a : JAcct) (t : I64) (σ : State) (r : Option Value) (σ' : State) : Prop :=
  ∃ w, r = some w ∧ AcctAt σ' w (jPost a t) ∧ Grows σ σ' ∧
    σ'.initOf "Cbact04c$Account" = .done ∧
    σ'.initOf "Cbact04c$Result" = σ.initOf "Cbact04c$Result" ∧
    σ'.initOf "Cbact04c" = σ.initOf "Cbact04c"

def postSpecG (v : Value) (t : I64) (a : JAcct) : Spec :=
  Spec.of (postPreG v t a) (fun _ σ r σ' => postPostG a t σ r σ')

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem post_vc (v : Value) (t : I64) (a : JAcct) :
    MethodVC Gen.prog (fun _ => none) 1 postRef (postSpecG v t a) [] 30 := by
  refine ⟨_, rfl, ?_⟩
  intro args σ0 hpre
  simp only [Invariants.inst, List.map_nil, List.lookup, List.not_mem_nil, false_implies,
    implies_true, and_true]
  simp only [postSpecG, Spec.of] at hpre
  obtain ⟨rfl, ⟨x, fs, _, rfl, hx, hid, hbal, hcc, hcd, hg, ⟨gy, rfl, hgy⟩⟩, hinit⟩ := hpre
  have hgy' : gy ≠ σ0.next := State.ne_next_of_heap hgy
  jvc [postSpecG, inlineFuel, fields_get_cons, fields_get_nil]
  unfold postPostG
  refine ⟨_, rfl, ?_, ⟨by simp [State.next_setObj, State.next_alloc], fun y hy => ?_⟩, ?_, ?_, ?_⟩
  · simp [AcctAt, StrAt, jPost, State.heap_setObj, State.next_setObj, State.heap_alloc,
      State.next_alloc, Fields.get_set, hgy', hgy]
  · have hy' : y ≠ σ0.next := Nat.ne_of_lt hy
    simp [State.heap_setObj, State.heap_alloc, hy']
  · simp [State.initOf_setObj, State.initOf_alloc, hinit]
  · simp [State.initOf_setObj, State.initOf_alloc]
  · simp [State.initOf_setObj, State.initOf_alloc]

/-! ## The contracts of `Cbact04c/Model.lean` -/

theorem readAccount_sat : Sat Gen.prog raRef readAccountSpec := by
  intro args σ o hpre hm
  obtain ⟨aa, id, et, xs, a, rfl, hheap, hlen, hall, hex, hid, hkey⟩ := hpre
  have hS : ∀ a', (∃ x ∈ xs, AcctAt σ x a') → a'.id = id →
      (∀ x ∈ xs, idOf σ x = some id → AcctAt σ x a') →
      (raSpecG aa id et xs a').post [.ref aa, .long id] σ o := fun a' h1 h2 h3 =>
    MethodVC.sat (ra_vc aa id et xs a') _ _ _ ⟨rfl, hheap, hlen, hall, h1, h2, h3⟩ hm
  cases o with
  | normal r σ' =>
    intro aa' id' et' xs' a' hargs hheap' hex' hid' hkey'
    simp only [List.cons.injEq, Value.ref.injEq, Value.long.injEq, and_true] at hargs
    obtain ⟨rfl, rfl⟩ := hargs
    rw [hheap] at hheap'
    simp only [Option.some.injEq, Obj.array.injEq] at hheap'
    obtain ⟨rfl, rfl⟩ := hheap'
    exact hS a' hex' hid' hkey'
  | exc e σ' => exact hS a hex hid hkey
  | wrong msg => exact hS a hex hid hkey

theorem readRate_sat : Sat Gen.prog rrRef readRateSpec := by
  intro args σ o hpre hm
  obtain ⟨da, g, t, gs, ts, cat, rate, et, xs, rfl, hgs, hts, hheap, hlen, hall, hex, hkey⟩ := hpre
  have hS : ∀ rate', (∃ x ∈ xs, DiscAt σ x ⟨g, t, cat, rate'⟩) →
      (∀ x ∈ xs, ∀ d, DiscAt σ x d → d.grp = g → d.ty = t → d.cat = cat → d.rate = rate') →
      (rrSpecG da gs ts g t cat rate' et xs).post [.ref da, .ref gs, .ref ts, .int cat] σ o :=
    fun rate' h1 h2 => MethodVC.sat (rr_vc da gs ts g t cat rate' et xs) _ _ _
      ⟨rfl, hgs, hts, hheap, hlen, hall, h1, h2⟩ hm
  cases o with
  | normal r σ' =>
    intro da' g' t' gs' ts' cat' rate' et' xs' hargs hgs' hts' hheap' hex' hkey'
    simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
    rw [hgs] at hgs'
    rw [hts] at hts'
    rw [hheap] at hheap'
    simp only [Option.some.injEq, Obj.str.injEq, Obj.array.injEq] at hgs' hts' hheap'
    obtain ⟨rfl, rfl⟩ := hheap'
    subst hgs'
    subst hts'
    exact hS rate' hex' hkey'
  | exc e σ' => exact hS rate hex hkey
  | wrong msg => exact hS rate hex hkey

theorem post_sat : Sat Gen.prog postRef postSpec := by
  intro args σ o hpre hm
  obtain ⟨v, t, a, rfl, hv, hinit⟩ := hpre
  have hS : ∀ a', AcctAt σ v a' → (postSpecG v t a').post [v, .long t] σ o := fun a' h =>
    MethodVC.sat_of_valid (valid_none _) (post_vc v t a') _ _ _ ⟨rfl, h, hinit⟩ hm
  cases o with
  | normal r σ' =>
    intro v' t' a' hargs hv'
    simp only [List.cons.injEq, Value.long.injEq, and_true] at hargs
    obtain ⟨rfl, rfl⟩ := hargs
    exact hS a' hv'
  | exc e σ' => exact hS a hv
  | wrong msg => exact hS a hv

/-! ## The contract table of `run`'s callees -/

def raSig : MethodSig :=
  { cls := "Cbact04c", ret := .cls "Cbact04c$Account", name := "readAccount",
    params := [.array (.cls "Cbact04c$Account"), .prim .long] }
def rrSig : MethodSig :=
  { cls := "Cbact04c", ret := .prim .long, name := "readRate",
    params := [.array (.cls "Cbact04c$Disc"), .cls "java.lang.String", .cls "java.lang.String",
      .prim .int] }
def postSig : MethodSig :=
  { cls := "Cbact04c", ret := .cls "Cbact04c$Account", name := "post",
    params := [.cls "Cbact04c$Account", .prim .long] }

def callees : Contracts :=
  [(raSig, readAccountSpec), (rrSig, readRateSpec), (postSig, postSpec)]

/-- The static call targets of `sig` (the method `m` itself). -/
theorem targets_sat {P : Program} {sig : MethodSig} {m : MethodRef} {S : Spec}
    (hst : P.selectStatic sig = .jimple m) (hsp : ∀ m', P.selectSpecial sig ≠ .jimple m')
    (hcl : ∀ c, sig ≠ clinitSig c) (h : Sat P m S) : ∀ m', Targets P sig m' → Sat P m' S := by
  intro m' ⟨hsel, _⟩
  rcases hsel with h1 | h1 | ⟨h1, _⟩
  · rw [hst] at h1; cases h1; exact h
  · exact absurd h1 (hsp m')
  · exact absurd h1 (hcl _)

set_option maxHeartbeats 0 in
theorem readAccount_ok : ContractOK Gen.prog raSig readAccountSpec := by
  refine ⟨targets_sat rfl (fun m' h => by cases h) (fun c h => by
    have := congrArg MethodSig.name h; simp [raSig, clinitSig] at this) readAccount_sat, ?_⟩
  -- a static method: nothing is owed for implementing classes (`P.staticDecl sig = true`)
  apply forall_progClass_of_mem
  simp (config := { decide := true }) only [jground, false_implies, implies_true]

set_option maxHeartbeats 0 in
theorem readRate_ok : ContractOK Gen.prog rrSig readRateSpec := by
  refine ⟨targets_sat rfl (fun m' h => by cases h) (fun c h => by
    have := congrArg MethodSig.name h; simp [rrSig, clinitSig] at this) readRate_sat, ?_⟩
  -- a static method: nothing is owed for implementing classes (`P.staticDecl sig = true`)
  apply forall_progClass_of_mem
  simp (config := { decide := true }) only [jground, false_implies, implies_true]

set_option maxHeartbeats 0 in
theorem post_ok : ContractOK Gen.prog postSig postSpec := by
  refine ⟨targets_sat rfl (fun m' h => by cases h) (fun c h => by
    have := congrArg MethodSig.name h; simp [postSig, clinitSig] at this) post_sat, ?_⟩
  -- a static method: nothing is owed for implementing classes (`P.staticDecl sig = true`)
  apply forall_progClass_of_mem
  simp (config := { decide := true }) only [jground, false_implies, implies_true]

theorem callees_valid : Valid Gen.prog callees.env := by
  apply Contracts.valid_of_ok
  simp only [callees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨readAccount_ok, readRate_ok, post_ok⟩

end EquivLean.Demo.Cbact04c.Java

#print axioms EquivLean.Demo.Cbact04c.Java.readAccount_sat
#print axioms EquivLean.Demo.Cbact04c.Java.readRate_sat
#print axioms EquivLean.Demo.Cbact04c.Java.post_sat
#print axioms EquivLean.Demo.Cbact04c.Java.callees_valid
