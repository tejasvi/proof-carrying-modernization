import EquivLean.Demo.Jimple.Cbact04c.JavaCallees

/-!
# CBACT04C in Java: definitions for the proof of `run`

The contract `runSpecG` fixes the ghost values (the three arrays and the record functions
`acctOf`, `rateOf`, `cs`) as parameters; `runSpec` follows in `Cbact04c/JavaRun.lean`.

Cut points of `run`'s body (statement indices of the imported Jimple):
* 12 — the loop head (`J12`): the locals hold the fields of
  `s = (cs.take i).foldl (jStep acctOf rateOf) jInit` (`LoopAt`);
* 21 — after `post(acct, totalInt)` (`J21`);
* 28 — before `readAccount(accounts, c.acctId)` (`J28`);
* 29 — the current account is known (`J29`): the state `s1 = jSel acctOf s c` of `jStep`;
* 33 — after `readRate(…)` (`J33`).
-/

open Jimple

namespace EquivLean.Demo.Cbact04c.Java

abbrev runMRef := Gen.Cbact04c.«run(Cbact04c$Cat[],Cbact04c$Account[],Cbact04c$Disc[])».ref
abbrev runBody := Gen.Cbact04c.«run(Cbact04c$Cat[],Cbact04c$Account[],Cbact04c$Disc[])»

/-! ## The loop in steps -/

/-- `s` is the loop state after the first `n` records. -/
def LoopAt (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64) (cs : List JCat) (n : Nat)
    (s : JState) : Prop :=
  s = (cs.take n).foldl (jStep acctOf rateOf) jInit

/-- The first half of `jStep`: the account change. -/
def jSel (acctOf : I64 → JAcct) (s : JState) (c : JCat) : JState :=
  if s.first || c.acct != s.last then
    { rewrites := if s.first then s.rewrites else s.rewrites ++ [jPost s.acct s.total],
      tx := s.tx, first := false, last := c.acct, total := 0, acct := acctOf c.acct }
  else s

/-- The second half of `jStep`: the interest of the record. -/
def jFin (rateOf : JStr → JStr → I32 → I64) (s1 : JState) (c : JCat) : JState :=
  if rateOf s1.acct.grp c.ty c.cat = 0 then s1
  else { s1 with
    total := (s1.total + ((c.bal * rateOf s1.acct.grp c.ty c.cat).sdiv 120000).srem 100000000000).srem
      100000000000,
    tx := s1.tx + 1 }

theorem jStep_eq_fin (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64) (s : JState)
    (c : JCat) : jStep acctOf rateOf s c = jFin rateOf (jSel acctOf s c) c := rfl

theorem loopAt_zero (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64) (cs : List JCat) :
    LoopAt acctOf rateOf cs 0 jInit := by
  simp [LoopAt]

theorem loopAt_succ {acctOf : I64 → JAcct} {rateOf : JStr → JStr → I32 → I64} {cs : List JCat}
    {n : Nat} {s : JState} {c : JCat} (h : LoopAt acctOf rateOf cs n s) (hc : cs[n]? = some c) :
    LoopAt acctOf rateOf cs (n + 1) (jStep acctOf rateOf s c) := by
  unfold LoopAt at *
  rw [List.take_add_one, hc]
  simp [List.foldl_append, h]

theorem loopAt_full {acctOf : I64 → JAcct} {rateOf : JStr → JStr → I32 → I64} {cs : List JCat}
    {n : Nat} {s : JState} (h : LoopAt acctOf rateOf cs n s) (hn : cs.length ≤ n) :
    s = jRun acctOf rateOf cs := by
  unfold LoopAt at h
  rw [List.take_of_length_le hn] at h
  exact h

theorem jSel_first {acctOf : I64 → JAcct} {s : JState} (c : JCat) (h : s.first = true) :
    jSel acctOf s c =
      { rewrites := s.rewrites, tx := s.tx, first := false, last := c.acct,
        total := 0, acct := acctOf c.acct } := by
  simp [jSel, h]

theorem jSel_new {acctOf : I64 → JAcct} {s : JState} {c : JCat} (h : s.first = false)
    (h2 : c.acct ≠ s.last) :
    jSel acctOf s c =
      { rewrites := s.rewrites ++ [jPost s.acct s.total], tx := s.tx,
        first := false, last := c.acct, total := 0, acct := acctOf c.acct } := by
  simp [jSel, h, h2]

theorem jSel_same {acctOf : I64 → JAcct} {s : JState} {c : JCat} (h : s.first = false)
    (h2 : c.acct = s.last) : jSel acctOf s c = s := by
  simp [jSel, h, h2]

/-! ## Contract of `run` with fixed ghost values -/

def runPreG (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (args : List Value) (σ : State) : Prop :=
  args = [.ref ca, .ref aa, .ref da] ∧ RunPre σ ca aa da acctOf rateOf cs

def runPostG (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64) (cs : List JCat)
    (_σ : State) (r : Option Value) (σ' : State) : Prop :=
  ∃ res fs l k xs mods, r = some (.ref res) ∧ σ'.heap res = some (.plain "Cbact04c$Result" fs) ∧
    Fields.get fs ("Cbact04c$Result", "rewrites") = some (.ref l) ∧
    Fields.get fs ("Cbact04c$Result", "transactions") = some (.int (jRun acctOf rateOf cs).tx) ∧
    σ'.heap l = some (.list k xs mods) ∧ Pairs (AcctAt σ') xs (jRun acctOf rateOf cs).rewrites

def runSpecG (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) : Spec :=
  Spec.of (runPreG ca aa da acctOf rateOf cs) (fun _ σ r σ' => runPostG acctOf rateOf cs σ r σ')

/-! ## Invariants -/

/-- Facts shared by the cut points inside an iteration: the loop index `i`, the loop state `s`
before the iteration, the record `c = cs[i]` and its object `co` (local `r4`), the `ArrayList`
`l` (local `$r3`). -/
def IterBase (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (σ0 : State) (fr : Frame) (σ : State) (i : I32) (s : JState) (c : JCat)
    (co : Value) (l : Addr) : Prop :=
  LoopAt acctOf rateOf cs i.toNat s ∧ 0 ≤ i.toInt ∧ i.toInt < cs.length ∧ cs[i.toNat]? = some c ∧
  fr.get 15 = some (.ref ca) ∧ fr.get 17 = some (.ref aa) ∧ fr.get 12 = some (.ref da) ∧
  fr.get 9 = some (.int i) ∧ fr.get 6 = some co ∧ Hide (CatAt σ0 co c) ∧
  fr.get 4 = some (.ref l) ∧ σ0.next ≤ l ∧ Grows σ0 σ ∧
  σ.initOf "Cbact04c" = .done ∧ σ.initOf "Cbact04c$Account" = .done ∧
  σ.initOf "Cbact04c$Result" = .done

/-- Loop head (statement 12). Locals: 15 `cats`, 17 `accounts`, 12 `discs`, 9 `i`,
8 `transactions`, 13/14 `firstTime`, 2 `lastAcct`, 1 `totalInt`, 16 `acct`, 4 `rewrites`. -/
def J12 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (s : JState) (r5 : Value) (l : Addr) (ys : List Value) (mods : Nat),
    LoopAt acctOf rateOf cs i.toNat s ∧ 0 ≤ i.toInt ∧ i.toInt ≤ cs.length ∧
    fr.get 15 = some (.ref ca) ∧ fr.get 17 = some (.ref aa) ∧ fr.get 12 = some (.ref da) ∧
    fr.get 9 = some (.int i) ∧ fr.get 8 = some (.int s.tx) ∧
    fr.get 13 = some (.int (JInt.ofBool s.first)) ∧ fr.get 14 = some (.int (JInt.ofBool s.first)) ∧
    fr.get 2 = some (.long s.last) ∧ fr.get 1 = some (.long s.total) ∧ fr.get 16 = some r5 ∧
    fr.get 4 = some (.ref l) ∧ σ.heap l = some (.list .arrayList ys mods) ∧ σ0.next ≤ l ∧
    Hide (s.first = false → AcctAt σ r5 s.acct) ∧ (s.first = false → s.acct = acctOf s.last) ∧
    Hide (Pairs (AcctAt σ) ys s.rewrites) ∧ Grows σ0 σ ∧
    σ.initOf "Cbact04c" = .done ∧ σ.initOf "Cbact04c$Account" = .done ∧
    σ.initOf "Cbact04c$Result" = .done

/-- After `post` (statement 21): `w` (local 16) is the posted account. -/
def J21 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (s : JState) (c : JCat) (co : Value) (l : Addr) (ys : List Value) (mods : Nat)
    (w : Value),
    IterBase ca aa da acctOf rateOf cs σ0 fr σ i s c co l ∧
    s.first = false ∧ c.acct ≠ s.last ∧
    fr.get 8 = some (.int s.tx) ∧ fr.get 13 = some (.int 0) ∧ fr.get 14 = some (.int 0) ∧
    fr.get 16 = some w ∧ Hide (AcctAt σ w (jPost s.acct s.total)) ∧
    σ.heap l = some (.list .arrayList ys mods) ∧ Hide (Pairs (AcctAt σ) ys s.rewrites)

/-- Before `readAccount` (statement 28): first record or a new account. -/
def J28 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (s : JState) (c : JCat) (co : Value) (l : Addr) (ys : List Value) (mods : Nat),
    IterBase ca aa da acctOf rateOf cs σ0 fr σ i s c co l ∧
    (s.first = true ∨ c.acct ≠ s.last) ∧
    fr.get 8 = some (.int s.tx) ∧ fr.get 13 = some (.int 0) ∧ fr.get 14 = some (.int 0) ∧
    fr.get 2 = some (.long c.acct) ∧ fr.get 1 = some (.long 0) ∧ fr.get 0 = some (.long c.acct) ∧
    σ.heap l = some (.list .arrayList ys mods) ∧
    Hide (Pairs (AcctAt σ) ys (jSel acctOf s c).rewrites)

/-- The account of the record is known (statement 29): `s1 = jSel acctOf s c`, local 16 holds
its account. -/
def J29 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (s : JState) (c : JCat) (co : Value) (l : Addr) (ys : List Value) (mods : Nat)
    (r5 : Value),
    IterBase ca aa da acctOf rateOf cs σ0 fr σ i s c co l ∧
    fr.get 8 = some (.int (jSel acctOf s c).tx) ∧ fr.get 13 = some (.int 0) ∧
    fr.get 14 = some (.int 0) ∧ fr.get 2 = some (.long (jSel acctOf s c).last) ∧
    fr.get 1 = some (.long (jSel acctOf s c).total) ∧ fr.get 16 = some r5 ∧
    Hide (AcctAt σ r5 (jSel acctOf s c).acct) ∧ (jSel acctOf s c).acct = acctOf c.acct ∧
    (jSel acctOf s c).first = false ∧
    σ.heap l = some (.list .arrayList ys mods) ∧
    Hide (Pairs (AcctAt σ) ys (jSel acctOf s c).rewrites)

/-- After `readRate` (statement 33): local 3 holds the rate. -/
def J33 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (s : JState) (c : JCat) (co : Value) (l : Addr) (ys : List Value) (mods : Nat)
    (r5 : Value),
    IterBase ca aa da acctOf rateOf cs σ0 fr σ i s c co l ∧
    fr.get 8 = some (.int (jSel acctOf s c).tx) ∧ fr.get 13 = some (.int 0) ∧
    fr.get 14 = some (.int 0) ∧ fr.get 2 = some (.long (jSel acctOf s c).last) ∧
    fr.get 1 = some (.long (jSel acctOf s c).total) ∧ fr.get 16 = some r5 ∧
    Hide (AcctAt σ r5 (jSel acctOf s c).acct) ∧ (jSel acctOf s c).acct = acctOf c.acct ∧
    (jSel acctOf s c).first = false ∧
    fr.get 3 = some (.long (rateOf (jSel acctOf s c).acct.grp c.ty c.cat)) ∧
    σ.heap l = some (.list .arrayList ys mods) ∧
    Hide (Pairs (AcctAt σ) ys (jSel acctOf s c).rewrites)

def runInv (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) : Invariants :=
  [(12, J12 ca aa da acctOf rateOf cs), (21, J21 ca aa da acctOf rateOf cs),
   (28, J28 ca aa da acctOf rateOf cs), (29, J29 ca aa da acctOf rateOf cs),
   (33, J33 ca aa da acctOf rateOf cs)]

/-- Symbolic execution of `run`'s body from `pc` (callees by their contracts, the `Result`
constructor inlined). -/
def RunWP (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog callees.env 1) runBody
    ((runInv ca aa da acctOf rateOf cs).inst [.ref ca, .ref aa, .ref da] σ0)
    ((runSpecG ca aa da acctOf rateOf cs).post [.ref ca, .ref aa, .ref da] σ0) 60 pc fr σ

/- `RunWP` is unfolded explicitly (`unfold RunWP`): `whnf` must not run the symbolic execution
when a verification condition is applied. -/
attribute [irreducible] RunWP

/-! ## Facts for the calls -/

theorem jSel_sel (acctOf : I64 → JAcct) {s : JState} {c : JCat}
    (h : s.first = true ∨ c.acct ≠ s.last) :
    (jSel acctOf s c).tx = s.tx ∧ (jSel acctOf s c).last = c.acct ∧ (jSel acctOf s c).total = 0 ∧
      (jSel acctOf s c).acct = acctOf c.acct ∧ (jSel acctOf s c).first = false := by
  have : (s.first || c.acct != s.last) = true := by rcases h with h | h <;> simp [h]
  simp [jSel, this]

/-- The accounts array as `readAccount`'s contract needs it, in a state the heap grew to. -/
theorem ra_facts {σ0 σ : State} {ca aa da : Addr} {acctOf : I64 → JAcct}
    {rateOf : JStr → JStr → I32 → I64} {cs : List JCat}
    (hrun : RunPre σ0 ca aa da acctOf rateOf cs) (hg : Grows σ0 σ) {c : JCat} (hc : c ∈ cs) :
    ∃ et xs, σ.heap aa = some (.array et xs) ∧ xs.length < 2147483647 ∧
      (∀ x ∈ xs, ∃ b, AcctAt σ x b) ∧ (∃ x ∈ xs, AcctAt σ x (acctOf c.acct)) ∧
      (acctOf c.acct).id = c.acct ∧ ∀ x ∈ xs, idOf σ x = some c.acct → AcctAt σ x (acctOf c.acct) := by
  obtain ⟨-, -, ⟨et, xs, hh, hlen, hall, hkey⟩, -⟩ := hrun
  obtain ⟨hid, ⟨x0, hx0, hx0a⟩, hk⟩ := hkey c hc
  refine ⟨et, xs, heap_of_grows hg hh, hlen, fun x hx => ?_, ⟨x0, hx0, acctAt_of_grows hg hx0a⟩,
    hid, fun x hx hidx => ?_⟩
  · obtain ⟨b, hb⟩ := hall x hx
    exact ⟨b, acctAt_of_grows hg hb⟩
  · obtain ⟨b, hb⟩ := hall x hx
    rw [idOf_of_grows hg hb] at hidx
    exact acctAt_of_grows hg (hk x hx hidx)

/-- The disclosure-group array as `readRate`'s contract needs it, in a state the heap grew to. -/
theorem rr_facts {σ0 σ : State} {ca aa da : Addr} {acctOf : I64 → JAcct}
    {rateOf : JStr → JStr → I32 → I64} {cs : List JCat}
    (hrun : RunPre σ0 ca aa da acctOf rateOf cs) (hg : Grows σ0 σ) {c : JCat} (hc : c ∈ cs) :
    ∃ et xs, σ.heap da = some (.array et xs) ∧ xs.length < 2147483647 ∧
      (∀ x ∈ xs, ∃ d, DiscAt σ x d) ∧
      (∃ x ∈ xs, DiscAt σ x ⟨(acctOf c.acct).grp, c.ty, c.cat,
        rateOf (acctOf c.acct).grp c.ty c.cat⟩) ∧
      ∀ x ∈ xs, ∀ d, DiscAt σ x d → d.grp = (acctOf c.acct).grp → d.ty = c.ty → d.cat = c.cat →
        d.rate = rateOf (acctOf c.acct).grp c.ty c.cat := by
  obtain ⟨-, -, -, ⟨et, xs, hh, hlen, hall, hkey⟩, -⟩ := hrun
  obtain ⟨⟨x0, hx0, hx0d⟩, hk⟩ := hkey c hc
  refine ⟨et, xs, heap_of_grows hg hh, hlen, fun x hx => ?_, ⟨x0, hx0, discAt_of_grows hg hx0d⟩,
    fun x hx d hd => ?_⟩
  · obtain ⟨d, hd⟩ := hall x hx
    exact ⟨d, discAt_of_grows hg hd⟩
  · obtain ⟨d0, hd0⟩ := hall x hx
    have e := discAt_unique (discAt_of_grows hg hd0) hd
    subst e
    exact hk x hx d0 hd0

/-! ## The second half of `jStep` -/

theorem jSel_last (acctOf : I64 → JAcct) (s : JState) (c : JCat) : (jSel acctOf s c).last = c.acct := by
  unfold jSel
  split
  · rfl
  · next h =>
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at h
    exact h.2.symm

theorem jStep_rate_zero {acctOf : I64 → JAcct} {rateOf : JStr → JStr → I32 → I64} {s : JState}
    {c : JCat} (h : rateOf (jSel acctOf s c).acct.grp c.ty c.cat = 0) :
    jStep acctOf rateOf s c = jSel acctOf s c := by
  rw [jStep_eq_fin]
  unfold jFin
  rw [ite_eq_left h]

theorem jStep_rate_ne {acctOf : I64 → JAcct} {rateOf : JStr → JStr → I32 → I64} {s : JState}
    {c : JCat} (h : ¬ rateOf (jSel acctOf s c).acct.grp c.ty c.cat = 0) :
    (jStep acctOf rateOf s c).tx = (jSel acctOf s c).tx + 1 ∧
    (jStep acctOf rateOf s c).total = ((jSel acctOf s c).total +
      ((c.bal * rateOf (jSel acctOf s c).acct.grp c.ty c.cat).sdiv 120000).srem 100000000000).srem
        100000000000 ∧
    (jStep acctOf rateOf s c).first = (jSel acctOf s c).first ∧
    (jStep acctOf rateOf s c).last = (jSel acctOf s c).last ∧
    (jStep acctOf rateOf s c).acct = (jSel acctOf s c).acct ∧
    (jStep acctOf rateOf s c).rewrites = (jSel acctOf s c).rewrites := by
  rw [jStep_eq_fin]
  unfold jFin
  rw [ite_eq_right h]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end EquivLean.Demo.Cbact04c.Java
