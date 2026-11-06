import EquivLean.Demo.Jimple.Cbact04c.Fixed.JavaCallees

/-!
# CBACT04C in Java, the fixed port: definitions for the proof of `run`

`Cbact04c/JavaRunDefs.lean` for `Cbact04cFixed`. The contract `runSpecG` fixes the ghost values (the
three arrays and the record functions `acctOf`, `rateOf`, `cs`) as parameters; `runFixSpec`
follows in `Cbact04c/Fixed/JavaRun.lean`.

Cut points of `run`'s body (statement indices of the imported Jimple; `firstTime` is held by the
three locals 14, 15, 16):
* 13 — the loop head (`J13`): the locals hold the fields of
  `s = (cs.take i).foldl (jStep acctOf rateOf) jInit` (`LoopAt`);
* 22 — after `post(acct, totalInt)` in the loop (`J22`);
* 30 — before `readAccount(accounts, c.acctId)` (`J30`);
* 31 — the current account is known (`J31`): the state `s1 = jSel acctOf s c` of `jStep`;
* 35 — after `readRate(…)` (`J35`);
* 48 — after the `post` of the last account, behind the loop (`J48`).
-/

open Jimple EquivLean.Demo.Cbact04c.Java

namespace EquivLean.Demo.Cbact04c.JavaF

abbrev runMRef := GenF.Cbact04cFixed.«run(Cbact04cFixed$Cat[],Cbact04cFixed$Account[],Cbact04cFixed$Disc[])».ref
abbrev runBody := GenF.Cbact04cFixed.«run(Cbact04cFixed$Cat[],Cbact04cFixed$Account[],Cbact04cFixed$Disc[])»

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
  args = [.ref ca, .ref aa, .ref da] ∧ RunPreF σ ca aa da acctOf rateOf cs

def runPostG (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64) (cs : List JCat)
    (_σ : State) (r : Option Value) (σ' : State) : Prop :=
  ∃ res fs l k xs mods, r = some (.ref res) ∧ σ'.heap res = some (.plain "Cbact04cFixed$Result" fs) ∧
    Fields.get fs ("Cbact04cFixed$Result", "rewrites") = some (.ref l) ∧
    Fields.get fs ("Cbact04cFixed$Result", "transactions") = some (.int (jRun acctOf rateOf cs).tx) ∧
    σ'.heap l = some (.list k xs mods) ∧
      Pairs (AcctAtC "Cbact04cFixed$Account" σ') xs (jRunFix acctOf rateOf cs)

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
  fr.get 4 = some (.ref ca) ∧ fr.get 17 = some (.ref aa) ∧ fr.get 18 = some (.ref da) ∧
  fr.get 10 = some (.int i) ∧ fr.get 19 = some co ∧ Hide (CatAtC "Cbact04cFixed$Cat" σ0 co c) ∧
  fr.get 5 = some (.ref l) ∧ σ0.next ≤ l ∧ Grows σ0 σ ∧
  σ.initOf "Cbact04cFixed" = .done ∧ σ.initOf "Cbact04cFixed$Account" = .done ∧
  σ.initOf "Cbact04cFixed$Result" = .done

/-- Loop head (statement 13). Locals: 4 `cats`, 17 `accounts`, 18 `discs`, 10 `i`,
9 `transactions`, 14/15/16 `firstTime`, 2 `lastAcct`, 1 `totalInt`, 13 `acct`, 5 `rewrites`. -/
def J13 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (s : JState) (r5 : Value) (l : Addr) (ys : List Value) (mods : Nat),
    LoopAt acctOf rateOf cs i.toNat s ∧ 0 ≤ i.toInt ∧ i.toInt ≤ cs.length ∧
    fr.get 4 = some (.ref ca) ∧ fr.get 17 = some (.ref aa) ∧ fr.get 18 = some (.ref da) ∧
    fr.get 10 = some (.int i) ∧ fr.get 9 = some (.int s.tx) ∧
    fr.get 14 = some (.int (JInt.ofBool s.first)) ∧ fr.get 15 = some (.int (JInt.ofBool s.first)) ∧
    fr.get 16 = some (.int (JInt.ofBool s.first)) ∧
    fr.get 2 = some (.long s.last) ∧ fr.get 1 = some (.long s.total) ∧ fr.get 13 = some r5 ∧
    fr.get 5 = some (.ref l) ∧ σ.heap l = some (.list .arrayList ys mods) ∧ σ0.next ≤ l ∧
    Hide (s.first = false → AcctAtC "Cbact04cFixed$Account" σ r5 s.acct) ∧ (s.first = false → s.acct = acctOf s.last) ∧
    Hide (Pairs (AcctAtC "Cbact04cFixed$Account" σ) ys s.rewrites) ∧ Grows σ0 σ ∧
    σ.initOf "Cbact04cFixed" = .done ∧ σ.initOf "Cbact04cFixed$Account" = .done ∧
    σ.initOf "Cbact04cFixed$Result" = .done

/-- After `post` in the loop (statement 22): `w` (local 13) is the posted account. -/
def J22 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (s : JState) (c : JCat) (co : Value) (l : Addr) (ys : List Value) (mods : Nat)
    (w : Value),
    IterBase ca aa da acctOf rateOf cs σ0 fr σ i s c co l ∧
    s.first = false ∧ c.acct ≠ s.last ∧
    fr.get 9 = some (.int s.tx) ∧ fr.get 14 = some (.int 0) ∧ fr.get 15 = some (.int 0) ∧
    fr.get 16 = some (.int 0) ∧
    fr.get 13 = some w ∧ Hide (AcctAtC "Cbact04cFixed$Account" σ w (jPost s.acct s.total)) ∧
    σ.heap l = some (.list .arrayList ys mods) ∧ Hide (Pairs (AcctAtC "Cbact04cFixed$Account" σ) ys s.rewrites)

/-- Before `readAccount` (statement 30): first record or a new account. -/
def J30 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (s : JState) (c : JCat) (co : Value) (l : Addr) (ys : List Value) (mods : Nat),
    IterBase ca aa da acctOf rateOf cs σ0 fr σ i s c co l ∧
    (s.first = true ∨ c.acct ≠ s.last) ∧
    fr.get 9 = some (.int s.tx) ∧ fr.get 14 = some (.int 0) ∧ fr.get 15 = some (.int 0) ∧
    fr.get 16 = some (.int 0) ∧
    fr.get 2 = some (.long c.acct) ∧ fr.get 1 = some (.long 0) ∧ fr.get 0 = some (.long c.acct) ∧
    σ.heap l = some (.list .arrayList ys mods) ∧
    Hide (Pairs (AcctAtC "Cbact04cFixed$Account" σ) ys (jSel acctOf s c).rewrites)

/-- The account of the record is known (statement 31): `s1 = jSel acctOf s c`, local 13 holds
its account. -/
def J31 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (s : JState) (c : JCat) (co : Value) (l : Addr) (ys : List Value) (mods : Nat)
    (r5 : Value),
    IterBase ca aa da acctOf rateOf cs σ0 fr σ i s c co l ∧
    fr.get 9 = some (.int (jSel acctOf s c).tx) ∧ fr.get 14 = some (.int 0) ∧
    fr.get 15 = some (.int 0) ∧ fr.get 16 = some (.int 0) ∧
    fr.get 2 = some (.long (jSel acctOf s c).last) ∧
    fr.get 1 = some (.long (jSel acctOf s c).total) ∧ fr.get 13 = some r5 ∧
    Hide (AcctAtC "Cbact04cFixed$Account" σ r5 (jSel acctOf s c).acct) ∧ (jSel acctOf s c).acct = acctOf c.acct ∧
    (jSel acctOf s c).first = false ∧
    σ.heap l = some (.list .arrayList ys mods) ∧
    Hide (Pairs (AcctAtC "Cbact04cFixed$Account" σ) ys (jSel acctOf s c).rewrites)

/-- After `readRate` (statement 35): local 3 holds the rate. -/
def J35 (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (i : I32) (s : JState) (c : JCat) (co : Value) (l : Addr) (ys : List Value) (mods : Nat)
    (r5 : Value),
    IterBase ca aa da acctOf rateOf cs σ0 fr σ i s c co l ∧
    fr.get 9 = some (.int (jSel acctOf s c).tx) ∧ fr.get 14 = some (.int 0) ∧
    fr.get 15 = some (.int 0) ∧ fr.get 16 = some (.int 0) ∧
    fr.get 2 = some (.long (jSel acctOf s c).last) ∧
    fr.get 1 = some (.long (jSel acctOf s c).total) ∧ fr.get 13 = some r5 ∧
    Hide (AcctAtC "Cbact04cFixed$Account" σ r5 (jSel acctOf s c).acct) ∧ (jSel acctOf s c).acct = acctOf c.acct ∧
    (jSel acctOf s c).first = false ∧
    fr.get 3 = some (.long (rateOf (jSel acctOf s c).acct.grp c.ty c.cat)) ∧
    σ.heap l = some (.list .arrayList ys mods) ∧
    Hide (Pairs (AcctAtC "Cbact04cFixed$Account" σ) ys (jSel acctOf s c).rewrites)

/-- After the `post` of the last account (statement 48): the loop has ended with a current
account, `w` (local 13) is that account posted; the `ArrayList` holds the earlier rewrites. -/
def J48 (_ca _aa _da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (l : Addr) (ys : List Value) (mods : Nat) (w : Value),
    (jRun acctOf rateOf cs).first = false ∧
    fr.get 9 = some (.int (jRun acctOf rateOf cs).tx) ∧ fr.get 13 = some w ∧
    Hide (AcctAtC "Cbact04cFixed$Account" σ w
      (jPost (jRun acctOf rateOf cs).acct (jRun acctOf rateOf cs).total)) ∧
    fr.get 5 = some (.ref l) ∧ σ.heap l = some (.list .arrayList ys mods) ∧ σ0.next ≤ l ∧
    Hide (Pairs (AcctAtC "Cbact04cFixed$Account" σ) ys (jRun acctOf rateOf cs).rewrites) ∧
    Grows σ0 σ ∧ σ.initOf "Cbact04cFixed$Result" = .done

def runInv (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) : Invariants :=
  [(13, J13 ca aa da acctOf rateOf cs), (22, J22 ca aa da acctOf rateOf cs),
   (30, J30 ca aa da acctOf rateOf cs), (31, J31 ca aa da acctOf rateOf cs),
   (35, J35 ca aa da acctOf rateOf cs), (48, J48 ca aa da acctOf rateOf cs)]

/-- Symbolic execution of `run`'s body from `pc` (callees by their contracts, the `Result`
constructor inlined). -/
def RunWP (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP GenF.prog (callWP GenF.prog callees.env 1) runBody
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
    (hrun : RunPreF σ0 ca aa da acctOf rateOf cs) (hg : Grows σ0 σ) {c : JCat} (hc : c ∈ cs) :
    ∃ et xs, σ.heap aa = some (.array et xs) ∧ xs.length < 2147483647 ∧
      (∀ x ∈ xs, ∃ b, AcctAtC "Cbact04cFixed$Account" σ x b) ∧ (∃ x ∈ xs, AcctAtC "Cbact04cFixed$Account" σ x (acctOf c.acct)) ∧
      (acctOf c.acct).id = c.acct ∧ ∀ x ∈ xs, idOfC "Cbact04cFixed$Account" σ x = some c.acct → AcctAtC "Cbact04cFixed$Account" σ x (acctOf c.acct) := by
  obtain ⟨-, -, ⟨et, xs, hh, hlen, hall, hkey⟩, -⟩ := hrun
  obtain ⟨hid, ⟨x0, hx0, hx0a⟩, hk⟩ := hkey c hc
  refine ⟨et, xs, heap_of_grows hg hh, hlen, fun x hx => ?_, ⟨x0, hx0, acctAtC_of_grows hg hx0a⟩,
    hid, fun x hx hidx => ?_⟩
  · obtain ⟨b, hb⟩ := hall x hx
    exact ⟨b, acctAtC_of_grows hg hb⟩
  · obtain ⟨b, hb⟩ := hall x hx
    rw [idOfC_of_grows hg hb] at hidx
    exact acctAtC_of_grows hg (hk x hx hidx)

/-- The disclosure-group array as `readRate`'s contract needs it, in a state the heap grew to. -/
theorem rr_facts {σ0 σ : State} {ca aa da : Addr} {acctOf : I64 → JAcct}
    {rateOf : JStr → JStr → I32 → I64} {cs : List JCat}
    (hrun : RunPreF σ0 ca aa da acctOf rateOf cs) (hg : Grows σ0 σ) {c : JCat} (hc : c ∈ cs) :
    ∃ et xs, σ.heap da = some (.array et xs) ∧ xs.length < 2147483647 ∧
      (∀ x ∈ xs, ∃ d, DiscAtC "Cbact04cFixed$Disc" σ x d) ∧
      (∃ x ∈ xs, DiscAtC "Cbact04cFixed$Disc" σ x ⟨(acctOf c.acct).grp, c.ty, c.cat,
        rateOf (acctOf c.acct).grp c.ty c.cat⟩) ∧
      ∀ x ∈ xs, ∀ d, DiscAtC "Cbact04cFixed$Disc" σ x d → d.grp = (acctOf c.acct).grp → d.ty = c.ty → d.cat = c.cat →
        d.rate = rateOf (acctOf c.acct).grp c.ty c.cat := by
  obtain ⟨-, -, -, ⟨et, xs, hh, hlen, hall, hkey⟩, -⟩ := hrun
  obtain ⟨⟨x0, hx0, hx0d⟩, hk⟩ := hkey c hc
  refine ⟨et, xs, heap_of_grows hg hh, hlen, fun x hx => ?_, ⟨x0, hx0, discAtC_of_grows hg hx0d⟩,
    fun x hx d hd => ?_⟩
  · obtain ⟨d, hd⟩ := hall x hx
    exact ⟨d, discAtC_of_grows hg hd⟩
  · obtain ⟨d0, hd0⟩ := hall x hx
    have e := discAtC_unique (discAtC_of_grows hg hd0) hd
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

/-! ## The rewrites of the fixed port -/

theorem jRunFix_first {acctOf : I64 → JAcct} {rateOf : JStr → JStr → I32 → I64} {cs : List JCat}
    (h : (jRun acctOf rateOf cs).first = true) :
    jRunFix acctOf rateOf cs = (jRun acctOf rateOf cs).rewrites := by
  simp [jRunFix, h]

theorem jRunFix_last {acctOf : I64 → JAcct} {rateOf : JStr → JStr → I32 → I64} {cs : List JCat}
    (h : (jRun acctOf rateOf cs).first = false) :
    jRunFix acctOf rateOf cs = (jRun acctOf rateOf cs).rewrites ++
      [jPost (jRun acctOf rateOf cs).acct (jRun acctOf rateOf cs).total] := by
  simp [jRunFix, h]

end EquivLean.Demo.Cbact04c.JavaF
