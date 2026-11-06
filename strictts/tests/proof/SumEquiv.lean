import StrictTS.Proof.Arrays
open StrictTS JS

/-!
Differential equivalence of two implementations of a sum:

```ts
function sumLoop(xs: number[]): number { let s = 0; for (const x of xs) { s = s + x; } return s; }
function sumReduce(xs: number[]): number { return xs.reduce((acc, x) => acc + x, 0); }
```
(IR written by hand in the translator's output format.)
-/

def TT0 : TypeTable := ⟨fun _ => .undef, fun _ => .nil⟩

def sumLoopRef : FunRef (.cons (.arr .num) .nil) .num := ⟨0, "sumLoop"⟩
def sumReduceRef : FunRef (.cons (.arr .num) .nil) .num := ⟨1, "sumReduce"⟩

def sumLoopDef : FunDef TT0 :=
  { name := "sumLoop", args := .cons (.arr .num) .nil, ret := .num,
    lam := .sync [⟨.arr .num, false⟩] rfl
      (.decl ⟨.num, true⟩ (.lit (.num 0))
        (.seq (.forOf (.var (.there .here))
            (.seq (.assign (.there .here)
              (.prim (.numBin .add) (.cons (.var (.there .here)) (.cons (.var .here) .nil)))) .nil))
        (.seq (.ret (.var .here)) .nil))) }

def addCb : Expr TT0 [⟨.arr .num, false⟩] (.fn (.cons .num (.cons .num (.cons .num (.cons (.arr .num) .nil)))) .num) :=
  .lam [] .nil (.sync [⟨.num, false⟩, ⟨.num, false⟩, ⟨.num, false⟩, ⟨.arr .num, false⟩] rfl
    (.seq (.ret (.prim (.numBin .add) (.cons (.var .here) (.cons (.var (.there .here)) .nil)))) .nil))

def sumReduceDef : FunDef TT0 :=
  { name := "sumReduce", args := .cons (.arr .num) .nil, ret := .num,
    lam := .sync [⟨.arr .num, false⟩] rfl
      (.seq (.ret (.builtin (.arrReduce .num .num) (.cons (.var .here) (.cons addCb (.cons (.lit (.num 0)) .nil))))) .nil) }

def prog : Program TT0 := { funs := [sumLoopDef, sumReduceDef], globals := [], main := .nil }

theorem sumLoop_call (I : Impl) (vs : Vals TT0 [.arr .num]) :
    callFun I prog sumLoopRef vs = applyLam I prog sumLoopDef.lam .nil vs := by
  rw [callFun.eq_1]; rfl

theorem sumReduce_call (I : Impl) (vs : Vals TT0 [.arr .num]) :
    callFun I prog sumReduceRef vs = applyLam I prog sumReduceDef.lam .nil vs := by
  rw [callFun.eq_1]; rfl

theorem foldl_num {β : Type} (f : F64 → β → F64) (z : F64) (l : List β) :
    l.foldl (fun (acc : Val TT0 .num) x => Val.num (f acc.toNum x)) (Val.num z) = Val.num (l.foldl f z) := by
  induction l generalizing z with
  | nil => rfl
  | cons x l ih => exact ih (f z x)

theorem afoldl_num {β : Type} (g : Val TT0 .num → β → F64) (z : F64) (l : Array β) :
    l.foldl (fun acc x => Val.num (g acc x)) (Val.num z) = Val.num (l.foldl (fun s x => g (.num s) x) z) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  generalize l.toList = l
  induction l generalizing z with
  | nil => rfl
  | cons x l ih => exact ih (g (.num z) x)

/-- The common meaning: a left fold of IEEE addition (no exactness assumption needed). -/
def sumSpec (xs : List (Val TT0 .num)) : F64 := xs.foldl (fun s x => s + x.toNum) 0

theorem sumReduce_spec (I : Impl) (a : Nat) (xs : Array (Val TT0 .num)) (w : World TT0)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I prog sumReduceRef (.cons (.arr a) .nil)) w =
      some (.ok (.num (sumSpec xs.toList)), w) := by
  rw [sumReduce_call]
  simp only [sumReduceDef, addCb, ts_sym]
  rw [arrReduce_pure' I prog a xs _ _ (fun acc x => .num (acc.toNum + x.toNum)) _ w hw]
  · simp [ts_sym, sumSpec, afoldl_num]
  · intro vs w'
    match vs with
    | .cons acc (.cons x (.cons i (.cons arr .nil))) => simp [ts_sym]

/-- The loop body of `sumLoop` (in context `[x, s, xs]`). -/
abbrev sumBody : Block TT0 [⟨.num, false⟩, ⟨.num, true⟩, ⟨.arr .num, false⟩] .num :=
  .seq (.assign (.there .here) (.prim (.numBin .add) (.cons (.var (.there .here)) (.cons (.var .here) .nil)))) .nil

theorem sumLoop_spec (I : Impl) (a : Nat) (xs : Array (Val TT0 .num)) (w : World TT0)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I prog sumLoopRef (.cons (.arr a) .nil)) w =
      some (.ok (.num (sumSpec xs.toList)), w) := by
  rw [sumLoop_call]
  simp only [sumLoopDef, ts_sym]
  have hk : KeepsCell I prog sumBody (.arr .num) a xs := by
    intro x env w₁ w₂ r h₁ h₂
    cases env with | cons s env =>
    simp [ts_sym] at h₂
    obtain ⟨-, rfl⟩ := h₂
    exact h₁
  rw [evalForOf_eq_forList I prog sumBody a xs hk _ w hw]
  obtain ⟨env', w', hrun, hinv⟩ := forList_inv I prog sumBody
    (fun done env w₁ => env = .cons (.num (sumSpec done)) (.cons (.arr a) .nil) ∧ w₁ = w) xs.toList
    (by
      intro done x env w₁ ⟨henv, hw₁⟩
      subst henv
      refine ⟨Env.cons x (Env.cons (Val.num (sumSpec done + x.toNum)) (Env.cons (Val.arr a) Env.nil)), w₁,
        by simp [ts_sym], ?_, hw₁⟩
      simp [sumSpec, List.foldl_append])
    [] (Env.cons (Val.num 0) (Env.cons (Val.arr a) Env.nil)) w ⟨by simp [sumSpec], rfl⟩
  obtain ⟨rfl, rfl⟩ := hinv
  simp [hrun, ts_sym]

/-- **Differential equivalence**: the loop and the `reduce` versions agree on every input
array and every world (same result, same final world). -/
theorem sumLoop_eq_sumReduce (I : Impl) (a : Nat) (xs : Array (Val TT0 .num)) (w : World TT0)
    (hw : w.heap.get? (.arr .num, a) = some xs) :
    exec (callFun I prog sumLoopRef (.cons (.arr a) .nil)) w =
      exec (callFun I prog sumReduceRef (.cons (.arr a) .nil)) w := by
  rw [sumLoop_spec I a xs w hw, sumReduce_spec I a xs w hw]

#print axioms sumLoop_eq_sumReduce
