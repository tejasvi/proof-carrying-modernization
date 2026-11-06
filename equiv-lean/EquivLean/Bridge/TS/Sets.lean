import EquivLean.Bridge.TS.Behaves

/-!
# StrictTS bridge: `Set` membership, `includes`, and `filter` with a heap-reading callback

Lemmas for refactorings that replace `arr.includes(x)` by a `Set` built from `arr`
(`new Set(arr)` and `s.has(x)`), as in es-toolkit's `difference`/`intersection` performance
commits (`Demo/TS/EsToolkit.lean`).

* SameValueZero on numbers (`Conv.svz .num`, the key equality of `Set`/`Map` and of
  `Array.prototype.includes`) is an equivalence (`svz_num_equiv`), and the key normalisation of
  `Set` insertion (`-0` stored as `+0`) does not change it (`svz_normKey_num`).
* The set built by `new Set(ys)` (`setOfArr`, a fold of `JSMap.set` over the normalised
  elements) contains `x` exactly when `ys.includes(x)` (`setOfArr_has_num`).
* `arr.filter(f)` when the callback `f` is pure *at the world where `filter` calls it*
  (`arrFilter_pure_at`): StrictTS's `arrFilter_pure'` asks for a callback that is pure in every
  world, which a closure reading a captured array or set (`secondArr.includes(item)`,
  `secondSet.has(item)`) is not.
-/

namespace EquivLean.TS
open StrictTS JS

variable {TT : TypeTable}

/-! ## SameValueZero on numbers -/

theorem numSVZ_refl (x : F64) : Conv.numSVZ x x = true := by
  cases x with
  | nan => rfl
  | inf s => cases s <;> rfl
  | fin a => simp [Conv.numSVZ, Conv.numEq]

theorem numSVZ_symm {x y : F64} (h : Conv.numSVZ x y = true) : Conv.numSVZ y x = true := by
  cases x <;> cases y <;> simp_all [Conv.numSVZ, Conv.numEq]
  · rename_i a b
    rcases h with ⟨h1, h2⟩ | h
    · exact .inl ⟨h2, h1⟩
    · exact .inr h.symm

theorem numSVZ_trans {x y z : F64} (h₁ : Conv.numSVZ x y = true) (h₂ : Conv.numSVZ y z = true) :
    Conv.numSVZ x z = true := by
  cases x <;> cases y <;> cases z <;> simp_all [Conv.numSVZ, Conv.numEq]
  · rename_i a b c
    rcases h₁ with ⟨h1a, h1b⟩ | h1 <;> rcases h₂ with ⟨h2a, h2b⟩ | h2 <;> subst_vars <;> simp_all

/-- SameValueZero on `number` values is an equivalence (the `Set`/`Map` key equality). -/
theorem svz_num_equiv : JSMap.Equiv (Conv.svz (TT := TT) .num) where
  refl a := by cases a; exact numSVZ_refl _
  symm a b h := by cases a; cases b; exact numSVZ_symm h
  trans a b c h₁ h₂ := by cases a; cases b; cases c; exact numSVZ_trans h₁ h₂

/-- The key normalisation of `Set` insertion (`-0` becomes `+0`) keeps SameValueZero. -/
theorem svz_normKey_num (v x : Val TT .num) :
    Conv.svz .num (normKey .num v) x = Conv.svz .num v x := by
  cases v with
  | num y =>
    cases x with
    | num z =>
      cases y with
      | nan => rfl
      | inf s => rfl
      | fin a =>
        by_cases ha : a.man = 0
        · have hz : F64.zero = .fin ⟨false, 0, -1074, by decide⟩ := by
            simp [F64.zero, F64.mkFin]
          have hn : normKey .num (Val.num (TT := TT) (.fin a)) = .num F64.zero := by
            simp [normKey, ha]
          rw [hn, hz]
          cases z with
          | nan => rfl
          | inf s => rfl
          | fin b =>
            show ((0 = 0 && b.man = 0) || decide (_ = b)) = ((a.man = 0 && b.man = 0) || decide (a = b))
            by_cases hb : b.man = 0
            · simp [ha, hb]
            · have h1 : ¬ (⟨false, 0, -1074, by decide⟩ : Fin64) = b := fun e => hb (e ▸ rfl)
              have h2 : ¬ a = b := fun e => hb (e ▸ ha)
              simp [hb, h1, h2]
        · have hn : normKey .num (Val.num (TT := TT) (.fin a)) = .num (.fin a) := by
            simp [normKey, ha]
          rw [hn]

/-! ## `new Set(ys).has(x)` is `ys.includes(x)` -/

theorem foldl_set_has {K : Type} (eq : K → K → Bool) (hE : JSMap.Equiv eq) (nk : K → K)
    (hnk : ∀ y x, eq (nk y) x = eq y x) (l : List K) (m : JSMap K Unit) (x : K) :
    (l.foldl (fun m y => m.set eq (nk y) ()) m).has eq x = (m.has eq x || l.any (fun y => eq y x)) := by
  induction l generalizing m with
  | nil => simp
  | cons y l ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih, JSMap.has_eq, JSMap.has_eq, JSMap.get?_set hE, hnk]
    cases eq y x <;> simp

/-- The set built by `new Set(ys)` (numbers) has `x` exactly when `ys.includes(x)`. -/
theorem setOfArr_has_num (ys : Array (Val TT .num)) (x : Val TT .num) :
    (ys.foldl (fun (m : JSMap (Val TT .num) Unit) y => m.set (Conv.svz .num) (normKey .num y) ())
        {}).has (Conv.svz .num) x = ys.any (fun y => Conv.svz .num y x) := by
  rw [← Array.foldl_toList, foldl_set_has _ svz_num_equiv _ svz_normKey_num, ← Array.any_toList]
  simp [JSMap.has_eq, JSMap.get?, JSMap.lookup]

/-! ## `filter` with a callback that is pure where it is called -/

/-- `arr.filter(f)` when `f` returns `g x` and keeps the world at the world where `filter`
calls it (after allocating the result array). -/
theorem arrFilter_pure_at (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool))
    (g : Val TT t → Val TT .bool) (w : World TT)
    (hw : w.heap.get? (.arr t, a) = some xs) (ha : a ≠ w.next)
    (hf : ∀ vs, exec (applyFn I P f vs)
        { w with heap := w.heap.insert (.arr t, w.next) (#[] : Array (Val TT t)), next := w.next + 1 } =
      some (.ok (g vs.a0),
        { w with heap := w.heap.insert (.arr t, w.next) (#[] : Array (Val TT t)), next := w.next + 1 })) :
    exec (evalBuiltin I P (.arrFilter t) (.cons (.arr a) (.cons f .nil))) w =
      some (.ok (.arr w.next), { w with
        heap := w.heap.insert (.arr t, w.next) (xs.filter (fun x => (g x).toBool)),
        next := w.next + 1 }) := by
  rw [evalBuiltin.eq_def]
  simp only [exec_bind, exec_readArr, hw, Vals.a0_cons, Vals.a1_cons, Val.arrAddr_arr, exec_alloc]
  have hw1 : (w.heap.insert (.arr t, w.next) (#[] : Array (Val TT t))).get? (.arr t, a) = some xs := by
    rw [heap_get_insert_addr_ne _ _ _ _ (Ne.symm ha), hw]
  rw [foldlM_range_pure' xs _ (fun acc x => if (g x).toBool = true then acc.push x else acc) _]
  · rw [foldl_push_filter]
    simp only [exec_writeArr, heap_insert_insert, exec_pure, Array.empty_append, toArray_filter_toList]
  · intro acc k hk
    simp only [exec_bind, exec_readArr, hw1, hk, dite_true]
    rw [hf]; simp

end EquivLean.TS
