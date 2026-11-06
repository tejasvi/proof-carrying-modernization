/-
`examples/Maps/count.ts`: after `countWords(words)`, the returned `Map` sends every string to its
number of occurrences in `words` (and has no entry for strings that do not occur).
-/
import Maps.CountEx
import StrictTS.Proof.Tactics

open StrictTS JS CountEx F64

/-- Number of occurrences of `k` in `xs`. -/
def cnt (xs : List (Val TT .str)) (k : Val TT .str) : Nat := xs.countP (fun x => x.toStr == k.toStr)

/-- The specified content of the counting map after the words `xs`. -/
def countSpec (xs : List (Val TT .str)) (k : Val TT .str) : Option (Val TT .num) :=
  if cnt xs k = 0 then none else some (.num (ofNat (cnt xs k)))

/-- SameValueZero on string keys is string equality, an equivalence. -/
theorem svz_str (x y : Val TT .str) : Conv.svz .str x y = (x.toStr == y.toStr) := rfl

theorem svz_str_equiv : JSMap.Equiv (Conv.svz (TT := TT) .str) where
  refl a := by simp [svz_str]
  symm a b h := by rw [svz_str] at *; simp only [beq_iff_eq] at *; exact h.symm
  trans a b c h1 h2 := by simp_all [svz_str]

theorem cnt_snoc (xs : List (Val TT .str)) (x k : Val TT .str) :
    cnt (xs ++ [x]) k = cnt xs k + (if x.toStr == k.toStr then 1 else 0) := by
  simp [cnt, List.countP_append]

theorem cnt_congr (l : List (Val TT .str)) {k k' : Val TT .str} (h : k.toStr = k'.toStr) :
    cnt l k = cnt l k' := by
  simp [cnt, h]

theorem take_succ_snoc {xs : Array (Val TT .str)} {i : Nat} (hi : i < xs.size) :
    xs.toList.take (i + 1) = xs.toList.take i ++ [xs[i]] := by
  simp [List.take_add_one, hi]

theorem countWords_spec (I : Impl) (a : Nat) (xs : Array (Val TT .str)) (w : World TT)
    (hw : w.heap.get? (.arr .str, a) = some xs) (hsize : xs.size < 2 ^ 52) :
    ∃ m w', exec (callFun I program countWordsRef (.cons (.arr a) .nil)) w = some (.ok (.map w.next), w') ∧
      w'.heap.get? (.map .str .num, w.next) = some m ∧
      ∀ k, m.get? (Conv.svz .str) k = countSpec xs.toList k := by
  rw [countWords_call]
  simp only [countWordsDef, ts_sym]
  ts_forof xs using (fun i env w₁ =>
    env = .cons (.map w.next) (.cons (.arr a) .nil) ∧ w₁.heap.get? (.arr .str, a) = some xs ∧
      ∃ m, w₁.heap.get? (.map .str .num, w.next) = some m ∧
        ∀ k, m.get? (Conv.svz .str) k = countSpec (xs.toList.take i) k)
  case cell => rintro i env w₁ ⟨-, h, -⟩; exact h
  case step =>
    rintro i env w₁ hi ⟨rfl, harr, m, hm, hspec⟩
    have hc : cnt (xs.toList.take i) xs[i] < 2 ^ 52 := by
      have := List.countP_le_length (p := fun x => x.toStr == xs[i].toStr) (l := xs.toList.take i)
      simp only [List.length_take, Array.length_toList] at this
      simp only [cnt]; omega
    by_cases hz : cnt (xs.toList.take i) xs[i] = 0
    · simp (disch := first | decide | omega) [ts_sym, hm, harr, hspec, countSpec, hz]
      intro k
      rw [JSMap.get?_set svz_str_equiv, hspec]
      simp only [normKey, countSpec, take_succ_snoc hi, cnt_snoc, svz_str]
      by_cases hk : xs[i].toStr = k.toStr
      · simp [hk, ← cnt_congr _ hk, hz]
      · simp [hk]
    · simp (disch := first | decide | omega) [ts_sym, hm, harr, hspec, countSpec, hz]
      intro k
      rw [JSMap.get?_set svz_str_equiv, hspec]
      simp only [normKey, countSpec, take_succ_snoc hi, cnt_snoc, svz_str]
      by_cases hk : xs[i].toStr = k.toStr
      · simp [hk, ← cnt_congr _ hk, hz]
      · simp [hk]
  case init =>
    refine ⟨rfl, by simp [hw], ⟨{}, by simp, fun k => by simp [countSpec, cnt, JSMap.get?, JSMap.lookup]⟩⟩
  obtain ⟨rfl, -, m, hm, hspec⟩ := hinv
  refine ⟨m, w', by simp [ts_sym], hm, fun k => ?_⟩
  rw [hspec, List.take_of_length_le (by simp)]
