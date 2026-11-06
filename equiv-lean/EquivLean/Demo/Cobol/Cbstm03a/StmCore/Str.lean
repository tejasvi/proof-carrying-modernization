/-
# `STRING … DELIMITED BY` on symbolic data: first tokens

`STRING src DELIMITED BY d` contributes the bytes of `src` before the first occurrence of `d`
(`Sem.strPiece`, by `Sem.findSub`).  For a symbolic source that search does not reduce;
`strPiece_single` and `strPiece_double` state it as the first token: `tokB b src` (the bytes
before the first byte `b`: `' '` in `5000-CREATE-STATEMENT`, `'*'` in the HTML lines) and
`tok2 src` (the bytes before the first two spaces, `5200-WRITE-HTML-NMADBS`).  `strRun_one`
puts the pieces into the receiver from position 1 in closed form: `ovw J dst` overwrites the
receiver's first bytes with the pieces' bytes `J`, as many as fit (the overflow flag tells
whether some did not).
-/
import Cobol

namespace Cobol.StmCore

/-- The bytes before the first byte `b`. -/
def tokB (b : UInt8) (src : List UInt8) : List UInt8 := src.takeWhile (· != b)

/-- The bytes before the first two consecutive spaces. -/
def tok2 : List UInt8 → List UInt8
  | x :: y :: rest => if x = 64 ∧ y = 64 then [] else x :: tok2 (y :: rest)
  | l => l

/-- `dst` with its first bytes replaced by those of `J` (as many as fit). -/
def ovw : List UInt8 → List UInt8 → List UInt8
  | b :: bs, _ :: d => b :: ovw bs d
  | [], d => d
  | _ :: _, [] => []

theorem length_ovw : ∀ (J dst : List UInt8), (ovw J dst).length = dst.length
  | b :: bs, _ :: d => by simp [ovw, length_ovw bs d]
  | [], _ => rfl
  | _ :: _, [] => rfl

theorem tokB_nil (b : UInt8) : tokB b [] = [] := rfl

theorem tokB_cons (b x : UInt8) (xs : List UInt8) :
    tokB b (x :: xs) = if x = b then [] else x :: tokB b xs := by
  by_cases h : x = b <;> simp [tokB, List.takeWhile_cons, h]

theorem tok2_nil : tok2 [] = [] := rfl

theorem tok2_single (x : UInt8) : tok2 [x] = [x] := rfl

theorem tok2_cons_cons (x y : UInt8) (rest : List UInt8) :
    tok2 (x :: y :: rest) = if x = 64 ∧ y = 64 then [] else x :: tok2 (y :: rest) := rfl

theorem strPiece_def (src d : List UInt8) :
    Sem.strPiece src (some d) = match Sem.findSub d src with
      | some i => src.take i
      | none => src := rfl

theorem strPiece_single (b : UInt8) :
    ∀ src : List UInt8, Sem.strPiece src (some [b]) = tokB b src
  | [] => rfl
  | x :: xs => by
    have ih := strPiece_single b xs
    rw [strPiece_def] at ih ⊢
    rw [Sem.findSub]
    by_cases h : x = b
    · subst h
      have hp : [x].isPrefixOf (x :: xs) = true := by simp [List.isPrefixOf]
      simp only [hp, ↓reduceIte, List.take_zero, tokB, List.takeWhile_cons, bne_self_eq_false,
        Bool.false_eq_true]
    · have hp : [b].isPrefixOf (x :: xs) = false := by
        simp [List.isPrefixOf, Ne.symm h]
      have hx : (x != b) = true := by simp [h]
      simp only [hp, Bool.false_eq_true, ↓reduceIte, tokB, List.takeWhile_cons, hx]
      rw [tokB] at ih
      revert ih
      cases Sem.findSub [b] xs with
      | none => intro ih; simp only [Option.map_none]; rw [← ih]
      | some i => intro ih; simp only [Option.map_some, List.take_succ_cons]; rw [← ih]

theorem strPiece_double : ∀ src : List UInt8, Sem.strPiece src (some [64, 64]) = tok2 src
  | [] => rfl
  | [x] => by
    rw [strPiece_def, Sem.findSub, Sem.findSub]
    have hp : [(64 : UInt8), 64].isPrefixOf [x] = false := by
      by_cases hx : x = 64 <;> simp [List.isPrefixOf, hx]
    simp [hp, tok2]
  | x :: y :: rest => by
    have ih := strPiece_double (y :: rest)
    rw [strPiece_def] at ih ⊢
    rw [Sem.findSub]
    by_cases h : x = 64 ∧ y = 64
    · obtain ⟨rfl, rfl⟩ := h
      have hp : [(64 : UInt8), 64].isPrefixOf (64 :: 64 :: rest) = true := by simp [List.isPrefixOf]
      simp only [hp, ↓reduceIte, List.take_zero, tok2, and_self]
    · have hp : [(64 : UInt8), 64].isPrefixOf (x :: y :: rest) = false := by
        by_cases hx : x = 64
        · have hy : y ≠ 64 := fun hy => h ⟨hx, hy⟩
          subst hx; simp [List.isPrefixOf, Ne.symm hy]
        · simp [List.isPrefixOf, Ne.symm hx]
      have ht : tok2 (x :: y :: rest) = x :: tok2 (y :: rest) := by
        simp only [tok2, h, ↓reduceIte]
      simp only [hp, Bool.false_eq_true, ↓reduceIte, ht]
      revert ih
      cases Sem.findSub [64, 64] (y :: rest) with
      | none => intro ih; simp only [Option.map_none]; rw [← ih]
      | some i => intro ih; simp only [Option.map_some, List.take_succ_cons]; rw [← ih]

/-- `strPiece_single` on the unfolded `strPiece` (the form symbolic execution meets). -/
theorem strPiece_match_single (b : UInt8) (src : List UInt8) :
    Sem.strPiece.match_1 (fun _ => List UInt8) (Sem.findSub [b] src) (fun i => List.take i src)
      (fun _ => src) = tokB b src := strPiece_single b src

/-- `strPiece_double` on the unfolded `strPiece`. -/
theorem strPiece_match_double (src : List UInt8) :
    Sem.strPiece.match_1 (fun _ => List UInt8) (Sem.findSub [64, 64] src) (fun i => List.take i src)
      (fun _ => src) = tok2 src := strPiece_double src

theorem set_append_cons {α : Type _} (A B : List α) (c b : α) :
    (A ++ c :: B).set A.length b = A ++ b :: B := by
  induction A with
  | nil => rfl
  | cons a A ih => simp [ih]

/-- `strPut` from just after a prefix `A`: the bytes of `x` overwrite `B`. -/
theorem strPut_ovw (x : List UInt8) :
    ∀ (A B : List UInt8), Sem.strPut (A ++ B) (A.length + 1) x =
      (A ++ ovw x B, A.length + 1 + min x.length B.length, decide (B.length < x.length)) := by
  induction x with
  | nil => intro A B; simp [Sem.strPut, ovw]
  | cons b bs ih =>
    intro A B
    cases B with
    | nil =>
      have h : (A ++ []).length < A.length + 1 := by simp
      simp [Sem.strPut, ovw]
    | cons c B =>
      have h : ¬ (A ++ c :: B).length < A.length + 1 := by simp
      rw [Sem.strPut, ite_eq_right_of_eq_false _ _ (eq_false h), show A.length + 1 - 1 = A.length by omega, set_append_cons,
        show A ++ b :: B = (A ++ [b]) ++ B by simp,
        show A.length + 1 + 1 = (A ++ [b]).length + 1 by simp, ih (A ++ [b]) B]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp [ovw]
      · simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]; omega
      · simp only [List.length_cons, decide_eq_decide]; omega

theorem ovw_append (x J B : List UInt8) (h : x.length ≤ B.length) :
    ovw (x ++ J) B = x ++ ovw J (B.drop x.length) := by
  induction x generalizing B with
  | nil => rfl
  | cons b bs ih =>
    cases B with
    | nil => simp at h
    | cons c B =>
      simp only [List.cons_append, ovw, List.length_cons, List.drop_succ_cons]
      rw [ih B (by simp at h; omega)]

theorem ovw_append_over (x J B : List UInt8) (h : B.length < x.length) :
    ovw (x ++ J) B = ovw x B := by
  induction x generalizing B with
  | nil => simp at h
  | cons b bs ih =>
    cases B with
    | nil => rfl
    | cons c B =>
      simp only [List.cons_append, ovw]
      rw [ih B (by simp at h; omega)]

theorem ovw_eq_append_drop (x B : List UInt8) (h : x.length ≤ B.length) :
    ovw x B = x ++ B.drop x.length := by
  have := ovw_append x [] B h
  simpa [ovw] using this

/-- `strRun` from just after a prefix `A`: the pieces' bytes overwrite `B`. -/
theorem strRun_ovw (xs : List (List UInt8)) :
    ∀ (A B : List UInt8), Sem.strRun (A ++ B) (A.length + 1) xs =
      (A ++ ovw xs.flatten B, A.length + 1 + min xs.flatten.length B.length,
        decide (B.length < xs.flatten.length)) := by
  induction xs with
  | nil => intro A B; simp [Sem.strRun, ovw]
  | cons x xs ih =>
    intro A B
    rw [Sem.strRun, strPut_ovw]
    by_cases hov : B.length < x.length
    · simp only [hov, decide_true]
      simp only [List.flatten_cons, List.length_append]
      rw [ovw_append_over x _ B hov]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · simp only; omega
      · simp only [eq_comm (a := true), decide_eq_true_eq]; omega
    · simp only [hov, decide_false]
      have hx : x.length ≤ B.length := by omega
      rw [ovw_eq_append_drop x B hx, ← List.append_assoc,
        show A.length + 1 + min x.length B.length = (A ++ x).length + 1 by simp; omega,
        ih (A ++ x) (B.drop x.length)]
      simp only [List.flatten_cons, List.length_append, List.length_drop, List.append_assoc]
      rw [ovw_append x _ B hx]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · simp only; omega
      · simp only [decide_eq_decide]; omega

/-- `STRING … INTO dst` (no pointer): the pieces overwrite `dst` from its first byte. -/
theorem strRun_one (dst : List UInt8) (xs : List (List UInt8)) :
    Sem.strRun dst 1 xs =
      (ovw xs.flatten dst, 1 + min xs.flatten.length dst.length,
        decide (dst.length < xs.flatten.length)) := by
  simpa using strRun_ovw xs [] dst

end Cobol.StmCore
