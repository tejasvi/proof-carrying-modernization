import EquivLean.Modernize.Cbact01c.JavaRunDefs

/-!
# CBACT01C → Java: string concatenation recipes, one character at a time

`concatRecipe` unfolded by its equations puts the rest of the recipe under three branches at
every character; on the long labels of CBACT01C (`"ACCT-CURR-CYC-CREDIT    :\u0001"`) the
symbolic execution then does not finish. These equations take one constant character, or the
argument at `\u0001`, without the branches.
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec

namespace EquivLean.Modernize.Cbact01c.Java

theorem concatRecipe_nil' (P : Program) (consts : List Value) (ts : List JType) (vs : List Value)
    (σ : Jimple.State) (acc : JStr) :
    concatRecipe P consts [] ts vs σ acc = .ret (retObj (.str acc) σ) := rfl

theorem concatRecipe_const (P : Program) (consts : List Value) (c : JChar) (rest : JStr)
    (ts : List JType) (vs : List Value) (σ : Jimple.State) (acc : JStr) (h1 : c ≠ 1) (h2 : c ≠ 2) :
    concatRecipe P consts (c :: rest) ts vs σ acc = concatRecipe P consts rest ts vs σ (acc ++ [c]) := by
  rw [concatRecipe.eq_def]
  simp only [h1, h2, ↓reduceIte]

theorem concatRecipe_arg (P : Program) (consts : List Value) (rest : JStr) (t : JType)
    (ts : List JType) (v : Value) (vs : List Value) (σ : Jimple.State) (acc : JStr) :
    concatRecipe P consts (1#16 :: rest) (t :: ts) (v :: vs) σ acc =
      Native.valueOfArg P t v σ fun s σ' => concatRecipe P consts rest ts vs σ' (acc ++ s) := by
  simp only [concatRecipe]
  rw [if_pos (by decide)]

end EquivLean.Modernize.Cbact01c.Java
