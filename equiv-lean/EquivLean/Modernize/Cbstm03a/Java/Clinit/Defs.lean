import EquivLean.Modernize.Cbstm03a.Java.Iface1

/-!
# CBSTM03A → Java: the contract of `Cbstm03a.<clinit>`

`<clinit>` stores 37 constants into statics, builds the `int[256]` table `CP037` with 256 array stores and
stores it into the static `CP037`. Its contract (`clinitSpec`) holds from every entry state: the first
`putstatic` initializes the class when it is not (running `<clinit>` itself, answered by this same contract),
throws `NoClassDefFoundError` when its initialization failed, and does nothing when it is done. On a normal
return the static `CP037` holds an allocated `int` array with the entries `cp037Arr`.
-/

open Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

abbrev clinitRef : MethodRef := Gen.Cbstm03a.«<clinit>()».ref

/-- The array `CP037` after the first `k` stores of `<clinit>`: the table's first `k` entries, then zeros. -/
@[irreducible] def arrP (k : Nat) : List Value := cp037Arr.take k ++ List.replicate (256 - k) (.int 0)

theorem cp037Arr_length : cp037Arr.length = 256 := by decide +kernel

theorem arrP_length (k : Nat) : (arrP k).length = 256 := by
  unfold arrP
  simp only [List.length_append, List.length_take, List.length_replicate, cp037Arr_length]
  omega

theorem arrP_zero : List.replicate 256 (Value.int 0) = arrP 0 := by decide +kernel

theorem arrP_full : arrP 256 = cp037Arr := by decide +kernel

/-- `<clinit>`: from any state; a normal return leaves the class initialized if it was and the table in the
static `CP037`; an exception only when the class's initialization had failed. -/
def clinitSpec : Spec := Spec.of (fun _ _ => True)
  (fun _ σ _ σ' => (σ.initOf "Cbstm03a" = .done → σ'.initOf "Cbstm03a" = .done) ∧
    ∃ a, σ'.static ("Cbstm03a", "CP037") = some (.ref a) ∧
      σ'.heap a = some (.array (.prim .int) cp037Arr) ∧ a < σ'.next)
  (fun _ σ _ _ => σ.initOf "Cbstm03a" = .failed)

/-- The contract table: `<clinit>` calls itself (through the class initialization of its first `putstatic`). -/
def clinitT : Contracts := [(clinitSig "Cbstm03a", clinitSpec)]

/-- At statement `38 + k`: local 0 (`$r0`) holds the array after `k` stores, the class is initialized. -/
def storeInv (k : Nat) (fr : Frame) (σ : State) : Prop :=
  ∃ a, fr.get 0 = some (.ref a) ∧ σ.heap a = some (.array (.prim .int) (arrP k)) ∧
    σ.initOf "Cbstm03a" = .done

/-- Cut points (they keep each symbolic run short): after the first `putstatic` (statement 1) the class is
initialized, and it stays so; from statement 38 on, every 16 stores. -/
def clinitInv : Invariants := [
  (1, fun _ _ _ σ => σ.initOf "Cbstm03a" = .done),
  (13, fun _ _ _ σ => σ.initOf "Cbstm03a" = .done),
  (25, fun _ _ _ σ => σ.initOf "Cbstm03a" = .done),
  (33, fun _ _ _ σ => σ.initOf "Cbstm03a" = .done),
  (38, fun _ _ fr σ => storeInv 0 fr σ),
  (54, fun _ _ fr σ => storeInv 16 fr σ),
  (70, fun _ _ fr σ => storeInv 32 fr σ),
  (86, fun _ _ fr σ => storeInv 48 fr σ),
  (102, fun _ _ fr σ => storeInv 64 fr σ),
  (118, fun _ _ fr σ => storeInv 80 fr σ),
  (134, fun _ _ fr σ => storeInv 96 fr σ),
  (150, fun _ _ fr σ => storeInv 112 fr σ),
  (166, fun _ _ fr σ => storeInv 128 fr σ),
  (182, fun _ _ fr σ => storeInv 144 fr σ),
  (198, fun _ _ fr σ => storeInv 160 fr σ),
  (214, fun _ _ fr σ => storeInv 176 fr σ),
  (230, fun _ _ fr σ => storeInv 192 fr σ),
  (246, fun _ _ fr σ => storeInv 208 fr σ),
  (262, fun _ _ fr σ => storeInv 224 fr σ),
  (278, fun _ _ fr σ => storeInv 240 fr σ)]

/-- Two writes of one address: the second wins (keeps the state of a run of array stores one update deep). -/
theorem setObj_setObj_same (σ : State) (a : Addr) (o o' : Obj) :
    (σ.setObj a o).setObj a o' = σ.setObj a o' := by
  cases σ; simp [State.setObj]

theorem clinitOf_eq : Gen.prog.clinitOf "Cbstm03a" = some clinitRef.decl := rfl

theorem staticDecl_clinit : Gen.prog.staticDecl (clinitSig "Cbstm03a") = true := rfl

theorem selectStatic_clinit : Gen.prog.selectStatic (clinitSig "Cbstm03a") = .jimple clinitRef := rfl

theorem clinitT_env : clinitT.env (clinitSig "Cbstm03a") = some clinitSpec := rfl

end EquivLean.Modernize.Cbstm03a.Java
