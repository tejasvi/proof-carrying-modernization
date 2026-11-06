import EquivLean.Modernize.Cbstm03a.Java.Clinit.Defs

/-! `<clinit>`'s verification conditions, part 3: runs of 16 array stores between cut points (the array
after the run is checked by evaluation). -/

open Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

/-- The weakest precondition of `<clinit>`'s body from statement `pc`, with the contract's cut list and
postcondition for the entry arguments `args` and state `σ0`. -/
local notation "clinitWP " args:max σ0:max pc:max fr:max σ:max =>
  bodyWP Gen.prog (callWP Gen.prog clinitT.env 0) Gen.Cbstm03a.«<clinit>()» (Invariants.inst clinitInv args σ0)
    (Spec.post clinitSpec args σ0) 100 pc fr σ

/-- One run of stores: symbolic execution, then the array equation by evaluation. -/
local macro "store_run" : tactic => `(tactic| (
  jvc [clinitT, clinitSpec, clinitInv, storeInv, Targets, arrP_length, setObj_setObj_same]
  all_goals first | (with_unfolding_all rfl) | (unfold arrP; decide)))

set_option maxRecDepth 8000
set_option maxHeartbeats 0

theorem store128_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 128)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 166 fr σ := by
  store_run

theorem store144_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 144)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 182 fr σ := by
  store_run

theorem store160_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 160)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 198 fr σ := by
  store_run

theorem store176_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 176)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 214 fr σ := by
  store_run

theorem store192_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 192)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 230 fr σ := by
  store_run

theorem store208_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 208)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 246 fr σ := by
  store_run

theorem store224_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 224)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 262 fr σ := by
  store_run

theorem store240_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 240)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 278 fr σ := by
  store_run

end EquivLean.Modernize.Cbstm03a.Java
