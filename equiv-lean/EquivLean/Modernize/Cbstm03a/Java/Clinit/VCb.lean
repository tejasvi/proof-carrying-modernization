import EquivLean.Modernize.Cbstm03a.Java.Clinit.Defs

/-! `<clinit>`'s verification conditions, part 2: runs of 16 array stores between cut points (the array
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

theorem store0_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 0)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 38 fr σ := by
  store_run

theorem store16_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 16)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 54 fr σ := by
  store_run

theorem store32_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 32)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 70 fr σ := by
  store_run

theorem store48_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 48)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 86 fr σ := by
  store_run

theorem store64_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 64)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 102 fr σ := by
  store_run

theorem store80_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 80)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 118 fr σ := by
  store_run

theorem store96_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 96)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 134 fr σ := by
  store_run

theorem store112_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr)
    (ha : fr.get 0 = some (.ref a)) (hh : σ.heap a = some (.array (.prim .int) (arrP 112)))
    (hσ : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 150 fr σ := by
  store_run

end EquivLean.Modernize.Cbstm03a.Java
