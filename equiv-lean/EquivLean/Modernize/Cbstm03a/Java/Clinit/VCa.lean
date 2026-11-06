import EquivLean.Modernize.Cbstm03a.Java.Clinit.Defs

/-! `<clinit>`'s verification conditions, part 1: the entry path (statement 0, by the class's
initialization state) and the `putstatic` runs between the cut points 1, 13, 25, 33 and 38. -/

open Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

/-- The weakest precondition of `<clinit>`'s body from statement `pc`, with the contract's cut list and
postcondition for the entry arguments `args` and state `σ0`. -/
local notation "clinitWP " args:max σ0:max pc:max fr:max σ:max =>
  bodyWP Gen.prog (callWP Gen.prog clinitT.env 0) Gen.Cbstm03a.«<clinit>()» (Invariants.inst clinitInv args σ0)
    (Spec.post clinitSpec args σ0) 100 pc fr σ

set_option maxRecDepth 8000
set_option maxHeartbeats 0

theorem entry_done_vc (args : List Value) (σ0 : State) (h : σ0.initOf "Cbstm03a" = .done) :
    clinitWP args σ0 0 (Frame.init true args) σ0 := by
  jvc [clinitT, clinitSpec, clinitInv, storeInv, Targets]

theorem entry_failed_vc (args : List Value) (σ0 : State) (h : σ0.initOf "Cbstm03a" = .failed) :
    clinitWP args σ0 0 (Frame.init true args) σ0 := by
  jvc [clinitT, clinitSpec, clinitInv, storeInv, Targets]

theorem entry_none_vc (args : List Value) (σ0 : State) (h : σ0.initOf "Cbstm03a" = .none) :
    clinitWP args σ0 0 (Frame.init true args) σ0 := by
  jvc [clinitT, clinitSpec, clinitInv, storeInv, Targets, List.filter_cons, List.filter_nil, runClinits]

theorem cut1_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (h : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 1 fr σ := by
  jvc [clinitT, clinitSpec, clinitInv, storeInv, Targets]

theorem cut13_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (h : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 13 fr σ := by
  jvc [clinitT, clinitSpec, clinitInv, storeInv, Targets]

theorem cut25_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (h : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 25 fr σ := by
  jvc [clinitT, clinitSpec, clinitInv, storeInv, Targets]

theorem cut33_vc (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (h : σ.initOf "Cbstm03a" = .done) : clinitWP args σ0 33 fr σ := by
  jvc [clinitT, clinitSpec, clinitInv, storeInv, Targets, arrP_length]
  all_goals with_unfolding_all rfl

end EquivLean.Modernize.Cbstm03a.Java
