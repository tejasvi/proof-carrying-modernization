import Examples.Cbcus01c
import Cobol.Logic.FuelMono
/-! Fuel monotonicity in use: `cbcus01c_lists` (fuel `n + 20` for any `n > recs.length`) holds
for every fuel `F ≥ recs.length + 21`. -/
open Cobol CardDemo Cbcus01c

example (m : Mem) (hm : m.size = 1023) (recs : List (List UInt8))
    (hrecs : ∀ r ∈ recs, r.length = 500) (F : Nat) (hF : recs.length + 21 ≤ F) :
    let r := Cbcus01c.run {} F (Cbcus01c.initState m [(1, recs)])
    r.1 = .stop .goback ∧ displays r.2 = [startMsg] ++ recs.flatMap (fun r => [r, r]) ++ [endMsg] := by
  have h := cbcus01c_lists m hm recs (recs.length + 1) hrecs (by omega)
  intro r
  have e : r = Cbcus01c.run {} (recs.length + 1 + 20) (Cbcus01c.initState m [(1, recs)]) :=
    Program.run_mono _ _ (by omega) (by rw [h.1]; decide)
  rw [e]; exact h
