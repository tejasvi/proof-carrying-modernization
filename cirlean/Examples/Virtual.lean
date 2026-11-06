import CIR
import Examples.Gen.Virtual

/-!
  Virtual dispatch (`Examples/cpp/virtual.cpp`).

  An object's vptr holds `Ptr.vtable vt i k` (slot `k` of array `i` of the
  vtable global `vt`); a virtual call reads the slot from the module's vtable
  initializer and calls the overrider with `this` adjusted to the derived
  object. Symbolic execution follows the dynamic type: `rect_area` and
  `square_area` call `area_of(const Shape&)`, which dispatches to
  `Rect::area` (inherited by `Square`).
-/

open CIR Gen.Virtual

set_option maxHeartbeats 4000000

namespace Examples.Virtual

/-- `int rect_area(int w, int h) { Rect r(w, h); return area_of(r); }` -/
theorem rect_area_spec (w h : Int) (m : Mem)
    (hw : -2147483648 ≤ w ∧ w ≤ 2147483647) (hh : -2147483648 ≤ h ∧ h ≤ 2147483647)
    (hwh : -2147483648 ≤ w * h ∧ w * h ≤ 2147483647) :
    Returns ctx fn_rect_area.sym [.int w, .int h] m (fun v _ => v = some (.int (w * h))) := by
  cir_start
  cir_vcg

/-- `int square_area(int s) { Square q(s); return area_of(q); }`: two levels of
inheritance, the overrider is inherited from `Rect`. -/
theorem square_area_spec (s : Int) (m : Mem) (hs : -2147483648 ≤ s ∧ s ≤ 2147483647)
    (hss : -2147483648 ≤ s * s ∧ s * s ≤ 2147483647) :
    Returns ctx fn_square_area.sym [.int s] m (fun v _ => v = some (.int (s * s))) := by
  cir_start
  cir_vcg

/-- `area_of` on any object whose dynamic type is `Rect`, given by its vptr. -/
@[cir_spec]
theorem area_of_rect (b : Nat) (w h : Int) (k : BlockKind) (m : Mem) (hb : b < m.next)
    (ho : m.blocks b = some ⟨k, true, .record "Rect",
      .agg [.agg [.ptr (.vtable "_ZTV4Rect" 0 2)], .int w, .int h]⟩)
    (hw : -2147483648 ≤ w ∧ w ≤ 2147483647) (hh : -2147483648 ≤ h ∧ h ≤ 2147483647)
    (hwh : -2147483648 ≤ w * h ∧ w * h ≤ 2147483647) :
    Returns ctx fn_area_of.sym [.ptr (.loc b [.idx 0])] m (fun v m' =>
      v = some (.int (w * h)) ∧ Frame m m' []) := by
  cir_start
  cir_vcg

end Examples.Virtual
