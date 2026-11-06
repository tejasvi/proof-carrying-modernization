import EquivLean.Bridge.Cir.PtrArgs
import EquivLean.Demo.Gen.Cir.POld
import EquivLean.Demo.Gen.Cir.PNew

/-!
# Demo: pointer arguments

`examples/cir/p_old.cpp` → `p_new.cpp`, the pointer functions of veriforch's CI demo:

* `sum_arr`: `for` → `while` over `a[i]` (element pointer steps into the caller's array);
* `swap`: the two writes in the other order (`a` and `b` may alias: one block and one position,
  one block and two positions, or two blocks);
* `get_or`: `if (p == 0) return d; return *p;` → `p ? *p : d`.

Each pointer argument comes with `∀ k q, x = .loc k q → k < m.next`: it is null, a function or
vtable pointer, or points into a block of the caller (a block at or above `m.next` would be a local
of the callee, which the two versions allocate differently).  No coupling invariant, case split or
memory fact is written: `equiv_cir` splits each pointer where the source first inspects it.
-/

namespace EquivLean.Demo.Cir.PtrArgs

open CIR EquivLean EquivLean.Cir EquivLean.Demo.Gen.Cir

set_option maxHeartbeats 4000000

theorem get_or_equiv (p : Ptr) (d : Int) (m : Mem) (hp : ∀ k q, p = .loc k q → k < m.next) :
    Equiv (ObsEq m) (evalCall PNew.ctx PNew.fn_get_or.sym [.ptr p, .int d] m)
      (evalCall POld.ctx POld.fn_get_or.sym [.ptr p, .int d] m) := by
  equiv_cir

-- a loop, both directions in one declaration: on cirlean bd8614f (heavier `cir_disch`) past 4M heartbeats
set_option maxHeartbeats 12000000 in
theorem sum_arr_equiv (a : Ptr) (n : Int) (m : Mem) (ha : ∀ k q, a = .loc k q → k < m.next) :
    Equiv (ObsEq m) (evalCall PNew.ctx PNew.fn_sum_arr.sym [.ptr a, .int n] m)
      (evalCall POld.ctx POld.fn_sum_arr.sym [.ptr a, .int n] m) := by
  equiv_cir

theorem swap_equiv (a b : Ptr) (m : Mem) (ha : ∀ k q, a = .loc k q → k < m.next)
    (hb : ∀ k q, b = .loc k q → k < m.next) :
    Equiv (ObsEq m) (evalCall PNew.ctx PNew.fn_swap.sym [.ptr a, .ptr b] m)
      (evalCall POld.ctx POld.fn_swap.sym [.ptr a, .ptr b] m) := by
  equiv_cir

end EquivLean.Demo.Cir.PtrArgs
