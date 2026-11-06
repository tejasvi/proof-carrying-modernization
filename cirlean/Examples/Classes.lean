import CIR
import Examples.Gen.Classes

/-!
  Classes (`Examples/cpp/classes.cpp`).

  An `Account` object is a block holding `Val.agg [.int balance]` (one value
  per data member). Member functions take `this` as their first argument.
  Each method has a `@[cir_spec]` specification; `transfer` and
  `open_and_use` are verified against these specifications only
  (`cir.inline false`), including the constructor of a local object.
-/

open CIR Gen.Classes

set_option maxHeartbeats 4000000

namespace Examples.Classes

/-- `explicit Account(int b) : balance_(b) {}` -/
@[cir_spec]
theorem ctor_spec (b : Nat) (old : Val) (bal : Int) (k : BlockKind) (m : Mem) (hb : b < m.next)
    (ho : m.blocks b = some ⟨k, true, .record "Account", .agg [old]⟩) (hk : k ≠ .readonly)
    (hbal : -2147483648 ≤ bal ∧ bal ≤ 2147483647) :
    Returns ctx fn_Account_Account.sym [.ptr (.loc b []), .int bal] m (fun v m' =>
      v = none ∧ m'.blocks b = some ⟨k, true, .record "Account", .agg [.int bal]⟩ ∧ Frame m m' [b]) := by
  cir_start
  cir_vcg

/-- `int balance() const` -/
@[cir_spec]
theorem balance_spec (b : Nat) (bal : Int) (k : BlockKind) (m : Mem) (hb : b < m.next)
    (ho : m.blocks b = some ⟨k, true, .record "Account", .agg [.int bal]⟩)
    (hbal : -2147483648 ≤ bal ∧ bal ≤ 2147483647) :
    Returns ctx fn_Account_balance.sym [.ptr (.loc b [])] m (fun v m' =>
      v = some (.int bal) ∧ Frame m m' []) := by
  cir_start
  cir_vcg

/-- `void deposit(int amt) { balance_ += amt; }` -/
@[cir_spec]
theorem deposit_spec (b : Nat) (bal amt : Int) (k : BlockKind) (m : Mem) (hb : b < m.next)
    (ho : m.blocks b = some ⟨k, true, .record "Account", .agg [.int bal]⟩) (hk : k ≠ .readonly)
    (hbal : -2147483648 ≤ bal ∧ bal ≤ 2147483647) (hamt : -2147483648 ≤ amt ∧ amt ≤ 2147483647)
    (hsum : -2147483648 ≤ bal + amt ∧ bal + amt ≤ 2147483647) :
    Returns ctx fn_Account_deposit.sym [.ptr (.loc b []), .int amt] m (fun v m' =>
      v = none ∧ m'.blocks b = some ⟨k, true, .record "Account", .agg [.int (bal + amt)]⟩ ∧
        Frame m m' [b]) := by
  cir_start
  cir_vcg

/-- `bool withdraw(int amt)`: succeeds iff `0 ≤ amt ≤ balance`. -/
@[cir_spec]
theorem withdraw_spec (b : Nat) (bal amt : Int) (k : BlockKind) (m : Mem) (hb : b < m.next)
    (ho : m.blocks b = some ⟨k, true, .record "Account", .agg [.int bal]⟩) (hk : k ≠ .readonly)
    (hbal : 0 ≤ bal ∧ bal ≤ 2147483647) (hamt : -2147483648 ≤ amt ∧ amt ≤ 2147483647) :
    Returns ctx fn_Account_withdraw.sym [.ptr (.loc b []), .int amt] m (fun v m' =>
      v = some (.bool (decide (0 ≤ amt ∧ amt ≤ bal))) ∧
      m'.blocks b = some ⟨k, true, .record "Account",
        .agg [.int (if 0 ≤ amt ∧ amt ≤ bal then bal - amt else bal)]⟩ ∧
      Frame m m' [b]) := by
  cir_start
  cir_vcg

set_option cir.inline false in
/-- `int transfer(Account& a, Account& b, int amt)`, from the method specifications. -/
theorem transfer_spec (ba bb : Nat) (x y amt : Int) (ka kb : BlockKind) (m : Mem) (hab : ba ≠ bb)
    (hba : ba < m.next) (hbb : bb < m.next)
    (ha : m.blocks ba = some ⟨ka, true, .record "Account", .agg [.int x]⟩)
    (hb : m.blocks bb = some ⟨kb, true, .record "Account", .agg [.int y]⟩)
    (hka : ka ≠ .readonly) (hkb : kb ≠ .readonly)
    (hx : 0 ≤ x ∧ x ≤ 2147483647) (hy : -2147483648 ≤ y ∧ y ≤ 2147483647)
    (hamt : -2147483648 ≤ amt ∧ amt ≤ 2147483647) (hfit : 0 ≤ amt → amt ≤ x → y + amt ≤ 2147483647) :
    Returns ctx fn_transfer.sym [.ptr (.loc ba []), .ptr (.loc bb []), .int amt] m (fun v m' =>
      v = some (.int (if 0 ≤ amt ∧ amt ≤ x then 1 else 0)) ∧
      m'.blocks ba = some ⟨ka, true, .record "Account",
        .agg [.int (if 0 ≤ amt ∧ amt ≤ x then x - amt else x)]⟩ ∧
      m'.blocks bb = some ⟨kb, true, .record "Account",
        .agg [.int (if 0 ≤ amt ∧ amt ≤ x then y + amt else y)]⟩) := by
  cir_start
  cir_vcg

set_option cir.inline false in
/-- `int open_and_use(int x)`: a local `Account`, constructed and used. -/
theorem open_and_use_spec (x : Int) (m : Mem) (hx : -70 ≤ x ∧ x ≤ 1000) :
    Returns ctx fn_open_and_use.sym [.int x] m (fun v _ => v = some (.int (70 + x))) := by
  cir_start
  cir_vcg

end Examples.Classes
