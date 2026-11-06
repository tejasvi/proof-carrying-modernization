import CIR

example (x : Int) (h0 : 0 ≤ x ∧ x ≤ 65535) (h1 : x ≤ 1023) : -2147483648 ≤ x * x ∧ x * x ≤ 2147483647 := by
  constructor <;> (cir_nlin; omega)

example (k : Int) (h0 : 1 ≤ k) (h1 : k ≤ 1000) : -2147483648 ≤ 36 * k * k := by
  cir_nlin; omega

example (a b : Int) (ha : -32767 ≤ a ∧ a ≤ 32767) (hb : -32767 ≤ b ∧ b ≤ 32767) :
    a * b + 5 ≤ 2147483647 := by
  cir_nlin; omega
