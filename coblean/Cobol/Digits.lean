/-
# Positional digit lists

Big-endian base-`b` digit lists, used by the zoned-decimal (base 10, one digit per byte),
packed-decimal (base 10, two digits per byte) and binary (base 256) codecs.  The round-trip
lemmas proved here once are what make `decode (encode v) = some v` a single `simp` step in
program proofs.
-/

namespace Cobol.Digits

/-- Induction on a list from the right (`[]`, then `l ++ [a]`). -/
@[elab_as_elim] theorem revInduction {α : Type _} {motive : List α → Prop} (l : List α)
    (nil : motive []) (append_singleton : ∀ l a, motive l → motive (l ++ [a])) : motive l := by
  have : ∀ r : List α, motive r.reverse := by
    intro r
    induction r with
    | nil => exact nil
    | cons a r ih => simpa using append_singleton _ a ih
  simpa using this l.reverse

/-- Exactly `n` big-endian base-`b` digits of `v` (that is, of `v % b ^ n`). -/
def toDigits (b : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => toDigits b n (v / b) ++ [v % b]

/-- Value of a big-endian base-`b` digit list. -/
def ofDigits (b : Nat) (ds : List Nat) : Nat :=
  ds.foldl (fun acc d => acc * b + d) 0

@[simp] theorem length_toDigits (b n v : Nat) : (toDigits b n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [toDigits, ih]

@[simp] theorem ofDigits_nil (b : Nat) : ofDigits b [] = 0 := rfl

theorem ofDigits_append_singleton (b : Nat) (l : List Nat) (d : Nat) :
    ofDigits b (l ++ [d]) = ofDigits b l * b + d := by
  simp [ofDigits, List.foldl_append]

theorem ofDigits_cons (b d : Nat) (l : List Nat) :
    ofDigits b (d :: l) = d * b ^ l.length + ofDigits b l := by
  induction l using revInduction with
  | nil => simp [ofDigits]
  | append_singleton l x ih =>
    have : ofDigits b (d :: (l ++ [x])) = ofDigits b (d :: l) * b + x := by
      rw [← List.cons_append, ofDigits_append_singleton]
    rw [this, ih, ofDigits_append_singleton]
    simp only [List.length_append, List.length_singleton, Nat.pow_succ, Nat.add_mul,
      Nat.mul_assoc]
    omega

theorem ofDigits_toDigits (b n v : Nat) : ofDigits b (toDigits b n v) = v % b ^ n := by
  induction n generalizing v with
  | zero => simp [toDigits, Nat.mod_one]
  | succ n ih =>
    rw [toDigits, ofDigits_append_singleton, ih, Nat.pow_succ, Nat.mul_comm (b ^ n) b,
      Nat.mod_mul]
    rw [Nat.mul_comm]; omega

theorem toDigits_lt {b : Nat} (hb : 0 < b) (n v : Nat) : ∀ d ∈ toDigits b n v, d < b := by
  induction n generalizing v with
  | zero => simp [toDigits]
  | succ n ih =>
    intro d hd
    simp only [toDigits, List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | hd
    · exact ih _ d hd
    · subst hd; exact Nat.mod_lt _ hb

theorem ofDigits_lt {b : Nat} (_hb : 0 < b) (ds : List Nat) (h : ∀ d ∈ ds, d < b) :
    ofDigits b ds < b ^ ds.length := by
  induction ds using revInduction with
  | nil => simp
  | append_singleton l x ih =>
    have hl : ∀ d ∈ l, d < b := fun d hd => h d (List.mem_append_left _ hd)
    have hx : x < b := h x (by simp)
    rw [ofDigits_append_singleton, List.length_append, List.length_singleton, Nat.pow_succ]
    have := ih hl
    have : ofDigits b l * b + x < (ofDigits b l + 1) * b := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have : (ofDigits b l + 1) * b ≤ b ^ l.length * b := Nat.mul_le_mul_right _ (by omega)
    omega

theorem toDigits_ofDigits {b : Nat} (ds : List Nat) (h : ∀ d ∈ ds, d < b) :
    toDigits b ds.length (ofDigits b ds) = ds := by
  induction ds using revInduction with
  | nil => rfl
  | append_singleton l x ih =>
    have hl : ∀ d ∈ l, d < b := fun d hd => h d (List.mem_append_left _ hd)
    have hx : x < b := h x (by simp)
    have hb : 0 < b := by omega
    rw [List.length_append, List.length_singleton, toDigits, ofDigits_append_singleton]
    have e1 : (ofDigits b l * b + x) / b = ofDigits b l := by
      rw [Nat.mul_comm, Nat.mul_add_div hb, Nat.div_eq_of_lt hx, Nat.add_zero]
    have e2 : (ofDigits b l * b + x) % b = x := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
    rw [e1, e2, ih hl]

/-- `toDigits` on a value that already fits is injective on values. -/
theorem toDigits_inj {b n v w : Nat} (hv : v < b ^ n) (hw : w < b ^ n)
    (h : toDigits b n v = toDigits b n w) : v = w := by
  have := congrArg (ofDigits b) h
  rwa [ofDigits_toDigits, ofDigits_toDigits, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hw] at this

end Cobol.Digits
