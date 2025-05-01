open Nat
notation "ℕ" => Nat

theorem one_eq_succ_zero: 1 = Nat.succ 0 := by rfl
theorem two_eq_succ_one: 2 = Nat.succ 1 := by rfl
theorem three_eq_succ_two: 3 = Nat.succ 2 := by rfl
theorem four_eq_succ_three: 4 = Nat.succ 3 := by rfl

theorem add_zero (a : ℕ) : a + 0 = a := by sorry
