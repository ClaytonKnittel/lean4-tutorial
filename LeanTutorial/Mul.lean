import LeanTutorial.MyNat
import LeanTutorial.Add

def mulNat : ℕ → ℕ → ℕ
  | .zero,   _ => .zero
  | .succ m, n => mulNat m n + n

infixl:66 " * " => mulNat

theorem zero_mul (a : ℕ) : zero * a = zero :=
  by rw [mulNat]

theorem mul_zero (a : ℕ) : a * zero = zero :=
  by
    induction a with
    | zero => rw [mulNat]
    | succ _ ih => rw [mulNat, add_zero, ih]

theorem succ_mul (a b : ℕ) : a.succ * b = a * b + b :=
  by rw [mulNat]

theorem mul_succ (a b : ℕ) : a * b.succ = a * b + a :=
  by
    induction a with
    | zero =>
      repeat rw [zero_mul]
      rw [add_zero]
    | succ _ ih =>
      repeat rw [succ_mul]
      rw [ih]
      repeat rw [add_succ]
      rw [add_right_comm]

theorem one_mul (m : ℕ) : one * m = m :=
  by
    rw [succ_mul, zero_mul, zero_add]

theorem mul_one (m : ℕ) : m * one = m :=
  by
    rw [mul_succ, mul_zero, zero_add]

theorem mul_comm (a b : ℕ) : a * b = b * a :=
  by
    induction a with
    | zero => rw [zero_mul, mul_zero]
    | succ _ ih => rw [succ_mul, mul_succ, ih]

theorem two_mul (m : ℕ) : two * m = m + m :=
  by
    rw [succ_mul, one_mul]

theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c :=
  by
    induction c with
    | zero => rw [add_zero, mul_zero, add_zero]
    | succ _ ih =>
      rw [add_succ, mul_succ, mul_succ, ih, add_assoc]

theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c :=
  by
    rw [mul_comm, mul_add]
    rw [mul_comm]
    nth_rw 2 [mul_comm]

theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) :=
  by
    induction b with
    | zero => rw [mul_zero, zero_mul, mul_zero]
    | succ _ ih =>
      rw [succ_mul, mul_succ, add_mul, mul_add, ih]
