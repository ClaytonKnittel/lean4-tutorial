import LeanTutorial.MyNat
import LeanTutorial.Add

def mulNat : MyNat → MyNat → MyNat
  | .zero,   _ => .zero
  | .succ m, n => mulNat m n + n

infixl:66 " * " => mulNat

theorem zero_mul (a : MyNat) : zero * a = zero := by
  rw [mulNat]

theorem mul_zero (a : MyNat) : a * zero = zero := by
  induction a with
  | zero => rw [mulNat]
  | succ _ ih => rw [mulNat, add_zero, ih]

theorem succ_mul (a b : MyNat) : a.succ * b = a * b + b := by
  rw [mulNat]

theorem mul_succ (a b : MyNat) : a * b.succ = a * b + a := by
  induction a with
  | zero =>
    repeat rw [zero_mul]
    rw [add_zero]
  | succ _ ih =>
    repeat rw [succ_mul]
    rw [ih]
    repeat rw [add_succ]
    rw [add_right_comm]

theorem one_mul (m : MyNat) : one * m = m := by
  rw [succ_mul, zero_mul, zero_add]

theorem mul_one (m : MyNat) : m * one = m := by
  rw [mul_succ, mul_zero, zero_add]

theorem mul_comm (a b : MyNat) : a * b = b * a := by
  induction a with
  | zero => rw [zero_mul, mul_zero]
  | succ _ ih => rw [succ_mul, mul_succ, ih]

theorem two_mul (m : MyNat) : two * m = m + m := by
  rw [succ_mul, one_mul]

theorem mul_add (a b c : MyNat) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => rw [add_zero, mul_zero, add_zero]
  | succ _ ih =>
    rw [add_succ, mul_succ, mul_succ, ih, add_assoc]

theorem add_mul (a b c : MyNat) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm, mul_comm c]

theorem mul_assoc (a b c : MyNat) : (a * b) * c = a * (b * c) := by
  induction b with
  | zero => rw [mul_zero, zero_mul, mul_zero]
  | succ _ ih =>
    rw [succ_mul, mul_succ, add_mul, mul_add, ih]

theorem mul_right_comm (a b c : MyNat) : (a * b) * c = (a * c) * b := by
  rw [mul_comm (a * b), ← mul_assoc, mul_comm c]

theorem mul_left_comm (a b c : MyNat) : a * (b * c) = b * (a * c) := by
  rw [mul_comm, mul_assoc, mul_comm a]
