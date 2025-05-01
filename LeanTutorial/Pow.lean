import Mathlib.Tactic.NthRewrite
import LeanTutorial.MyNat
import LeanTutorial.Add
import LeanTutorial.Mul

def powNat : ℕ → ℕ → ℕ
  | _, .zero => one
  | a, .succ b => powNat a b * a

infixl:80 " ^ " => powNat

theorem pow_zero (a : ℕ) : a ^ zero = one := by
  rw [powNat]

theorem pow_succ (a b : ℕ) : a ^ b.succ = a ^ b * a := by
  rw [powNat]

theorem zero_pow_zero : zero ^ zero = one := by
  rw [pow_zero]

theorem zero_pow_succ (a : ℕ) : zero ^ (a.succ) = zero := by
  rw [pow_succ, mul_zero]

theorem pow_one (a : ℕ) : a ^ one = a := by
  rw [pow_succ, pow_zero, one_mul]

theorem one_pow (a : ℕ) : one ^ a = one := by
  induction a with
  | zero => rw [pow_zero]
  | succ _ ih => rw [pow_succ, mul_one, ih]

theorem pow_two (a : ℕ) : a ^ two = a * a := by
  rw [pow_succ, pow_one]

theorem pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [add_zero, pow_zero, mul_one]
  | succ _ ih =>
    rw [add_succ, pow_succ, pow_succ, ih, mul_assoc]

theorem mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero =>
    repeat rw [pow_zero]
    rw [mul_one]
  | succ _ ih =>
    repeat rw [pow_succ]
    rw [ih, mul_assoc]
    nth_rw 2 [mul_left_comm]
    rw [mul_assoc]

theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero => rw [pow_zero, mul_zero, pow_zero]
  | succ _ ih =>
    rw [pow_succ, ih, mul_succ, pow_add]

theorem add_sq (a b : ℕ) : (a + b) ^ two = a ^ two + b ^ two + (two * a) * b := by
  repeat rw [pow_two]
  rw [add_mul]
  repeat rw [mul_add]
  rw [← add_assoc]
  nth_rw 2 [add_assoc]
  nth_rw 3 [mul_comm]
  rw [← two_mul, mul_assoc, add_right_comm]
