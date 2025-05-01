import LeanTutorial.MyNat
import LeanTutorial.Add

def myMul : ℕ → ℕ → ℕ
  | .zero,   _ => .zero
  | .succ m, n => myMul m n + n

infixl:66 " * " => myMul

theorem mul_zero (a : ℕ) : a * zero = zero :=
  by
    induction a with
    | zero => rw [myMul]
    | succ _ ih => rw [myMul, add_zero, ih]

theorem mul_succ (a b : ℕ) : a * b.succ = a * b + a :=
  by
    induction a with
    | zero =>
      repeat rw [myMul]
      rw [add_zero]
    | succ _ ih =>
      rw [add_comm]
      repeat rw [myMul]
      rw [ih]
      nth_rw 2 [add_comm]
      repeat rw [add_succ, succ_add]
      rw [add_assoc]

theorem mul_one (m : ℕ) : m * one = m :=
  by
    induction m with
    | zero => rw [myMul]
    | succ m ih => rw [mul_succ, mul_zero, zero_add]
