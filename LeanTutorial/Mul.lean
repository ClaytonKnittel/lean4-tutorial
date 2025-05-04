import LeanTutorial.MyNat
import LeanTutorial.Add
import LeanTutorial.Inequality
import Mathlib.Tactic.Tauto

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

theorem mul_le_mul_right {a b : MyNat} (c : MyNat) : a ≤ b → a * c ≤ b * c := by
  intro a_le_b
  cases a_le_b with
  | intro d h =>
    rw [← h, add_mul]
    exists d * c

theorem mul_left_ne_zero {a : MyNat} (b : MyNat) : a * b ≠ 0 → b ≠ 0 := by
  intro a_b_ne_zero
  by_contra b_eq_0
  apply a_b_ne_zero
  rw [b_eq_0]
  exact mul_zero a

theorem le_mul_right (a b : MyNat) (ha : a * b ≠ 0) : a ≤ a * b := by
  let b_ge_one := one_le_of_ne_zero (mul_left_ne_zero b ha)
  nth_rewrite 1 [← mul_one a]
  repeat rw [mul_comm a]
  exact mul_le_mul_right a b_ge_one

theorem mul_right_eq_one {y : MyNat} (x : MyNat) : x * y = 1 → x = 1 := by
  intro h
  have x_ne_0 : x ≠ 0 := by
    by_contra x_eq_0
    rw [x_eq_0] at h
    trivial
  have x_le_1 := le_mul_right x y (by rw [h]; trivial)
  rw [h] at x_le_1
  cases le_one x_le_1 <;> trivial

example {y : MyNat} (x : MyNat) : x * y = 1 → x = 1 := by
  intro h
  have h2 : x * y ≠ 0 := by rw [h]; trivial
  let h3 := le_mul_right _ _ h2
  rw [h] at h3
  cases le_one h3 with
  | inl x_eq_0 =>
    rw [x_eq_0, zero_mul] at h
    trivial
  | inr _ => trivial

theorem mul_ne_zero {a b : MyNat} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  let ⟨_, ha⟩ := eq_succ_of_ne_zero ha
  let ⟨_, hb⟩ := eq_succ_of_ne_zero hb
  rw [ha, hb, mul_succ, succ_mul, add_succ]
  symm
  exact zero_ne_succ

theorem mul_eq_zero {a b : MyNat} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  cases a with
  | zero => left; trivial
  | succ _ =>
    cases b with
    | zero => right; trivial
    | succ _ =>
      rw [mul_succ, succ_mul, add_succ] at h
      apply False.elim
      apply zero_ne_succ (Eq.symm h)

example {a b : MyNat} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have h2 : _ → _ → a * b ≠ 0 := mul_ne_zero
  tauto

theorem mul_left_cancel {a : MyNat} (b c : MyNat) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  induction b generalizing c with
  | zero =>
    rw [mul_zero] at h
    let a_or_d_eq_0 := mul_eq_zero h.symm
    tauto
  | succ b' ih =>
    cases c with
    | zero =>
      rw [mul_succ, mul_zero] at h
      let a_eq_0 := add_left_eq_zero h
      trivial
    | succ _ =>
      repeat rw [mul_succ] at h
      let ihp := add_right_cancel a h
      rw [ih _ ihp]

theorem mul_right_eq_self {a b : MyNat} {ha : a ≠ 0} (h : a * b = a) : b = 1 := by
  nth_rw 2 [← mul_one a] at h
  exact mul_left_cancel _ _ ha h
