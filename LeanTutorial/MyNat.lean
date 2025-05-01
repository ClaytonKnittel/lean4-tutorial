import Mathlib.Tactic.NthRewrite

inductive MyNat where
| zero : MyNat
| succ : MyNat -> MyNat
deriving Repr, DecidableEq

notation "ℕ" => MyNat

def zero := MyNat.zero
def one := MyNat.succ zero
def two := MyNat.succ one
def three := MyNat.succ two
def four := MyNat.succ three

theorem one_eq_succ_zero: one = MyNat.succ zero := by rfl
theorem two_eq_succ_one: two = MyNat.succ one := by rfl
theorem three_eq_succ_two: three = MyNat.succ two := by rfl
theorem four_eq_succ_three: four = MyNat.succ three := by rfl
