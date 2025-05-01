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

def myAdd : ℕ → ℕ → ℕ
  | MyNat.zero,    n => n
  | MyNat.succ m,  n => MyNat.succ (myAdd m n)

infixl:65 " + " => myAdd

theorem succ_add (a b : ℕ) : a.succ + b = (a + b).succ :=
  by
    rw [myAdd]

theorem add_zero (a : ℕ) : a + MyNat.zero = a :=
  by
    induction a with
    | zero =>
      rewrite [myAdd]
      eq_refl
    | succ b ih =>
      rewrite [myAdd]
      rewrite [ih]
      eq_refl

theorem add_succ (a b : ℕ) : a + b.succ = (a + b).succ :=
  by
    induction b with
    | zero =>
      rewrite [add_zero]
      sorry
    | succ => sorry
