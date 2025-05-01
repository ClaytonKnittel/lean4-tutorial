import LeanTutorial.MyNat

def m : Nat := 0

theorem lvl1 (x y : ℕ) : 37 * x + y = 37 * x + y := by eq_refl

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by
    apply And.intro hp
    exact And.intro hq hp

theorem lvl2 (x y : ℕ) : y = x + 7 → 2*y = 2*(x + 7) :=
  by
    intro h
    rw [h]

theorem lvl2' (x y : ℕ) : y = x + 7 → 2 * y = 2 * (x + 7) :=
  fun h => congrArg (fun n => 2 * n) h

theorem lvl3: 2 = Nat.succ (Nat.succ 0) :=
  by
    rewrite [two_eq_succ_one]
    rewrite [one_eq_succ_zero]
    eq_refl

theorem lvl4: 2 = Nat.succ (Nat.succ 0) :=
  by
    rewrite [← one_eq_succ_zero]
    rewrite [← two_eq_succ_one]
    eq_refl

theorem lvl5: a + (b + 0) + (c + 0) = a + b + c :=
  by
    repeat rewrite [add_zero]
    eq_refl

theorem lvl6: a + (b + 0) + (c + 0) = a + b + c :=
  by
    rewrite [add_zero c]
    rewrite [add_zero b]
    eq_refl

theorem lvl7 (n : ℕ) : Nat.succ n = n + 1 :=
  by
    rewrite [one_eq_succ_zero]
    rewrite [Nat.add_succ]
    rewrite [add_zero]
    eq_refl

theorem lvl8 : 2 + 2 = 4 :=
  by
    rewrite [four_eq_succ_three, three_eq_succ_two]
    rewrite [two_eq_succ_one, one_eq_succ_zero]
    repeat rewrite [Nat.add_succ]
    rewrite [add_zero]
    eq_refl
