import Mathlib.Tactic.NthRewrite
import LeanTutorial.MyNat

theorem zero_add (n : ℕ) : zero + n = n :=
  by
    induction n with
    | zero => eq_refl
    | succ n ih =>
      rewrite [add_succ]
      rewrite [ih]
      eq_refl

theorem succ_add (a b : ℕ) : a.succ + b = (a + b).succ :=
  by
    induction b with
    | zero =>
      rewrite [add_zero]
      nth_rewrite 2 [add_zero]
      eq_refl
    | succ d ih =>
      sorry
