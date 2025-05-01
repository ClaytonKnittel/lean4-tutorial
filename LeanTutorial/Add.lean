import Mathlib.Tactic.NthRewrite
import LeanTutorial.MyNat

def addNat : ℕ → ℕ → ℕ
  | .zero, n => n
  | .succ m, n => MyNat.succ (addNat m n)

infixl:65 " + " => addNat

theorem succ_add (a b : ℕ) : a.succ + b = (a + b).succ :=
  by
    rw [addNat]

theorem add_succ (a b : ℕ) : a + b.succ = (a + b).succ :=
  by
    induction a with
    | zero => repeat rw [addNat]
    | succ _ ih =>
      repeat rw [succ_add]
      rw [ih]

theorem add_zero (a : ℕ) : a + MyNat.zero = a :=
  by
    induction a with
    | zero => rw [addNat]
    | succ _ ih => rw [addNat, ih]

theorem zero_add (a : ℕ) : MyNat.zero + a = a :=
  by
    induction a with
    | zero => rw [add_zero]
    | succ b ih => rw [add_succ, ih]

theorem add_comm (a b : ℕ) : a + b = b + a :=
  by
    induction a with
    | zero => rw [add_zero, zero_add]
    | succ _ ih => rw [add_succ, succ_add, ih]

theorem add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) :=
  by
    induction a with
    | zero => repeat rw [zero_add]
    | succ _ ih =>
      repeat rw [succ_add]
      rw [ih]

theorem add_right_comm (a b c : ℕ) : (a + b) + c = (a + c) + b :=
  by
    rw [add_comm, ← add_assoc]
    nth_rw 2 [add_comm]
