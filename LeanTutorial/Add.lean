import Mathlib.Tactic.NthRewrite
import LeanTutorial.MyNat

def addNat : MyNat → MyNat → MyNat
  | .zero, n => n
  | .succ m, n => MyNat.succ (addNat m n)

infixl:65 " + " => addNat

theorem succ_add (a b : MyNat) : a.succ + b = (a + b).succ := by
  rw [addNat]

theorem add_succ (a b : MyNat) : a + b.succ = (a + b).succ := by
  induction a with
  | zero => repeat rw [addNat]
  | succ _ ih =>
    repeat rw [succ_add]
    rw [ih]

theorem add_zero (a : MyNat) : a + zero = a := by
  induction a with
  | zero => rw [addNat]
  | succ _ ih => rw [addNat, ih]

theorem zero_add (a : MyNat) : zero + a = a := by
  induction a with
  | zero => rw [add_zero]
  | succ b ih => rw [add_succ, ih]

theorem add_comm' (a b : MyNat) : a + b = b + a :=
  match a with
  | .zero => Eq.trans (zero_add b) (Eq.symm (add_zero b))
  | .succ n => Eq.trans
    (congrArg MyNat.succ (add_comm' n b)) -- (n + b).succ = (b + n).succ
    (Eq.symm (add_succ b n))              -- (b + n).succ = b + n.succ

theorem add_comm (a b : MyNat) : a + b = b + a := by
  induction a with
  | zero => rw [add_zero, zero_add]
  | succ _ ih => rw [add_succ, succ_add, ih]

theorem add_assoc' (a b c : MyNat) : (a + b) + c = a + (b + c) :=
  match a with
  | .zero => Eq.refl (b + c)
  | .succ n => congrArg MyNat.succ (add_assoc' n b c)

theorem add_assoc (a b c : MyNat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero => repeat rw [zero_add]
  | succ _ ih =>
    repeat rw [succ_add]
    rw [ih]

theorem add_right_comm' (a b c : MyNat) : (a + b) + c = (a + c) + b :=
  Eq.trans
    (Eq.trans
      (add_comm (a + b) c)
      (Eq.symm (add_assoc c a b)))
    (congrArg (· + b) (add_comm c a))

theorem add_right_comm (a b c : MyNat) : (a + b) + c = (a + c) + b := by
  rw [add_comm, ← add_assoc, add_comm a]

theorem succ_eq_add_one (a : MyNat) : a.succ = a + one := by
  rw [add_succ, add_zero]

theorem add_right_cancel' {a b : MyNat} (n : MyNat) (h : a + n = b + n)
    : a = b :=
  match n with
  | .zero =>
    Eq.trans
      (Eq.trans (Eq.symm (add_zero a)) h)
      (add_zero b)
  | .succ m => add_right_cancel' m
    (succ_inj
      (Eq.trans
        (Eq.trans (Eq.symm (add_succ a m)) h)
        (add_succ b m))
    )

theorem add_right_cancel {a b : MyNat} (n : MyNat)
    : a + n = b + n → a = b := by
  induction n with
  | zero =>
    repeat rw [add_zero]
    exact id
  | succ _ ih =>
    repeat rw [add_succ]
    exact ih ∘ succ_inj

theorem add_left_cancel {a b : MyNat} (n : MyNat)
    : n + a = n + b → a = b := by
  repeat rw [add_comm n]
  apply add_right_cancel

theorem add_left_eq_self {a b : MyNat} : a + b = b → a = 0 := by
  nth_rw 2 [← zero_add b]
  apply add_right_cancel

theorem add_right_eq_self {a b : MyNat} : a + b = a → b = 0 := by
  rw [add_comm]
  apply add_left_eq_self

theorem add_right_eq_zero {a b : MyNat} : a + b = zero → a = zero := by
  cases b with
  | zero =>
    rw [add_zero]
    exact id
  | succ =>
    rw [add_succ]
    exact False.elim ∘ succ_ne_zero

theorem add_left_eq_zero {a b : MyNat} : a + b = zero → b = zero := by
  rw [add_comm]
  exact add_right_eq_zero

theorem add_eq_zero {a b : MyNat} : a + b = zero → a = zero ∧ b = zero := by
  intro h
  exact And.intro (add_right_eq_zero h) (add_left_eq_zero h)

theorem add_left_comm (a b c : MyNat) : a + (b + c) = b + (a + c) := by
  rw [add_comm, add_assoc, add_comm a]

theorem add_rearrange {a b c d : MyNat} : (a + b) + (c + d) = a + c + d + b := by
  rw [add_assoc, add_comm b]
  repeat rw [← add_assoc]
