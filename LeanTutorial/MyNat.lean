import Mathlib.Logic.Function.Iterate

inductive MyNat where
| zero : MyNat
| succ : MyNat -> MyNat
deriving Repr

@[reducible] def zero := MyNat.zero
@[reducible] def one := MyNat.succ zero
@[reducible] def two := MyNat.succ one
@[reducible] def three := MyNat.succ two
@[reducible] def four := MyNat.succ three
@[reducible] def five := MyNat.succ four

def thirty_seven := ((MyNat.succ)^[37]) zero

@[reducible]
instance : OfNat MyNat 0 where
  ofNat := zero
@[reducible]
instance : OfNat MyNat 1 where
  ofNat := one
@[reducible]
instance : OfNat MyNat 2 where
  ofNat := two
@[reducible]
instance : OfNat MyNat 3 where
  ofNat := three
@[reducible]
instance : OfNat MyNat 4 where
  ofNat := four
@[reducible]
instance : OfNat MyNat 5 where
  ofNat := five

def pred : MyNat → MyNat
| .zero => thirty_seven
| .succ n => n

theorem pred_succ (n : MyNat) : pred (n.succ) = n := rfl

theorem succ_inj {a b : MyNat} : a.succ = b.succ → a = b := by
  intro h
  rw [← pred_succ a, h, pred_succ]

def is_zero : MyNat → Bool
| .zero => true
| .succ _ => false

theorem is_zero_zero : is_zero zero = True :=
  eq_self (is_zero zero)

theorem is_zero_succ' {n : MyNat} : is_zero n.succ = False :=
  eq_false (ne_true_of_eq_false rfl)

theorem zero_ne_succ {n : MyNat} : 0 ≠ n.succ := by
  by_contra h
  rw [← is_zero_succ', ← h]
  rfl

theorem succ_ne_zero {n : MyNat} : n.succ ≠ 0 :=
  Ne.symm zero_ne_succ

theorem succ_ne_succ {a b : MyNat} : a ≠ b → a.succ ≠ b.succ := by
  intro a_eq_b
  by_contra succ_eq
  exact a_eq_b (succ_inj succ_eq)

instance instDecidableEq : DecidableEq MyNat
| 0, 0 => isTrue <| by
  show zero = zero
  rfl
| .succ m, 0 => isFalse <| by
  show m.succ ≠ 0
  exact succ_ne_zero
| 0, .succ n => isFalse <| by
  show 0 ≠ n.succ
  exact zero_ne_succ
| .succ m, .succ n =>
  match instDecidableEq m n with
  | isTrue (h : m = n) => isTrue <| by
    show m.succ = n.succ
    rw [h]
  | isFalse (h : m ≠ n) => isFalse <| by
    show m.succ ≠ n.succ
    exact succ_ne_succ h
