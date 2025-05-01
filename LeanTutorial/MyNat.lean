inductive MyNat where
| zero : MyNat
| succ : MyNat -> MyNat
deriving Repr, DecidableEq

notation "ℕ" => MyNat

@[reducible] def zero := MyNat.zero
@[reducible] def one := MyNat.succ zero
@[reducible] def two := MyNat.succ one
@[reducible] def three := MyNat.succ two
@[reducible] def four := MyNat.succ three
@[reducible] def five := MyNat.succ four

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

theorem succ_inj {a b : ℕ} : a.succ = b.succ → a = b := by
  intro h
  injection h

theorem zero_ne_succ (a : ℕ) : 0 ≠ a.succ := by
  intro h
  contradiction
