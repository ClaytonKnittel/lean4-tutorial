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
