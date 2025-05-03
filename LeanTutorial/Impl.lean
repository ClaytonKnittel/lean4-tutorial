import LeanTutorial.MyNat
import LeanTutorial.Add

theorem lvl2 (h : zero + x = (zero + y) + two) : x = y + two := by
  repeat rw [zero_add] at h
  exact h

theorem lvl3 (hx : x = three) (hxy : x = three → y = four) : y = four := by
  apply hxy hx

theorem lvl4 (x : MyNat) : x + one = 4 → x = 3 := by
  intro h
  rw [add_succ, add_zero] at h
  injection h

theorem lvl5 (x : MyNat) : x + one = 4 → x = 3 := by
  intro h
  apply succ_inj
  rw [succ_eq_add_one]
  exact h

theorem lvl7 : x + one = y + one → x = y := by
  intro h
  repeat rw [← succ_eq_add_one] at h
  injection h

theorem lvl8 (h₁ : x = y) (h₂ : x ≠ y) : False := by
  apply h₂
  exact h₁

theorem lvl9 : zero ≠ one := zero_ne_succ zero

theorem lvl10 : one ≠ zero := zero_ne_succ zero ∘ Eq.symm

theorem lvl11 : two + two ≠ five := by
  repeat rw [add_succ, succ_add]
  rw [add_zero]
  intro h
  let h := (succ_inj ∘ succ_inj ∘ succ_inj ∘ succ_inj) h
  exact lvl9 h
