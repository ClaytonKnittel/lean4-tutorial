import LeanTutorial.MyNat
import LeanTutorial.Add

def leNat : MyNat → MyNat → Prop
  | a, b => ∃ (c : MyNat), a + c = b

infixl:40 " ≤ " => leNat

theorem le_refl {x : MyNat} : x ≤ x := by
  exists zero
  rw [add_zero]

theorem le_refl_pf {x : MyNat} : x ≤ x := Exists.intro zero (add_zero x)

theorem zero_le {x : MyNat} : 0 ≤ x := by exists x

theorem zero_le_pf {x : MyNat} : 0 ≤ x := Exists.intro x (zero_add x)

theorem le_succ_self (x : MyNat) : x ≤ x.succ := by
  exists one
  rw [succ_eq_add_one]

theorem le_trans (x y z : MyNat) : x ≤ y ∧ y ≤ z → x ≤ z := by
  intro ⟨h₁, h₂⟩
  cases h₁ with
  | intro c hy =>
    cases h₂ with
    | intro d hz =>
      rw [← hy, add_assoc] at hz
      exists c + d

theorem le_zero {x : MyNat} : x ≤ zero → x = zero := by
  intro h
  cases h with
  | intro _ ha => exact add_right_eq_zero ha

theorem le_antisymm (x y : MyNat) : x ≤ y ∧ y ≤ x → x = y := by
  intro ⟨h₁, h₂⟩
  cases h₁ with
  | intro a ha =>
    cases h₂ with
    | intro b hb =>
      rw [← ha, add_assoc] at hb
      let hb := add_right_eq_self hb
      rw [add_right_eq_zero hb, add_zero] at ha
      exact ha

theorem le_succ_inj {x y : MyNat} : x ≤ y → x.succ ≤ y.succ := by
  intro h
  cases h with
  | intro c h =>
    let h := congrArg MyNat.succ h
    rw [← succ_add] at h
    exists c

theorem le_total (x y : MyNat) : x ≤ y ∨ y ≤ x := by
  induction x with
  | zero =>
    left
    exact zero_le
  | succ a ia =>
    cases y with
    | zero =>
      right
      exact zero_le
    | succ b =>
      let h := le_total a b
      cases h with
      | inl l => exact Or.inl (le_succ_inj l)
      | inr r => exact Or.inr (le_succ_inj r)

theorem succ_le_succ {x y : MyNat} : x.succ ≤ y.succ → x ≤ y := by
  intro h
  cases h with
  | intro c h =>
    rw [succ_eq_add_one, add_assoc, add_comm one] at h
    rw [← succ_eq_add_one, add_succ] at h
    exists c
    exact succ_inj h

theorem le_one {x : MyNat} : x ≤ one → x = zero ∨ x = one := by
  intro h
  cases x with
  | zero =>
    left
    rfl
  | succ a =>
    cases h with
    | intro c h =>
      rw [succ_add] at h
      right
      rw [add_right_eq_zero (succ_inj h)]

theorem one_le_of_ne_zero {a : MyNat} (ha : a ≠ 0) : 1 ≤ a := by
  let x := eq_succ_of_ne_zero ha
  cases x with
  | intro n a_eq_n_succ =>
    rw [a_eq_n_succ]
    exact le_succ_inj zero_le
