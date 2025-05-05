
universe u

def MySet (α : Type u) := α → Prop

namespace MySet

def Mem (s : MySet α) (a : α) : Prop :=
  s a

instance : Membership α (MySet α) :=
  ⟨MySet.Mem⟩

def Subset (s₁ s₂ : MySet α) :=
  ∀ {a}, a ∈ s₁ → a ∈ s₂

instance : HasSubset (MySet α) :=
  ⟨MySet.Subset⟩

theorem Subset.refl {α : Type u} {A : MySet α} : A ⊆ A := id

theorem Subset.trans {α : Type u} {A B C : MySet α} {ha : A ⊆ B} {hb : B ⊆ C} : A ⊆ C :=
  hb ∘ ha
