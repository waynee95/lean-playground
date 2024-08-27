variable (a b c : Prop)

-- and
example : (a ∧ b) ↔ b ∧ a :=
  Iff.intro
    (λ hab : a ∧ b => And.intro hab.right hab.left)
    (λ hba : b ∧ a => And.intro hba.right hba.left)

example : (a ∧ b ↔ b ∧ a) := by
  apply Iff.intro
  intro hab
  apply And.intro hab.right hab.left
  intro hba
  apply And.intro hba.right hba.left

example : (a ∧ b ↔ b ∧ a) := by
  apply Iff.intro
  intro hab
  apply And.intro
  . exact hab.right
  . exact hab.left
  intro hba
  apply And.intro
  . exact hba.right
  . exact hba.left

-- or
example : (a ∨ b → b ∨ a) := by
  intro h
  cases h with
    | inr hb => apply Or.inl hb
    | inl ha => apply Or.inr ha

example : (a ∨ b → b ∨ a) := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption

example : (a ∨ b → b ∨ a) := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption
