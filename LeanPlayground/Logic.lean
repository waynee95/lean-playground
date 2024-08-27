variable {p q : Prop}

theorem t1 : p → q → p := λ hp hq => hp

-- the lambda abstractions can be viewed as temporary assumptions
-- we can specify the final term explictly via show

theorem t2 : p → q → p :=
  λ hp : p =>
  λ hq : q =>
  show p from hp

#print t1
#print t2

-- as with ordanary definitions, we can move the lambda abstracted
-- variables to the left of the colon
theorem t3 (hp : p) (hq : q) : p :=
  hp

-- assume the existence of a proof of p
axiom hp : p

-- theorem t3 can be used as a function
theorem t4 : q → p :=
  t1 hp

-- can lead to logical contradictions
axiom unsound : False

theorem x1 : 1 = 0 :=
  False.elim unsound

-- some proofs
example (ha : a) : a :=
  ha

example (ha : a) : a ∧ a :=
  And.intro ha ha

example (hab : a ∧ b) : b ∧ a :=
  And.intro (And.right hab) (And.left hab)

example (hab : a ∧ b) : b ∧ a :=
  And.intro hab.2 hab.1

example (hab : a ∧ b) : b ∧ a :=
  ⟨hab.2, hab.1⟩

example (hab : a ∧ b) : b ∧ a := by {
  apply And.intro;
  exact hab.2;
  exact hab.1
}

#check Or.inl -- a → a ∨ b
#check Or.inr -- b → a ∨ b

example (ha : a) : a ∨ a := Or.inl ha
example (ha : a) : a ∨ a := Or.inr ha

example (h : a ∨ b) : b ∨ a :=
  Or.elim h
    (λ ha : a => Or.inr ha) -- right injection
    (λ hb : b => Or.inl hb) -- left injection

example (h : a ∨ b) : b ∨ a :=
  h.elim
    (λ ha : a => Or.inr ha)
    (λ hb : b => Or.inl hb)

example (h : a ∨ b) : b ∨ a := by
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption

example (h : a ∨ b) : b ∨ a := by {
  cases h;
    { apply Or.inr; assumption };
    { apply Or.inl; assumption }
}

example (h : a ∧ b) : b ∧ a :=
  have ha : a := h.left
  have hb : b := h.right
  show b ∧ a from And.intro hb ha

example (h : a ∧ b) : b ∧ a := by
  apply And.intro
  apply h.right
  apply h.left
