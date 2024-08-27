-- define constants
def n : Nat := 42
def b : Bool := true

-- show type
#check n
#check b

-- evaluate expressions
#eval n
#eval n + n
#eval b
#eval b && not b

#check Nat → Nat
#check Bool → Bool

#check Nat.succ n

-- tuples
#check Nat × Nat
#check (42, 23)
#eval (42, 23).1 -- 42
#eval (42, 23).2 -- 23

def α : Type := Nat

#check List α

#check Type
#check Type 1

-- universe
universe u

def F (α : Type u) : Type u := Prod α α

#check F

-- function abstraction and application

-- write fun or \lambda
#check fun (x : Nat) => x + 42
#check λ (x : Nat) => x + 42

#check fun x => x + 42
#check λ x => x + 42

def add: Nat → Nat → Nat := λ x y => x + y

-- infered types
def add2 := λ (x : Nat) y => x + y

#check add
#eval add 42 23

-- types as parrameters
#check fun (α β : Type) (f : α → α → β) (x : α) => f x x

def compose {α β γ : Type} (g : β → γ) (f : α → β) : α → γ := λ x => g (f x)

-- sections
section sec
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β)
  variable (x : α)

  def compose2 := g (f x)
end sec

-- section variables are out of scope here

-- namespaces
namespace hello
  def hello_world := "Hello, World!"
end hello

#eval hello.hello_world

open hello
#eval hello_world
