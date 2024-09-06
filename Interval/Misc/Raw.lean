import Mathlib.Tactic.TypeStar

/-!
# Mark an object to print raw, so that we get all the bits
-/

variable {α : Type*}

structure Raw (α : Type*) where
  val : α

def raw (x : α) : Raw α := ⟨x⟩
