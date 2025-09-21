import Mathlib.Algebra.Group.Basic

/-!
# Unbundled arithmetic typeclasses for `Interval` friendliness

`Interval` is not a monoid, so we special type classes if we want to use facts like `add_zero`.
Keeping them unbundled makes things a lot simpler.
-/

/-- Unbundled version of `NegZeroClass` -/
class NegZeroClass' (α : Type) [Zero α] [Neg α] where
  neg_zero' : -(0 : α) = 0

/-- Typeclass to express `a - 0 = a`, `0 - a = -a`, without requiring exact monoid structure. -/
class AddZeroClass' (α : Type) [Zero α] [Add α] where
  zero_add' : ∀ a : α, 0 + a = a
  add_zero' : ∀ a : α, a + 0 = a

/-- Typeclass to express `a - 0 = a`, `0 - a = -a`, without requiring exact monoid structure. -/
class SubZeroClass (α : Type) [Zero α] [Neg α] [Sub α] where
  zero_sub' : ∀ a : α, 0 - a = -a
  sub_zero' : ∀ a : α, a - 0 = a

export NegZeroClass' (neg_zero')
export AddZeroClass' (zero_add' add_zero')
export SubZeroClass (zero_sub' sub_zero')

variable {α : Type}

instance [NegZeroClass α] : NegZeroClass' α where
  neg_zero' := neg_zero

instance [AddZeroClass α] : AddZeroClass' α where
  zero_add' a := zero_add a
  add_zero' a := add_zero a

instance [SubNegZeroMonoid α] : SubZeroClass α where
  zero_sub' a := zero_sub a
  sub_zero' a := sub_zero a
