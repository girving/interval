module

public import Interval.Approx.Approx
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Ring.Action.Rat
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Division by 2
-/

@[expose] public section

variable {α 𝕜 : Type}

/-!
### Definitions
-/

section Defs

/-- Division by 2 -/
class Div2 α where
  div2 : α → α

/-- Division by 2 respects zero -/
class Div2Zero α [Zero α] [Div2 α] where
  div2_zero : Div2.div2 (0 : α) = 0

export Div2 (div2)
export Div2Zero (div2_zero)
attribute [simp] div2_zero

/-- Division by 2 is conservative -/
class ApproxDiv2 (α α' : Type) [Approx α α'] [Div2 α] [Div2 α'] where
  approx_div2 {x : α} {x' : α'} (a : approx x x') : approx (div2 x) (div2 x')

export ApproxDiv2 (approx_div2)
attribute [approx] approx_div2

end Defs

/-!
### Modules over the rationals

Including the rationals themselves!
-/

section Module
variable {𝕜 : Type} [Field 𝕜] [CharZero 𝕜]
variable {E : Type} [Zero E] [SMulZeroClass ℚ E]

/-- Division by 2 for modules -/
instance {E : Type} [Zero E] [SMulZeroClass ℚ E] : Div2 E where
  div2 x := (2⁻¹ : ℚ) • x

/-- Division by 2 respects zero for modules -/
instance {E : Type} [Zero E] [SMulZeroClass ℚ E] : Div2Zero E where
  div2_zero := smul_zero _

lemma div2_eq_smul {E : Type} [Zero E] [SMulZeroClass ℚ E] (x : E) : div2 x = (2⁻¹ : ℚ) • x := rfl
lemma div2_eq_mul (x : 𝕜) : div2 x = 2⁻¹ * x := by simp [div2_eq_smul, Rat.smul_def]

end Module
