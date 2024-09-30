import Interval.Interval.Exp

/-!
## Hyperbolic functions: `sinh` and `cosh`
-/

open Set
open scoped Real
namespace Interval

variable {a : ℝ} {x : Interval}

/-- Hyperbolic sine -/
@[irreducible] def sinh (x : Interval) : Interval :=
  (exp x - exp (-x)).div2

/-- Hyperbolic cosine -/
@[irreducible] def cosh (x : Interval) : Interval :=
  (exp x + exp (-x)).div2

@[approx] lemma mem_approx_sinh (ax : a ∈ approx x) : Real.sinh a ∈ approx x.sinh := by
  rw [sinh, Real.sinh_eq]; approx

@[approx] lemma mem_approx_cosh (ax : a ∈ approx x) : Real.cosh a ∈ approx x.cosh := by
  rw [cosh, Real.cosh_eq]; approx
