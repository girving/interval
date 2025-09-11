import Interval.Interval.Exp

/-!
## Hyperbolic functions: `sinh` and `cosh`
-/

open Set
open scoped Real
namespace Interval

variable {x : Interval} {x' : ℝ}

/-- Hyperbolic sine -/
@[irreducible] def sinh (x : Interval) : Interval :=
  (exp x - exp (-x)).div2

/-- Hyperbolic cosine -/
@[irreducible] def cosh (x : Interval) : Interval :=
  (exp x + exp (-x)).div2

@[approx] lemma mem_approx_sinh (ax : approx x x') : approx x.sinh (Real.sinh x') := by
  rw [sinh, Real.sinh_eq]; approx

@[approx] lemma mem_approx_cosh (ax : approx x x') : approx x.cosh (Real.cosh x') := by
  rw [cosh, Real.cosh_eq]; approx
