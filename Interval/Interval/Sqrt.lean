import Interval.Interval.Pow

/-!
## Interval square root

This is an extremely slow way of computing square roots.
-/

open Set
open scoped Real

variable {x : Interval} {x' : ℝ}

/-- `sqrt x = x ^ 0.5` -/
@[irreducible] def Interval.sqrt (x : Interval) : Interval :=
  x ^ (Interval.div2 1)

/-- `Interval.sqrt` is conservative -/
@[approx] lemma Interval.approx_sqrt (m : approx x x') : approx x.sqrt x'.sqrt := by
  rw [Interval.sqrt, Real.sqrt_eq_rpow]
  approx
