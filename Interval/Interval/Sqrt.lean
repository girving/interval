import Interval.Interval.Pow

/-!
## Interval square root

This is an extremely slow way of computing square roots.
-/

open Set
open scoped Real

/-- `sqrt x = x ^ 0.5` -/
@[irreducible] def Interval.sqrt (x : Interval) : Interval :=
  x ^ (Interval.div2 1)

/-- `Interval.sqrt` is conservative -/
@[approx] lemma Interval.mem_approx_sqrt {x : Interval} {a : ℝ}
    (ax : a ∈ approx x) : Real.sqrt a ∈ approx x.sqrt := by
  rw [Interval.sqrt, Real.sqrt_eq_rpow]
  approx
