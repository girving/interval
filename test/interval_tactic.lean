import Interval.Tactic.Interval

/-!
#### Tests for the `interval` tactic
-/

open IntervalTactic (ile ilt)
open Real (log exp)

example : (2 : ℝ) < 3 := by interval
example : exp 1 < 2.7182818284591 := by interval
example : log 200 * 20000 ≤ 106000 := by interval
example : |exp (1 + log 7) - 19.02797279921331| < 1e-14 := by interval
example : (5 : ℝ) ^ (0.18732 : ℝ) < 1.351858 := by interval
