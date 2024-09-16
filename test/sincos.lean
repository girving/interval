import Interval.Interval.Sincos

/-!
### Unit tests for `sin` and `cos`

We test only the width of the resulting intervals, since their correctness is proven earlier.
-/

open Interval

/-- `sin` series tests (for small `x`) -/
def sin_small_test (x : ℚ) (e : Interval) : Bool :=
  (sin_small (ofRat x)).size ≤ e.hi
example : sin_small_test 0 0 := by native_decide
example : sin_small_test (1/7) 6e-20 := by native_decide
example : sin_small_test (-1/7) 6e-20 := by native_decide
example : sin_small_test 0.785 5e-19 := by native_decide
example : sin_small_test (-0.785) 5e-19 := by native_decide

/-- `cos` series tests (for small `x`) -/
def cos_small_test (x : ℚ) (e : Interval) : Bool :=
  (cos_small (ofRat x)).size ≤ e.hi
example : cos_small_test 0 4e-19 := by native_decide
example : cos_small_test (1/7) 4e-19 := by native_decide
example : cos_small_test (-1/7) 4e-19 := by native_decide
example : cos_small_test 0.785 5e-19 := by native_decide
example : cos_small_test (-0.785) 5e-19 := by native_decide

/-- `sin` tests -/
def sin_test (x : ℚ) (e : Interval) : Bool :=
  (sin (ofRat x)).size ≤ e.hi
example : sin_test 0 0 := by native_decide
example : sin_test (1/7) 6e-20 := by native_decide
example : sin_test (-1/7) 6e-20 := by native_decide
example : sin_test 0.785 5e-19 := by native_decide
example : sin_test (-0.785) 5e-19 := by native_decide
example : sin_test 2 5e-19 := by native_decide
example : sin_test 3 5e-19 := by native_decide
example : sin_test 4 2e-18 := by native_decide
example : sin_test 5 2e-18 := by native_decide
example : sin_test 6 2e-18 := by native_decide
example : sin_test 7 2e-18 := by native_decide
example : sin_test 100 2e-17 := by native_decide
example : sin_test (-100) 2e-17 := by native_decide

/-- `cos` tests -/
def cos_test (x : ℚ) (e : Interval) : Bool :=
  (cos (ofRat x)).size ≤ e.hi
example : cos_test 0 2e-19 := by native_decide
example : cos_test (1/7) 2e-19 := by native_decide
example : cos_test (-1/7) 2e-19 := by native_decide
example : cos_test 0.785 3e-19 := by native_decide
example : cos_test (-0.785) 3e-19 := by native_decide
example : cos_test 2 4e-19 := by native_decide
example : cos_test 3 4e-19 := by native_decide
example : cos_test 4 3e-18 := by native_decide
example : cos_test 5 2e-18 := by native_decide
example : cos_test 6 2e-18 := by native_decide
example : cos_test 7 2e-18 := by native_decide
example : cos_test 100 2e-17 := by native_decide
example : cos_test (-100) 2e-17 := by native_decide

-- Overflow cases
example : sin 1e100 = pm1 := by native_decide
example : cos 1e100 = pm1 := by native_decide
example : sin nan = pm1 := by native_decide
example : cos nan = pm1 := by native_decide
