import Interval.Interval.Exp
import Interval.Interval.Log
import Interval.Interval.Pow

/-!
### Unit tests for series computations: `exp`, `log` and `pow`

We test only the width of the resulting intervals, since their correctness is proven earlier.
-/

open Interval

/-- `exp` series tests (for small `x`) -/
def exp_series_test (x : ℚ) (e : Float := 4e-19) : Bool :=
  (exp_series_16.eval (.ofRat x)).size.toFloat < e
lemma exp_series_test1 : exp_series_test 0 := by native_decide
lemma exp_series_test2 : exp_series_test (1/7) := by native_decide
lemma exp_series_test3 : exp_series_test (-1/7) := by native_decide
lemma exp_series_test4 : exp_series_test 0.34656 := by native_decide
lemma exp_series_test5 : exp_series_test (-0.34656) := by native_decide

/-- `log1p_div` series tests (for small `x`) -/
def log1p_div_series_test (x : ℚ) (e : Float := 3e-18) : Bool :=
  (log1p_div_series_38.eval (.ofRat x)).size.toFloat < e
lemma log1p_div_series_test1 : log1p_div_series_test 0 := by native_decide
lemma log1p_div_series_test2 : log1p_div_series_test (1/7) := by native_decide
lemma log1p_div_series_test3 : log1p_div_series_test (-1/7) := by native_decide
lemma log1p_div_series_test4 : log1p_div_series_test (1/3) := by native_decide
lemma log1p_div_series_test5 : log1p_div_series_test (-1/3) := by native_decide

/-- `exp` tests -/
def exp_test (x : ℚ) (e : Interval) : Bool :=
  let y := (Interval.ofRat x).exp
  y.size ≤ e.hi.mul y.lo true
example : exp_test 0 3.3e-19 := by native_decide
example : exp_test 10 3.7e-18 := by native_decide
example : exp_test (-10) 7e-18 := by native_decide

/-- `log` tests -/
def log_test (x : ℚ) (e : Float) : Bool := (Interval.ofRat x).log.size.toFloat ≤ e
example : log_test 1 0 := by native_decide
example : log_test 2 2e-19 := by native_decide
example : log_test 1237821 6e-18 := by native_decide
example : log_test 1e-8 7e-18 := by native_decide

/-- `pow` tests -/
def pow_test (x y : ℚ) (e : Float) : Bool :=
  ((Interval.ofRat x) ^ (Interval.ofRat y)).size.toFloat ≤ e
example : pow_test 3.7 4.2 2e-15 := by native_decide
example : pow_test 0.1 (-1/2) 5e-18 := by native_decide
example : pow_test 2 (1/2) 7e-19 := by native_decide
example : pow_test 2 (1/100) 3e-19 := by native_decide
