import Interval


open Interval

/-!
### Unit tests for Interval: `exp`, `log` and `pow`

We test only the width of the resulting intervals, since their correctness is proved above.

I'm not happy with the precision we reach, but I will set debugging that aside for now.
-/

/-- `exp` series tests (for small `x`) -/
def exp_series_test (x : ℚ) (e : Float := 1e-17) : Bool :=
  (exp_series_16.eval (.ofRat x)).size.toFloat < e
lemma exp_series_test1 : exp_series_test 0 := by native_decide
lemma exp_series_test2 : exp_series_test (1/7) := by native_decide
lemma exp_series_test3 : exp_series_test (-1/7) := by native_decide
lemma exp_series_test4 : exp_series_test 0.34656 := by native_decide
lemma exp_series_test5 : exp_series_test (-0.34656) := by native_decide

/-- `log1p_div` series tests (for small `x`) -/
def log1p_div_series_test (x : ℚ) (e : Float := 2e-17) : Bool :=
  (log1p_div_series_38.eval (.ofRat x)).size.toFloat < e
lemma log1p_div_series_test1 : log1p_div_series_test 0 := by native_decide
lemma log1p_div_series_test2 : log1p_div_series_test (1/7) := by native_decide
lemma log1p_div_series_test3 : log1p_div_series_test (-1/7) := by native_decide
lemma log1p_div_series_test4 : log1p_div_series_test (1/3) := by native_decide
lemma log1p_div_series_test5 : log1p_div_series_test (-1/3) := by native_decide

/-- Our constants are accurately estimated -/
lemma log_2_size_test : Interval.log_2.size.toFloat < 2e-17 := by native_decide
lemma untrusted_inv_log_2_test : untrusted_inv_log_2.toFloat * 0.693147180559945309417 == 1 := by
  native_decide

/-- `exp` tests -/
def exp_test (x : ℚ) (e : Float) : Bool :=
  let y := (Interval.ofRat x).exp
  y.size.toFloat ≤ e * y.lo.toFloat
example : exp_test 0 1e-18 := by native_decide
example : exp_test 10 1e-16 := by native_decide
example : exp_test (-10) 1e-15 := by native_decide

/-- `log` tests -/
def log_test (x : ℚ) (e : Float) : Bool := (Interval.ofRat x).log.size.toFloat ≤ e
example : log_test 1 0 := by native_decide
example : log_test 2 1e-17 := by native_decide
example : log_test 1237821 1e-15 := by native_decide
example : log_test 1e-8 1e-15 := by native_decide

/-- `pow` tests -/
def pow_test (x y : ℚ) (e : Float) : Bool :=
  ((Interval.ofRat x).pow (Interval.ofRat y)).size.toFloat ≤ e
example : pow_test 3.7 4.2 1e-13 := by native_decide
example : pow_test 0.1 (-1/2) 1e-16 := by native_decide
example : pow_test 2 (1/2) 1e-16 := by native_decide
example : pow_test 2 (1/100) 1e-17 := by native_decide
