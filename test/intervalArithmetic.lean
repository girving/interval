import Interval

open Interval

/-!
### Division
-/

/-- We're don't verify anything about `inv_guess`, but we do need some tests -/
def guess_test (x : Float) (e : Float := 1e-10) : Bool :=
  ((inv_guess (.ofFloat x false : Floating) : Floating).toFloat - 1 / x).abs < e
example : guess_test 0.5 := by native_decide
example : guess_test 0.67862 := by native_decide
example : guess_test 0.999 (1e-9) := by native_decide
example : guess_test 0.67862 := by native_decide
example : guess_test 1e-4 := by native_decide
example : guess_test 7 := by native_decide

/-- `Interval.inv` is provably conservative, but we need to test that it's accurate -/
def inv_test (l h : Float) (e : Float := 1e-100) : Bool :=
  let x : Interval := ofFloat l ∪ ofFloat h
  let r := x⁻¹
  (r.lo.toFloat * h - 1).abs < e && (r.hi.toFloat * l - 1).abs ≤ e
example : inv_test 0.4 0.6 := by native_decide
example : inv_test 0.4871231 17.87341 := by native_decide
example : inv_test 0.001871 17.87341 1e-15 := by native_decide
example : inv_test (-0.6) (-0.4) 1e-100 := by native_decide
example : inv_test (-17.87341) (-0.4871231) := by native_decide
example : inv_test (-17.87341) (-0.001871) 1e-15 := by native_decide
example : inv_test 7 7 := by native_decide
