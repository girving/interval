import Interval.Fixed

/-!
## Unit tests for `Fixed`
-/

/-- Test `Fixed.repoint` -/
example : (.ofNat 7 false : Fixed 0).repoint (-60) true != nan := by native_decide
example : (.ofNat 7 false : Fixed 0).repoint (-60) false != nan := by native_decide
example : (.ofNat 14 false : Fixed 0).repoint 2 false == (.ofNat 14 false) := by native_decide
example : (.ofNat 14 false : Fixed 0).repoint 2 true == (.ofNat 14 true) := by native_decide
example : (.ofNat 14 false : Fixed 0).repoint 2 true != (.ofNat 14 false) := by native_decide
