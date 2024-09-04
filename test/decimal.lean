import Interval.Misc.Decimal

/-!
# Unit tests for `Decimal`
-/

open Decimal

-- Test `ofBinary`. Note that `2^20 = 1048576, 2^(-20) = 9.5367431640625e-07`
example : ofBinary 1 20 3 false = 1.048e6 := by native_decide
example : ofBinary 1 20 3 true = 1.049e6 := by native_decide
example : ofBinary 1 20 5 false = 1.04857e6 := by native_decide
example : ofBinary 1 20 5 true = 1.04858e6 := by native_decide
example : ofBinary 1 (-20) 2 false = 9.53e-7 := by native_decide
example : ofBinary 1 (-20) 2 true = 9.54e-7 := by native_decide
example : ofBinary 1 (-20) 4 false = 9.5367e-7 := by native_decide
example : ofBinary 1 (-20) 4 true = 9.5368e-7 := by native_decide
example : ofBinary (-1) (-20) 4 true = -9.5367e-7 := by native_decide
