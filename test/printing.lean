import Interval

open Interval


/-!
## Print `Decimal`
-/

private def print_test (x : Decimal) (s : String) : Bool := toString (repr x) == s
example : print_test 123e-2 "1.23" := by native_decide
example : print_test 1.23 "1.23" := by native_decide
example : print_test 1.0 "1" := by native_decide
example : print_test 1.70 "1.7" := by native_decide
example : print_test 1.7e7 "1.7e7" := by native_decide
example : print_test 1.7e-7 "1.7e-7" := by native_decide
example : print_test 1.7e-0 "1.7" := by native_decide
example : print_test 1e7 "1e7" := by native_decide
example : print_test 1e-7 "1e-7" := by native_decide
example : print_test 100e-7 "1e-5" := by native_decide
example : print_test 200e7 "2e9" := by native_decide
example : print_test 501e7 "5.01e9" := by native_decide
example : print_test 301e-7 "3.01e-5" := by native_decide
example : print_test (-3e-7) "-3e-7" := by native_decide
