import Interval.Misc.Decimal

/-!
## `Repr Decimal` unit tests
-/

namespace Decimal

private def repr_test (x : Decimal) (s : String) : Bool := reprStr x == s

example : repr_test 123e-2 "1.23" := by native_decide
example : repr_test 1.23 "1.23" := by native_decide
example : repr_test 1.0 "1" := by native_decide
example : repr_test 1.70 "1.7" := by native_decide
example : repr_test 1.7e7 "1.7e7" := by native_decide
example : repr_test 1.7e-7 "1.7e-7" := by native_decide
example : repr_test 1.7e-0 "1.7" := by native_decide
example : repr_test 1e7 "1e7" := by native_decide
example : repr_test 1e-7 "1e-7" := by native_decide
example : repr_test 100e-7 "1e-5" := by native_decide
example : repr_test 200e7 "2e9" := by native_decide
example : repr_test 501e7 "5.01e9" := by native_decide
example : repr_test 301e-7 "3.01e-5" := by native_decide
example : repr_test (-3e-7) "-3e-7" := by native_decide

/--
info: 3.01e-5
-/
#guard_msgs in #eval (301e-7 : Decimal)

/--
info: 3.04565464561e-4564564556
-/
#guard_msgs in #eval (304565464561e-4564564567 : Decimal)

/--
info: 1.23456789012341234123412341234123412341234234123412341234123412341234e9
-/
#guard_msgs in #eval (
    1234567890.12341234123412341234123412341234234123412341234123412341234 : Decimal)
