import Interval.Interval.Basic
import Interval.Interval.Conversion
import Interval.Series
import Mathlib.Tactic.Basic

section Decimal

/-!
## Print `Decimal`
-/

private def Decimal.print_test (x : Decimal) (s : String) : Bool := toString (repr x) == s

example : Decimal.print_test 123e-2 "1.23" := by native_decide
example : Decimal.print_test 1.23 "1.23" := by native_decide
example : Decimal.print_test 1.0 "1" := by native_decide
example : Decimal.print_test 1.70 "1.7" := by native_decide
example : Decimal.print_test 1.7e7 "1.7e7" := by native_decide
example : Decimal.print_test 1.7e-7 "1.7e-7" := by native_decide
example : Decimal.print_test 1.7e-0 "1.7" := by native_decide
example : Decimal.print_test 1e7 "1e7" := by native_decide
example : Decimal.print_test 1e-7 "1e-7" := by native_decide
example : Decimal.print_test 100e-7 "1e-5" := by native_decide
example : Decimal.print_test 200e7 "2e9" := by native_decide
example : Decimal.print_test 501e7 "5.01e9" := by native_decide
example : Decimal.print_test 301e-7 "3.01e-5" := by native_decide
example : Decimal.print_test (-3e-7) "-3e-7" := by native_decide

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

end Decimal


/-!
## Print `Interval`
-/

section Interval

-- #eval repr (0 : Interval) -- STACK OVERFLOW

private def Interval.print (x : Interval) : String := toString (repr x)

-- #eval Interval.print 0 == "0"
#guard Interval.print nan == "nan"
#guard Interval.print 1 == "1"
#guard Interval.print 1.0 == "1"
#guard Interval.print 123e-2 == "1.2299999999999999999 ± 1.2e-19"
#guard Interval.print 1.23 == "1.2299999999999999999 ± 1.2e-19"
#guard Interval.print 1.70 == "1.69999999999999999993 ± 1.2e-19"
#guard Interval.print 1.7e-7 == "1.70000000000000000002e-7 ± 1.4e-26"
#guard Interval.print 1.7e-0 == "1.69999999999999999993 ± 1.2e-19"
#guard Interval.print 1e7 == "1e7"
#guard Interval.print 2e7 == "2e7"
#guard Interval.print 1e-7 == "1.000000000000000000049e-7 ± 6.5e-27"
#guard Interval.print 100e-7 == "9.99999999999999999994e-6 ± 8.4e-25"
#guard Interval.print 200e7 == "2e9"
#guard Interval.print 501e7 == "5.01e9"
#guard Interval.print 301e-7 == "3.00999999999999999994e-5 ± 1.8e-24"
#guard Interval.print (-3e-7) == "-2.99999999999999999996e-7 ± 2.7e-26"

#guard Interval.print (.exp 1) == "2.718281828459045235 ± 1.2e-17"

/--
info: 2.718281828459045235 ± 1.2e-17
-/
#guard_msgs in
#eval Interval.exp 1

/--
info: 1.23456789012341234122e9 ± 1.3e-10
-/
#guard_msgs in #eval (
    1234567890.12341234123412341234123412341234234123412341234123412341234 : Interval)

end Interval
