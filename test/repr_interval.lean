import Interval.Interval.Basic
import Interval.Interval.Conversion
import Interval.Series

/-!
# `Repr Interval` unit tests
-/

namespace Interval

private def repr_test (x : Interval) : String := reprStr x

#guard repr_test 0 == "0"
#guard repr_test nan == "nan"
#guard repr_test 1 == "1"
#guard repr_test 1.0 == "1"
#guard repr_test 123e-2 == "1.2299999999999999999 ± 1.2e-19"
#guard repr_test 1.23 == "1.2299999999999999999 ± 1.2e-19"
#guard repr_test 1.70 == "1.69999999999999999993 ± 1.2e-19"
#guard repr_test 1.7e-7 == "1.70000000000000000002e-7 ± 1.4e-26"
#guard repr_test 1.7e-0 == "1.69999999999999999993 ± 1.2e-19"
#guard repr_test 1e7 == "1e7"
#guard repr_test 2e7 == "2e7"
#guard repr_test 1e-7 == "1.000000000000000000049e-7 ± 6.5e-27"
#guard repr_test 100e-7 == "9.99999999999999999994e-6 ± 8.4e-25"
#guard repr_test 200e7 == "2e9"
#guard repr_test 501e7 == "5.01e9"
#guard repr_test 301e-7 == "3.00999999999999999994e-5 ± 1.8e-24"
#guard repr_test (-3e-7) == "-2.99999999999999999996e-7 ± 2.7e-26"
#guard repr_test (.exp 1) == "2.71828182845904523542 ± 2.3e-19"

/--
info: 2.71828182845904523542 ± 2.3e-19
-/
#guard_msgs in
#eval Interval.exp 1

/--
info: 1.23456789012341234122e9 ± 1.3e-10
-/
#guard_msgs in #eval (
    1234567890.12341234123412341234123412341234234123412341234123412341234 : Interval)

end Interval
