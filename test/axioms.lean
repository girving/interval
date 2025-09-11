import Interval.Interval.Division
import Interval.Interval.Exp
import Interval.Interval.Log
import Interval.Interval.Pow
import Interval.Interval.Sincos

/-!
# Verify that `Interval` proofs do not depend on `native_decide`
-/

open Real in
/-- Arbitrary function that uses a lot of definitions from the library. -/
noncomputable def f (x : ℝ) : ℝ :=
  2 * x + (1 / x) + x⁻¹ + exp x + log x + sin x + cos x + x ^ (6 : ℝ) + x * x

open Interval in
/-- Arbitrary function that uses a lot of definitions from the library. -/
def Interval.f (x : Interval) : Interval :=
  2 * x + (1 / x) + x⁻¹ + exp x + log x + sin x + cos x + x ^ (6 : Interval) + x * x

lemma without_native_decide {x : Interval} {x' : ℝ} (hx : approx x x') : approx (x.f) (f x') := by
  simp only [f, Interval.f]
  approx

/-- info: 'without_native_decide' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms without_native_decide
