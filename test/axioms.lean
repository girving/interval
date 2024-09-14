import Interval.Interval.Division
import Interval.Interval.Exp
import Interval.Interval.Log
import Interval.Interval.Pow

/-!
# Verify that `Interval` proofs do not depend on `native_decide`
-/

open Real in
/-- Arbitrary function that uses a lot of definitions from the library. -/
noncomputable def f (x : ℝ) : ℝ :=
  2 * x + (1 / x) + x⁻¹ + exp x + log x + x ^ (6 : ℝ) + x * x

open Interval in
/-- Arbitrary function that uses a lot of definitions from the library. -/
def Interval.f (x : Interval) : Interval :=
  2 * x + (1 / x) + x⁻¹ + exp x + log x + x ^ (6 : Interval) + x * x

lemma without_native_decide (x : ℝ) (x' : Interval) (hx : x ∈ approx x') :
    f x ∈ approx (x'.f) := by
  simp only [f, Interval.f]
  approx

/-- info: 'without_native_decide' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms without_native_decide
