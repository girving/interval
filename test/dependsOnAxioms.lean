import Interval.Series

open Real in
/-- Arbitrary function that uses a lot of definitions from the library. -/
noncomputable def f (x : ℝ) : ℝ :=
  2 * x + (1 / x) + x⁻¹ + exp x + log x + x ^ (6 : ℝ) + x * x

open Interval in
/-- Arbitrary function that uses a lot of definitions from the library. -/
def Interval.f (x : Interval) : Interval :=
  2 * x + (1 / x) + x⁻¹ + exp x + log x + x.pow 6 + x * x

lemma example_lemma_noNativedecide (x : ℝ) (x' : Interval) (hx : x ∈ approx x') :
    f x ∈ approx (x'.f) := by
  simp only [f, Interval.f]
  approx

/-- info: 'example_lemma_noNativedecide' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms example_lemma_noNativedecide
