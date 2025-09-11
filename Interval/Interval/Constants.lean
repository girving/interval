import Interval.Interval.Conversion

open Pointwise

/-!
## Generic constant approximation machinery

We approximate irrational constants by computing a rational ball which contains the value, then
converting the ball to `Interval` in two ways:
1. Via just the midpoint.
2. As a union of the two endpoints.
For sufficiently small rational balls these two methods coincide, so we also know we have a tight
`Interval`.

Warning: It is crucial for downstream `decide` performance that the defined constants in this file
are as simple as possible. That is, we do not want to define them as results of nontrivial interval
computations, including coersions, since this will slow all downstream use.
-/

open Set
open scoped Real
namespace Interval

/-- Approximate a real given a rational `m ± r` ball containing it -/
lemma approx_of_rat_ball {x : ℝ} {m r : ℚ} (h : |x - m| ≤ r) :
    approx (Interval.ofRat (m - r) ∪ .ofRat (m + r)) x := by
  simp only [abs_le, neg_le_sub_iff_le_add, tsub_le_iff_right] at h
  simp only [approx, lo_eq_nan, or_iff_not_imp_left]
  intro n
  obtain ⟨n0, n1⟩ := ne_nan_of_union n
  simp only [Union.union, Floating.max_comm, Floating.val_min, min_le_iff, le_max_iff,
    Floating.val_max (hi_ne_nan n1) (hi_ne_nan n0)]
  refine ⟨.inl ?_, .inl ?_⟩
  · refine le_trans (lo_le n0 ?_) (by linarith : m - r ≤ x)
    rw [← Rat.cast_sub]
    approx
  · refine le_trans (by linarith : x ≤ m + r) (le_hi n1 ?_)
    rw [← Rat.cast_add]
    approx
