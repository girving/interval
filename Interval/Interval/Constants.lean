import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Interval.Interval.Conversion
import Interval.Tactic.Decide

open Pointwise

/-!
## High accuracy computation of particular constants
-/

open Set
open scoped Real
namespace Interval

/-!
### Generic approximation machinery

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

/-- Approximate a real given a rational `m ± r` ball containing it -/
lemma approx_of_rat_ball {x : ℝ} {m r : ℚ} (h : |x - m| ≤ r) :
    x ∈ approx (Interval.ofRat (m - r) ∪ .ofRat (m + r)) := by
  simp only [abs_le, neg_le_sub_iff_le_add, tsub_le_iff_right] at h
  simp only [approx, lo_eq_nan, mem_ite_univ_left, mem_Icc]
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

/-!
### `log 2` and friends
-/

-- We do some calculations over `ℚ`, then convert to `Interval`
namespace Log2

def n : ℕ := 70
def x : ℚ := 1/2
def radius : ℚ := 1 / 1180591620717411303424
def mid : ℚ := -81026204946914272618346609082102250801114907729 /
    116896104058966015646750947554978314987992252416
lemma radius_eq : radius = |x| ^ (n + 1) / (1 - |x|) := by rfl
lemma mid_eq : mid = -∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1 : ℚ) := by rfl
def interval : Interval := ((mid - radius : ℚ) : Interval) ∪ ((mid + radius : ℚ) : Interval)

lemma close : |Real.log (1/2) - mid| ≤ radius := by
  rw [(by norm_num : (1/2 : ℝ) = 1 - 1/2), sub_eq_neg_add]
  simp only [mid_eq, x, radius_eq, Rat.cast_neg, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_one, neg_neg, Rat.cast_ofNat, Rat.cast_abs,
    Rat.cast_sub]
  refine Real.abs_log_sub_add_sum_range_le ?_ n
  rw [abs_of_pos]
  all_goals norm_num

def inv_mid : ℚ := 1 / -mid
def inv_radius : ℚ := radius / (|mid| * |-mid - radius|)
def inv_interval : Interval :=
  ((inv_mid - inv_radius : ℚ) : Interval) ∪ ((inv_mid + inv_radius : ℚ) : Interval)

lemma inv_close : |(Real.log 2)⁻¹ - inv_mid| ≤ inv_radius := by
  have e : (Real.log 2)⁻¹ = -(Real.log (1/2))⁻¹ := by
    simp only [one_div, Real.log_inv, _root_.inv_neg, neg_neg]
  have c := close
  have c1 : Real.log (1/2) ≤ mid + radius := by simp only [abs_le] at c; linarith
  have c0 : Real.log (1/2) < 0 := by
    refine lt_of_le_of_lt c1 ?_
    simp only [← Rat.cast_add, Rat.cast_lt_zero]
    rfl
  have c2 : -mid - radius ≤ |Real.log (1/2)| := by
    simp only [abs_le, abs_of_neg c0] at c ⊢; linarith
  have mid0 : 0 < |(mid : ℝ)| := by simp only [← Rat.cast_abs, Rat.cast_pos]; rfl
  simp only [e, inv_mid, one_div, _root_.inv_neg, Rat.cast_neg, Rat.cast_inv, sub_neg_eq_add,
    ← sub_eq_neg_add] at c c0 c1 c2 ⊢
  rw [inv_sub_inv _ c0.ne, abs_div, abs_mul]
  refine le_trans (div_le_div_of_nonneg_right c (by positivity)) ?_
  refine le_trans (div_le_div_of_nonneg_left ?_ ?_ (mul_le_mul_of_nonneg_left c2 ?_)) ?_
  all_goals try simp only [Rat.cast_nonneg, ← Rat.cast_sub, ← Rat.cast_mul, Rat.cast_pos,
    ← Rat.cast_div, Rat.cast_le, ← Rat.cast_neg, ← Rat.cast_abs, Rat.cast_ne_zero, c0.ne]
  all_goals fast_decide

lemma v0 : Floating.Valid 12053589751108223786 9223372036854775745 := by decide
lemma v1 : Floating.Valid 12053589751108223787 9223372036854775745 := by decide
lemma v2 : Interval.Valid ⟨12053589751108223786, 9223372036854775745, v0⟩
    ⟨12053589751108223787, 9223372036854775745, v1⟩ := by fast_decide

end Log2

/-- Optimal `Interval` approximation of `log (1/2)` -/
@[irreducible] def log_half : Interval :=
  -- Created via `#eval raw (Log2.mid : Interval)`
  ⟨⟨12053589751108223786, 9223372036854775745, Log2.v0⟩,
   ⟨12053589751108223787, 9223372036854775745, Log2.v1⟩, Log2.v2⟩

/-- Optimal `Interval` approximation of `log 2` -/
@[irreducible] def log_two : Interval := -log_half

/-- Optimal `Interval` approximation of `(log 2)⁻¹` -/
@[irreducible] def inv_log_two : Interval := Log2.inv_mid

set_option trace.profiler true in
set_option trace.profiler.useHeartbeats true in
@[approx] lemma approx_log_half : Real.log (1/2) ∈ approx log_half := by
  rw [(by fast_decide : log_half = Log2.interval)]
  exact approx_of_rat_ball Log2.close

#exit

@[approx] lemma approx_log_two : Real.log 2 ∈ approx log_two := by
  rw [(by norm_num : (2:ℝ) = (1/2)⁻¹), Real.log_inv, log_two]
  approx

@[approx] lemma approx_inv_log_two : (Real.log 2)⁻¹ ∈ approx inv_log_two := by
  rw [(by native_decide : inv_log_two = Log2.inv_interval)]
  exact approx_of_rat_ball Log2.inv_close

/-- For use in untrusted contexts, `inv_log_two.hi` is closer to the true value -/
def _root_.Floating.inv_log_two := Interval.inv_log_two.hi
