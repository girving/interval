import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Interval.Interval.Constants
import Interval.Tactic.Decide

open Pointwise

/-!
## Interval approximations of `log 2` and friends
-/

open Set
open scoped Real
namespace Interval

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

@[approx] lemma approx_log_half : Real.log (1/2) ∈ approx log_half := by
  rw [(by fast_decide : log_half = Log2.interval)]
  exact approx_of_rat_ball Log2.close

@[approx] lemma approx_log_two : Real.log 2 ∈ approx log_two := by
  rw [(by norm_num : (2:ℝ) = (1/2)⁻¹), Real.log_inv, log_two]
  approx

@[approx] lemma approx_inv_log_two : (Real.log 2)⁻¹ ∈ approx inv_log_two := by
  rw [(by fast_decide : inv_log_two = Log2.inv_interval)]
  exact approx_of_rat_ball Log2.inv_close

/-- For use in untrusted contexts, `inv_log_two.hi` is closer to the true value -/
def _root_.Floating.inv_log_two := Interval.inv_log_two.hi
