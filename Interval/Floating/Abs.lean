import Interval.Floating.Basic
import Interval.Floating.Order

/-!
## Floating point absolute value
-/

open Set
open scoped Real
namespace Floating

/-- `abs` is valid -/
lemma valid_abs {x : Floating} : Valid x.n.uabs.toInt64 x.s where
  zero_same := by
    intro h
    apply x.zero_same
    simpa only [Int64.ext_iff, Int64.n_zero, Int64.uabs_eq_zero_iff,
      UInt64.toUInt64_toInt64] using h
  nan_same := by
    intro h
    apply x.nan_same
    simpa only [Int64.ext_iff, Int64.n_min, Int64.uabs_eq_pow_iff,
      UInt64.toUInt64_toInt64] using h
  norm := by
    intro n0 nm s0
    simp only [Int64.uabs_uabs, Int64.ext_iff, Int64.n_zero, Int64.n_min,
      Int64.uabs_eq_zero_iff, Ne, Int64.uabs_eq_pow_iff, UInt64.toUInt64_toInt64] at n0 nm ⊢
    refine x.norm ?_ ?_ s0
    all_goals simp only [ne_eq, Int64.ext_iff, Int64.n_zero, ne_eq, Int64.ext_iff, Int64.n_min]
    · exact n0
    · exact nm

/-- Absolute value -/
@[irreducible] def abs (x : Floating) : Floating where
  n := x.n.uabs.toInt64
  s := x.s
  v := valid_abs

-- Definition lemmas
@[simp] lemma n_abs {x : Floating} : x.abs.n = x.n.uabs.toInt64 := by rw [abs]
@[simp] lemma s_abs {x : Floating} : x.abs.s = x.s := by rw [abs]

/-- `abs` preserves `nan` -/
@[simp] lemma abs_nan : (nan : Floating).abs = nan := by simp only [abs, nan]; decide

/-- `abs` preserves `nan` -/
@[simp] lemma abs_eq_nan {x : Floating} : x.abs = nan ↔ x = nan := by
  simp only [ext_iff, n_abs, n_nan, Int64.ext_iff, Int64.n_min, Int64.uabs_eq_pow_iff, s_abs, s_nan,
    UInt64.toUInt64_toInt64]

/-- `abs` is exact away from `nan` -/
@[simp] lemma val_abs {x : Floating} (n : x ≠ nan) : x.abs.val = |x.val| := by
  rw [val, val]
  simp only [abs_mul, abs_of_pos (two_zpow_pos (𝕜 := ℝ)), n_abs, s_abs]
  refine congr_arg₂ _ ?_ rfl
  simp only [Int64.coe_of_nonneg (Int64.isNeg_uabs (x.n_ne_min n)), Int64.toNat_uabs,
    Int.natCast_natAbs, Int.cast_abs, UInt64.toUInt64_toInt64]

/-- `abs` is nonnegative away from `nan` -/
@[simp] lemma abs_nonneg {x : Floating} (n : x ≠ nan) : 0 ≤ x.abs.val := by
  simp only [val_abs n]; apply _root_.abs_nonneg

/-- `abs` is the identity for nonnegatives (since `nan < 0`) -/
@[simp] lemma abs_of_nonneg {x : Floating} (x0 : 0 ≤ x.val) : x.abs = x := by
  have xn : 0 ≤ x.n := by simpa only [n_nonneg_iff]
  simp only [ext_iff, n_abs, s_abs, and_true, Int64.uabs_eq_self' xn, Int64.toInt64_toUInt64]

/-- `abs` is negates nonpositives (since `-nan = nan`) -/
@[simp] lemma abs_of_nonpos {x : Floating} (x0 : x.val ≤ 0) : x.abs = -x := by
  by_cases z : x = 0
  · simp only [z, val_zero, le_refl, abs_of_nonneg, neg_zero]
  have x0' := Ne.lt_of_le (val_ne_zero.mpr z) x0
  have xn : x.n < 0 := by simpa only [isNeg_iff, decide_eq_true_eq]
  simp only [ext_iff, n_abs, Int64.uabs_eq_neg' xn, Int64.neg_def, n_neg, s_abs, s_neg, and_self,
    Int64.toInt64_toUInt64]

/-- `abs` is conservative -/
@[approx] lemma mem_approx_abs {a : ℝ} {x : Floating} (ax : a ∈ approx x) : |a| ∈ approx x.abs := by
  by_cases n : x = nan
  · simp only [n, abs_nan, approx_nan, mem_univ]
  · simp only [ne_eq, n, not_false_eq_true, approx_eq_singleton, mem_singleton_iff, abs_eq_nan,
      val_abs] at ax ⊢
    rw [ax]
