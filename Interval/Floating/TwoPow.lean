import Interval.Floating.Standardization

open Pointwise

/-!
## Floating point powers of two
-/

open Set
open scoped Real
namespace Floating

/-!
### Exact powers of two
-/

/-- `two_pow` is valid -/
lemma valid_two_pow {n : Fixed 0} :
    let s : UInt64 := n.n.toUInt64 + (2^63 : UInt64)
    Valid (2^62) (s - 62) where
  zero_same := by intro n; contrapose n; clear n; fast_decide
  nan_same := by intro n; contrapose n; clear n; fast_decide
  norm := by intro _ _ _; fast_decide

/-- Exact powers of two -/
@[irreducible] def two_pow (n : Fixed 0) : Floating :=
  let s : UInt64 := n.n.toUInt64 + (2^63 : UInt64)
  bif n == nan || s < 62 then nan else
  { n := 2^62
    s := s - 62
    v := valid_two_pow }

/-- `two_pow` is conservative -/
@[approx] lemma mem_approx_two_pow (n : Fixed 0) : 2^n.val ∈ approx (two_pow n) := by
  rw [two_pow]
  simp only [bif_eq_if, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  by_cases b : n = nan ∨ n.n.toUInt64 + (2^63 : UInt64) < 62
  · rcases b with b | b; all_goals simp [b]
  simp only [not_or, not_lt, Ne] at b
  rcases b with ⟨nn, le⟩
  simp only [approx, ne_eq, neg_neg, nn, not_false_eq_true, Fixed.ne_nan_of_neg, not_lt.mpr le,
    or_self, ite_false, mem_ite_univ_left, mem_singleton_iff]
  intro h; clear h
  rw [val, Fixed.val]
  have e62 : ((2^62 : Int64) : ℤ) = 2^62 := by fast_decide
  have le' : 62 ≤ (n.n.toUInt64 + 2^63).toNat := by simpa only [UInt64.le_iff_toNat_le, u62] using le
  have v : ((n.n.toUInt64 + 2^63).toNat : ℤ) = (n.n : ℤ) + 2^63 := by
    have v := Int64.toNat_add_pow_eq_coe n.n
    have e : (2 ^ 63 : Int64).toUInt64 = 2 ^ 63 := by fast_decide
    rw [Int64.add_def, e] at v
    exact v
  simp only [Int64.coe_zero, zpow_zero, mul_one, Real.rpow_intCast, e62, Int.cast_pow,
    Int.cast_ofNat, UInt64.toInt, UInt64.toNat_sub'' le, u62, Nat.cast_sub le', v, Nat.cast_ofNat,
    sub_right_comm _ (62 : ℤ), add_sub_cancel_right]
  rw [mul_comm, zpow_sub₀ (by norm_num), ←zpow_natCast, Nat.cast_ofNat,
    div_mul_cancel₀ _ two_zpow_pos.ne']

/-!
### The special case of `n = 2^62`
-/

/-- `two_pow_special` is valid -/
lemma valid_two_pow_special {s : UInt64} : Valid (2^62) s where
  zero_same := by intro n; contrapose n; clear n; fast_decide
  nan_same := by intro n; contrapose n; clear n; fast_decide
  norm := by intro _ _ _; fast_decide

/-- Build `2^62 * 2^(s - 2^63)` -/
@[irreducible] def two_pow_special (s : UInt64) : Floating where
  n := 2^62
  s := s
  v := valid_two_pow_special

/-- `two_pow_special` never makes `nan` -/
@[simp] lemma two_pow_special_ne_nan (s : UInt64) : two_pow_special s ≠ nan := by
  rw [two_pow_special]
  simp only [ne_eq, ext_iff, n_nan, s_nan, not_and]
  intro n; contrapose n; clear n; fast_decide

/-- `two_pow_special` never makes `nan` -/
@[simp] lemma val_two_pow_special (s : UInt64) :
    (two_pow_special s).val = 2^(62 + (s.toNat : ℤ) - 2^63) := by
  have t0 : (2 : ℝ) ≠ 0 := by norm_num
  have e : ((2^62 : Int64) : ℤ) = 2^62 := by fast_decide
  rw [two_pow_special, val, e]
  simp only [Int.cast_pow, Int.cast_ofNat, UInt64.toInt, pow_mul_zpow t0]
  ring_nf
