import Interval.Floating.Basic
import Interval.Floating.Order

/-!
## Floating point floor, producing `Int64` or `ℕ`
-/

open Set
open scoped Real
namespace Floating

/-- Floor -/
@[irreducible] def floor (x : Floating) : Fixed 0 :=
  bif x == nan || 2^63 < x.s then nan else
  ⟨x.n.shiftRightRound (2^63 - x.s) false⟩

/-- `floor` is conservative -/
@[approx] lemma mem_approx_floor (x : Floating) : ↑⌊x.val⌋ ∈ approx x.floor := by
  rw [floor]
  generalize hc : decide (2 ^ 63 < x.s) = c  -- Needed to avoid kernel blowups
  simp only [bif_eq_if, Bool.or_eq_true, beq_iff_eq]
  by_cases xn : x = nan
  · simp only [xn, s_nan, true_or, n_nan, ite_true, Fixed.approx_nan, mem_univ]
  simp only [xn, false_or]
  split_ifs with s63
  · simp only [Fixed.approx_nan, mem_univ]
  simp only [← hc, decide_eq_true_eq, not_lt] at s63
  simp only [approx, mem_if_univ_iff]
  intro n; clear n
  rw [val, Fixed.val]
  have eq : ((x.n : ℤ) : ℝ) * 2^(x.s.toInt - 2 ^ 63) =
      ((x.n : ℤ) / (2^(2^63 - x.s.toNat) : ℕ) : ℚ) := by
    simp only [UInt64.le_iff_toNat_le, UInt64.toNat_2_pow_63] at s63
    simp only [UInt64.toInt, Nat.cast_pow, Nat.cast_ofNat, Rat.cast_div, Rat.cast_intCast,
      Rat.cast_ofNat, ← neg_sub (2 ^ 63 : ℤ), zpow_neg, ← div_eq_mul_inv, ← zpow_natCast,
      Nat.cast_sub s63, Rat.cast_zpow, Rat.cast_ofNat]
  simp only [Int64.coe_shiftRightRound, UInt64.toNat_sub'' s63, UInt64.toNat_2_pow_63,
    Int64.coe_zero, zpow_zero, mul_one, mem_singleton_iff, Int.cast_inj, eq, Rat.floor_cast,
    Rat.floor_intCast_div_natCast]
  rw [Int.rdiv, Nat.cast_pow, Nat.cast_ofNat, cond_false]

@[simp] lemma floor_nan : (nan : Floating).floor = nan := by
  rw [floor]; simp only [beq_self_eq_true, s_nan, Bool.true_or, n_nan, cond_true]

@[simp] lemma ne_nan_of_floor {x : Floating} (n : x.floor ≠ nan) : x ≠ nan := by
  contrapose n; simp only [not_not] at n; simp [n]

lemma floor_mono {x y : Floating} (le : x ≤ y) (yn : y.floor ≠ nan) : x.floor ≤ y.floor := by
  by_cases xn : x.floor = nan
  · simp [xn]
  have hx := mem_approx_floor x
  have hy := mem_approx_floor y
  simp only [approx, xn, ↓reduceIte, mem_singleton_iff, yn] at hx hy
  simp only [Fixed.le_iff, ← hx, ← hy, Int.cast_le]
  bound

/-!
### `natFloor` producing `ℕ`
-/

/-- The greatest natural definitely `≤ x` (or 0 if that fails) -/
def natFloor (x : Floating) : ℕ :=
  x.floor.n.natFloor

@[simp] lemma natFloor_nan : (nan : Floating).natFloor = 0 := by decide +kernel

lemma natFloor_le {a : ℝ} {x : Floating} (ax : a ∈ approx x) : x.natFloor ≤ ⌊a⌋₊ := by
  rw [natFloor, Int64.natFloor_eq]
  by_cases fn : x.floor = nan
  · simp [fn]
  have af := mem_approx_floor x
  simp only [approx, ne_eq, fn, not_false_eq_true, Floating.ne_nan_of_floor, ↓reduceIte,
    mem_singleton_iff] at ax af
  trans ⌊x.floor.val⌋₊
  · simp [Fixed.val_of_s0]
  · simp only [← af, ax]
    apply Nat.floor_le_floor
    apply Int.floor_le
