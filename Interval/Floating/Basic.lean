import Mathlib.Data.Real.Basic
import Interval.Approx
import Interval.Fixed
import Interval.Int64
import Interval.UInt128
import Interval.Misc.Decimal
import Interval.Misc.Int
import Interval.Misc.Raw
import Interval.Misc.Real

open Pointwise

/-!
## Floating point arithmetic

The floating point number `⟨n,s⟩` represents `n * 2^(s - 2^63)`, where `n : Int64`, `s : UInt64`.
-/

open Set
open scoped Real

/-!
## `Floating` basics
-/

/-- Validity of a `Floating` as a single type -/
structure Floating.Valid (n : Int64) (s : UInt64) : Prop where
  /-- `0` has a single, standardized representation -/
  zero_same : n = 0 → s = 0
  /-- `nan` has a single, standardized representation -/
  nan_same : n = .minValue → s = .max
  /-- If we're not `0`, `nan`, or denormalized, the high bit of `n` is set -/
  norm : n ≠ 0 → n ≠ .minValue → s ≠ 0 → 2^62 ≤ n.uabs

/-- Floating point number -/
@[unbox] structure Floating where
  /-- Unscaled value -/
  n : Int64
  /-- Binary exponent + `2^63` -/
  s : UInt64
  /-- We're valid and normalized -/
  v : Floating.Valid n s
  deriving DecidableEq

namespace Floating

variable {a : ℝ}

-- Direct access to the fields of `Floating.Valid`
lemma zero_same (x : Floating) : x.n = 0 → x.s = 0 := x.v.zero_same
lemma nan_same (x : Floating) : x.n = .minValue → x.s = .max := x.v.nan_same
lemma norm (x : Floating) : x.n ≠ 0 → x.n ≠ .minValue → x.s ≠ 0 → 2^62 ≤ x.n.uabs := x.v.norm

/-- Computational version of `Floating.Valid` -/
def valid (n : Int64) (s : UInt64) : Bool :=
  bif n == 0 then s == 0 else
  bif n == .minValue then s == .max else
  s == 0 || ((1 : UInt64) <<< 62) ≤ n.uabs

/-- `Floating.valid` decides `Floating.Valid` -/
lemma valid_iff {n : Int64} {s : UInt64} : Valid n s ↔ valid n s = true := by
  rw [valid]
  have e : (2 : UInt64)^62 = (1 : UInt64) <<< 62 := by decide +kernel
  simp only [Bool.cond_eq_true_distrib, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro ⟨zs, ns, norm⟩
    split_ifs
    all_goals simp_all
    by_cases s0 : s = 0
    all_goals simp_all
  · split_ifs
    · intro s0; refine ⟨by simp_all, by simp_all, by simp_all⟩
    · intro s0; refine ⟨by simp_all, by simp_all, by simp_all⟩
    · intro s0; refine ⟨by simp_all, by simp_all, by intro _ _ s0; simp_all⟩

/-- `Valid` is decidable -/
instance (n : Int64) (s : UInt64) : Decidable (Valid n s) :=
  if v : valid n s then .isTrue (valid_iff.mpr v)
  else .isFalse (valid_iff.not.mpr v)

instance : BEq Floating where
  beq x y := x.n == y.n && x.s == y.s

lemma beq_def {x y : Floating} : (x == y) = (x.n == y.n && x.s == y.s) := rfl

instance : LawfulBEq Floating where
  eq_of_beq {x y} e := by
    induction x
    induction y
    simp only [Floating.beq_def, Bool.and_eq_true, beq_iff_eq] at e
    simp only [e.1, e.2]
  rfl {x} := by
    induction x
    simp only [Floating.beq_def, Bool.and_eq_true, beq_iff_eq, true_and]

lemma ext_iff {x y : Floating} : x = y ↔ x.n = y.n ∧ x.s = y.s := by
  induction x; induction y; simp only [mk.injEq]

/-- Standard floating point nan -/
instance : Nan Floating where
  nan := ⟨.minValue, .max, by decide⟩

/-- The `ℝ` that a `Floating` represents, if it's not `nan` -/
noncomputable def val (x : Floating) : ℝ :=
  ((x.n : ℤ) : ℝ) * (2 : ℝ)^(x.s.toInt - 2^63)

/-- The `ℚ` that a `Floating` represents, if it's not `nan` -/
def valq (x : Floating) : ℚ :=
  ((x.n : ℤ) : ℚ) * (2 : ℚ)^(x.s.toInt - 2^63)

/-- `Floating` approximates `ℝ` -/
instance : Approx Floating ℝ where
  approx x a := x = nan ∨ x.val = a

/-- `0 : Floating` -/
instance : Zero Floating where
  zero := ⟨0, 0, by decide⟩

/-- `1 : Floating` -/
instance : One Floating where
  one := ⟨2^62, 2^63 - 62, by decide +kernel⟩

-- Definition lemmas
@[simp] lemma n_zero : (0 : Floating).n = 0 := rfl
@[simp] lemma s_zero : (0 : Floating).s = 0 := rfl
@[simp] lemma n_one : (1 : Floating).n = 2^62 := rfl
@[simp] lemma s_one : (1 : Floating).s = 2^63 - 62 := rfl
@[simp] lemma n_nan : (nan : Floating).n = .minValue := rfl
@[simp] lemma s_nan : (nan : Floating).s = .max := rfl

/-- `nan` could be anything -/
instance : ApproxNan Floating ℝ where
  approx_nan a := by simp only [approx, true_or]

/-- `0 = 0` -/
@[simp] lemma val_zero : (0 : Floating).val = 0 := by
  simp only [val, n_zero, Int64.coe_zero, Int.cast_zero, s_zero, zero_mul]

/-- `0 ≠ nan` -/
@[simp] lemma zero_ne_nan : (0 : Floating) ≠ nan := by decide

/-- `nan ≠ 0` -/
@[simp] lemma nan_ne_zero : (nan : Floating) ≠ 0 := by decide

/-- `1 ≠ nan` -/
@[simp] lemma one_ne_nan : (1 : Floating) ≠ nan := by decide +kernel

/-- `nan ≠ 1` -/
@[simp] lemma nan_ne_one : (nan : Floating) ≠ 1 := by decide +kernel

/-- `0` is just zero -/
@[simp] lemma approx_zero_iff : approx (0 : Floating) a ↔ a = 0 := by
  simp only [approx, eq_comm, nan_ne_zero, val_zero, false_or]

instance : ApproxZero Floating ℝ where
  approx_zero := by simp only [approx, val_zero, or_true]

instance : ApproxZeroIff Floating ℝ where
  approx_zero_imp x a := by simpa only [approx_zero_iff] using a

/-- `1 = 1` -/
@[simp] lemma val_one : (1 : Floating).val = 1 := by
  have e0 : ((2^62 : Int64) : ℤ) = 2^62 := by decide +kernel
  have e1 : (2^63 - 62 : UInt64).toInt - 2^63 = -62 := by decide +kernel
  simp only [val, n_one, e0, Int.cast_pow, Int.cast_ofNat, s_one, e1, zpow_neg]
  apply mul_inv_cancel₀; norm_num

instance : ApproxOne Floating ℝ where
  approx_one := by simp only [approx, val_one, or_true]

lemma val_nan : (nan : Floating).val = -(2 ^ 63) * 2 ^ (2 ^ 63 - 1) := by
  generalize ha : 63 = a
  simp only [Floating.val, Floating.n_nan, Int64.coe_min', Int.reducePow,
    Int.cast_neg, Int.cast_ofNat, Floating.s_nan]
  rw [show UInt64.max.toInt - (9223372036854775808) = 2 ^ 63 - 1 by decide]
  rw [show (9223372036854775808 : ℝ) = 2 ^ 63 by norm_num, ha]
  convert rfl
  simp only [← zpow_natCast]
  convert rfl
  simp only [Nat.ofNat_pos, pow_pos, Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat]

/-- If we're not `nan`, `approx` is a singleton -/
@[simp] lemma approx_eq_singleton {x : Floating} (n : x ≠ nan) : approx x a ↔ x.val = a := by
  simp only [approx, n, false_or]

@[simp, approx] lemma approx_val {x : Floating} : approx x x.val := by
  by_cases n : x = nan
  · simp only [n, approx_nan]
  · simp only [ne_eq, n, not_false_eq_true, approx_eq_singleton]

/-- If we're not nan, `x.n ≠ .min` -/
lemma n_ne_min {x : Floating} (n : x ≠ nan) : x.n ≠ .minValue := by
  contrapose n
  simp only [ne_eq, not_not, ext_iff, n_nan, s_nan, not_and, not_forall, exists_prop] at n ⊢
  exact ⟨n, x.nan_same n⟩

/-- If we're not zero, `x.n ≠ 0` -/
lemma n_ne_zero {x : Floating} (n : x ≠ 0) : x.n ≠ 0 := by
  contrapose n
  simp only [ne_eq, not_not, ext_iff, not_and, not_forall, exists_prop] at n ⊢
  exact ⟨n, x.zero_same n⟩

/-- If `x.s ≠ 0`, `x.n ≠ 0` -/
lemma n_ne_zero' {x : Floating} (n : x.s ≠ 0) : x.n ≠ 0 := by
  contrapose n
  simp only [ne_eq, not_not] at n ⊢
  simp only [x.zero_same n]

/-- `x.n = 0` exactly at 0 -/
lemma n_eq_zero_iff {x : Floating} : x.n = 0 ↔ x = 0 := by
  constructor
  · intro e; simp only [ext_iff, e, n_zero, x.zero_same e, s_zero, and_self]
  · intro e; simp only [e, n_zero]

/-- More user friendly version of `x.norm` -/
lemma norm' {x : Floating} (x0 : x ≠ 0) (s0 : x.s.toNat ≠ 0) : 2^62 ≤ x.n.uabs.toNat := by
  by_cases xn : x = nan
  · simp only [xn]; decide
  · have n := x.norm (x.n_ne_zero x0) (x.n_ne_min xn) (UInt64.ne_zero_iff_toNat_ne_zero.mpr s0)
    simp only [UInt64.le_iff_toNat_le] at n
    exact le_trans (le_of_eq (by decide +kernel)) n

/-- Only `0` has zero `val` -/
lemma val_eq_zero {x : Floating} : x.val = 0 ↔ x = 0 := by
  rw [val]
  simp only [mul_eq_zero, Int.cast_eq_zero, Int64.coe_eq_zero, two_zpow_pos.ne', or_false, ext_iff,
    n_zero, s_zero, iff_self_and]
  exact x.zero_same

/-- Only `0` has zero `val` -/
lemma val_ne_zero {x : Floating} : x.val ≠ 0 ↔ x ≠ 0 := by
  rw [←not_iff_not, not_not, not_not, val_eq_zero]

/-- `valq = val` -/
lemma coe_valq {x : Floating} : x.valq = x.val := by
  rw [valq, val]; simp

/-!
### Simplification lemmas used elsewhere

This should really be cleaned up
-/

@[simp] lemma u62 : (62 : UInt64).toNat = 62 := rfl
@[simp] lemma u64 : (64 : UInt64).toNat = 64 := rfl
@[simp] lemma u65 : (65 : UInt64).toNat = 65 := rfl
@[simp] lemma u126 : (126 : UInt64).toNat = 126 := rfl
@[simp] lemma u127 : (127 : UInt64).toNat = 127 := rfl
@[simp] lemma up62 : (2^62 : UInt64).toNat = 2^62 := by decide +kernel
@[simp] lemma up63 : (2^63 : UInt64).toNat = 2^63 := by decide +kernel
@[simp] lemma ua2 : (2 : ℤ).natAbs = 2 := rfl

lemma rounds_iff {x : Floating} {up : Bool} :
    Rounds x a up ↔ (x ≠ nan → if up then a ≤ x.val else x.val ≤ a) := by
  simp only [Rounds, approx]
  constructor
  · aesop
  · intro h
    by_cases n : x = nan
    · use a
      simp only [n, true_or, le_refl, ite_self, and_self]
    · aesop

/-- Remove a `nan` possibility from a rounding statement -/
lemma rounds_of_ne_nan {a : ℝ} {x : Floating} {up : Bool}
    (h : x ≠ nan → if up = true then a ≤ x.val else x.val ≤ a) : Rounds x a up := by
  simpa only [rounds_iff]

/-- `val` if we're nonnegative -/
lemma val_of_nonneg {x : Floating} (x0 : 0 ≤ x.val) :
    x.val = (x.n.toUInt64.toNat : ℝ) * 2^((x.s.toNat : ℤ) - 2^63) := by
  rw [val, UInt64.toInt, Int64.coe_of_nonneg, Int.cast_natCast]
  rw [val] at x0
  simpa only [Int64.isNeg_eq_le, decide_eq_false_iff_not, not_le, gt_iff_lt, two_zpow_pos,
    mul_nonneg_iff_of_pos_right, Int.cast_nonneg, Int64.coe_nonneg_iff] using x0

/-!
### The smallest normalized value
-/

/-- The smallest normalized floating point value -/
@[irreducible] def min_norm : Floating :=
  ⟨UInt64.toInt64 ⟨2^62⟩, 0, by decide +kernel, by decide +kernel, by decide +kernel⟩

@[simp] lemma min_norm_ne_nan : min_norm ≠ nan := by unfold min_norm nan; decide +kernel

@[simp] lemma val_min_norm : min_norm.val = 2^(62 - 2^63 : ℤ) := by
  have t0 : (2 : ℝ) ≠ 0 := by norm_num
  have e : (2 ^ 62 : BitVec 64).toNat = 2^62 := by decide +kernel
  rw [val]
  unfold min_norm  -- Tred delicately to avoid deep recursion
  simp only [UInt64.toInt_zero, zero_sub]
  rw [Int64.coe_of_nonneg (by decide +kernel)]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Int.cast_pow, Int.cast_ofNat, pow_mul_zpow t0,
    UInt64.toUInt64_toInt64, UInt64.toNat, e, ← sub_eq_add_neg]

/-!
### Conversion to `Float`
-/

/-- Approximate `Floating` by a `Float` -/
@[irreducible] def toFloat (x : Floating) : Float :=
  bif x == nan then Float.nan else x.n.toFloat.scaleB (x.s.toInt - 2^63)

/-!
### Print `Floating` in 7 significant digits, rounding down arbitrarily
-/

/-- Convert to `Decimal` with a given precision and rounding. Ignores `nan` and takes `abs`. -/
@[irreducible] def decimal (x : Floating) (prec : ℕ) (up : Bool) : Decimal :=
  .ofBinary x.n.toInt (x.s.toInt - 2^63) prec up

/-- `decimal` rounds down if desired -/
lemma decimal_le (x : Floating) (prec : ℕ) : (x.decimal prec false).val ≤ x.val := by
  rw [decimal, val]
  apply Decimal.ofBinary_le

/-- `decimal` rounds up if desired -/
lemma le_decimal (x : Floating) (prec : ℕ) : x.val ≤ (x.decimal prec true).val := by
  rw [decimal, val]
  apply Decimal.le_ofBinary

/-- We print `Fixed s` as an approximate floating point number -/
instance : Repr Floating where
  reprPrec x _ :=
    bif x == nan then "nan" else
    let y := x.n.toInt
    toString (repr (Decimal.ofBinary y (x.s.toInt - 2^63) 7 false))

/-- Print raw representation of a `Floating` -/
instance : Repr (Raw Floating) where
  reprPrec x _ := f!"⟨⟨{x.val.n.toUInt64}⟩, ⟨{x.val.s}⟩, _⟩"
