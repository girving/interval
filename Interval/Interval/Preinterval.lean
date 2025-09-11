import Interval.Interval.Basic

open Classical
open Pointwise

/-!
## `Preinterval` is `Interval` without the correctness properties

This lets us write a routine, prove it correct, then finalize it.
-/

open Set
open scoped Real

/-- `Interval` without the correctness properties. -/
@[unbox] structure Preinterval where
  /-- Lower bound -/
  lo : Floating
  /-- Upper bound -/
  hi : Floating

namespace Preinterval

variable {a : ℝ}

/-- Standard `Preinterval` nan -/
instance : Nan Preinterval where
  nan := ⟨nan, nan⟩

/-- `Preinterval` approximates `ℝ` -/
instance : Approx Preinterval ℝ where
  approx x a := x.lo = nan ∨ x.hi = nan ∨ a ∈ Icc x.lo.val x.hi.val

lemma nan_def : (nan : Preinterval) = ⟨nan, nan⟩ := rfl

instance : ApproxNan Preinterval ℝ where
  approx_nan a := by simp only [approx, nan_def, Icc_self, mem_singleton_iff, true_or, or_self]

@[simp] lemma approx_nan_lo {x : Floating} : approx (⟨nan,x⟩ : Preinterval) a := by
  simp only [approx, nan, true_or]

@[simp] lemma approx_nan_hi {x : Floating} : approx (⟨x,nan⟩ : Preinterval) a := by
  simp only [approx, nan, mem_Icc, true_or, or_true]

@[simp] lemma lo_nan : (nan : Preinterval).lo = nan := rfl
@[simp] lemma hi_nan : (nan : Preinterval).hi = nan := rfl

/-!
### `mix`: Turn a `Preinterval` into an `Interval`
-/

/-- If a `Preinterval` is nonempty`, it can be turned into an `Interval` -/
@[irreducible, inline] def mix (x : Preinterval)
    (le : x.lo ≠ nan → x.hi ≠ nan → x.lo.val ≤ x.hi.val) : Interval :=
  Interval.mix x.lo x.hi le

/-- If a `Preinterval` is nonempty`, it can be turned into an `Interval` -/
@[irreducible, inline] def mix' (x : Preinterval) {a : ℝ} (m : approx x a) : Interval :=
  x.mix (by
    intro ln hn
    simp only [approx, ln, hn, mem_Icc, false_or] at m
    linarith)

/-- `mix` commutes with `approx` -/
@[simp] lemma approx_mix (x : Preinterval) (le : x.lo ≠ nan → x.hi ≠ nan → x.lo.val ≤ x.hi.val) :
    approx (x.mix le) a ↔ approx x a := by
  rw [mix, Interval.mix]
  by_cases n : x.lo = nan ∨ x.hi = nan
  · rcases n with n | n
    all_goals simp only [n, true_or, or_true, dite_true, approx]
    all_goals simp only [Interval.lo_nan, Interval.hi_nan, true_or]
  rcases not_or.mp n with ⟨ln,hn⟩
  simp only [approx, ln, hn, or_self, dite_false, false_or, mem_Icc]

/-- `mix'` commutes with `approx` -/
@[simp] lemma approx_mix' (x : Preinterval) {a b : ℝ} (m : approx x a) :
    approx (x.mix' m) b = approx x b := by
  rw [mix', approx_mix]

/-- `mix` propagates `nan` -/
@[simp] lemma mix_nan (le : (nan : Preinterval).lo ≠ nan →
    (nan : Preinterval).hi ≠ nan → (nan : Preinterval).lo.val ≤ (nan : Preinterval).hi.val) :
    mix nan le = nan := by
  rw [mix]; simp only [lo_nan, hi_nan, Interval.mix_self, Interval.coe_nan]

/-- `mix'` propagates `nan` -/
@[simp] lemma mix_nan' {a : ℝ} (m : approx (nan : Preinterval) a) : mix' nan m = nan := by
  rw [mix', mix_nan]
