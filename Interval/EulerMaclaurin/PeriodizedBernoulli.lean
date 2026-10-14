/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import Mathlib.NumberTheory.ZetaValues

/-!
# Periodized Bernoulli polynomials

Mathlib's `periodizedBernoulli k : UnitAddCircle → ℝ` is the Bernoulli polynomial `bernoulliFun k`
on `[0, 1)`, extended periodically. At the class of a real number `x` it is
`bernoulliFun k (Int.fract x)`. This file proves what the general Euler-Maclaurin formula in
`Interval.EulerMaclaurin.Formula` needs: the value on `[m, m + 1)` and at the integers,
measurability (also for `k = 1`, where the function jumps at the integers), interval integrability
of products, and integration by parts against a translated Bernoulli polynomial.

## Main results

* `periodizedBernoulli_coe`: `periodizedBernoulli k x = bernoulliFun k (Int.fract x)`.
* `periodizedBernoulli_coe_of_mem_Ico_intCast`: the value `bernoulliFun k (x - m)` on `[m, m + 1)`.
* `periodizedBernoulli_intCast`: the value `bernoulli k` at an integer, with `simp` companions for
  natural numbers, numerals, `0` and `1`.
* `IntervalIntegrable.periodizedBernoulli_smul`: products with interval integrable functions are
  interval integrable.
* `integral_bernoulliFun_comp_sub_right_smul`: integration by parts against
  `t ↦ bernoulliFun n (t - c)`.
-/

public section

namespace AddCircle

variable {T : ℝ} [Fact (0 < T)] {β : Type*} [MeasurableSpace β] {a : ℝ} {f : ℝ → β}

/-- The periodization `AddCircle.liftIco T a f` of a measurable function `f : ℝ → β`, which agrees
with `f` on `[a, a + T)`, is measurable. -/
@[fun_prop]
theorem measurable_liftIco (hf : Measurable f) : Measurable (AddCircle.liftIco T a f) :=
  (hf.comp measurable_subtype_coe).comp (measurableEquivIco T a).measurable

end AddCircle

open MeasureTheory

/-- The periodized Bernoulli polynomial at the class of a real number `x` is `B_k` at the
fractional part of `x`. This is the bridge between `periodizedBernoulli`, defined on the unit
circle, and the periodic function on `ℝ`. -/
theorem periodizedBernoulli_coe (k : ℕ) (x : ℝ) :
    periodizedBernoulli k x = bernoulliFun k (Int.fract x) := by
  rw [← AddCircle.coe_fract x]
  exact AddCircle.liftIco_zero_coe_apply
    (show Int.fract x ∈ Set.Ico (0 : ℝ) 1 from ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩)

/-- On `[m, m + 1)`, for an integer `m`, the periodized Bernoulli polynomial is the translate
`x ↦ bernoulliFun k (x - m)` of the Bernoulli polynomial. -/
theorem periodizedBernoulli_coe_of_mem_Ico_intCast {k : ℕ} {m : ℤ} {x : ℝ}
    (hx : x ∈ Set.Ico (m : ℝ) (m + 1)) : periodizedBernoulli k x = bernoulliFun k (x - m) := by
  rw [periodizedBernoulli_coe, ← Int.self_sub_floor, Int.floor_eq_iff.2 ⟨hx.1, hx.2⟩]

/-- At an integer, the periodized Bernoulli polynomial is the Bernoulli number. -/
@[simp]
theorem periodizedBernoulli_intCast (k : ℕ) (m : ℤ) :
    periodizedBernoulli k (m : ℝ) = bernoulli k := by
  rw [periodizedBernoulli_coe, Int.fract_intCast, bernoulliFun_eval_zero]

/-- At a natural number, the periodized Bernoulli polynomial is the Bernoulli number. -/
@[simp]
theorem periodizedBernoulli_natCast (k n : ℕ) : periodizedBernoulli k (n : ℝ) = bernoulli k := by
  have h := periodizedBernoulli_intCast k n
  rwa [Int.cast_natCast] at h

/-- At a numeral `n ≥ 2`, the periodized Bernoulli polynomial is the Bernoulli number. -/
@[simp]
theorem periodizedBernoulli_ofNat (k n : ℕ) [n.AtLeastTwo] :
    periodizedBernoulli k (ofNat(n) : ℝ) = bernoulli k :=
  periodizedBernoulli_natCast k n

/-- The periodized Bernoulli polynomial of order `k` at the real number `1` is the Bernoulli number
`B_k`. Here `one` in the name refers to the argument, not to the order. -/
@[simp]
theorem periodizedBernoulli_apply_one (k : ℕ) : periodizedBernoulli k (1 : ℝ) = bernoulli k := by
  have h := periodizedBernoulli_natCast k 1
  rwa [Nat.cast_one] at h

/-- The periodized Bernoulli polynomial of order `k` at the zero of the circle is the Bernoulli
number `B_k`. Here `zero` in the name refers to the argument, not to the order. It is the form to
which `simp` reduces the value at the real number `0`. -/
@[simp]
theorem periodizedBernoulli_apply_zero (k : ℕ) : periodizedBernoulli k 0 = bernoulli k := by
  have h := periodizedBernoulli_natCast k 0
  rw [Nat.cast_zero] at h
  exact h

/-- The periodized Bernoulli polynomial is measurable on the circle for every `k`, including
`k = 1`, where it jumps at the origin. -/
@[fun_prop]
theorem measurable_periodizedBernoulli (k : ℕ) : Measurable (periodizedBernoulli k) :=
  AddCircle.measurable_liftIco (continuous_bernoulliFun k).measurable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The product of the periodized Bernoulli polynomial with an interval integrable function is
interval integrable. No continuity is needed: the periodized Bernoulli polynomial is measurable
and bounded. -/
theorem IntervalIntegrable.periodizedBernoulli_smul {k : ℕ} {g : ℝ → E} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t : ℝ ↦ periodizedBernoulli k t • g t) volume a b := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_bernoulliFun k).continuousOn
  have hmeas : Measurable fun x : ℝ ↦ periodizedBernoulli k (x : UnitAddCircle) := by
    fun_prop
  have hbound : ∀ x : ℝ, ‖periodizedBernoulli k (x : UnitAddCircle)‖ ≤ C := fun x ↦ by
    rw [periodizedBernoulli_coe]
    exact hC _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  rw [intervalIntegrable_iff] at hg ⊢
  exact hg.bdd_smul C hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

variable [CompleteSpace E]

/-- **Integration by parts against a translated Bernoulli polynomial.** If `f` has derivative
`f'` within `[a, b]`, with `f'` interval integrable, then
`∫ B_n(t - c) • f(t) dt = (n + 1)⁻¹ • (B_{n+1}(b - c) • f(b) - B_{n+1}(a - c) • f(a)
  - ∫ B_{n+1}(t - c) • f'(t) dt)`. -/
theorem integral_bernoulliFun_comp_sub_right_smul (n : ℕ) {f f' : ℝ → E} {a b c : ℝ}
    (hf : ∀ x ∈ Set.uIcc a b, HasDerivWithinAt f (f' x) (Set.uIcc a b) x)
    (hf' : IntervalIntegrable f' volume a b) :
    ∫ t in a..b, bernoulliFun n (t - c) • f t =
      ((n : ℝ) + 1)⁻¹ • (bernoulliFun (n + 1) (b - c) • f b - bernoulliFun (n + 1) (a - c) • f a -
        ∫ t in a..b, bernoulliFun (n + 1) (t - c) • f' t) := by
  have hu : ∀ x : ℝ, HasDerivAt (fun t : ℝ ↦ bernoulliFun (n + 1) (t - c) / ((n : ℝ) + 1))
      (bernoulliFun n (x - c)) x := fun x ↦
    HasDerivAt.comp_sub_const x c (antideriv_bernoulliFun n (x - c))
  have hibp := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (a := a) (b := b) (u := fun t : ℝ ↦ bernoulliFun (n + 1) (t - c) / ((n : ℝ) + 1))
    (u' := fun t : ℝ ↦ bernoulliFun n (t - c)) (v := f) (v' := f')
    (fun x _ ↦ (hu x).hasDerivWithinAt) hf
    (((continuous_bernoulliFun n).comp (continuous_sub_right c)).intervalIntegrable _ _) hf'
  have hscal : ∫ t in a..b, (bernoulliFun (n + 1) (t - c) / ((n : ℝ) + 1)) • f' t =
      ((n : ℝ) + 1)⁻¹ • ∫ t in a..b, bernoulliFun (n + 1) (t - c) • f' t := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp only [smul_smul, div_eq_inv_mul]
  rw [hscal] at hibp
  linear_combination (norm := module) hibp
