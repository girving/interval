/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
module

public import Interval.EulerMaclaurin.Bernoulli
public import Interval.EulerMaclaurin.Formula
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Bounds for the remainder of the Euler-Maclaurin formula

The remainder term of the formula of order `p` in `Interval.EulerMaclaurin.Formula` is
`((-1) ^ (p + 1) / p !) • ∫ t in a..b, periodizedBernoulli p t • g t`, where `g` is the `p`-th
derivative. If `|bernoulliFun p x| ≤ D` on `[0, 1]`, its norm is at most `D / p ! * ∫ ‖g‖`, which
bounds the error of every form of the formula. Useful choices of `D` are `bernoulliBound p` (the
best constant, `abs_bernoulliFun_le`), `|bernoulli p|` for even `p` (`abs_bernoulliFun_le_even`),
and the rational constant `4 * p ! / 6 ^ p`, valid for every `p`, which needs no transcendental
number and so suits certified numerics.

## Main results

* `abs_bernoulliFun_le_tsum`: `|bernoulliFun k x| ≤ 2 * (∑' n, 1 / n ^ k) * k ! / (2 * π) ^ k`
  for `2 ≤ k` and `x ∈ [0, 1]`, from the Fourier expansion of the Bernoulli polynomials.
* `abs_bernoulliFun_le_four_mul_factorial_div_six_pow`: `|bernoulliFun k x| ≤ 4 * k ! / 6 ^ k`
  for every `k` and `x ∈ [0, 1]`.
* `bernoulliBound_le_four_mul_factorial_div_six_pow` and `sawBound_le_four_div_six_pow`:
  `bernoulliBound k ≤ 4 * k ! / 6 ^ k` and `sawBound k ≤ 4 / 6 ^ k`, so that with `abs_saw_le`,
  `|saw k x| ≤ 4 / 6 ^ k` in every order, including odd orders, where `bernoulliBound` is not
  evaluated.
* `EulerMaclaurin.norm_smul_integral_periodizedBernoulli_smul_le`: the bound for the remainder term.
* `EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt` and
  `EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le`: the error bound in terms
  of any uniform bound `D`, for a family of derivatives and for a `C^p` function.
* `EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_hasDerivWithinAt`: the error bound
  `4 / 6 ^ p * ∫ ‖F p‖`.
* `EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_abs_bernoulli_of_hasDerivWithinAt`: the
  classical error bound `|bernoulli (2 * m)| / (2 * m) ! * ∫ ‖F (2 * m)‖` in even order.
-/

public section

open scoped Nat Real

open Complex in
/-- **Explicit bound for the Bernoulli polynomials** in terms of `∑' n, 1 / n ^ k`. For `k ≥ 2` and
`x ∈ [0, 1]`, `|B_k(x)| ≤ 2 * (∑ n ≥ 1, 1 / n ^ k) * k! / (2 π) ^ k`. The proof takes norms
termwise in the Fourier expansion `hasSum_one_div_nat_pow_mul_fourier`. -/
theorem abs_bernoulliFun_le_tsum {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun k x| ≤ 2 * (∑' n : ℕ, 1 / (n : ℝ) ^ k) * k ! / (2 * π) ^ k := by
  have hs := (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k)).hasSum
  have hnorm : ‖-(2 * (π : ℂ) * I) ^ k / (k ! : ℂ) * (bernoulliFun k x : ℂ)‖ ≤
      2 * ∑' n : ℕ, 1 / (n : ℝ) ^ k := by
    refine (hasSum_one_div_nat_pow_mul_fourier hk hx).norm_le_of_bounded (hs.mul_left 2)
      fun n ↦ ?_
    have hfourier : ∀ m : ℤ, ‖fourier m (x : UnitAddCircle)‖ = 1 := fun m ↦ Circle.norm_coe _
    have h1 : ‖fourier (n : ℤ) (x : UnitAddCircle) +
        (-1 : ℂ) ^ k * fourier (-(n : ℤ)) (x : UnitAddCircle)‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hfourier, hfourier]
      norm_num
    have h2 : ‖(1 : ℂ) / (n : ℂ) ^ k‖ = 1 / (n : ℝ) ^ k := by simp [norm_pow]
    rw [norm_mul, h2, mul_comm 2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hval : ‖-(2 * (π : ℂ) * I) ^ k / (k ! : ℂ) * (bernoulliFun k x : ℂ)‖ =
      (2 * π) ^ k * |bernoulliFun k x| / k ! := by
    rw [norm_mul, norm_div, norm_neg, norm_pow,
      show ‖(2 * (π : ℂ) * I)‖ = 2 * π by simp [abs_of_pos Real.pi_pos],
      Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    ring
  rw [hval, div_le_iff₀ (by positivity)] at hnorm
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- The series `∑ 1 / n ^ k` is dominated by `ζ(2) = π ^ 2 / 6` for `k ≥ 2`. -/
private theorem tsum_one_div_nat_pow_le {k : ℕ} (hk : 2 ≤ k) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ k ≤ π ^ 2 / 6 := by
  refine hasSum_le (fun n ↦ ?_) (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k)).hasSum
    hasSum_zeta_two
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [zero_pow (show k ≠ 0 by omega)]
  · exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by exact_mod_cast hn) hk)

/-- **Rational bound for the Bernoulli polynomials.** For every `k` and `x ∈ [0, 1]`,
`|B_k(x)| ≤ 4 * k! / 6 ^ k`. No transcendental constant occurs, which is convenient for certified
numerical estimates. For `k ≥ 2` it follows from `abs_bernoulliFun_le_tsum` since the series is at
most `π ^ 2 / 6 < 2` and `6 < 2 π`; the cases `k = 0` and `k = 1` are direct. -/
theorem abs_bernoulliFun_le_four_mul_factorial_div_six_pow (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : |bernoulliFun k x| ≤ 4 * k ! / 6 ^ k := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · calc |bernoulliFun 0 x| = 1 := by simp
        _ ≤ 4 * (0 ! : ℝ) / 6 ^ 0 := by norm_num
    · have h : |x - 1 / 2| ≤ 1 / 2 := by
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2]
      calc |bernoulliFun 1 x| = |x - 1 / 2| := by rw [bernoulliFun_one]
        _ ≤ 1 / 2 := h
        _ ≤ 4 * (1 ! : ℝ) / 6 ^ 1 := by norm_num
  · refine (abs_bernoulliFun_le_tsum hk hx).trans ?_
    have hπ : π ^ 2 < 12 :=
      calc π ^ 2 < 3.15 ^ 2 := pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le two_ne_zero
        _ < 12 := by norm_num
    have h2 : 2 * (∑' n : ℕ, 1 / (n : ℝ) ^ k) ≤ 4 := by
      linarith [tsum_one_div_nat_pow_le hk]
    have h6 : (6 : ℝ) ^ k ≤ (2 * π) ^ k :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) k
    calc 2 * (∑' n : ℕ, 1 / (n : ℝ) ^ k) * k ! / (2 * π) ^ k ≤ 4 * k ! / (2 * π) ^ k := by
          gcongr
      _ ≤ 4 * k ! / 6 ^ k := by gcongr

/-- The best constant `bernoulliBound k` is at most the rational constant `4 * k ! / 6 ^ k`. -/
theorem bernoulliBound_le_four_mul_factorial_div_six_pow (k : ℕ) :
    bernoulliBound k ≤ 4 * k ! / 6 ^ k :=
  abs_bernoulliFun_le_four_mul_factorial_div_six_pow k (exists_max_bernoulli k).choose_spec.1

/-- **An explicit upper bound for `sawBound` in every order**:
`|saw k x| ≤ sawBound k ≤ 4 / 6 ^ k`. `bernoulliBound` is defined as a maximum and is evaluated
only in even order (`bernoulliBound_eq_abs_bernoulli'`); this bound needs no parity assumption. -/
theorem sawBound_le_four_div_six_pow (k : ℕ) : sawBound k ≤ 4 / 6 ^ k := by
  have hk : (k ! : ℝ) ≠ 0 := by positivity
  calc sawBound k = (k ! : ℝ)⁻¹ * bernoulliBound k := rfl
    _ ≤ (k ! : ℝ)⁻¹ * (4 * k ! / 6 ^ k) := by
        gcongr
        exact bernoulliBound_le_four_mul_factorial_div_six_pow k
    _ = 4 / 6 ^ k := by field_simp

open MeasureTheory

namespace EulerMaclaurin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ → E} {a b : ℝ}

/-- **The generic bound for the remainder integral.** If `|B_p(x)| ≤ D` for `x ∈ [0, 1]`, then
`‖∫ t in a..b, P_p t • g t‖ ≤ D * ∫ t in a..b, ‖g t‖` for `a ≤ b` and `g` interval integrable,
where `P_p = periodizedBernoulli p`. Only interval integrability of `g` is used, not that of the
product with the periodic Bernoulli function. -/
theorem norm_integral_periodizedBernoulli_smul_le {p : ℕ} {D : ℝ} (hab : a ≤ b)
    (hD : ∀ x ∈ Set.Icc (0 : ℝ) 1, |bernoulliFun p x| ≤ D) (hg : IntervalIntegrable g volume a b) :
    ‖∫ t in a..b, periodizedBernoulli p t • g t‖ ≤ D * ∫ t in a..b, ‖g t‖ := by
  have hint : ‖∫ t in a..b, periodizedBernoulli p t • g t‖ ≤ ∫ t in a..b, D * ‖g t‖ :=
    intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ fun t _ ↦ by
      rw [norm_smul, Real.norm_eq_abs, periodizedBernoulli_coe]
      exact mul_le_mul_of_nonneg_right (hD _ ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩)
        (norm_nonneg _)) (hg.norm.const_mul D)
  rwa [intervalIntegral.integral_const_mul] at hint

/-- **Bound for the remainder term of the Euler-Maclaurin formula**, with its coefficient. The term
`((-1) ^ (p + 1) / p !) • ∫ t in a..b, periodizedBernoulli p t • g t` is the remainder term of every
form of the formula in `Interval.EulerMaclaurin.Formula`, where `g` is the `p`-th derivative. If
`|B_p(x)| ≤ D` for `x ∈ [0, 1]`, its norm is at most `D / p ! * ∫ t in a..b, ‖g t‖`. Rewriting with
a form of the formula and applying this bound gives the error bound for that form. -/
theorem norm_smul_integral_periodizedBernoulli_smul_le {p : ℕ} {D : ℝ} (hab : a ≤ b)
    (hD : ∀ x ∈ Set.Icc (0 : ℝ) 1, |bernoulliFun p x| ≤ D)
    (hg : IntervalIntegrable g volume a b) :
    ‖((-1 : ℝ) ^ (p + 1) / (p ! : ℝ)) • ∫ t in a..b, periodizedBernoulli p t • g t‖ ≤
      D / p ! * ∫ t in a..b, ‖g t‖ := by
  have hcoef : |(-1 : ℝ) ^ (p + 1) / (p ! : ℝ)| = 1 / (p ! : ℝ) := by
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
  rw [norm_smul, Real.norm_eq_abs, hcoef]
  calc 1 / (p ! : ℝ) * ‖∫ t in a..b, periodizedBernoulli p t • g t‖
      ≤ 1 / (p ! : ℝ) * (D * ∫ t in a..b, ‖g t‖) :=
        mul_le_mul_of_nonneg_left (norm_integral_periodizedBernoulli_smul_le hab hD hg)
          (by positivity)
    _ = D / p ! * ∫ t in a..b, ‖g t‖ := by ring

/-- The constant `4 * p ! / 6 ^ p` of the rational bound for the Bernoulli polynomials, divided by
`p !`. -/
private theorem four_mul_factorial_div_six_pow_div_factorial (p : ℕ) :
    4 * (p ! : ℝ) / 6 ^ p / p ! = 4 / 6 ^ p := by
  have hne : (p ! : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Error bound for the Euler-Maclaurin formula** in terms of a uniform bound for the Bernoulli
polynomial, for a family of derivatives. Under the hypotheses of
`EulerMaclaurin.sum_Ioc_eq_integral_add_of_hasDerivWithinAt`, if `|B_p(x)| ≤ D` for `x ∈ [0, 1]`,
the difference between the sum over the integers in `(a, b]` and the integral plus the boundary
terms of order `p` is at most `D / p ! * ∫ ‖F p‖`. Useful choices of `D` are `D = bernoulliBound p`
for every `p` (`abs_bernoulliFun_le`), `D = 1 / 2` for `p = 1`,
`D = 2 * ζ(p) * p ! / (2 * π) ^ p` for `p ≥ 2` (`abs_bernoulliFun_le_tsum`), `D = |B_p|` for even
`p`, and `D = 4 * p ! / 6 ^ p`. -/
theorem norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt
    [CompleteSpace E] {p : ℕ} {D : ℝ} (hp : p ≠ 0) {F : ℕ → ℝ → E} (hab : a ≤ b)
    (hD : ∀ x ∈ Set.Icc (0 : ℝ) 1, |bernoulliFun p x| ≤ D)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc a b, HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc a b) x)
    (hFp : IntervalIntegrable (F p) volume a b) :
    ‖∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F 0 (i : ℝ) - (∫ t in a..b, F 0 t) -
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • F k b - periodizedBernoulli (k + 1) a • F k a)‖ ≤
      D / p ! * ∫ t in a..b, ‖F p t‖ := by
  rw [sum_Ioc_eq_integral_add_of_hasDerivWithinAt hp hab hF hFp]
  refine (le_of_eq ?_).trans (norm_smul_integral_periodizedBernoulli_smul_le hab hD hFp)
  congr 1
  abel

/-- **Error bound for the Euler-Maclaurin formula** for a `C^p` function, in terms of a uniform
bound for the Bernoulli polynomial: the case of
`EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt` for the
derivatives `iteratedDerivWithin k f (Set.Icc a b)`. -/
theorem norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le [CompleteSpace E]
    {f : ℝ → E} {p : ℕ} {D : ℝ} (hp : p ≠ 0) (hab : a ≤ b)
    (hD : ∀ x ∈ Set.Icc (0 : ℝ) 1, |bernoulliFun p x| ≤ D)
    (hf : ContDiffOn ℝ p f (Set.Icc a b)) :
    ‖∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, f (i : ℝ) - (∫ t in a..b, f t) -
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • iteratedDerivWithin k f (Set.Icc a b) b -
            periodizedBernoulli (k + 1) a • iteratedDerivWithin k f (Set.Icc a b) a)‖ ≤
      D / p ! * ∫ t in a..b, ‖iteratedDerivWithin p f (Set.Icc a b) t‖ := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  · have hU : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hlt
    simpa only [iteratedDerivWithin_zero] using
      norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt
        (F := fun k ↦ iteratedDerivWithin k f (Set.Icc a b)) hp hab hD
        (fun k hk x hx ↦ hf.hasDerivWithinAt_iteratedDerivWithin (by exact_mod_cast hk) hU hx)
        ((hf.continuousOn_iteratedDerivWithin le_rfl hU).intervalIntegrable_of_Icc hab)

/-- **Error bound for the Euler-Maclaurin formula** with the rational constant. Under the
hypotheses of `EulerMaclaurin.sum_Ioc_eq_integral_add_of_hasDerivWithinAt`, the difference between
the sum over the integers in `(a, b]` and the integral plus the boundary terms of order `p` is at
most `4 / 6 ^ p * ∫ ‖F p‖`. -/
theorem norm_sum_Ioc_sub_integral_sub_le_of_hasDerivWithinAt [CompleteSpace E] {p : ℕ}
    (hp : p ≠ 0) {F : ℕ → ℝ → E} (hab : a ≤ b)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc a b, HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc a b) x)
    (hFp : IntervalIntegrable (F p) volume a b) :
    ‖∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F 0 (i : ℝ) - (∫ t in a..b, F 0 t) -
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • F k b - periodizedBernoulli (k + 1) a • F k a)‖ ≤
      4 / 6 ^ p * ∫ t in a..b, ‖F p t‖ :=
  (norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt hp hab
    (fun _ hx ↦ abs_bernoulliFun_le_four_mul_factorial_div_six_pow p hx) hF hFp).trans_eq
    (by rw [four_mul_factorial_div_six_pow_div_factorial])

/-- **Error bound for the Euler-Maclaurin formula in even order.** Under the hypotheses of
`EulerMaclaurin.sum_Ioc_eq_integral_add_of_hasDerivWithinAt` with `p = 2 * m`, the difference
between the sum over the integers in `(a, b]` and the integral plus the boundary terms of order
`2 * m` is at most `|B_{2m}| / (2m)! * ∫ ‖F (2 * m)‖`, the classical form of the error term. -/
theorem norm_sum_Ioc_sub_integral_sub_le_abs_bernoulli_of_hasDerivWithinAt [CompleteSpace E]
    {m : ℕ} (hm : m ≠ 0) {F : ℕ → ℝ → E} (hab : a ≤ b)
    (hF : ∀ k < 2 * m, ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc a b) x)
    (hFp : IntervalIntegrable (F (2 * m)) volume a b) :
    ‖∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F 0 (i : ℝ) - (∫ t in a..b, F 0 t) -
        ∑ k ∈ Finset.range (2 * m), ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • F k b - periodizedBernoulli (k + 1) a • F k a)‖ ≤
      |(bernoulli (2 * m) : ℝ)| / (2 * m)! * ∫ t in a..b, ‖F (2 * m) t‖ :=
  norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt (by omega) hab
    (fun _ hx ↦ by simpa only [Rat.cast_abs] using abs_bernoulliFun_le_even m hx) hF hFp

end EulerMaclaurin
