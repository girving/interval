import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
## Bounds for `sin` and `cos`
-/

open Set
open scoped Real

/-!
### Monotonicity of `sin` on intervals
-/

/-- All the intervals on which `sin` is increasing -/
lemma Real.sin_monotone (n : ℤ) :
    MonotoneOn sin (Icc (n * (2 * π) - π / 2) (n * (2 * π) + π / 2)) := by
  apply monotoneOn_of_deriv_nonneg
  · apply convex_Icc
  · exact Continuous.continuousOn (by continuity)
  · exact differentiable_sin.differentiableOn
  · intro x m
    simp only [interior_Icc, mem_Ioo, deriv_sin] at m ⊢
    rw [← cos_sub_int_mul_two_pi _ n]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩

/-- All the intervals on which `sin` is decreasing -/
lemma Real.sin_antitone (n : ℤ) :
    AntitoneOn sin (Icc (n * (2 * π) + π / 2) (n * (2 * π) + 3 * π / 2)) := by
  intro x xm y ym xy
  simp only [mem_Icc] at xm ym
  rw [← neg_neg (sin x), ← Real.sin_sub_pi x, ← neg_neg (sin y), ← Real.sin_sub_pi y,
    neg_le_neg_iff]
  refine Real.sin_monotone (n := n) ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_
  all_goals linarith

/-!
### Taylor series with remainder for `sin` and `cos`
-/

/-- Double the range of a `Finset.sum` -/
lemma Finset.sum_range_even {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ k ∈ Finset.range n, f k = ∑ k ∈ Finset.range (2 * n), if Even k then f (k / 2) else 0 := by
  induction' n with n h
  · simp
  · simp [Finset.sum_range_succ, h, mul_add]

lemma Complex.sin_series_bound {z : ℂ} (z1 : ‖z‖ ≤ 1) (n : ℕ) :
    ‖sin z - z * ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k + 1).factorial‖ ≤
      ‖z‖ ^ (2 * n + 1) * ((2 * n + 2) / ((2 * n + 1).factorial * (2 * n + 1))) := by
  have e : z * ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k + 1).factorial =
      (∑ k ∈ Finset.range (2 * n + 1), (-z * I) ^ k / k.factorial -
       ∑ k ∈ Finset.range (2 * n + 1), (z * I) ^ k / k.factorial) * I / 2 := by
    simp only [← Finset.sum_sub_distrib, ← sub_div, Finset.sum_range_even n, Finset.sum_div,
      Finset.mul_sum, Finset.sum_mul]
    simp only [Finset.sum_range_succ', pow_zero, Nat.factorial_zero, sub_self, zero_div, add_zero,
      zero_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rcases Nat.even_or_odd' k with ⟨a, e | e⟩
    · simp only [e, even_two, Even.mul_right, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, mul_div_cancel_left₀, pow_mul, pow_succ', pow_zero, mul_one, mul_pow,
      neg_mul, mul_neg, neg_neg]
      ring_nf
      simp only [mul_comm _ 2, pow_mul, I_sq, mul_neg]
      simp only [neg_mul, neg_neg, mul_one]
    · simp [e, pow_mul, pow_add, mul_pow]
  have r : ∀ a b c d : ℂ, (a - b) - (c - d) = (a - c) - (b - d) := fun _ _ _ _ ↦ by ring
  rw [sin, e, ← sub_div, ← sub_mul, r, norm_div, Complex.norm_two, div_le_iff₀ (by norm_num),
    norm_mul, Complex.norm_I, mul_one]
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (Complex.exp_bound (x := -z * I) (by simpa) (by omega))
    (Complex.exp_bound (x := z * I) (by simpa) (by omega))) (le_of_eq ?_)
  simp only [norm_mul, Complex.norm_I, norm_neg, Nat.succ_eq_add_one,
    Nat.cast_add, Nat.cast_mul]
  ring_nf

lemma Complex.cos_series_bound {z : ℂ} (z1 : ‖z‖ ≤ 1) {n : ℕ} (n0 : 0 < n) :
    ‖cos z - ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k).factorial‖ ≤
      ‖z‖ ^ (2 * n) * ((2 * n + 1) / ((2 * n).factorial * (2 * n))) := by
  have e : ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k).factorial =
      (∑ k ∈ Finset.range (2 * n), (z * I) ^ k / k.factorial +
       ∑ k ∈ Finset.range (2 * n), (-z * I) ^ k / k.factorial) / 2 := by
    simp only [← Finset.sum_add_distrib, Finset.sum_range_even n, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rcases Nat.even_or_odd' k with ⟨a, e | e⟩
    · simp only [e, even_two, Even.mul_right, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_div_cancel_left₀, pow_mul, mul_pow, I_sq, mul_neg, mul_one, neg_mul,
        Even.neg_pow, ← add_div, neg_pow' (z^2), mul_comm _ ((-1 : ℂ) ^ a), ← add_mul]
      ring
    · simp [e, pow_mul, pow_add, mul_pow, neg_div]
  have r : ∀ a b c d : ℂ, (a + b) - (c + d) = (a - c) + (b - d) := fun _ _ _ _ ↦ by ring
  rw [cos, e, ← sub_div, r, norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (Complex.exp_bound (x := z * I) (by simpa) (by omega))
    (Complex.exp_bound (x := -z * I) (by simpa) (by omega))) (le_of_eq ?_)
  simp only [norm_mul, Complex.norm_I, norm_neg, Nat.succ_eq_add_one,
    Nat.cast_add, Nat.cast_mul]
  ring_nf

lemma Real.sin_series_bound {x : ℝ} (x1 : |x| ≤ 1) (n : ℕ) :
    |sin x - x * ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k) / (2 * k + 1).factorial| ≤
      |x| ^ (2 * n + 1) * ((2 * n + 2) / ((2 * n + 1).factorial * (2 * n + 1))) := by
  have b := Complex.sin_series_bound (z := x) (by simpa only [Complex.norm_real]) n
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_pow, ← Complex.ofReal_one,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
    ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.norm_real] at b
  exact b

lemma Real.cos_series_bound {x : ℝ} (x1 : |x| ≤ 1) {n : ℕ} (n0 : 0 < n) :
    |cos x - ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k) / (2 * k).factorial| ≤
      |x| ^ (2 * n) * ((2 * n + 1) / ((2 * n).factorial * (2 * n))) := by
  have b := Complex.cos_series_bound (z := x) (by simpa only [Complex.norm_real]) n0
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_pow, ← Complex.ofReal_one,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
    ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.norm_real] at b
  exact b

/-!
### `Real.sinc` and `Complex.sinc`
-/

noncomputable def Complex.sinc (z : ℂ) : ℂ := if z = 0 then 1 else Complex.sin z / z

/-- `sinc` suffices to compute `sin` -/
lemma Real.sin_eq_sinc (x : ℝ) : sin x = x * sinc x := by
  by_cases x0 : x = 0
  · simp [x0]
  · rw [sinc]
    simp only [x0, ↓reduceIte]
    field_simp [x0]

/-- `sinc` suffices to compute `sin` -/
lemma Complex.sin_eq_sinc (z : ℂ) : sin z = z * sinc z := by
  by_cases z0 : z = 0
  · simp [z0]
  · rw [sinc]
    simp only [z0, ↓reduceIte]
    field_simp [z0]

@[simp] lemma Complex.sinc_neg (x : ℝ) : sinc (-x) = sinc x := by simp [sinc]

/-- `sinc` is even -/
@[simp] lemma Real.sinc_abs (x : ℝ) : sinc |x| = sinc x := by
  by_cases x0 : 0 ≤ x
  · simp only [abs_of_nonneg x0]
  · simp only [abs_of_neg (not_le.mp x0), sinc_neg]

@[simp] lemma Complex.ofReal_sinc (x : ℝ) : Real.sinc x = Complex.sinc x := by
  rw [sinc, Real.sinc]; aesop

/-!
### Taylor series with remainder for `sinc`
-/

lemma Complex.sinc_series_bound {z : ℂ} (z1 : ‖z‖ ≤ 1) (n : ℕ) :
    ‖sinc z - ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k + 1).factorial‖ ≤
      ‖z‖ ^ (2 * n) * ((2 * n + 2) / ((2 * n + 1).factorial * (2 * n + 1))) := by
  by_cases z0 : z = 0
  · induction' n with n _
    all_goals simp [sinc, z0, Finset.sum_range_succ']
  · rw [← mul_div_cancel_left₀ (∑ k ∈ Finset.range _, _) z0]
    simp only [sinc, z0, if_false, ← sub_div, norm_div, div_le_iff₀ (norm_pos_iff.mpr z0),
      mul_comm _ ‖z‖, ← mul_assoc ‖z‖, ← pow_succ']
    exact sin_series_bound z1 n

lemma Real.sinc_series_bound {x : ℝ} (x1 : |x| ≤ 1) (n : ℕ) :
    |sinc x - ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k) / (2 * k + 1).factorial| ≤
      |x| ^ (2 * n) * ((2 * n + 2) / ((2 * n + 1).factorial * (2 * n + 1))) := by
  have b := Complex.sinc_series_bound (z := x) (by simpa only [Complex.norm_real]) n
  simp only [← Complex.ofReal_sinc, ← Complex.ofReal_pow, ← Complex.ofReal_one,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
    ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.norm_real] at b
  exact b

/-!
### Auxiliary functions with cleaner power series
-/

noncomputable def sinc_sqrt (x : ℝ) : ℝ := Real.sinc (Real.sqrt x)

noncomputable def cos_sqrt (x : ℝ) : ℝ := Real.cos (Real.sqrt x)

/-- `sinc_sqrt` suffices to compute `sinc` -/
lemma Real.sinc_eq_sinc_sqrt (x : ℝ) : sinc x = sinc_sqrt (|x| ^ 2) := by
  simp only [sinc_sqrt, sq_abs, sqrt_sq_eq_abs, sinc_abs]

/-- `sinc_sqrt` suffices to compute `sin` -/
lemma Real.sin_eq_sinc_sqrt (x : ℝ) : sin x = x * sinc_sqrt (|x| ^ 2) := by
  simp only [sin_eq_sinc, sinc_eq_sinc_sqrt]

/-- `cos_sqrt` suffices to compute `cos` -/
lemma cos_eq_cos_sqrt (x : ℝ) : Real.cos x = cos_sqrt (|x| ^ 2) := by
  simp only [cos_sqrt, sq_abs, Real.sqrt_sq_eq_abs, Real.cos_abs]
