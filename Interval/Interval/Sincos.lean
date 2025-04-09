import Interval.Floating.Floor
import Interval.Interval.Monotone
import Interval.Interval.Pi
import Interval.Interval.Scale
import Interval.Interval.Series
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.Tactic.FinCases

/-!
## Interval `sin` and `cos`
-/

open Set
open scoped Real
open scoped UInt64.CommRing

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
### Auxiliary functions with cleaner power series
-/

noncomputable def Complex.sinc (z : ℂ) : ℂ := if z = 0 then 1 else Complex.sin z / z

noncomputable def Real.sinc (x : ℝ) : ℝ := if x = 0 then 1 else Real.sin x / x

noncomputable def sinc_sqrt (x : ℝ) : ℝ := Real.sinc (Real.sqrt x)

noncomputable def cos_sqrt (x : ℝ) : ℝ := Real.cos (Real.sqrt x)

/-- `sinc` suffices to compute `sin` -/
lemma Complex.sin_eq_sinc (z : ℂ) : sin z = z * sinc z := by
  by_cases z0 : z = 0
  · simp [z0]
  · rw [sinc]; field_simp [z0]

/-- `sinc` suffices to compute `sin` -/
lemma Real.sin_eq_sinc (x : ℝ) : sin x = x * sinc x := by
  by_cases x0 : x = 0
  · simp [x0]
  · rw [sinc]; field_simp [x0]

@[simp] lemma Complex.sinc_neg (x : ℝ) : sinc (-x) = sinc x := by simp [sinc]
@[simp] lemma Real.sinc_neg (x : ℝ) : sinc (-x) = sinc x := by simp [sinc]

/-- `sinc` is even -/
@[simp] lemma Real.sinc_abs (x : ℝ) : sinc |x| = sinc x := by
  by_cases x0 : 0 ≤ x
  · simp only [abs_of_nonneg x0]
  · simp only [abs_of_neg (not_le.mp x0), sinc_neg]

@[simp] lemma Complex.ofReal_sinc (x : ℝ) : Real.sinc x = Complex.sinc x := by
  rw [sinc, Real.sinc]; aesop

/-- `sinc_sqrt` suffices to compute `sinc` -/
lemma Real.sinc_eq_sinc_sqrt (x : ℝ) : sinc x = sinc_sqrt (|x| ^ 2) := by
  simp only [sinc_sqrt, sq_abs, sqrt_sq_eq_abs, sinc_abs]

/-- `sinc_sqrt` suffices to compute `sin` -/
lemma Real.sin_eq_sinc_sqrt (x : ℝ) : sin x = x * sinc_sqrt (|x| ^ 2) := by
  simp only [sin_eq_sinc, sinc_eq_sinc_sqrt]

/-- `cos_sqrt` suffices to compute `cos` -/
lemma cos_eq_cos_sqrt (x : ℝ) : Real.cos x = cos_sqrt (|x| ^ 2) := by
  simp only [cos_sqrt, sq_abs, Real.sqrt_sq_eq_abs, Real.cos_abs]

/-!
### Taylor series with remainder for `sin` and `cos`
-/

/-- Double the range of a `Finset.sum` -/
lemma Finset.sum_range_even {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ k ∈ Finset.range n, f k = ∑ k ∈ Finset.range (2 * n), if Even k then f (k / 2) else 0 := by
  induction' n with n h
  · simp
  · simp [Finset.sum_range_succ, h, mul_add]

lemma Complex.sin_series_bound {z : ℂ} (z1 : abs z ≤ 1) {n : ℕ} (n0 : 0 < n) :
    abs (sin z - z * ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k + 1).factorial) ≤
      abs z ^ (2 * n + 1) * ((2 * n + 2) / ((2 * n + 1).factorial * (2 * n + 1))) := by
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
        neg_mul, mul_neg, neg_neg, sub_neg_eq_add, ← add_mul]
      ring_nf
      simp only [mul_comm _ 2, pow_mul, I_sq, inv_I, mul_neg]
      simp only [mul_comm _ I, ← mul_assoc, I_mul_I, neg_mul, one_mul, neg_neg, mul_one]
    · simp [e, pow_mul, pow_add, mul_pow, neg_div]
  have r : ∀ a b c d : ℂ, (a - b) - (c - d) = (a - c) - (b - d) := fun _ _ _ _ ↦ by ring
  rw [sin, e, ← sub_div, ← sub_mul, r, map_div₀, Complex.abs_two, div_le_iff₀ (by norm_num),
    Complex.abs.map_mul, Complex.abs_I, mul_one]
  refine le_trans (Complex.abs.sub_le_add _ _) ?_
  refine le_trans (add_le_add (Complex.exp_bound (x := -z * I) (by simpa) (by omega))
    (Complex.exp_bound (x := z * I) (by simpa) (by omega))) (le_of_eq ?_)
  simp only [Complex.abs.map_mul, Complex.abs_I, Complex.abs.map_neg, Nat.succ_eq_add_one,
    Nat.cast_add, Nat.cast_mul]
  ring_nf

lemma Complex.sinc_series_bound {z : ℂ} (z1 : abs z ≤ 1) {n : ℕ} (n0 : 0 < n) :
    abs (sinc z - ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k + 1).factorial) ≤
      abs z ^ (2 * n) * ((2 * n + 2) / ((2 * n + 1).factorial * (2 * n + 1))) := by
  by_cases z0 : z = 0
  · induction' n with n _
    all_goals simp [sinc, z0, Finset.sum_range_succ']
  · rw [← mul_div_cancel_left₀ (∑ k ∈ Finset.range _, _) z0]
    simp only [sinc, z0, if_false, ← sub_div, map_div₀, div_le_iff₀ (Complex.abs.pos_iff.mpr z0),
      mul_comm _ (abs z), ← mul_assoc (abs z), ← pow_succ']
    exact sin_series_bound z1 n0

lemma Complex.cos_series_bound {z : ℂ} (z1 : abs z ≤ 1) {n : ℕ} (n0 : 0 < n) :
    abs (cos z - ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k).factorial) ≤
      abs z ^ (2 * n) * ((2 * n + 1) / ((2 * n).factorial * (2 * n))) := by
  have e : ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k).factorial =
      (∑ k ∈ Finset.range (2 * n), (z * I) ^ k / k.factorial +
       ∑ k ∈ Finset.range (2 * n), (-z * I) ^ k / k.factorial) / 2 := by
    simp only [← Finset.sum_add_distrib, ← sub_div, Finset.sum_range_even n, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rcases Nat.even_or_odd' k with ⟨a, e | e⟩
    · simp only [e, even_two, Even.mul_right, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_div_cancel_left₀, pow_mul, mul_pow, I_sq, mul_neg, mul_one, neg_mul,
        Even.neg_pow, ← add_div, neg_pow' (z^2), mul_comm _ ((-1 : ℂ) ^ a), ← add_mul]
      ring
    · simp [e, pow_mul, pow_add, mul_pow, neg_div]
  have r : ∀ a b c d : ℂ, (a + b) - (c + d) = (a - c) + (b - d) := fun _ _ _ _ ↦ by ring
  rw [cos, e, ← sub_div, r, map_div₀, Complex.abs_two, div_le_iff₀ (by norm_num)]
  refine le_trans (Complex.abs.add_le _ _) ?_
  refine le_trans (add_le_add (Complex.exp_bound (x := z * I) (by simpa) (by omega))
    (Complex.exp_bound (x := -z * I) (by simpa) (by omega))) (le_of_eq ?_)
  simp only [Complex.abs.map_mul, Complex.abs_I, Complex.abs.map_neg, Nat.succ_eq_add_one,
    Nat.cast_add, Nat.cast_mul]
  ring_nf

lemma Real.sin_series_bound {x : ℝ} (x1 : |x| ≤ 1) {n : ℕ} (n0 : 0 < n) :
    |sin x - x * ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k) / (2 * k + 1).factorial| ≤
      |x| ^ (2 * n + 1) * ((2 * n + 2) / ((2 * n + 1).factorial * (2 * n + 1))) := by
  have b := Complex.sin_series_bound (z := x) (by simpa only [Complex.abs_ofReal]) n0
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_pow, ← Complex.ofReal_one,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
    ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.abs_ofReal] at b
  exact b

lemma Real.sinc_series_bound {x : ℝ} (x1 : |x| ≤ 1) {n : ℕ} (n0 : 0 < n) :
    |sinc x - ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k) / (2 * k + 1).factorial| ≤
      |x| ^ (2 * n) * ((2 * n + 2) / ((2 * n + 1).factorial * (2 * n + 1))) := by
  have b := Complex.sinc_series_bound (z := x) (by simpa only [Complex.abs_ofReal]) n0
  simp only [← Complex.ofReal_sinc, ← Complex.ofReal_pow, ← Complex.ofReal_one,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
    ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.abs_ofReal] at b
  exact b

lemma Real.cos_series_bound {x : ℝ} (x1 : |x| ≤ 1) {n : ℕ} (n0 : 0 < n) :
    |cos x - ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k) / (2 * k).factorial| ≤
      |x| ^ (2 * n) * ((2 * n + 1) / ((2 * n).factorial * (2 * n))) := by
  have b := Complex.cos_series_bound (z := x) (by simpa only [Complex.abs_ofReal]) n0
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_pow, ← Complex.ofReal_one,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
    ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.abs_ofReal] at b
  exact b

/-!
### `sinc (sqrt x)` and `cos (sqrt x)` for small `x` via series
-/

/-- Our series will be accurate on `[-r,r]` for `r` slightly larger than `sqrt (π / 4)`. -/
def sincos_sqrt_series_radius : ℚ := 0.886227

/-- A power series approximation for `sinc_sqrt` -/
@[irreducible] def sinc_sqrt_series (n : ℕ) : Series where
  radius := .ofRat sincos_sqrt_series_radius false
  coeffs := (Array.range n).map (fun n ↦ .ofRat ((-1)^n * (Nat.factorial (2 * n + 1) : ℚ)⁻¹))
  error := bif n == 0 then nan
           else .ofRat (sincos_sqrt_series_radius ^ n * ((2 * n + 2) /
             ((2 * n + 1).factorial * (2 * n + 1)))) true

/-- A power series approximation for `cos_sqrt` -/
@[irreducible] def cos_sqrt_series (n : ℕ) : Series where
  radius := .ofRat sincos_sqrt_series_radius false
  coeffs := (Array.range n).map (fun n ↦ .ofRat ((-1)^n * (Nat.factorial (2 * n) : ℚ)⁻¹))
  error := bif n == 0 then nan
           else .ofRat (sincos_sqrt_series_radius ^ n * ((2 * n + 1) /
             ((2 * n).factorial * (2 * n)))) true

lemma abs_sqrt_abs_le_one {x : ℝ} (xr : |x| ≤ sincos_sqrt_series_radius) : |√(|x|)| ≤ 1 := by
  simp only [abs_le, Real.sqrt_le_one]
  refine ⟨le_trans (by norm_num) (Real.sqrt_nonneg _), abs_le.mp ?_⟩
  simp only [sincos_sqrt_series_radius] at xr
  exact le_trans xr (by norm_num)

/-- Our power series for `sinc (sqrt x)` is correct -/
lemma mem_approx_sinc_sqrt_series (n : ℕ) (x : ℝ) (x0 : 0 ≤ x) (y : Interval)
    (xy : x ∈ approx y) : sinc_sqrt x ∈ approx ((sinc_sqrt_series n).eval y) := by
  have nn : (sinc_sqrt_series n).coeffs.size = n := by
    rw [sinc_sqrt_series, Array.size_map, Array.size_range]
  by_cases n0 : n = 0
  · have e : (sinc_sqrt_series 0).error = nan := by rw [sinc_sqrt_series]; simp
    simp [n0, Series.eval, e]
  · apply (sinc_sqrt_series n).approx_of_taylor'
        (a := fun n ↦ (-1)^n * (Nat.factorial (2 * n + 1) : ℝ)⁻¹) (xy := xy)
        (b := sincos_sqrt_series_radius ^ n * ((2 * n + 2) /
          ((2 * n + 1).factorial * (2 * n + 1))))
    · intro rn xr
      rw [sinc_sqrt_series] at xr rn
      simp only at xr
      have xr' : |x| ≤ sincos_sqrt_series_radius := le_trans xr (Floating.ofRat_le rn)
      have x1 : |√(|x|)| ≤ 1 := abs_sqrt_abs_le_one xr'
      simp only [nn, sinc_sqrt]
      have h := Real.sinc_series_bound x1 (Nat.pos_iff_ne_zero.mpr n0)
      simp only [div_eq_inv_mul, ← mul_assoc, mul_comm _ ((-1 : ℝ)^_), pow_mul, abs_nonneg,
        Real.sq_sqrt x0, sq_abs, abs_of_nonneg x0] at h ⊢
      refine le_trans h ?_
      simp only [mul_assoc]
      apply mul_le_mul_of_nonneg_right
      · simp only [abs_of_nonneg x0] at xr'
        bound
      · positivity
    · intro k
      have e : (Nat.factorial (2 * k + 1) : ℝ)⁻¹ = (Nat.factorial (2 * k + 1) : ℚ)⁻¹ := by
        simp only [Rat.cast_inv, Rat.cast_natCast]
      simp only [sinc_sqrt_series, Array.getElem_map, Array.range_getElem, ← Rat.cast_inv, e,
        (by norm_num : (-1 : ℝ) = (-1 : ℚ)), ← Rat.cast_pow, ← Rat.cast_inv, ← Rat.cast_mul]
      apply Interval.approx_ofRat
    · intro en
      rw [sinc_sqrt_series, bif_eq_if] at en ⊢
      simp only [beq_iff_eq, ne_eq, ite_eq_left_iff, not_forall, exists_prop, n0, not_false_iff,
        true_or, if_false] at en ⊢
      refine le_trans (le_of_eq ?_) (Floating.le_ofRat en)
      simp only [div_eq_inv_mul, mul_inv, mul_comm _ ((n:ℚ)⁻¹), Rat.cast_mul, Rat.cast_pow,
        Rat.cast_inv, Rat.cast_natCast, Rat.cast_add, Rat.cast_one]
      ring

/-- Our power series for `cos (sqrt x)` is correct -/
lemma mem_approx_cos_sqrt_series (n : ℕ) (x : ℝ) (x0 : 0 ≤ x) (y : Interval)
    (xy : x ∈ approx y) : cos_sqrt x ∈ approx ((cos_sqrt_series n).eval y) := by
  have nn : (cos_sqrt_series n).coeffs.size = n := by
    rw [cos_sqrt_series, Array.size_map, Array.size_range]
  by_cases n0 : n = 0
  · have e : (cos_sqrt_series 0).error = nan := by rw [cos_sqrt_series]; simp
    simp [n0, Series.eval, e]
  · apply (cos_sqrt_series n).approx_of_taylor'
        (a := fun n ↦ (-1)^n * (Nat.factorial (2 * n) : ℝ)⁻¹) (xy := xy)
        (b := sincos_sqrt_series_radius ^ n * ((2 * n + 1) / ((2 * n).factorial * (2 * n))))
    · intro rn xr
      rw [cos_sqrt_series] at xr rn
      simp only at xr
      have xr' : |x| ≤ sincos_sqrt_series_radius := le_trans xr (Floating.ofRat_le rn)
      have x1 : |√(|x|)| ≤ 1 := abs_sqrt_abs_le_one xr'
      simp only [nn, cos_sqrt]
      have h := Real.cos_series_bound x1 (Nat.pos_iff_ne_zero.mpr n0)
      simp only [div_eq_inv_mul, ← mul_assoc, mul_comm _ ((-1 : ℝ)^_), pow_mul, abs_nonneg,
        Real.sq_sqrt x0, sq_abs, abs_of_nonneg x0] at h ⊢
      refine le_trans h ?_
      simp only [mul_assoc]
      apply mul_le_mul_of_nonneg_right
      · simp only [abs_of_nonneg x0] at xr'
        bound
      · positivity
    · intro k
      have e : (Nat.factorial (2 * k) : ℝ)⁻¹ = (Nat.factorial (2 * k) : ℚ)⁻¹ := by
        simp only [Rat.cast_inv, Rat.cast_natCast]
      simp only [cos_sqrt_series, Array.getElem_map, Array.range_getElem, ← Rat.cast_inv, e,
        (by norm_num : (-1 : ℝ) = (-1 : ℚ)), ← Rat.cast_pow, ← Rat.cast_inv, ← Rat.cast_mul]
      apply Interval.approx_ofRat
    · intro en
      rw [cos_sqrt_series, bif_eq_if] at en ⊢
      simp only [beq_iff_eq, ne_eq, ite_eq_left_iff, not_forall, exists_prop, n0, not_false_iff,
        true_or, if_false] at en ⊢
      refine le_trans (le_of_eq ?_) (Floating.le_ofRat en)
      simp only [div_eq_inv_mul, mul_inv, mul_comm _ ((n:ℚ)⁻¹), Rat.cast_mul, Rat.cast_pow,
        Rat.cast_inv, Rat.cast_natCast, Rat.cast_add, Rat.cast_one]
      ring

@[approx] lemma mem_approx_sin_series {a : ℝ} {x : Interval} (ax : a ∈ approx x) {n : ℕ} :
    Real.sin a ∈ approx (x * (sinc_sqrt_series n).eval x.sqr) := by
  simp only [Real.sin_eq_sinc_sqrt, sq_abs]
  apply mem_approx_mul ax
  apply mem_approx_sinc_sqrt_series
  · bound
  · approx

@[approx] lemma mem_approx_cos_series {a : ℝ} {x : Interval} (ax : a ∈ approx x) {n : ℕ} :
    Real.cos a ∈ approx ((cos_sqrt_series n).eval x.sqr) := by
  simp only [cos_eq_cos_sqrt, sq_abs]
  apply mem_approx_cos_sqrt_series
  · bound
  · approx

/-- 11 terms are about enough for 64 bits of precision -/
@[irreducible] def sinc_sqrt_series_11 := sinc_sqrt_series 11
@[irreducible] def cos_sqrt_series_11 := cos_sqrt_series 11

@[irreducible] def Interval.sin_small (x : Interval) : Interval :=
  x * sinc_sqrt_series_11.eval x.sqr

@[irreducible] def Interval.cos_small (x : Interval) : Interval :=
  cos_sqrt_series_11.eval x.sqr

@[approx] lemma Interval.mem_approx_sin_small {a : ℝ} {x : Interval} (ax : a ∈ approx x) :
    Real.sin a ∈ approx x.sin_small := by
  rw [sin_small, Real.sin_eq_sinc_sqrt, sq_abs, sinc_sqrt_series_11]
  exact mem_approx_mul ax (mem_approx_sinc_sqrt_series _ _ (by bound) _ (by approx))

@[approx] lemma Interval.mem_approx_cos_small {a : ℝ} {x : Interval} (ax : a ∈ approx x) :
    Real.cos a ∈ approx x.cos_small := by
  rw [cos_small, cos_eq_cos_sqrt, sq_abs, cos_sqrt_series_11]
  exact mem_approx_cos_sqrt_series _ _ (by bound) _ (by approx)

@[simp] lemma Interval.sin_small_nan : Interval.sin_small nan = nan := by
  rw [sin_small]; simp only [nan_mul]

@[simp] lemma Interval.cos_small_nan : Interval.cos_small nan = nan := by
  rw [cos_small]; simp only [sqr_nan, Series.eval_nan]

/-!
### `sin x` and `cos x` for arbitrary `x`, via argument reduction

To compute either of these, we subtract a multiple of `π / 2` to get into the interval
`[-π / 4, π / 4]`, compute one of `sin` and `cos` (possibly flipped from our original), and negate
if necessary to recover the original value. Since `sin` and `cos` are not monotonic, we must take
into account extrema reached in between the endpoints.
-/

/-- We always know that `sin x, cos x ∈ [-1, 1]` -/
@[irreducible] def Interval.pm1 : Interval := -1 ∪ 1

-- `pm1` is exact
@[simp] lemma Interval.pm1_ne_nan : pm1 ≠ nan := by fast_decide
@[simp] lemma Interval.lo_pm1 : pm1.lo.val = -1 := by
  simp [← Floating.coe_valq, (by fast_decide : pm1.lo.valq = -1)]
@[simp] lemma Interval.hi_pm1 : pm1.hi.val = 1 := by
  simp [← Floating.coe_valq, (by fast_decide : pm1.hi.valq = 1)]
@[simp] lemma Interval.approx_pm1 : approx pm1 = Icc (-1) 1 := by simp [approx]

/-- `sin (x + π / 2 * d)` for potentially large `x`, via argument reduction, sending `nan → nan` -/
@[irreducible] def Floating.presin (x : Floating) (d : Fixed 0) : Interval :=
  -- Helpful picture:
  --   https://en.wikipedia.org/wiki/Sine_and_cosine#/media/File:Sine_cosine_one_period.svg
  let n := ((x.mul Interval.two_div_pi.lo false).add (.ofRat (1/2) false) false).floor
  let m := n + d
  bif m == nan then nan else
  -- Conceptually, we can subtract n / 2 * 4 with no change, so w.l.o.g. 0 ≤ n < 8
  let k := m.n.toUInt64 % 4
  -- We handle the interval `[-π/4, 3π/2]` via case analysis
  let x := x - Interval.pi_div_2.mul_float n
  let y := bif k == 0 || k == 2 then x.sin_small else x.cos_small
  bif decide (2 ≤ k) then -y else y

lemma Int64.n_mod_4 (x : Int64) : (x.toUInt64.toNat % 4 : ℕ) = x.toInt % 4 := by
  by_cases xn : x < 0
  · have e : ((2 ^ 64 : ℕ) : ℤ) % 4 = 0 := rfl
    rw [Int64.coe_of_neg xn, Int.sub_emod, e, sub_zero, Int.emod_emod, Int.ofNat_emod,
      Nat.cast_ofNat]
  · simp only [Bool.not_eq_true] at xn
    rw [Int64.coe_of_nonneg (not_lt.mp xn), Int.ofNat_emod, Nat.cast_ofNat]

/-- `Floating.presin` is conservative -/
@[approx] lemma Floating.mem_approx_presin {x' : ℝ} {x : Floating} (ax : x'  ∈ approx x)
    (d : Fixed 0) : Real.sin (x' + π / 2 * d.val) ∈ approx (x.presin d) := by
  rw [presin]
  generalize hn : ((x.mul Interval.two_div_pi.lo false).add (.ofRat (1/2) false) false).floor = n
  generalize hm : n + d = m
  generalize hk : m.n.toUInt64 % 4 = k
  simp only [hm, hk]
  simp only [bif_eq_if, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hk ⊢
  by_cases mn : m = nan
  · simp only [mn, ↓reduceIte, Interval.approx_nan, mem_univ]
  simp only [mn, ↓reduceIte]
  have hmv : n.val + d.val = m.val := by rw [← hm, Fixed.val_add]; rwa [hm]
  have k4 : k.toNat < 4 := by
    rw [← hk, UInt64.toNat_mod, (by rfl : UInt64.toNat 4 = 4)]
    exact Nat.mod_lt _ (by norm_num)
  generalize ha : Fin.mk k.toNat k4 = a
  have ak : k = (a.val : UInt64) := by simp only [← ha, UInt64.cast_toNat]
  generalize hq : m.n.toInt / 4 = q
  have q4 : 4 % UInt64.size = 4 := rfl
  have e4 : UInt64.toNat 4 = 4 := rfl
  have nq : m.val = 4 * q + a.val := by
    simp only [Fixed.val_of_s0, ← hq, ← ha, ← hk, UInt64.toNat_mod, UInt64.toNat_ofNat,
      (by norm_num : (4 : ℝ) = (4 : ℤ)), ← Int.cast_mul, ← Int.cast_natCast (R := ℝ),
      ← Int.cast_add, Int.cast_inj, q4, Int64.n_mod_4, Int.ediv_add_emod, e4]
  have p0 : π / 2 * (4 * q) = q * (2 * π) := by ring
  have p1 : ∀ d, π / 2 * (4 * q + d) = π / 2 * d + q * (2 * π) := fun _ ↦ by ring
  simp only [ak, beq_iff_eq] at hk ⊢
  have fa : ∀ {n : Fixed 0} {f : ℝ → ℝ} {g : Interval → Interval},
      (h : ∀ (z : ℝ) (w : Interval), z ∈ approx w → f (z + π / 2 * n.val) ∈ approx (g w)) →
      f x' ∈ approx (g (x - Interval.pi_div_2.mul_float n)) := by
    intro n f g h
    have e : x' = x' - π / 2 * n.val + π / 2 * n.val := by ring
    rw [e]; apply h; approx
  fin_cases a
  all_goals simp
  · refine fa (f := fun x ↦ Real.sin (x + π / 2 * d.val)) fun z w zw ↦ ?_
    simp only [nq, CharP.cast_eq_zero, add_zero, p0, Real.sin_add_int_mul_two_pi, add_assoc,
      ← mul_add, hmv]
    approx
  · refine fa (f := fun x ↦ Real.sin (x + π / 2 * d.val)) fun z w zw ↦ ?_
    simp only [nq, Nat.cast_one, p1, mul_one, Real.sin_add_int_mul_two_pi,
      Real.sin_add_pi_div_two, add_assoc _ (_ * _), ← mul_add, hmv, ← add_assoc _ (π / 2)]
    approx
  · refine fa (f := fun x ↦ -Real.sin (x + π / 2 * d.val)) fun z w zw ↦ ?_
    simp only [nq, Nat.cast_ofNat, p1, (by ring : π / 2 * 2 = π), ← add_assoc _ π,
      Real.sin_add_int_mul_two_pi, Real.sin_add_pi, neg_neg, add_assoc _ (_ * _), ← mul_add, hmv]
    approx
  · refine fa (f := fun x ↦ -Real.sin (x + π / 2 * d.val)) fun z w zw ↦ ?_
    simp only [nq, Nat.cast_ofNat, p1, (by ring : z + π / 2 * 3 = z + π + π / 2),
      Real.sin_add_int_mul_two_pi, Real.sin_add_pi_div_two, Real.cos_add_pi, neg_neg,
      add_assoc _ (_ * n.val), ← mul_add, hmv, ← add_assoc _ (_ * (3 : ℝ))]
    approx

/-- `Floating.presin` always touches `[-1, 1]` -/
lemma Floating.presin_inter_pm1 (x : Floating) (d : Fixed 0) :
    (approx (x.presin d) ∩ approx Interval.pm1).Nonempty := by
  use Real.sin (x.val + π / 2 * d.val)
  simp only [Interval.approx_pm1, mem_inter_iff, mem_Icc]
  exact ⟨by approx, Real.neg_one_le_sin _, Real.sin_le_one _⟩

/-- `sin (x + π / 2 * d)` for potentially large `x`, via argument reduction -/
@[irreducible] def Floating.sin (x : Floating) (d : Fixed 0) : Interval :=
  (x.presin d).inter Interval.pm1 (x.presin_inter_pm1 d)

/-- `Floating.sin` is conservative -/
@[approx] lemma Floating.mem_approx_sin {x' : ℝ} {x : Floating} (ax : x'  ∈ approx x)
    (d : Fixed 0) : Real.sin (x' + π / 2 * d.val) ∈ approx (x.sin d) := by
  have m : Real.sin (x' + π / 2 * d.val) ∈ approx Interval.pm1 := by
    simp [Real.neg_one_le_sin, Real.sin_le_one]
  rw [sin]
  approx

@[simp] lemma Floating.presin_nan (d : Fixed 0) : (nan : Floating).presin d = nan := by
  rw [presin]; simp

@[simp] lemma Floating.sin_nan (d : Fixed 0) : (nan : Floating).sin d = Interval.pm1 := by
  rw [sin]; simp only [presin_nan, Interval.nan_inter]

/-- `sin (x + π / 2 * d)` for potentially large `x`, via argument reduction -/
@[irreducible] def Interval.sincos (x : Interval) (d : Bool) : Interval :=
  -- Helpful picture:
  --   https://en.wikipedia.org/wiki/Sine_and_cosine#/media/File:Sine_cosine_one_period.svg
  -- Sin is monotonic on each `[-π/2, π/2] + πn` interval, so figure out `n` for `lo` and `hi`.
  let n := x * inv_pi + bif d then 1 else ofRat (1/2)
  let n0 := n.lo.floor
  let n1 := n.hi.floor
  -- If `n0` and `n1` differ by more than 1, during the `n0 + 1` interval `sin` covers `[-1, 1]`
  bif n0 == nan || n1 == nan || n0 + 1 = nan || (n0 + 1).blt n1 then .pm1 else
  let d' : Fixed 0 := bif d then 1 else 0
  let y := x.lo.sin d' ∪ x.hi.sin d'
  -- If `n0 = n1`, `sin` is monotonic on the interval. Otherwise, we need to add in either +1 or -1.
  bif n0 == n1 then y else
  bif n0.n.toUInt64 &&& 1 == 0 then y ∪ 1 else y ∪ (-1)

lemma Even.sub_iff {a b : ℤ} (be : Even b) : Even (a - b) ↔ Even a := by
  simp only [Int.even_iff] at be ⊢
  omega

lemma floor_even_iff {n : Floating} (nn : n.floor ≠ nan) :
    n.floor.n.toUInt64 &&& 1 = 0 ↔ Even ⌊n.val⌋ := by
  have a := n.mem_approx_floor
  simp only [approx, nn, ↓reduceIte, Fixed.val_of_s0, mem_singleton_iff, Int.cast_inj] at a
  have ep : Even (if n.floor.n.isNeg = true then 18446744073709551616 else 0 : ℤ) := by
    split_ifs; all_goals decide
  simp only [UInt64.eq_iff_toNat_eq, UInt64.toNat_and, UInt64.toNat_ofNat, Nat.one_mod,
    Nat.and_one_is_mod, Nat.zero_mod, a, Int64.toInt_eq_if, Nat.reducePow, bif_eq_if, Nat.cast_ite,
    Nat.cast_ofNat, CharP.cast_eq_zero, Even.sub_iff ep, Int.even_iff, UInt64.toNat_one,
    Nat.and_one_is_mod, UInt64.toNat_zero]
  omega

/-- `Interval.sincos` is conservative -/
@[approx] lemma Interval.mem_approx_sincos {x : Interval} {a : ℝ} (ax : a ∈ approx x) (d : Bool) :
    Real.sin (a + bif d then π / 2 else 0) ∈ approx (x.sincos d) := by
  rw [Interval.sincos]
  by_cases xn : x = nan
  · simp [xn, Real.neg_one_le_sin, Real.sin_le_one]
  generalize hn : x * inv_pi + (if d then 1 else ofRat 2⁻¹) = n
  generalize hj : (if d then (1 : Fixed 0) else 0) = j
  simp only [one_div, hn, bif_eq_if, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq, or_assoc, hj]
  by_cases h : n.lo.floor = nan ∨ n.hi.floor = nan ∨ n.lo.floor + 1 = nan ∨
      (n.lo.floor + 1).blt n.hi.floor = true
  · simp [h, Real.neg_one_le_sin, Real.sin_le_one]
  simp only [h, if_false]
  simp only [not_or, Bool.not_eq_true, ← ne_eq] at h
  obtain ⟨n0n, n1n, n0n', le⟩ := h
  have f0 := n.lo.mem_approx_floor
  have f1 := n.hi.mem_approx_floor
  generalize hk0 : ⌊n.lo.val⌋ = k0 at f0
  generalize hk1 : ⌊n.hi.val⌋ = k1 at f1
  simp only [approx, n0n, ↓reduceIte, mem_singleton_iff, n1n] at f0 f1
  have parity : n.lo.floor.n.toUInt64 &&& 1 = 0 ↔ Even k0 := by
    simp only [floor_even_iff n0n, ← f0, Int.floor_intCast, hk0]
  have an0 : x.lo.val * π⁻¹ + ((if d then 1 else (2⁻¹ : ℚ)) : ℝ) ∈ approx n := by rw [← hn]; approx
  have an1 : x.hi.val * π⁻¹ + ((if d then 1 else (2⁻¹ : ℚ)) : ℝ) ∈ approx n := by rw [← hn]; approx
  have ax' : a ∈ Icc x.lo.val x.hi.val := by
    simpa only [approx, x.lo_ne_nan xn, ↓reduceIte, mem_Icc] using ax
  have nn := n.lo.ne_nan_of_floor n0n
  have jv : ((if d then 1 else 2⁻¹) : ℝ) = 2⁻¹ + j.val / 2 := by
    induction' d; all_goals norm_num [← hj]
  have jv' : (if d then π / 2 else 0) = π / 2 * j.val := by induction' d; all_goals simp [← hj]
  simp only [ne_eq, lo_eq_nan] at nn
  simp only [approx, lo_eq_nan, nn, ↓reduceIte, Rat.cast_inv, Rat.cast_ofNat, mem_Icc,
    jv] at an0 an1
  replace an0 := le_trans (Int.floor_le _) an0.1
  replace an1 := lt_of_le_of_lt an1.2 (Int.lt_floor_add_one _)
  simp only [hk0, hk1] at an0 an1
  have kle : k0 ≤ k1 := by
    rw [← Int.cast_le (R := ℝ), f0, f1, ← Fixed.le_iff]
    exact Floating.floor_mono n.lo_le_hi n1n
  replace an0 : k0 * π - π / 2 ≤ x.lo.val + π / 2 * j.val := by
    calc k0 * π - π / 2
      _ ≤ (x.lo.val * π⁻¹ + (2⁻¹ + j.val / 2)) * π - π / 2 := by bound
      _ = x.lo.val + π / 2 * j.val := by ring_nf; field_simp [Real.pi_ne_zero]
  replace an1 : x.hi.val + π / 2 * j.val ≤ k1 * π + π / 2 := by
    calc k1 * π + π / 2
      _ = (k1 + 1) * π - π / 2 := by ring
      _ ≥ (x.hi.val * π⁻¹ + (2⁻¹ + j.val / 2)) * π - π / 2 := by bound
      _ = x.hi.val + π / 2 * j.val := by ring_nf; field_simp [Real.pi_ne_zero]
  generalize hb : a + π / 2 * j.val = b
  simp only [Fixed.blt_eq_decide_lt, Fixed.lt_iff, Fixed.val_add n0n', ← f0, ← f1,
    decide_eq_false_iff_not, not_lt, Fixed.val_one_of_s0, ← Int.cast_one (R := ℝ),
    ← Int.cast_add, Int.cast_le, ← Fixed.val_eq_val, Int.cast_inj, parity, jv', hb] at le ⊢
  clear hk0 hk1 nn parity n0n n1n n0n' hn
  rcases k0.even_or_odd' with ⟨k, e | e⟩
  · by_cases k01 : k0 = k1
    · simp only [e, Int.cast_mul, Int.cast_ofNat, ← k01, mul_right_comm _ _ π] at an0 an1
      simp only [k01, ↓reduceIte]
      apply mem_approx_of_monotone' (u := x.lo.val + π / 2 * j.val) (v := x.hi.val + π / 2 * j.val)
      · exact (Real.sin_monotone k).mono (Icc_subset_Icc (by linarith) (by linarith))
      · rw [← hb]; exact ⟨by linarith [ax'.1], by linarith [ax'.2]⟩
      · approx
      · approx
    · replace k01 : k1 = k0 + 1 := by omega
      simp only [e, k01, Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_one, add_mul,
        mul_right_comm _ _ π, one_mul, (by ring : π + π / 2 = 3 * π / 2), add_assoc] at an0 an1
      have u : x.lo.sin j ∪ x.hi.sin j ∪ 1 = (x.lo.sin j ∪ 1) ∪ (1 ∪ x.hi.sin j) := by
        simp only [union_comm _ 1, ← union_assoc, union_self]
      simp only [e, k01, self_eq_add_right, one_ne_zero, ↓reduceIte, even_two, Even.mul_right, u]
      by_cases s : b ≤ 2 * π * ↑k + π / 2
      · apply approx_union_left
        apply mem_approx_of_monotone' (u := x.lo.val + π / 2 * j.val) (v := 2 * π * k + π / 2)
        · exact (Real.sin_monotone k).mono (Icc_subset_Icc (by linarith) (by linarith))
        · exact ⟨by linarith [ax'.1], by linarith⟩
        · approx
        · simp [Real.sin_add_pi_div_two, mul_comm (2 * π)]
      · apply approx_union_right
        apply mem_approx_of_antitone' (u := 2 * π * k + π / 2) (v := x.hi.val + π / 2 * j.val)
        · exact (Real.sin_antitone k).mono (Icc_subset_Icc (by linarith) (by linarith))
        · exact ⟨by linarith, by linarith [ax'.2]⟩
        · simp [Real.sin_add_pi_div_two, mul_comm (2 * π)]
        · approx
  · by_cases k01 : k0 = k1
    · simp only [e, Int.cast_mul, Int.cast_ofNat, Int.cast_add, Int.cast_one, ← k01,
        mul_right_comm _ _ π] at an0 an1
      simp only [k01, ↓reduceIte]
      apply mem_approx_of_antitone' (u := x.lo.val + π / 2 * j.val) (v := x.hi.val + π / 2 * j.val)
      · exact (Real.sin_antitone k).mono (Icc_subset_Icc (by linarith) (by linarith))
      · rw [← hb]; exact ⟨by linarith [ax'.1], by linarith [ax'.2]⟩
      · approx
      · approx
    · replace k01 : k1 = k0 + 1 := by omega
      simp only [e, k01, Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_one, add_mul,
        mul_right_comm _ _ π, one_mul, (by ring : π - π / 2 = π / 2), add_sub_assoc] at an0 an1
      have u : x.lo.sin j ∪ x.hi.sin j ∪ -1 = (x.lo.sin j ∪ -1) ∪ (-1 ∪ x.hi.sin j) := by
        simp only [union_comm _ (-1), ← union_assoc, union_self]
      simp only [e, k01, self_eq_add_right, one_ne_zero, ↓reduceIte, even_two, Even.mul_right, u,
        Int.not_even_two_mul_add_one]
      by_cases s : b ≤ 2 * π * k + 3 * π / 2
      · apply approx_union_left
        apply mem_approx_of_antitone' (u := x.lo.val + π / 2 * j.val) (v := 2 * π * k + 3 * π / 2)
        · exact (Real.sin_antitone k).mono (Icc_subset_Icc (by linarith) (by linarith))
        · exact ⟨by linarith [ax'.1], by linarith⟩
        · approx
        · simp [(by ring : 3 * π / 2 = π + π / 2), ← add_assoc, Real.sin_add_pi_div_two,
            mul_comm (2 * π)]
      · apply approx_union_right
        apply mem_approx_of_monotone' (u := 2 * π * k + 3 * π / 2) (v := x.hi.val + π / 2 * j.val)
        · refine (Real.sin_monotone (k + 1)).mono (Icc_subset_Icc ?_ ?_)
          all_goals simp only [Int.cast_add, Int.cast_one]; linarith
        · exact ⟨by linarith, by linarith [ax'.2]⟩
        · simp [Real.sin_add_pi_div_two, mul_comm (2 * π), (by ring : 3 * π / 2 = π + π / 2),
            ← add_assoc]
        · approx

/-- `Interval.sincos` turns `nan` to `±1` -/
@[simp] lemma Interval.sincos_nan (d : Bool) : (nan : Interval).sincos d = pm1 := by
  rw [Interval.sincos]; simp

/-- `sin x` for potentially large `x`, via argument reduction -/
@[irreducible] def Interval.sin (x : Interval) : Interval := x.sincos false

/-- `cos x` for potentially large `x`, via argument reduction -/
@[irreducible] def Interval.cos (x : Interval) : Interval := x.sincos true

/-- `Interval.sin` is conservative -/
@[approx] lemma Interval.mem_approx_sin {x : Interval} {a : ℝ} (ax : a ∈ approx x)
    : Real.sin a ∈ approx x.sin := by
  have e : a = a + bif false then π / 2 else 0 := by simp
  rw [sin, e]
  exact mem_approx_sincos ax false

/-- `Interval.cos` is conservative -/
@[approx] lemma Interval.mem_approx_cos {x : Interval} {a : ℝ} (ax : a ∈ approx x)
    : Real.cos a ∈ approx x.cos := by
  have e : Real.cos a = Real.sin (a + bif true then π / 2 else 0) := by
    simp [Real.sin_add_pi_div_two]
  rw [cos, e]
  exact mem_approx_sincos ax true

@[simp] lemma Interval.sin_nan : (nan : Interval).sin = pm1 := by rw [Interval.sin]; simp
@[simp] lemma Interval.cos_nan : (nan : Interval).cos = pm1 := by rw [Interval.cos]; simp
