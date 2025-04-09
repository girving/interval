import Interval.EulerMaclaurin.EulerMaclaurin
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# The Stirling series for the gamma function
-/

open Filter
open MeasureTheory
open Real (Gamma log sqrt)
open Real.BohrMollerup (logGammaSeq)
open Set
open Stirling (stirlingSeq)
open scoped Real
open scoped Topology
noncomputable section

/-!
### Derivatives of `y ↦ log (x + y)`
-/

section LogAdd

variable {x y : ℝ}

lemma contDiffAt_log_add (xy : 0 < x + y) :
    ContDiffAt ℝ ⊤ (fun y ↦ log (x + y)) y :=
  (contDiffAt_const.add contDiffAt_id).log xy.ne'

lemma contDiffOn_log_add {s : WithTop ℕ∞} : ContDiffOn ℝ s (fun y ↦ log (x + y)) (Ioi (-x)) := by
  intro x m
  refine (contDiffAt_log_add ?_).contDiffWithinAt.of_le le_top
  simp only [mem_Ioi] at m
  linarith

lemma deriv_log_add (xy : 0 < x + y) : deriv (fun y ↦ log (x + y)) y = (x + y)⁻¹ := by
  suffices h : HasDerivAt (fun y ↦ log (x + y)) (1 / (x + y)) y by
    simp only [one_div] at h
    exact h.deriv
  apply ((hasDerivAt_id _).const_add _).log xy.ne'

lemma HasDerivAt.zpow {f : ℝ → ℝ} {f' : ℝ} (df : HasDerivAt f f' x) {n : ℤ}
    (g : f x ≠ 0 ∨ 0 ≤ n) : HasDerivAt (fun x ↦ (f x) ^ n) (n * (f x) ^ (n - 1) * f') x := by
  have e : (fun x ↦ (f x) ^ n) = (fun y : ℝ ↦ y ^ n) ∘ f := rfl
  rw [e]
  refine HasDerivAt.comp x ?_ df
  rwa [← deriv_zpow, hasDerivAt_deriv_iff, differentiableAt_zpow]

lemma iteratedDeriv_log_add (xy : 0 < x + y) (s : ℕ) :
    iteratedDeriv (s + 1) (fun y ↦ log (x + y)) y =
      (-1) ^ s * s.factorial * (x + y) ^ (-(s : ℤ) - 1) := by
  induction' s with s h generalizing y
  · simp [deriv_log_add xy]
  · rw [iteratedDeriv_succ]
    generalize hf : (iteratedDeriv (s + 1) fun y ↦ log (x + y)) = f at h
    apply HasDerivAt.deriv
    apply HasDerivAt.congr_of_eventuallyEq
      (f := fun y ↦ (-1) ^ s * s.factorial * (x + y) ^ (-(s : ℤ) - 1))
    · simp only [pow_succ (-1 : ℝ), Nat.factorial_succ, Nat.cast_mul, mul_assoc, Nat.cast_add,
        Nat.cast_one, neg_add, ← sub_eq_add_neg]
      apply HasDerivAt.const_mul
      simp only [← mul_assoc, mul_comm _ (s.factorial : ℝ)]
      simp only [mul_assoc]
      apply HasDerivAt.const_mul
      simp only [← mul_assoc, neg_one_mul, neg_add']
      have e : (-s - 1 : ℝ) = (-s - 1 : ℤ) := by simp
      rw [← mul_one (((-s - 1 : ℝ) * (x + y) ^ (-s - 1 - 1 : ℤ))), e]
      exact ((hasDerivAt_id _).const_add _).zpow (.inl xy.ne')
    · have p : ∀ᶠ z in 𝓝 y, 0 < x + z := by
        simp only [← neg_lt_iff_pos_add'] at xy ⊢
        exact eventually_gt_nhds xy
      filter_upwards [p]
      exact fun _ xz ↦ h xz

lemma iteratedDerivWithin_eq_iteratedDeriv {𝕜 E : Type} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (x : 𝕜) (t : Set 𝕜) (n : ℕ)
    (fc : ContDiffAt 𝕜 n f x) (u : UniqueDiffOn 𝕜 t) (m : x ∈ t) :
    iteratedDerivWithin n f t x = iteratedDeriv n f x := by
  rw [iteratedDerivWithin, iteratedDeriv, iteratedFDerivWithin_eq_iteratedFDeriv u fc m]

@[simp] lemma iteratedDerivWithin_log_add_succ (s : ℕ) (xy : 0 < x + y) :
    iteratedDerivWithin (s + 1) (fun y ↦ log (x + y)) (Ioi (-x)) y =
      (-1) ^ s * s.factorial * (x + y) ^ (-(s : ℤ) - 1) := by
  rw [iteratedDerivWithin_eq_iteratedDeriv, iteratedDeriv_log_add xy]
  · exact (contDiffAt_log_add xy).of_le le_top
  · apply uniqueDiffOn_Ioi
  · simp only [mem_Ioi]; linarith

@[simp] lemma iteratedDerivWithin_log_add_one (xy : 0 < x + y) :
    iteratedDerivWithin 1 (fun y ↦ log (x + y)) (Ioi (-x)) y = (x + y)⁻¹ := by
  simp only [iteratedDerivWithin_log_add_succ 0 xy, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one, CharP.cast_eq_zero, neg_zero, zero_sub, Int.reduceNeg, zpow_neg, zpow_one, one_mul]

end LogAdd

/-!
### Rising log factorials and `logGammaSeq`
-/

/-- `log x + log (x + 1) + ... + log (x + n)` -/
def log_rising (x : ℝ) (n : ℕ) : ℝ :=
  (2⁻¹ : ℝ) * (log x + log (x + n)) + trapezoid_sum (fun k ↦ log (x + k)) 0 n

@[simp] lemma log_rising_zero (x : ℝ) : log_rising x 0 = log x := by
  simp only [log_rising, CharP.cast_eq_zero, add_zero, trapezoid_sum_zero]
  ring

lemma log_rising_succ (x : ℝ) (n : ℕ) :
    log_rising x (n + 1) = log_rising x n + log (x + n + 1) := by
  simp only [log_rising, Nat.cast_add, Nat.cast_one, ← add_assoc, trapezoid_sum_succ, Int.cast_zero,
    zero_add, smul_eq_mul]
  ring

lemma log_rising_eq_sum (x : ℝ) (n : ℕ) :
    log_rising x n = ∑ m ∈ Finset.range (n + 1), log (x + m) := by
  induction' n with n h
  · simp
  · rw [Finset.sum_range_succ, ← h, log_rising_succ, Nat.cast_add_one, add_assoc]

lemma log_factorial_eq_log_rising (n : ℕ) : log n.factorial = log_rising 1 (n - 1) := by
  induction' n with n h
  · simp
  · induction' n with n l
    · simp
    · have e : n + 1 + 1 - 1 = n + 1 - 1 + 1 := by omega
      rw [e, log_rising_succ, Nat.factorial_succ, Nat.cast_mul, Real.log_mul, h, add_comm]
      · refine congr_arg₂ _ rfl (congr_arg _ ?_)
        simp only [add_comm, Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
      · simp only [Nat.cast_ne_zero]; omega
      · simp only [Nat.cast_ne_zero]; apply Nat.factorial_ne_zero

lemma logGammaSeq_eq_rising (x : ℝ) (n : ℕ) :
    logGammaSeq x n = x * log n + log_rising 1 (n - 1) - log_rising x n := by
  simp only [logGammaSeq, log_factorial_eq_log_rising, log_rising_eq_sum]

/-!
### Approximating `log_rising` and `gamma` via Euler-Maclaurin
-/

def term (x : ℝ) (s : ℕ) : ℝ :=
  bernoulli (s + 2) / ((s + 1) * (s + 2)) / x ^ (s + 1)

def sum (x : ℝ) (s : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (s + 1), term x m

def rem_n (x : ℝ) (n s : ℕ) : ℝ :=
  (s + 1).factorial * ∫ t in (0 : ℝ)..n, saw (s + 2) t / (x + t) ^ (s + 2)

def rem (x : ℝ) (s : ℕ) : ℝ :=
  (s + 1).factorial * ∫ t in Ioi (0 : ℝ), saw (s + 2) t / (x + t) ^ (s + 2)

def pre_n (x : ℝ) (n : ℕ) : ℝ :=
  (x + n + 2⁻¹) * log (n / (x + n))

def const_n (n s : ℕ) : ℝ :=
  1 + sum n s - sum 1 s + rem_n 1 (n - 1) s

def const (s : ℕ) : ℝ :=
  1 - sum 1 s + rem 1 s

lemma log_rising_em (x : ℝ) (n s : ℕ) (x0 : 0 < x) :
    log_rising x n = (2⁻¹ : ℝ) * (log x + log (x + n)) + (x + n) * log (x + n) - x * log x - n +
      sum (x + n) s - sum x s + rem_n x n s := by
  have xn0 : 0 < x + n := by linarith
  generalize hA : 2⁻¹ * (log x + log (x + n)) = A
  generalize hB : (x + n) * log (x + n) - x * log x = B
  have hAB : A + (x + n) * log (x + n) - x * log x = A + B := by rw [← hA, ← hB]; abel
  generalize hD : (s + 1).factorial * ∫ t in (0 : ℝ)..n, saw (s + 2) t / (x + t) ^ (s + 2) = D
  rw [log_rising, hA, trapezoid_sum_eq_integral_add (s := s + 1) (t := Ioi (-x))
      contDiffOn_log_add (uniqueDiffOn_Ioi _)]
  · simp only [Int.cast_zero, zero_add, intervalIntegral.integral_comp_add_left, add_zero,
      smul_eq_mul, ← mul_assoc, Nat.add_assoc, Nat.reduceAdd, integral_log,
      rem_n, sum, hD, hB, term]
    rw [Finset.sum_congr rfl (g := fun m : ℕ ↦ (-1) ^ m * saw (m + 2) 0 *
        ((-1) ^ m * m.factorial * (x + n) ^ (-(m : ℤ) - 1) -
         (-1) ^ m * m.factorial * (x + 0) ^ (-(m : ℤ) - 1))),
      intervalIntegral.integral_congr (g := fun t ↦
        (-1) ^ (s + 1) * (s + 1).factorial * saw (s + 2) t / (x + t) ^ (s + 2))]
    · have e : ∀ m : ℕ, ((m + 2).factorial : ℝ)⁻¹ * bernoulli (m + 2) * m.factorial =
          bernoulli (m + 2) / ((m + 1) * (m + 2)) := by
        intro m
        simp only [Nat.factorial_succ]
        field_simp
        ring
      simp only [← neg_add', Int.reduceNeg, add_zero, mul_sub, ← mul_assoc,
        mul_comm _ ((-1 : ℝ) ^ _), ← mul_pow, mul_neg, mul_one, neg_neg, one_pow, one_mul,
        mul_comm (saw (_ + 2) 0) (Nat.factorial _), mul_div_assoc, zpow_neg, zpow_natCast,
        intervalIntegral.integral_const_mul, hD, ← Nat.cast_add_one, saw_eval_zero,
        Finset.sum_sub_distrib, hB, hAB]
      simp only [e, Nat.cast_add, ← div_eq_mul_inv, Nat.cast_one]
      abel
    · intro t m
      simp only
      rw [iteratedDerivWithin_log_add_succ]
      · simp only [← neg_add', ← Nat.cast_add_one, zpow_neg, zpow_natCast]
        ring
      · simp only [Nat.cast_nonneg, uIcc_of_le, mem_Icc] at m
        linarith
    · intro m ms
      rw [iteratedDerivWithin_log_add_succ, iteratedDerivWithin_log_add_succ]
      all_goals linarith
  · simpa only [Int.cast_zero, zero_add, Nat.cast_nonneg, Icc_subset_Ioi_iff, Left.neg_neg_iff]

lemma logGammaSeq_em (x : ℝ) (n s : ℕ) (x0 : 0 < x) (n1 : 1 ≤ n) :
    logGammaSeq x n = pre_n x n + const_n n s +
    (x - 2⁻¹) * log x - sum (x + n) s + sum x s - rem_n x n s := by
  rw [logGammaSeq_eq_rising, log_rising_em _ _ s (by norm_num), log_rising_em _ _ s x0, pre_n,
    Real.log_div (by simp; omega) (by simp; linarith), const_n]
  simp [Real.log_one, Nat.cast_sub n1]
  ring

lemma tendsto_pre {x : ℝ} : Tendsto (pre_n x) atTop (𝓝 (-x)) := by
  have e : ∀ᶠ n in atTop, pre_n x n = -(n * log (1 + x / n)) - (x + 2⁻¹) * log (1 + x / n) := by
    filter_upwards [eventually_gt_atTop 0]
    intro n n0
    rw [pre_n, ← neg_neg (log _), ← Real.log_inv, inv_div, add_div, div_self (by simp; omega)]
    ring_nf
  rw [tendsto_congr' e, (by simp : -x = -x - 0)]
  have l0 : Tendsto (fun t ↦ -(t * log (1 + x / t))) atTop (𝓝 (-x)) :=
    (Real.tendsto_mul_log_one_plus_div_atTop x).neg
  have l1 : Tendsto (fun t ↦ (x + 2⁻¹) * log (1 + x / t)) atTop (𝓝 ((x + 2⁻¹) * log 1)) := by
    apply Tendsto.const_mul
    have e : (fun t ↦ log (1 + x / t)) = log ∘ (fun t ↦ 1 + x / t) := rfl
    have c : Tendsto log (𝓝 1) (𝓝 (log 1)) := Real.continuousAt_log (by norm_num)
    have i : Tendsto (fun t ↦ 1 + x / t) atTop (𝓝 (1 + x * 0)) :=
      (tendsto_inv_atTop_zero.const_mul _).const_add _
    simp only [mul_zero, add_zero] at i
    rw [e]
    refine c.comp i
  simp only [mul_zero, Real.log_one] at l1
  exact (l0.sub l1).comp tendsto_natCast_atTop_atTop

lemma tendsto_sum {x : ℝ} {s : ℕ} (x0 : 0 ≤ x) :
    Tendsto (fun n : ℕ ↦ sum (x + n) s) atTop (𝓝 0) := by
  simp only [sum, term]
  rw [(by rw [Finset.sum_const_zero] : (0 : ℝ) = ∑ m ∈ Finset.range (s + 1), 0)]
  refine tendsto_finset_sum _ fun m _ ↦ ?_
  generalize hc : (bernoulli (m + 2) : ℝ) / ((↑m + 1) * (↑m + 2)) = c
  simp only [div_eq_mul_inv]
  rw [(by simp : 0 = c * 0)]
  refine (tendsto_inv_atTop_zero.comp ?_).const_mul _
  refine (tendsto_pow_atTop (by omega)).comp ?_
  apply tendsto_atTop_add_nonneg_left
  · intro _; linarith
  · exact tendsto_natCast_atTop_atTop

lemma integrableOn_bound {c x : ℝ} {s : ℕ} (x0 : 0 < x) :
    IntegrableOn (fun t ↦ c * (x + t) ^ (-s - 2 : ℝ)) (Ioi 0) volume := by
  apply Integrable.const_mul
  refine (integrable_indicator_iff measurableSet_Ioi).mp ?_
  apply Integrable.congr (f := fun t ↦
      ((Ioi x).indicator (fun t ↦ t ^ (-s - 2 : ℝ)) ∘ (fun t ↦ x + t)) t)
  · apply Integrable.comp_add_left (f := (Ioi x).indicator (fun t ↦ t ^ (-s - 2 : ℝ))) (g := x)
    · rw [integrable_indicator_iff measurableSet_Ioi, integrableOn_Ioi_rpow_iff x0]
      linarith
  · filter_upwards []
    intro y
    simp only [Function.comp_apply, indicator, mem_Ioi, lt_add_iff_pos_right]

lemma integrableOn_bound' {c x : ℝ} {s : ℕ} (x0 : 0 < x) :
    IntegrableOn (fun t ↦ c / (x + t) ^ (s + 2)) (Ioi 0) volume := by
  apply (integrableOn_bound (c := c) (s := s) x0).congr
  simp only [ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ioi]
  filter_upwards []
  intro y
  simp only [indicator, mem_Ioi]
  split_ifs with y0
  · rw [← Real.rpow_natCast, div_eq_mul_inv, ← Real.rpow_neg, Nat.cast_add]
    · ring_nf
    · linarith
  · rfl

lemma tendsto_rem {x : ℝ} {s : ℕ} (x0 : 0 < x) :
    Tendsto (fun n ↦ rem_n x n s) atTop (𝓝 (rem x s)) := by
  set f : ℝ → ℝ := fun t ↦ saw (s + 2) t / (x + t) ^ (s + 2)
  have hf : ∀ t, saw (s + 2) t / (x + t) ^ (s + 2) = f t := by intro; rfl
  have le : ∀ {n : ℕ}, (0 : ℝ) ≤ n := by intro n; simp only [Nat.cast_nonneg]
  simp only [rem_n, rem, intervalIntegral.integral_of_le le, hf,
    ← integral_indicator measurableSet_Ioc,
    ← integral_indicator measurableSet_Ioi]
  apply Tendsto.const_mul
  set bound := (Ioi 0).indicator (fun t ↦ sawBound (s + 2) / (x + t) ^ (s + 2))
  apply tendsto_integral_of_dominated_convergence (bound := bound)
  · intro n
    refine AEStronglyMeasurable.indicator ?_ measurableSet_Ioc
    simp only [f]
    have e : (univ : Set ℝ) = {-x} ∪ {-x}ᶜ := (union_compl_self _).symm
    rw [← Measure.restrict_univ (μ := volume), e,
      aestronglyMeasurable_union_iff]
    constructor
    · simp only [Measure.restrict_singleton, measure_singleton, zero_smul,
        aestronglyMeasurable_zero_measure]
    · refine ContinuousOn.aestronglyMeasurable ?_ ?_
      · apply ContinuousOn.div
        · exact continuous_saw.continuousOn
        · exact Continuous.continuousOn (by continuity)
        · intro y m
          contrapose m
          simp only [ne_eq, add_eq_zero, OfNat.ofNat_ne_zero, and_false,
            not_false_eq_true, pow_eq_zero_iff, not_not, mem_compl_iff, mem_singleton_iff] at m ⊢
          linarith
      · simp only [MeasurableSet.compl_iff, MeasurableSet.singleton]
  · simp only [bound, integrable_indicator_iff measurableSet_Ioi]
    apply integrableOn_bound' x0
  · intro n
    filter_upwards []
    intro y
    simp only [indicator, bound, mem_Ioc]
    by_cases y0 : y ≤ 0
    · simp only [not_lt.mpr y0, false_and, ↓reduceIte, norm_zero, mem_Ioi, le_refl]
    · simp only [not_le.mp y0, true_and, Real.norm_eq_abs, y0, ↓reduceIte]
      have xy0 : 0 < x + y := by linarith
      by_cases yn : y ≤ n
      · simp only [yn, ↓reduceIte, abs_div, abs_pow, abs_of_pos xy0, f, mem_Ioi, not_le.mp y0]
        exact div_le_div_of_nonneg_right (abs_saw_le _ _) (by positivity)
      · simp only [yn, ↓reduceIte, abs_zero, ge_iff_le]
        bound
  · filter_upwards []
    intro y
    apply EventuallyEq.tendsto
    filter_upwards [eventually_gt_atTop ⌈y⌉₊]
    intro n yn
    simp only [indicator, mem_Ioc, mem_Ioi]
    by_cases y0 : 0 < y
    · simp only [y0, true_and, ↓reduceIte, ite_eq_left_iff, not_le]
      intro ny
      rw [← Nat.cast_lt (α := ℝ)] at yn
      have nn := lt_trans ny (lt_of_le_of_lt (Nat.le_ceil _) yn)
      simp only [lt_self_iff_false] at nn
    · simp only [y0, false_and, ↓reduceIte]

lemma tendsto_const {s : ℕ} : Tendsto (fun n ↦ const_n n s) atTop (𝓝 (const s)) := by
  have e : 1 - sum 1 s + rem 1 s = 1 + 0 - sum 1 s + rem 1 s := by abel
  simp only [const_n, const, e]
  refine Tendsto.add (Tendsto.sub (tendsto_const_nhds.add ?_) tendsto_const_nhds) ?_
  · convert tendsto_sum (le_refl (0 : ℝ))
    abel
  · rw [← Filter.tendsto_add_atTop_iff_nat (f := fun n ↦ rem_n 1 (n - 1) s) 1]
    simp only [add_tsub_cancel_right]
    exact tendsto_rem (by norm_num)

lemma log_gamma_em (x : ℝ) (s : ℕ) (x0 : 0 < x) :
    log (Gamma x) = (x - 2⁻¹) * log x - x + const s + sum x s - rem x s := by
  have t0 := (Real.BohrMollerup.tendsto_log_gamma x0).comp (tendsto_add_atTop_nat 1)
  suffices t1 : Tendsto (fun n ↦ logGammaSeq x (n + 1)) atTop
      (𝓝 ((x - 2⁻¹) * log x - x + const s + sum x s - rem x s)) by
    exact tendsto_nhds_unique t0 t1
  have e : ∀ n, logGammaSeq x (n + 1) = pre_n x (n + 1) + const_n (n + 1) s +
      (x - 2⁻¹) * log x - sum (x + (n + 1 : ℕ)) s + sum x s - rem_n x (n + 1) s :=
    fun n ↦ logGammaSeq_em _ _ _ x0 (by omega)
  have r : (x - 2⁻¹) * log x - x + const s + sum x s - rem x s =
      -x + const s + (x - 2⁻¹) * log x - 0 + sum x s - rem x s := by abel
  simp only [e, r]
  clear e r t0
  rw [Filter.tendsto_add_atTop_iff_nat (f := fun n ↦ pre_n x n + const_n n s + (x - 2⁻¹) * log x -
    sum (x + n) s + sum x s - rem_n x n s) 1]
  exact ((((tendsto_pre.add tendsto_const).add tendsto_const_nhds).sub (tendsto_sum x0.le)).add
    tendsto_const_nhds).sub (tendsto_rem x0)

/-!
### Delegate the constant to Stirling's formula
-/

lemma MeasureTheory.norm_set_integral_le_set_integral_norm {α G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {m : MeasurableSpace α} {μ : Measure α}
    (f : α → G) (s : Set α) : ‖∫ a in s, f a ∂μ‖ ≤ ∫ a in s, ‖f a‖ ∂μ := by
  apply norm_integral_le_integral_norm

lemma MeasureTheory.norm_set_integral_le_of_norm_le {α G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {m : MeasurableSpace α} {μ : Measure α}
    {f : α → G} {g : α → ℝ} {s : Set α} (hg : IntegrableOn g s μ)
    (h : ∀ᵐ x ∂(μ.restrict s), ‖f x‖ ≤ g x) :
    ‖∫ x in s, f x ∂μ‖ ≤ ∫ x in s, g x ∂μ :=
  norm_integral_le_of_norm_le hg h

lemma tendsto_sum_atTop {s : ℕ} : Tendsto (fun x ↦ sum x s) atTop (𝓝 0) := by
  simp only [sum]
  rw [(by rw [Finset.sum_const_zero] : (0 : ℝ) = ∑ m ∈ Finset.range (s + 1), 0)]
  refine tendsto_finset_sum _ fun m _ ↦ ?_
  apply Filter.Tendsto.const_div_atTop
  exact tendsto_pow_atTop (by omega)

lemma integral_bound {c x a : ℝ} (x0 : 0 < x) (a1 : a < -1) :
    ∫ t in Ioi 0, c * (x + t) ^ a = c * (x ^ (a + 1) / (-a - 1)) := by
  simp only [MeasureTheory.integral_mul_left, mul_div_assoc]
  refine congr_arg₂ _ rfl ?_
  simp only [← integral_indicator measurableSet_Ioi]
  rw [← MeasureTheory.integral_add_left_eq_self _ (-x)]
  simp only [indicator, mem_Ioi, lt_neg_add_iff_add_lt, add_zero, add_neg_cancel_left]
  refine Eq.trans ?_ (Eq.trans (integral_Ioi_rpow_of_lt (c := x) a1 x0) ?_)
  · simp only [← integral_indicator measurableSet_Ioi, indicator, mem_Ioi]
  · simp only [(by ring : -a - 1 = -(a + 1)), neg_div, div_neg]

lemma tendsto_rem_atTop {s : ℕ} : Tendsto (fun x ↦ rem x s) atTop (𝓝 0) := by
  simp only [rem]
  nth_rw 2 [← mul_zero ((s + 1).factorial : ℝ)]
  apply Tendsto.const_mul
  have bound : ∀ x, 0 < x → abs (∫ t in Ioi 0, saw (s + 2) t / (x + t) ^ (s + 2)) ≤
      sawBound (s + 2) * x ^ (-s - 1 : ℝ) / (s + 1) := by
    intro x x0
    simp only [← Real.norm_eq_abs]
    refine le_trans (norm_set_integral_le_of_norm_le
        (g := fun t ↦ sawBound (s + 2) * (x + t) ^ (-s - 2 : ℝ)) ?_ ?_) ?_
    · exact integrableOn_bound x0
    · simp only [ae_restrict_iff' measurableSet_Ioi, mem_Ioi]
      filter_upwards []
      intro t t0
      have xy0 : 0 < x + t := by linarith
      simp only [div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_neg xy0.le, Nat.cast_add,
        Nat.cast_ofNat, neg_add', norm_mul, Real.norm_eq_abs, Real.abs_rpow_of_nonneg xy0.le,
        abs_of_pos xy0]
      bound
    · exact le_of_eq ((integral_bound x0 (by linarith)).trans (by ring_nf))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := 0) (h := fun x ↦
      sawBound (s + 2) * x ^ (-s - 1 : ℝ) / (s + 1))
  · exact tendsto_const_nhds
  · clear bound
    simp only [div_eq_inv_mul, ← mul_assoc]
    generalize (s + 1 : ℝ)⁻¹ * sawBound (s + 2) = c
    rw [← mul_zero c]
    apply Tendsto.const_mul
    simp only [(by ring : (-s - 1 : ℝ) = -(s + 1))]
    exact tendsto_rpow_neg_atTop (by linarith)
  · simp
  · filter_upwards [eventually_gt_atTop 0]
    apply bound

lemma tendsto_log_gamma_stirling :
    Tendsto (fun n : ℕ ↦ log (Gamma n) - (n - 2⁻¹) * log n + n) atTop (𝓝 (log (2 * π) / 2)) := by
  have s0 : ∀ᶠ n in atTop,
      log (stirlingSeq n) = log (Gamma n) - (n - 2⁻¹) * log n + n - 2⁻¹ * log 2 := by
    filter_upwards [eventually_gt_atTop 0]
    intro n n0
    rw [stirlingSeq, Real.log_div, Real.log_mul, Real.log_sqrt, Real.log_pow, Real.log_div,
      ← Real.Gamma_nat_eq_factorial, Real.Gamma_add_one, Real.log_mul, Real.log_exp, Real.log_mul]
    ring
    all_goals positivity
  have s1 : ∀ᶠ n : ℕ in atTop,
      log (Gamma n) - (n - 2⁻¹) * log n + n = log (stirlingSeq n) + log 2 / 2 := by
    filter_upwards [s0]
    intro n e
    rw [e]
    ring
  rw [tendsto_congr' s1, mul_comm _ π, Real.log_mul (by positivity) (by norm_num), add_div,
    ← Real.log_sqrt Real.pi_nonneg]
  have c : ContinuousAt log √π := Real.continuousAt_log (by positivity)
  exact (c.tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi).add tendsto_const_nhds

lemma const_eq (s : ℕ) : const s = log (2 * π) / 2 := by
  generalize hc : log (2 * π) / 2 = c
  suffices t : Tendsto (fun n : ℕ ↦ const s) atTop (𝓝 c) by
    exact tendsto_nhds_unique tendsto_const_nhds t
  have e0 : (fun n : ℕ ↦ const s) =ᶠ[atTop]
      fun n ↦ log (Gamma n) - (n - 2⁻¹) * log n + n - sum n s + rem n s := by
    filter_upwards [eventually_gt_atTop 0]
    intro x x0
    rw [log_gamma_em _ s (Nat.cast_pos.mpr x0)]
    abel
  have e1 : c = c - 0 + 0 := by abel
  rw [tendsto_congr' e0, e1, ← hc]
  exact (tendsto_log_gamma_stirling.sub (tendsto_sum_atTop.comp tendsto_natCast_atTop_atTop)).add
    (tendsto_rem_atTop.comp tendsto_natCast_atTop_atTop)

/-!
### Sum needs only even powers
-/

lemma Finset.sum_range_even_odd {α : Type*} [AddCommMonoid α] {f : ℕ → α} {n : ℕ} :
    ∑ k ∈ Finset.range n, f k = (∑ k ∈ Finset.range ((n + 1) / 2), f (2 * k)) +
      (∑ k ∈ Finset.range (n / 2), f (2 * k + 1)) := by
  induction' n with n h
  · simp only [range_zero, sum_empty, Nat.zero_div, zero_add, Nat.reduceDiv, add_zero]
  · simp only [sum_range_succ, h]
    by_cases p : n % 2 = 0
    · rw [(by omega : (n + 1) / 2 = n / 2), (by omega : (n + 1 + 1) / 2 = n / 2 + 1),
        Finset.sum_range_succ, (by omega : 2 * (n / 2) = n)]
      abel
    · rw [(by omega : (n + 1 + 1) / 2 = (n + 1) / 2), (by omega : (n + 1) / 2 = n / 2 + 1),
        add_assoc]
      apply congr_arg₂ _ rfl
      rw [Finset.sum_range_succ, (by omega : 2 * (n / 2) + 1 = n)]

lemma sum_eq_even (x : ℝ) (s : ℕ) : sum x (2 * s) = ∑ m ∈ Finset.range (s + 1), term x (2 * m) := by
  have o : ∀ s, bernoulli (2 * s + 1 + 2) = 0 := by
    intro s
    rw [bernoulli, bernoulli'_odd_eq_zero, mul_zero]
    · simp only [Nat.odd_iff]
      omega
    · omega
  simp only [sum, Finset.sum_range_even_odd (n := 2 * s + 1), add_assoc, Nat.reduceAdd,
    Nat.ofNat_pos, Nat.add_div_right, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    mul_div_cancel_left₀, Nat.cast_mul, Nat.cast_ofNat, o, Rat.cast_zero, Nat.cast_add,
    Nat.cast_one, zero_div, Finset.sum_const_zero, add_zero, term]

/-!
### Bounding the remainder
-/

/-- Not sure if this is tight -/
lemma abs_rem_le (x : ℝ) (s : ℕ) (e : Even s) (x0 : 0 < x) :
    |rem x s| ≤ |bernoulli (s + 2)| / (s + 1) / (s + 2) / x ^ (s + 1) := by
  simp only [rem, Nat.cast_mul, Nat.cast_add_one, Rat.cast_abs, abs_mul, ← Real.norm_eq_abs]
  have le : ∀ᵐ t ∂volume.restrict (Ioi 0), ‖saw (s + 2) t / (x + t) ^ (s + 2)‖ ≤
      ((s + 2).factorial : ℝ)⁻¹ * |bernoulli (s + 2)| * (x + t) ^ (-s - 2 : ℝ) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards []
    intro t m
    simp only [mem_Ioi] at m
    have p : 0 < x + t := by linarith
    simp only [← Real.rpow_natCast, Nat.cast_add, Nat.cast_ofNat, div_eq_mul_inv, ←
      Real.rpow_neg p.le, neg_add', norm_mul, Real.norm_eq_abs, Rat.cast_abs]
    rw [abs_of_pos (a := _ ^ (_ : ℝ)) (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine le_trans (abs_saw_le _ _) (le_of_eq ?_)
    rw [sawBound, bernoulliBound_eq_abs_bernoulli', Rat.cast_abs]
    simp only [Nat.even_iff] at e ⊢
    omega
  refine le_trans (mul_le_mul_of_nonneg_left (MeasureTheory.norm_integral_le_of_norm_le ?_ le)
    (by positivity)) (le_of_eq ?_)
  · exact integrableOn_bound x0
  · clear le
    rw [integral_bound x0 (by linarith)]
    simp only [Real.norm_natCast, Nat.factorial_succ (s + 1), Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, mul_inv_rev, Rat.cast_abs, neg_sub, sub_neg_eq_add, ← mul_assoc,
      Rat.norm_cast_real]
    rw [mul_inv_cancel₀ (by positivity)]
    ring_nf
    rw [Real.rpow_sub x0, Real.rpow_neg x0.le, Real.rpow_one, Real.rpow_natCast,
      ← Rat.norm_cast_real, Real.norm_eq_abs]
    ring_nf

/-- Not sure if this is tight -/
lemma abs_rem_le' (x : ℝ) (s : ℕ) (e : Even s) (x0 : 0 < x) : |rem x s| ≤ |term x s| := by
  refine le_trans (abs_rem_le x s e x0) (le_of_eq ?_)
  simp only [Rat.cast_abs, term, div_mul_eq_div_div, abs_div, abs_pow, abs_of_pos x0]
  repeat rw [abs_of_pos (a := _ + _) (by linarith)]

/-!
### The main result, stated succinctly
-/

/-- Each term in the Stirling series -/
lemma term_eq (x : ℝ) (s : ℕ) : term x s = bernoulli (s + 2) / ((s + 1) * (s + 2)) / x ^ (s + 1) :=
  rfl

/-- Effective Stirling series for `log Gamma`, but with a non-tight remainder bound -/
lemma abs_log_gamma_sub_le (x : ℝ) (x0 : 0 < x) (s : ℕ) :
    |log (Gamma x) - ((x - 2⁻¹) * log x - x + log (2 * π) / 2 +
      ∑ m ∈ Finset.range (s + 1), term x (2 * m))| ≤ |term x (2 * s)| := by
  rw [log_gamma_em x (2 * s) x0, ← sum_eq_even, const_eq]
  ring_nf
  simp only [abs_neg]
  exact abs_rem_le' _ _ (by simp) x0
