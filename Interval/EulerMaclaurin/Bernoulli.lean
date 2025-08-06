import Interval.EulerMaclaurin.DerivUnderIntegral
import Interval.EulerMaclaurin.IteratedDerivArith
import Interval.EulerMaclaurin.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.ZetaValues

/-!
# Bernoulli polynomials

Mathlib has a lot of this, so possibly I should shift to using those results in future.
See `periodizedBernoulli` in particular.
-/

open Classical
open Filter
open Set
open Complex (I)
open Function (uncurry)
open MeasureTheory (volume)
open scoped Real
open scoped Topology
open intervalIntegral
noncomputable section

/-!
### The Bernoulli polynomials
-/

variable {s : ℕ}

/-- Polynomials are smooth -/
lemma contDiff_polynomial (f : Polynomial ℚ) : ContDiff ℝ ⊤ (fun x : ℝ ↦ f.aeval x) := by
  induction' f using Polynomial.induction_on' with f g fc gc n a
  · simp only [map_add]
    exact fc.add gc
  · simp only [Polynomial.aeval_monomial, eq_ratCast]
    exact contDiff_const.mul (contDiff_id.pow _)

lemma contDiff_bernoulliFun : ContDiff ℝ ⊤ (bernoulliFun s) := by
  have e : bernoulliFun s = fun x ↦ bernoulliFun s x := rfl
  rw [e]
  simp only [bernoulliFun]
  simp only [Polynomial.eval_map_algebraMap]
  apply contDiff_polynomial

@[continuity] lemma continuous_bernoulliFun : Continuous (bernoulliFun s) :=
  contDiff_bernoulliFun.continuous

@[simp] lemma bernoulliFun_zero {x : ℝ} : bernoulliFun 0 x = 1 := by
  simp only [bernoulliFun, Polynomial.bernoulli_zero, Polynomial.map_one, Polynomial.eval_one]

@[simp] lemma deriv_bernoulliFun :
    deriv (bernoulliFun s) = fun x ↦ s * bernoulliFun (s - 1) x := by
  ext x
  exact (hasDerivAt_bernoulliFun _ _).deriv

/-- Bernoulli polys have mean `n = 0` -/
lemma mean_bernoulliFun (s : ℕ) :
    ∫ x in (0 : ℝ)..1, bernoulliFun s x = if s = 0 then 1 else 0 := by
  induction' s with s _
  · simp only [bernoulliFun_zero, integral_const, sub_zero, smul_eq_mul, mul_one, ↓reduceIte]
  · apply integral_bernoulliFun_eq_zero
    omega

@[simp] lemma bernoulliFun_one {x : ℝ} : bernoulliFun 1 x = x - 1 / 2 := by
  simp [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ]
  ring

@[simp] lemma bernoulli_two : bernoulli 2 = 6⁻¹ := by
  simp [bernoulli]

@[simp] lemma bernoulliFun_two {x : ℝ} : bernoulliFun 2 x = x ^ 2 - x + 6⁻¹ := by
  simp [bernoulliFun, Polynomial.bernoulli_def, Finset.sum_range_succ]
  ring

/-!
### Integrability tactic
-/

/-- Show interval integrability via continuity -/
macro "integrable" : tactic =>
  `(tactic|
    · intros
      apply Continuous.intervalIntegrable
      continuity)

/-!
### Reflection principle: `B_s(1 - x) = (-)^s B_s(x)`
-/

/-- Fundamental theorem of calculus to express a Bernoulli polynomial via the previous one -/
lemma bernoulliFun_eq_integral (s : ℕ) (x y : ℝ) :
    bernoulliFun (s + 1) y =
      bernoulliFun (s + 1) x + ∫ t in x..y, (s + 1 : ℕ) * bernoulliFun (s + 1 - 1) t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := bernoulliFun (s + 1))]
  · abel
  · intro y _
    apply hasDerivAt_bernoulliFun
  · integrable

lemma bernoulliFun_eval_one_sub {s : ℕ} {x : ℝ} :
    bernoulliFun s (1 - x) = (-1) ^ s * bernoulliFun s x := by
  induction' s with s h generalizing x
  · simp only [bernoulliFun_zero, pow_zero, mul_one]
  · simp only [bernoulliFun_eq_integral _ 1 (1 - x), bernoulliFun_eval_one, bernoulliFun_eval_zero,
      add_eq_right, Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, integral_const_mul,
      bernoulliFun_eq_integral _ 0 x]
    by_cases s0 : s = 0
    · simp [s0]
      ring
    · have ev : (-1) ^ (s + 1) * (bernoulli (s + 1) : ℝ) = bernoulli (s + 1) := by
        cases' (s + 1).even_or_odd with e o
        · simp only [e, Even.neg_pow, one_pow, one_mul]
        · rw [bernoulli, bernoulli'_odd_eq_zero o (by omega)]
          simp only [mul_zero, Rat.cast_zero]
      simp only [s0, ↓reduceIte, add_zero, mul_add, ev, add_right_inj]
      rw [← mul_assoc, mul_comm _ (s + 1 : ℝ), mul_assoc]
      apply congr_arg₂ _ rfl
      nth_rw 1 [← sub_zero 1]
      rw [← intervalIntegral.integral_comp_sub_left, intervalIntegral.integral_symm]
      simp only [h, integral_const_mul, pow_succ, mul_neg, mul_one, neg_mul]

@[simp] lemma bernoulli_odd_eq_zero {s : ℕ} (s0 : s ≠ 0) : bernoulli (2 * s + 1) = 0 := by
  rw [bernoulli, bernoulli'_odd_eq_zero]
  all_goals simp; try omega

/-- The values at 0 and 1 match for `2 ≤ s` -/
lemma bernoulliPoly_one_eq_zero (s : ℕ) : bernoulliFun (s + 2) 1 = bernoulliFun (s + 2) 0 := by
  simp only [bernoulliFun_eval_one, bernoulliFun_eval_zero, Nat.reduceEqDiff, ↓reduceIte, add_zero]

/-!
### Multiplication theorem
-/

lemma hasDerivAt_const_mul {𝕜 : Type*} [NontriviallyNormedField 𝕜] {x : 𝕜} (c : 𝕜) :
    HasDerivAt (fun x ↦ c * x) c x := by
  simp only [mul_comm c, hasDerivAt_mul_const c]

lemma integrable_bernoulliFun {s : ℕ} {a b : ℝ} :
    IntervalIntegrable (bernoulliFun s) volume a b := by
  apply contDiff_bernoulliFun.continuous.intervalIntegrable

lemma integrable_bernoulliFun_comp_add_right {s : ℕ} {a b c : ℝ} :
    IntervalIntegrable (fun x ↦ bernoulliFun s (x + c)) volume a b := by
  apply Continuous.intervalIntegrable
  continuity

/-- The multiplication theorem. Proof follows https://math.stackexchange.com/a/1721099/38218. -/
lemma bernoulliFun_mul (s m : ℕ) (m0 : m ≠ 0) (x : ℝ) :
    bernoulliFun s (m * x) =
      m ^ s / m * ∑ k ∈ Finset.range m, bernoulliFun s (x + k / m) := by
  have m0' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m0
  set f := fun s x ↦ bernoulliFun s (m * x) -
    m ^ s / m * ∑ k ∈ Finset.range m, bernoulliFun s (x + k / ↑m)
  suffices h : ∀ x, f s x = 0 by
    rw [← sub_eq_zero]
    exact h x
  induction' s with s h
  · intro x
    simp only [f, bernoulliFun_zero, pow_zero, one_div, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, sub_eq_zero]
    rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr m0)]
  · have d : ∀ x, HasDerivAt (fun x ↦ f (s + 1) x) (m * (s + 1) * f s x) x := by
      intro x
      simp only [f, mul_sub, Finset.mul_sum, pow_succ, mul_div_cancel_right₀ _ m0',
        ← mul_assoc, mul_comm _ (_ / _), div_mul_cancel₀ _ m0']
      apply HasDerivAt.sub
      · rw [mul_assoc, mul_comm (m : ℝ) _, ← Nat.cast_add_one]
        apply (hasDerivAt_bernoulliFun _ _).comp
        apply hasDerivAt_const_mul
      · refine HasDerivAt.fun_sum fun k _ ↦ ?_
        simp only [mul_assoc, ← Nat.cast_add_one]
        apply HasDerivAt.const_mul
        rw [← mul_one (_ * _)]
        apply (hasDerivAt_bernoulliFun _ _).comp
        exact (hasDerivAt_id _).add_const _
    simp only [h, mul_zero] at d
    have fc : ∀ x y, f (s + 1) x = f (s + 1) y :=
      is_const_of_deriv_eq_zero (fun _ ↦ (d _).differentiableAt) (fun _ ↦ (d _).deriv)
    replace fc := fun x ↦ fc x 0
    generalize f (s + 1) 0 = c at fc
    have i : ∫ x in (0 : ℝ)..m⁻¹, f (s + 1) x = 0 := by
      simp only [f]
      rw [intervalIntegral.integral_sub, intervalIntegral.integral_comp_mul_left _ m0', mul_zero,
        mul_inv_cancel₀ m0', integral_bernoulliFun_eq_zero (by omega), smul_zero, sub_eq_zero,
        intervalIntegral.integral_const_mul, eq_comm (a := 0), mul_eq_zero]
      · right
        rw [intervalIntegral.integral_finset_sum]
        · simp only [intervalIntegral.integral_comp_add_right, zero_add, ← one_div, ← add_div,
            add_comm (1 : ℝ), ← Nat.cast_add_one]
          rw [intervalIntegral.sum_integral_adjacent_intervals]
          · simp [div_self m0', integral_bernoulliFun_eq_zero]
          · integrable
        · integrable
      · integrable
      · integrable
    simp only [fc, integral_const, sub_zero, smul_eq_mul, mul_eq_zero, inv_eq_zero,
      Nat.cast_eq_zero, m0, false_or] at i
    simpa only [i] using fc

/-!
### Values at 1/2
-/

lemma bernoulliFun_eval_half_eq_zero {s : ℕ} : bernoulliFun (2 * s + 1) 2⁻¹ = 0 := by
  have h := bernoulliFun_eval_one_sub (s := 2 * s + 1) (x := 2⁻¹)
  simp only [pow_succ, even_two, Even.mul_right, Even.neg_pow, one_pow, mul_neg, mul_one, neg_mul,
    one_mul] at h
  linarith

lemma bernoulliFun_eval_half (s : ℕ) : bernoulliFun s 2⁻¹ = (2 / 2 ^ s - 1) * bernoulli s := by
  by_cases s1 : s = 1
  · simp [s1]
  · have m := bernoulliFun_mul s 2 (by omega) 2⁻¹
    norm_num [Finset.sum_range_succ, bernoulliFun_eval_one, s1, bernoulliFun_eval_zero] at m
    rw [← inv_mul_eq_iff_eq_mul₀ (by positivity), ← sub_eq_iff_eq_add, ← sub_one_mul, inv_div] at m
    rw [m, one_div]

/-!
### The presaw functions

These are `saw s x` smoothly extended from a particular `[a,a+1)` interval.
-/

variable {a : ℤ}

/-- The saw functions are scaled, shifted versions of the Bernoulli polynomials -/
def presaw (s : ℕ) (a : ℤ) (x : ℝ) : ℝ :=
  (s.factorial : ℝ)⁻¹ • bernoulliFun s (x - a)

/-- `presaw` is smooth -/
lemma contDiff_presaw : ContDiff ℝ ⊤ (presaw s a) := by
  exact (contDiff_bernoulliFun.comp (contDiff_id.sub contDiff_const)).const_smul _

@[simp] lemma presaw_start {x : ℝ} : presaw 0 a x = 1 := by simp [presaw]

lemma hasDerivAt_presaw {x : ℝ} : HasDerivAt (presaw (s + 1) a) (presaw s a x) x := by
  have e : presaw (s + 1) a = (fun x ↦ presaw (s + 1) a x) := rfl
  simp only [presaw, Nat.factorial_succ, mul_comm _ s.factorial, Nat.cast_mul,
    mul_inv, ← smul_smul, e]
  apply HasDerivAt.fun_const_smul
  have s0 : ((s + 1 : ℕ) : ℝ) ≠ 0 := by simp only [Nat.cast_ne_zero]; omega
  have sc : s = s + 1 - 1 := by omega
  rw [← inv_smul_smul₀ s0 (x := (bernoulliFun s (x - ↑a)))]
  nth_rw 5 [sc]
  apply HasDerivAt.fun_const_smul
  rw [Nat.cast_smul_eq_nsmul]
  rw [← mul_one (((s + 1) • bernoulliFun (s + 1 - 1) (x - ↑a)))]
  simp only [nsmul_eq_mul]
  exact HasDerivAt.comp _ (hasDerivAt_bernoulliFun (s + 1) _) (h := fun x : ℝ ↦ x - a)
    ((hasDerivAt_id' x).sub_const _)

@[simp] lemma deriv_presaw {x : ℝ} : deriv (presaw (s + 1) a) x = presaw s a x := by
  rw [hasDerivAt_presaw.deriv]

@[simp] lemma presaw_zero {x : ℝ} : presaw 0 a x = 1 := by
  simp only [presaw, Nat.factorial_zero, Nat.cast_one, inv_one, bernoulliFun_zero, smul_eq_mul,
    mul_one]

/-!
### The saw functions
-/

/-- The saw functions are scaled, periodic versions of the Bernoulli polynomials -/
def saw (s : ℕ) (x : ℝ) :=
  (s.factorial : ℝ)⁻¹ • bernoulliFun s (Int.fract x)

/-- Saw is nice on `[a,a+1)` -/
lemma saw_eqOn {a : ℤ} :
    EqOn (saw s) (presaw s a) (Ico a (a+1)) := by
  intro x m
  simp only [mem_Ico, ← Int.floor_eq_iff] at m
  simp only [saw, presaw, smul_eq_mul, Int.fract, m]

/-- `presaw` at integer values in terms of `saw` -/
@[simp] lemma presaw_coe_same {a : ℤ} : presaw s a a = saw s 0 := by
  rw [← saw_eqOn (a := a)]
  all_goals simp [saw]

/-- `presaw` at integer values in terms of `saw` -/
@[simp] lemma presaw_coe_succ {a : ℤ} : presaw (s + 2) a (a + 1) = saw (s + 2) 0 := by
  simp only [presaw, add_sub_cancel_left, bernoulliPoly_one_eq_zero, smul_eq_mul, saw,
    Int.fract_zero]

/-- `presaw` at integer values in terms of `saw` -/
@[simp] lemma presaw_one_coe_succ {a : ℤ} : presaw 1 a (a + 1) = 1 / 2 := by
  simp only [presaw, Nat.factorial_one, Nat.cast_one, inv_one, add_sub_cancel_left,
    bernoulliFun_one, one_div, smul_eq_mul, one_mul]
  norm_num

/-- Saw is nice on `[a,a+1)` -/
lemma contDiff_saw : ContDiffOn ℝ ⊤ (saw s) (Ico a (a+1)) := by
  rw [contDiffOn_congr saw_eqOn]
  exact contDiff_presaw.contDiffOn

@[simp] lemma saw_zero {x : ℝ} : saw 0 x = 1 := by
  simp only [saw, Nat.factorial_zero, Nat.cast_one, inv_one, bernoulliFun_zero, smul_eq_mul,
    mul_one]

@[simp] lemma saw_int {x : ℤ} : saw s x = saw s 0 := by
  simp only [saw, Int.fract_intCast, smul_eq_mul, Int.fract_zero]

lemma hasDerivAt_saw {s : ℕ} {a : ℤ} {x : ℝ} (m : x ∈ Ioo (a : ℝ) (a + 1)) :
    HasDerivAt (saw (s + 1)) (saw s x) x := by
  have e : saw (s + 1) =ᶠ[𝓝 x] (fun x ↦ presaw (s + 1) a x) := by
    apply saw_eqOn.eventuallyEq_of_mem
    exact Ico_mem_nhds_iff.mpr m
  refine HasDerivAt.congr_of_eventuallyEq ?_ e
  simp only [saw_eqOn (mem_Ico_of_Ioo m)]
  exact hasDerivAt_presaw

@[simp] lemma deriv_saw {x : ℝ} (m : x ∈ Ioo (a : ℝ) (a + 1)) :
    deriv (saw (s + 1)) x = saw s x := by
  rw [(hasDerivAt_saw m).deriv]

/-- `saw 1` is a saw-tooth function -/
lemma saw_one {x : ℝ} : saw 1 x = Int.fract x - 1 / 2 := by
  simp only [saw, Nat.factorial_one, Nat.cast_one, inv_one, bernoulliFun_one, one_div, smul_eq_mul,
    one_mul]

@[simp] lemma saw_one_zero : saw 1 0 = -2⁻¹ := by
  simp only [saw_one, Int.fract_zero, one_div, zero_sub]

/-- `saw` is continuous for `2 ≤ s` -/
lemma continuous_saw : Continuous (saw (s + 2)) := by
  rw [continuous_iff_continuousAt]
  intro x
  set a := ⌊x⌋
  by_cases xa : x = a
  · simp only [xa, continuousAt_iff_continuous_left'_right']
    constructor
    · apply ContinuousWithinAt.congr_of_eventuallyEq (f := presaw (s + 2) (a - 1))
      · exact contDiff_presaw.continuous.continuousWithinAt
      · apply saw_eqOn.eventuallyEq_of_mem
        apply Ico_mem_nhdsLT_of_mem
        simp only [Int.cast_sub, Int.cast_one, sub_add_cancel, mem_Ioc, sub_lt_self_iff,
          zero_lt_one, le_refl, and_self]
      · nth_rw 2 [← sub_add_cancel (a : ℝ) 1]
        rw [saw_int, ← Int.cast_one (R := ℝ), ← Int.cast_sub, Int.cast_one, presaw_coe_succ]
    · apply ContinuousWithinAt.congr_of_eventuallyEq (f := presaw (s + 2) a)
      · exact contDiff_presaw.continuous.continuousWithinAt
      · apply saw_eqOn.eventuallyEq_of_mem
        apply Ico_mem_nhdsGT_of_mem
        simp only [mem_Ico, le_refl, lt_add_iff_pos_right, zero_lt_one, and_self]
      · simp only [saw_int, presaw_coe_same]
  · apply ContinuousAt.congr_of_eventuallyEq (f := presaw (s + 2) a)
    · exact contDiff_presaw.continuous.continuousAt
    · apply saw_eqOn.eventuallyEq_of_mem
      apply Ico_mem_nhds
      · exact (Ne.symm xa).lt_of_le (Int.floor_le x)
      · simp only [Int.lt_floor_add_one, a]

/-!
### Saw values at 0
-/

lemma saw_eval_zero : saw s 0 = (s.factorial : ℝ)⁻¹ * bernoulli s := by
  simp only [saw, Int.fract_zero, bernoulliFun_eval_zero, smul_eq_mul]

/-!
### Explicit bounds on Bernoulli polynomials

We first count the zeros of even and odd Bernoulli polynomials by induction, using Rolle's theorem.
-/

/-- Rolle's theorem specialised to the Bernoulli polynomials -/
lemma bernoulliFun_rolle {s : ℕ} (s0 : s ≠ 0) {x y : ℝ} (xy : x < y)
    (e : bernoulliFun s x = bernoulliFun s y) : ∃ z ∈ Ioo x y, bernoulliFun (s - 1) z = 0 := by
  obtain ⟨z, m, r⟩ := exists_hasDerivAt_eq_zero xy contDiff_bernoulliFun.continuous.continuousOn e
      (f' := s * bernoulliFun (s - 1)) (fun _ _ ↦ hasDerivAt_bernoulliFun _ _)
  refine ⟨z, m, ?_⟩
  simpa only [Pi.natCast_def, Pi.mul_apply, mul_eq_zero, Nat.cast_eq_zero, s0, false_or] using r

/-- Number of Bernoulii polynomial preimages in an open interval -/
def pres (s : ℕ) (x y b : ℝ) : ℕ∞ :=
  (Ioo x y ∩ bernoulliFun s ⁻¹' {b}).encard

/-- Reflecting `pres` about the midpoint -/
lemma pres_eq_reflect {s : ℕ} {x y b : ℝ} :
    pres s (1 - y) (1 - x) ((-1) ^ s * b) = pres s x y b := by
  suffices h : ∀ {x y b}, pres s (1 - y) (1 - x) ((-1) ^ s * b) ≤ pres s x y b by
    apply le_antisymm h
    convert h
    all_goals norm_num [sub_sub_cancel, ← mul_assoc, ← mul_pow]
  intro x y b
  apply Set.encard_le_encard_of_injOn (f := fun x ↦ 1 - x)
  · intro u m
    simp only [mem_inter_iff, mem_Ioo, mem_preimage, mem_singleton_iff,
      bernoulliFun_eval_one_sub] at m ⊢
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    simp only [m.2, ← mul_assoc, ← mul_pow, mul_neg, mul_one, neg_neg, one_pow, one_mul]
  · simp only [InjOn, sub_right_inj, imp_self, implies_true]

/-- `bernoulliFun 0` has no zeros -/
@[simp] lemma pres_zero_eq_zero {x y : ℝ} : pres 0 x y 0 = 0 := by
  apply Set.encard_eq_zero.mpr
  ext
  simp

/-- `bernoulliFun 1` has no zeros in `Ioo 0 2⁻¹` -/
@[simp] lemma pres_one_eq_zero : pres 1 0 2⁻¹ 0 = 0 := by
  apply Set.encard_eq_zero.mpr
  ext x
  simp only [mem_inter_iff, mem_Ioo, mem_preimage, bernoulliFun_one, one_div, mem_singleton_iff,
    sub_eq_zero, mem_empty_iff_false, iff_false, not_and, and_imp]
  intros
  linarith

/-- `bernoulliFun 2` never hits `bernoulli 2` in `Ioo 0 1` -/
@[simp] lemma pres_two_eq_zero : pres 2 0 1 6⁻¹ = 0 := by
  apply Set.encard_eq_zero.mpr
  ext x
  simp only [mem_inter_iff, mem_Ioo, mem_preimage, bernoulliFun_two, mem_singleton_iff,
    add_eq_right, mem_empty_iff_false, iff_false, not_and, and_imp, sub_eq_zero]
  intro x0 x1
  by_contra h
  cases' eq_zero_or_one_of_sq_eq_self h
  all_goals linarith

/-- `bernoulliFun 2` has exactly one zero in `Ioo 0 2⁻¹` -/
@[simp] lemma pres_two_eq_one : pres 2 0 2⁻¹ 0 = 1 := by
  apply Set.encard_eq_one.mpr
  set s := Real.sqrt 3⁻¹
  use (1 - s) / 2
  have d : discrim 1 (-1) (6⁻¹ : ℝ) = s * s := by norm_num [discrim, s, ← mul_inv]
  have q := quadratic_eq_zero_iff (by norm_num) d
  simp only [← sq, one_mul, neg_mul, ← sub_eq_add_neg, neg_neg, mul_one] at q
  ext x
  simp only [mem_inter_iff, mem_Ioo, mem_preimage, bernoulliFun_two, mem_singleton_iff]
  constructor
  · intro ⟨⟨x0,xh⟩,e⟩
    replace q := (q x).mp e
    have ne : x ≠ (1 + s) / 2 := by
      contrapose xh
      simp only [ne_eq, not_not] at xh
      simp only [xh, Real.sqrt_inv, not_lt, s]
      simp only [Real.sqrt_inv, s] at xh
      rw [le_div_iff₀]
      all_goals norm_num
    simpa only [ne, false_or] using q
  · intro e
    refine ⟨?_, (q x).mpr (.inr e)⟩
    simp only [e, Real.sqrt_inv, Nat.ofNat_pos, div_pos_iff_of_pos_right, sub_pos, s]
    rw [inv_lt_comm₀, Real.lt_sqrt, div_lt_iff₀]
    all_goals norm_num

/-- If there's at most one derivative zero betwen two preimages, there are no preimages between -/
lemma pres_eq_zero {s : ℕ} {x y b : ℝ} (xy : x < y) (h : pres s x y 0 ≤ 1)
    (xb : bernoulliFun (s + 1) x = b) (yb : bernoulliFun (s + 1) y = b) :
    pres (s + 1) x y b = 0 := by
  simp only [pres, encard_le_one_iff, mem_inter_iff, mem_Ioo, mem_preimage, mem_singleton_iff,
    and_imp, encard_eq_zero] at h ⊢
  ext t
  simp only [mem_inter_iff, mem_Ioo, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
    iff_false, not_and, and_imp]
  intro xt ty
  by_contra tb
  obtain ⟨z, ⟨_, _⟩, zb⟩ := bernoulliFun_rolle (by omega) xy (xb.trans yb.symm)
  by_cases tz : t < z
  · obtain ⟨u, ⟨_, _⟩, ub⟩ := bernoulliFun_rolle (by omega) xt (xb.trans tb.symm)
    specialize h u z ?_ ?_ ub ?_ ?_ zb
    all_goals linarith
  · obtain ⟨u, ⟨_, _⟩, ub⟩ := bernoulliFun_rolle (by omega) ty (tb.trans yb.symm)
    specialize h u z ?_ ?_ ub ?_ ?_ zb
    all_goals linarith

/-- If there's no derivative zeros in an interval, there is at most one preimage -/
lemma pres_le_one {s : ℕ} {x y b : ℝ} (h : pres s x y 0 = 0) : pres (s + 1) x y b ≤ 1 := by
  simp only [pres, encard_eq_zero, eq_empty_iff_forall_notMem, mem_inter_iff, mem_Ioo,
    mem_preimage, mem_singleton_iff, not_and, and_imp, encard_le_one_iff] at h ⊢
  intro u v xu uy ub xv vy vb
  apply le_antisymm
  · by_contra vu
    simp only [not_le] at vu
    obtain ⟨z, ⟨_, _⟩, zb⟩ := bernoulliFun_rolle (by omega) vu (vb.trans ub.symm)
    refine h z ?_ ?_ zb
    all_goals linarith
  · by_contra uv
    simp only [not_le] at uv
    obtain ⟨z, ⟨_, _⟩, zb⟩ := bernoulliFun_rolle (by omega) uv (ub.trans vb.symm)
    refine h z ?_ ?_ zb
    all_goals linarith

/-- Bound `pres` on an interval by breaking it into two pieces -/
lemma pres_union_le {s : ℕ} {x y z b : ℝ} (xy : x < y) (yz : y < z) :
    pres s x z b ≤ pres s x y b + 1 + pres s y z b := by
  simp only [pres]
  generalize bernoulliFun s ⁻¹' {b} = t
  have sub : Ioo x z ∩ t = (Ioo x y ∩ t) ∪ ({y} ∩ t) ∪ (Ioo y z ∩ t) := by
    simp only [← Set.union_inter_distrib_right]
    apply congr_arg₂ _ ?_ rfl
    ext s
    simp only [mem_Ioo, union_singleton, mem_union, mem_insert_iff]
    constructor
    · intro ⟨a, b⟩
      simp only [a, true_and, ← le_iff_eq_or_lt, b, and_true, le_or_gt]
    · intro h
      rcases h with (h | h) | h
      · simp only [h, xy, yz, true_and]
      · exact ⟨h.1, h.2.trans yz⟩
      · exact ⟨xy.trans h.1, h.2⟩
  rw [sub]
  refine le_trans (Set.encard_union_le _ _) ?_
  refine add_le_add_right ?_ _
  refine le_trans (Set.encard_union_le _ _) ?_
  refine add_le_add_left ?_ _
  simp only [encard_le_one_iff, mem_inter_iff, mem_singleton_iff, and_imp]
  aesop

/-- Count various preimages of Bernoulli polynomials -/
lemma bernoulliFun_zeros (s : ℕ) (s1 : 2 ≤ s) :
    if Even s then pres s 0 1 (bernoulli s) = 0 ∧ pres s 0 2⁻¹ 0 ≤ 1 else pres s 0 2⁻¹ 0 = 0 := by
  refine Nat.le_induction ?_ ?_ s s1
  · simp only [even_two, ↓reduceIte, bernoulli_two, Rat.cast_inv, Rat.cast_ofNat, pres_two_eq_zero,
      pres_two_eq_one, le_refl, and_self]
  · intro s s2 h
    rcases s.even_or_odd' with ⟨t, e | e⟩
    · simp only [e, even_two, Even.mul_right, ↓reduceIte, Nat.not_even_bit1] at h ⊢
      obtain ⟨h, r⟩ := h
      refine pres_eq_zero (by norm_num) r ?_ bernoulliFun_eval_half_eq_zero
      rw [bernoulliFun_eval_zero, bernoulli_odd_eq_zero (by omega), Rat.cast_zero]
    · simp only [e, Nat.not_even_bit1, ↓reduceIte, add_assoc, Nat.reduceAdd, Nat.even_add_one,
        not_false_eq_true] at h ⊢
      constructor
      · refine pres_eq_zero (by norm_num) ?_ ?_ ?_
        · refine le_trans (pres_union_le (y := 2⁻¹) (by norm_num) (by norm_num)) ?_
          have r : pres (2 * t + 1) 2⁻¹ 1 0 = 0 := by
            rw [← pres_eq_reflect]
            norm_num at h ⊢
            exact h
          simp only [h, zero_add, r, add_zero, le_refl]
        · simp only [bernoulliFun_eval_zero]
        · simp only [bernoulliFun_eval_one, bernoulliFun_eval_zero]
          aesop
      · exact pres_le_one h

lemma bernoulliFun_pres_eq_zero (s : ℕ) (o : Odd s) : pres s 0 2⁻¹ 0 = 0 := by
  by_cases s1 : s = 1
  · simp only [s1, pres_one_eq_zero]
  · have h := bernoulliFun_zeros s (by simp [Odd] at o; omega)
    simpa only [Nat.not_even_iff_odd.mpr o, ↓reduceIte] using h

lemma abs_bernoulliFun_le_half (s : ℕ) : |bernoulliFun s 2⁻¹| ≤ |bernoulli s| := by
  simp only [bernoulliFun_eval_half, abs_mul, Rat.cast_abs]
  apply mul_le_of_le_one_left (by positivity)
  by_cases s0 : 1 ≤ s
  · rw [abs_of_nonpos, neg_sub]
    · rw [sub_le_self_iff]
      positivity
    · rw [sub_nonpos, div_le_iff₀ (by positivity), one_mul]
      exact le_self_pow₀ (by norm_num) (by omega)
  · simp only [not_le, Nat.lt_one_iff] at s0
    norm_num [s0]

lemma IsLocalMax.deriv_eq_zero_of_abs {f : ℝ → ℝ} {y : ℝ} (m : IsLocalMax (fun x ↦ |f x|) y) :
    deriv f y = 0 := by
  by_cases fy0 : 0 ≤ f y
  · apply IsLocalMax.deriv_eq_zero
    filter_upwards [m]
    intro x le
    simp only [abs_of_nonneg fy0] at le
    exact le_trans (le_abs_self _) le
  · simp only [not_le] at fy0
    rw [← neg_eq_zero, ← deriv.fun_neg]
    apply IsLocalMax.deriv_eq_zero
    filter_upwards [m]
    intro x le
    simp only [abs_of_neg fy0] at le ⊢
    exact le_trans (neg_le_abs _) le

lemma abs_bernoulliFun_le_even (s : ℕ) {x : ℝ} (m : x ∈ Icc 0 1) :
    |bernoulliFun (2 * s) x| ≤ |bernoulli (2 * s)| := by
  obtain ⟨x0, x1⟩ := m
  wlog h : x ≤ 2⁻¹
  · simpa only [Rat.cast_abs, bernoulliFun_eval_one_sub, even_two, Even.mul_right, Even.neg_pow,
      one_pow, one_mul] using this s (x := 1 - x) (by linarith) (by linarith) (by linarith)
  by_cases s0 : s = 0
  · simp only [s0, mul_zero, bernoulliFun_zero, abs_one, bernoulli_zero, Rat.cast_one, le_refl]
  have m : ∃ y ∈ Icc 0 2⁻¹, IsMaxOn (fun x ↦ |bernoulliFun (2 * s) x|) (Icc 0 2⁻¹) y :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num))
      (Continuous.continuousOn (by continuity))
  obtain ⟨y, ⟨y0, y1⟩, m⟩ := m
  refine le_trans (m ⟨x0,h⟩) ?_
  simp only
  by_cases e : y = 0 ∨ y = 2⁻¹
  · cases' e with e e
    · simp only [e, bernoulliFun_eval_zero, Rat.cast_abs, le_refl]
    · simp only [e, abs_bernoulliFun_le_half]
  · simp only [not_or, ← ne_eq] at e
    replace y0 := e.1.symm.lt_of_le y0
    replace y1 := e.2.lt_of_le y1
    have blah := (m.on_subset Ioo_subset_Icc_self).isLocalMax (Ioo_mem_nhds y0 y1)
    have d := ((m.on_subset Ioo_subset_Icc_self).isLocalMax
      (Ioo_mem_nhds y0 y1)).deriv_eq_zero_of_abs
    simp only [deriv_bernoulliFun, Nat.cast_mul, Nat.cast_ofNat, mul_eq_zero, OfNat.ofNat_ne_zero,
      Nat.cast_eq_zero, s0, or_self, false_or] at d
    have z := Set.encard_eq_zero.mp (bernoulliFun_pres_eq_zero (2 * s - 1) ?_)
    · contrapose z
      simp only [← nonempty_iff_ne_empty]
      exact ⟨y, ⟨y0, y1⟩, d⟩
    · simp only [Odd]
      use s - 1
      omega

/-!
### Nonexplicit bounds on Bernoulli polynomials
-/

lemma exists_max_bernoulli (s : ℕ) :
    ∃ x ∈ Icc 0 1, IsMaxOn (fun x ↦ |bernoulliFun s x|) (Icc 0 1) x := by
  by_cases s1 : s = 1
  · use 0
    simp only [mem_Icc, le_refl, zero_le_one, and_self, s1, bernoulliFun_one, one_div, true_and]
    intro x m
    simp only [zero_sub, abs_neg, mem_setOf_eq, mem_Icc] at m ⊢
    nth_rw 2 [abs_of_pos (by norm_num)]
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  · apply isCompact_Icc.exists_isMaxOn
    · exact Nonempty.of_subtype
    · apply Continuous.continuousOn
      continuity

/-- The maximum absolute value of each Bernoulli polynomial -/
def bernoulliBound (s : ℕ) : ℝ :=
  |bernoulliFun s (exists_max_bernoulli s).choose|

/-- The maximum absolute value of each saw function -/
def sawBound (s : ℕ) : ℝ :=
  (↑s.factorial)⁻¹ * bernoulliBound s

lemma abs_bernoulliFun_le (s : ℕ) (x : ℝ) (m : x ∈ Icc 0 1) :
    |bernoulliFun s x| ≤ bernoulliBound s := by
  simp only [bernoulliBound]
  obtain ⟨_, max⟩ := choose_spec (exists_max_bernoulli s)
  exact max m

@[bound] lemma abs_saw_le (s : ℕ) (x : ℝ) : |saw s x| ≤ sawBound s := by
  have sp : 0 < (s.factorial : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos _))
  simp only [saw, sawBound, smul_eq_mul, abs_mul, abs_of_pos sp]
  refine mul_le_mul_of_nonneg_left ?_ sp.le
  exact abs_bernoulliFun_le _ _ (unitInterval.fract_mem x)

@[simp, bound] lemma bernoulliBound_nonneg {s : ℕ} : 0 ≤ bernoulliBound s := by
  simp only [bernoulliBound, abs_nonneg]

@[simp, bound] lemma sawBound_nonneg {s : ℕ} : 0 ≤ sawBound s := by
  simp only [sawBound]
  bound

@[simp] lemma bernoulliBound_eq_abs_bernoulli (s : ℕ) :
    bernoulliBound (2 * s) = |bernoulli (2 * s)| := by
  have e := exists_max_bernoulli (2 * s)
  set x := e.choose
  have m : x ∈ Icc 0 1 := (choose_spec e).1
  have max : IsMaxOn (fun x ↦ |bernoulliFun (2 * s) x|) (Icc 0 1) x := (choose_spec e).2
  apply le_antisymm
  · exact abs_bernoulliFun_le_even _ (choose_spec e).1
  · refine le_trans ?_ (abs_bernoulliFun_le _ 0 (by simp))
    simp only [Rat.cast_abs, bernoulliFun_eval_zero, le_refl]

@[simp] lemma bernoulliBound_eq_abs_bernoulli' (s : ℕ) (e : Even s) :
    bernoulliBound s = |bernoulli s| := by
  simp only [Nat.even_iff] at e
  convert bernoulliBound_eq_abs_bernoulli (s / 2)
  all_goals omega
