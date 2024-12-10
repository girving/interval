import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Topology.ContinuousOn
import Interval.EulerMaclaurin.DerivUnderIntegral
import Interval.EulerMaclaurin.IteratedDerivArith
import Interval.EulerMaclaurin.LHopital
import Interval.EulerMaclaurin.PartialDerivCommute

/-!
# Euler-Maclaurin formula

This lets us approximate finite sums of `C^k` functions with integrals, with known bounds on the
remainder.
-/

open Classical
open Filter
open Set
open Complex (I)
open Function (uncurry)
open MeasureTheory (volume)
open Metric (closedBall)
open scoped Real
open scoped Topology
open intervalIntegral
noncomputable section
namespace EulerMaclaurin

/-!
### The generating function of the Bernoulli polynomials
-/

/-- The generating function of the saw-tooth functions -/
def gen (t x : ℝ) : ℝ :=
  (if t = 0 then 1 else t / (rexp t - 1)) * rexp (x * t)

/-- `gen` for `x = 0`, over complex numbers -/
def genc (t : ℂ) : ℂ :=
  if t = 0 then 1 else t / (Complex.exp t - 1)

/-- `genc` is analytic in `t`, away from `2πiℤ` -/
lemma analyticAt_genc_ae {t : ℂ} (h : Complex.exp t ≠ 1) : AnalyticAt ℂ genc t := by
  rw [analyticAt_congr (g := fun t ↦ t / (Complex.exp t - 1))]
  · apply analyticAt_id.div (analyticAt_cexp.sub analyticAt_const)
    simpa only [Pi.sub_apply, sub_ne_zero] using h
  · filter_upwards [ContinuousAt.eventually_ne (Complex.continuous_exp).continuousAt h]
    intro t ne
    have t0 : t ≠ 0 := by contrapose ne; simp only [not_not] at ne; simp [ne]
    simp only [genc, t0, if_false]

/-- If `exp t = 1`, it is locally not 1 -/
lemma isolated_exp {z : ℂ} (h : Complex.exp z = 1) : ∀ᶠ w in 𝓝[≠] z, Complex.exp w ≠ 1 := by
  simp only [Complex.exp_eq_one_iff, ne_eq, not_exists, eventually_nhdsWithin_iff, mem_compl_iff,
    mem_singleton_iff, Metric.eventually_nhds_iff] at h ⊢
  obtain ⟨n, h⟩ := h
  refine ⟨2 * π, by positivity, ?_⟩
  intro w d
  rw [not_imp_comm, not_forall]
  intro ⟨k, e⟩
  simp only [not_not] at e
  simp only [e, h, Complex.dist_eq, ← sub_mul, map_mul, Complex.abs_ofNat, Complex.abs_ofReal,
    abs_of_pos Real.pi_pos, Complex.abs_I, mul_one, ← Int.cast_sub, Complex.abs_intCast] at d
  rw [← lt_div_iff₀ (by positivity), div_self (by positivity), ← Int.cast_abs, ← Int.cast_one,
    Int.cast_lt, Int.abs_lt_one_iff, sub_eq_zero] at d
  simp [e, h, d]

/-- The limit we need, via L'Hopital's rule -/
lemma tendsto_genc_div : Tendsto (fun t ↦ t / (Complex.exp t - 1)) (𝓝[≠] 0) (𝓝 1) := by
  nth_rw 2 [(by norm_num : (1 : ℂ) = 1 / 1)]
  apply lhopital_field (f := fun t ↦ t)
  · apply hasDerivAt_id'
  · refine HasDerivAt.sub_const ?_ 1
    rw [← Complex.exp_zero]
    apply Complex.hasDerivAt_exp
  · norm_num
  · norm_num
  · simp

/-- `genc` is continuous at 0 -/
lemma continuousAt_genc : ContinuousAt genc 0 := by
  simp only [← continuousWithinAt_compl_self, ContinuousWithinAt, genc, Complex.exp_zero,
    ↓reduceIte]
  apply tendsto_genc_div.congr' (f₁ := fun t ↦ t / (Complex.exp t - 1))
  filter_upwards [isolated_exp Complex.exp_zero]
  intro t ne
  have t0 : t ≠ 0 := by contrapose ne; simp only [not_not] at ne; simp [ne]
  simp only [genc, t0, if_false]

/-- `genc` is analytic at `0` -/
lemma analyticAt_genc_zero : AnalyticAt ℂ genc 0 := by
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ continuousAt_genc
  simp only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff]
  filter_upwards [eventually_norm_sub_lt 0 Real.two_pi_pos]
  intro t d t0
  refine (analyticAt_genc_ae ?_).differentiableAt
  simp only [ne_eq, Complex.exp_eq_one_iff, not_exists]
  intro n
  by_cases n0 : n = 0
  · contrapose t0
    simp only [not_not] at t0
    simp [t0, n0]
  · contrapose d
    simp only [not_not] at d
    simp [d, abs_of_pos Real.pi_pos]
    have le : 1 ≤ |(n : ℝ)| := by
      rw [← Int.cast_one, ← Int.cast_abs, Int.cast_le]
      exact Int.one_le_abs n0
    exact le_mul_of_one_le_left (by bound) le

/-- `genc` is analytic on the real axis -/
lemma analyticAt_genc_real (t : ℝ) : AnalyticAt ℂ genc t := by
  by_cases t0 : t = 0
  · simp only [t0, Complex.ofReal_zero, analyticAt_genc_zero]
  · apply analyticAt_genc_ae
    simpa only [← Complex.ofReal_exp, ← Complex.ofReal_one, ne_eq, Complex.ofReal_inj,
      Real.exp_eq_one_iff]

/-- `gen` is analytic -/
lemma analyticAt_gen {t x : ℝ} : AnalyticAt ℝ (uncurry gen) (t, x) := by
  apply AnalyticAt.mul
  · have e : ∀ (d : (x : ℝ × ℝ) → Decidable (x.1 = 0)),
        (fun x : ℝ × ℝ ↦ @ite _ (x.1 = 0) (d x) 1 (x.1 / (rexp x.1 - 1))) =
        Complex.reCLM ∘ genc ∘ (fun x : ℝ × ℝ ↦ (x.1 : ℂ)) := by
      intro d; ext ⟨t, x⟩; simp [genc]; split_ifs
      · simp only [Complex.one_re]
      · simp only [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_sub,
          ← Complex.ofReal_div, Complex.ofReal_re]
    rw [e]
    refine AnalyticAt.comp ?_ (AnalyticAt.comp ?_ ?_)
    · apply Complex.reCLM.analyticAt
    · simp only [Complex.ofReal_zero]
      exact (analyticAt_genc_real _).restrictScalars
    · exact (Complex.ofRealCLM.analyticAt _).comp analyticAt_fst
  · exact analyticAt_rexp.comp (analyticAt_snd.mul analyticAt_fst)

/-- `gen` is smooth -/
lemma contDiff_gen : ContDiff ℝ ⊤ (uncurry gen) := by
  rw [contDiff_iff_contDiffAt]
  intro ⟨t,x⟩
  exact analyticAt_gen.contDiffAt

/-- `gen` has mean `1` on `x ∈ [0,1]` -/
lemma mean_gen (t : ℝ) : ∫ x in (0 : ℝ)..1, gen t x = 1 := by
  by_cases t0 : t = 0
  · simp [t0, gen]
  · simp only [gen, t0, ↓reduceIte, div_eq_mul_inv, integral_const_mul, ne_eq, not_false_eq_true,
      integral_comp_mul_right, zero_mul, one_mul, integral_exp, Real.exp_zero, smul_eq_mul,
      mul_comm _ t⁻¹, ← mul_assoc, inv_mul_cancel₀ t0]
    exact inv_mul_cancel₀ (by simp [sub_eq_zero, t0])

/-- Differentiating w.r.t. `x` pulls out a `t` -/
lemma deriv_gen (t x : ℝ) : deriv (fun x ↦ gen t x) x = t * gen t x := by
  generalize hc : (if t = 0 then 1 else t / (rexp t - 1)) = c
  simp [gen, hc, deriv_const_mul_field]
  ring

/-!
### The Bernoulli polynomials
-/

variable {s : ℕ}

/-- The Bernoulli polynomials are generated by `gen` -/
def bernoulliPoly (s : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv s (fun t ↦ gen t x) 0

lemma contDiff_bernoulliPoly : ContDiff ℝ ⊤ (bernoulliPoly s) :=
  (contDiff_gen.comp₂ contDiff_snd contDiff_fst).iteratedDeriv contDiff_const

@[simp] lemma bernoulliPoly_zero {x : ℝ} : bernoulliPoly 0 x = 1 := by
  simp [bernoulliPoly, gen]

@[simp] lemma deriv_bernoulliPoly :
    deriv (bernoulliPoly s) = fun x ↦ s • bernoulliPoly (s - 1) x := by
  ext x
  rw [(by rfl : bernoulliPoly s = fun y ↦ bernoulliPoly s y)]
  have comm := deriv_iteratedDeriv_comm (z := (x,0)) (n := s)
    (contDiff_gen.comp (contDiff_snd.prod contDiff_fst))
  simp only [uncurry, Function.comp] at comm
  simp only [bernoulliPoly, comm, deriv_gen]
  clear comm
  have gc : ContDiff ℝ ⊤ (fun t ↦ gen t x) := contDiff_gen.comp₂ contDiff_id contDiff_const
  simp only [← smul_eq_mul, iteratedDeriv_mul (gc.of_le le_top), zero_smul, zero_add]

lemma hasDerivAt_bernoulliPoly {x : ℝ} :
    HasDerivAt (bernoulliPoly s) (s • bernoulliPoly (s - 1) x) x := by
  have e : s • bernoulliPoly (s - 1) x = deriv (bernoulliPoly s) x := by simp
  rw [e, hasDerivAt_deriv_iff]
  exact contDiff_bernoulliPoly.contDiffAt.differentiableAt le_top

/-- Bernoulli polys have mean `n = 0` -/
lemma mean_bernoulliPoly (s : ℕ) :
    ∫ x in (0 : ℝ)..1, bernoulliPoly s x = if s = 0 then 1 else 0 := by
  simp only [bernoulliPoly]
  rw [← iteratedDeriv_interval_integral_of_contDiff]
  · simp only [mean_gen, iteratedDeriv_const]
  · exact contDiff_gen
  · exact zero_le_one

/-- The values at 0 and 1 match for `2 ≤ s` -/
lemma bernoulliPoly_one_eq_zero (s : ℕ) : bernoulliPoly (s + 2) 1 = bernoulliPoly (s + 2) 0 := by
  have nz : (s + 2 : ℝ) ≠ 0 := by linarith
  have e : ∀ x, bernoulliPoly (s + 1) x = (s + 2 : ℝ)⁻¹ • deriv (bernoulliPoly (s + 2)) x := by
    intro x
    simp only [deriv_bernoulliPoly, Nat.add_one_sub_one, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat,
      smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ nz, one_mul]
  have m := mean_bernoulliPoly (s + 1)
  simp only [e, smul_eq_mul, intervalIntegral.integral_const_mul, Nat.add_one_ne_zero,
    if_false, mul_eq_zero, inv_ne_zero nz, false_or] at m
  rwa [intervalIntegral.integral_deriv_eq_sub, sub_eq_zero] at m
  · intro x _
    exact (contDiff_bernoulliPoly.differentiable le_top).differentiableAt
  · apply ContinuousOn.intervalIntegrable
    exact (contDiff_bernoulliPoly.continuous_deriv le_top).continuousOn

@[simp] lemma bernoulliPoly_one {x : ℝ} : bernoulliPoly 1 x = x - 1 / 2 := by
  generalize hc : bernoulliPoly 1 0 = c
  have i : ∀ y, bernoulliPoly 1 y = y + c := by
    intro y
    rw [← hc, ← sub_eq_iff_eq_add, ← intervalIntegral.integral_deriv_eq_sub]
    · simp only [deriv_bernoulliPoly, Nat.sub_self, bernoulliPoly_zero, one_smul, integral_const,
        sub_zero, smul_eq_mul, mul_one]
    · intro x _
      exact (contDiff_bernoulliPoly.differentiable le_top).differentiableAt
    · simp only [deriv_bernoulliPoly, Nat.sub_self, bernoulliPoly_zero, one_smul,
        _root_.intervalIntegrable_const]
  have m := mean_bernoulliPoly 1
  simp only [i, intervalIntegrable_id, _root_.intervalIntegrable_const, integral_add, integral_id,
    one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, one_div,
    integral_const, smul_eq_mul, one_mul, one_ne_zero, ↓reduceIte] at m
  simp only [i, one_div]
  linarith

/-!
### The presaw functions

These are `saw s x` smoothly extended from a particular `[a,a+1)` interval.
-/

variable {a : ℤ}

/-- The saw functions are scaled, shifted versions of the Bernoulli polynomials -/
def presaw (s : ℕ) (a : ℤ) (x : ℝ) : ℝ :=
  (s.factorial : ℝ)⁻¹ • bernoulliPoly s (x - a)

/-- `presaw` is smooth -/
lemma contDiff_presaw : ContDiff ℝ ⊤ (presaw s a) := by
  exact (contDiff_bernoulliPoly.comp (contDiff_id.sub contDiff_const)).const_smul _

@[simp] lemma presaw_start {x : ℝ} : presaw 0 a x = 1 := by simp [presaw]

lemma hasDerivAt_presaw {x : ℝ} : HasDerivAt (presaw (s + 1) a) (presaw s a x) x := by
  have e : presaw (s + 1) a = (fun x ↦ presaw (s + 1) a x) := rfl
  simp only [presaw, Nat.factorial_succ, mul_comm _ s.factorial, Nat.cast_mul,
    mul_inv, ← smul_smul, e]
  apply HasDerivAt.const_smul
  have s0 : ((s + 1 : ℕ) : ℝ) ≠ 0 := by simp only [Nat.cast_ne_zero]; omega
  have sc : s = s + 1 - 1 := by omega
  rw [← inv_smul_smul₀ s0 (x := (bernoulliPoly s (x - ↑a)))]
  nth_rw 5 [sc]
  apply HasDerivAt.const_smul
  rw [Nat.cast_smul_eq_nsmul]
  rw [← mul_one (((s + 1) • bernoulliPoly (s + 1 - 1) (x - ↑a)))]
  exact HasDerivAt.comp _ (hasDerivAt_bernoulliPoly (s := s + 1)) (h := fun x : ℝ ↦ x - a)
    ((hasDerivAt_id' x).sub_const _)

@[simp] lemma deriv_presaw {x : ℝ} : deriv (presaw (s + 1) a) x = presaw s a x := by
  rw [hasDerivAt_presaw.deriv]

@[simp] lemma presaw_zero {x : ℝ} : presaw 0 a x = 1 := by
  simp only [presaw, Nat.factorial_zero, Nat.cast_one, inv_one, bernoulliPoly_zero, smul_eq_mul,
    mul_one]

/-!
### The saw functions
-/

/-- The saw functions are scaled, periodic versions of the Bernoulli polynomials -/
def saw (s : ℕ) (x : ℝ) :=
  (s.factorial : ℝ)⁻¹ • bernoulliPoly s (Int.fract x)

/-- Saw is nice on `[a,a+1)` -/
lemma saw_eqOn {a : ℤ} :
    EqOn (saw s) (presaw s a) (Ico a (a+1)) := by
  intro x m
  simp only [Int.cast_add, Int.cast_one, mem_Ico, ← Int.floor_eq_iff] at m
  simp only [saw, presaw, smul_eq_mul, mul_eq_mul_left_iff, inv_eq_zero, Nat.cast_eq_zero,
    Int.fract, m]

/-- `presaw` at integer values in terms of `saw` -/
@[simp] lemma presaw_coe_same {a : ℤ} : presaw s a a = saw s 0 := by
  rw [← saw_eqOn (a := a)]
  all_goals simp [saw]

/-- `presaw` at integer values in terms of `saw` -/
@[simp] lemma presaw_coe_succ {a : ℤ} : presaw (s + 2) a (a + 1) = saw (s + 2) 0 := by
  simp only [presaw, Int.cast_add, Int.cast_one, add_sub_cancel_left, bernoulliPoly_one_eq_zero,
    smul_eq_mul, saw, Int.fract_zero]

/-- `presaw` at integer values in terms of `saw` -/
@[simp] lemma presaw_one_coe_succ {a : ℤ} : presaw 1 a (a + 1) = 1 / 2 := by
  simp only [presaw, Nat.factorial_one, Nat.cast_one, inv_one, Int.cast_add, Int.cast_one,
    add_sub_cancel_left, bernoulliPoly_one, one_div, smul_eq_mul, one_mul]
  norm_num

/-- Saw is nice on `[a,a+1)` -/
lemma contDiff_saw : ContDiffOn ℝ ⊤ (saw s) (Ico a (a+1)) := by
  rw [contDiffOn_congr saw_eqOn]
  exact contDiff_presaw.contDiffOn

@[simp] lemma saw_zero {x : ℝ} : saw 0 x = 1 := by
  simp only [saw, Nat.factorial_zero, Nat.cast_one, inv_one, bernoulliPoly_zero, smul_eq_mul,
    mul_one]

@[simp] lemma saw_int {x : ℤ} : saw s x = saw s 0 := by
  simp only [saw, Int.fract_intCast, smul_eq_mul, Int.fract_zero]

lemma hasDerivAt_saw {s : ℕ} {a : ℤ} {x : ℝ} (m : x ∈ Ioo (a : ℝ) (a + 1)) :
    HasDerivAt (saw (s + 1)) (saw s x) x := by
  have e : saw (s + 1) =ᶠ[𝓝 x] (fun x ↦ presaw (s + 1) a x) := by
    apply saw_eqOn.eventuallyEq_of_mem
    exact Ico_mem_nhds_iff.mpr m
  refine HasDerivAt.congr_of_eventuallyEq ?_ e
  simp only [saw_eqOn (mem_Ico_of_Ioo m), Nat.factorial_succ, mul_comm _ s.factorial, Nat.cast_mul,
    mul_inv, ← smul_smul]
  exact hasDerivAt_presaw

@[simp] lemma deriv_saw {x : ℝ} (m : x ∈ Ioo (a : ℝ) (a + 1)) :
    deriv (saw (s + 1)) x = saw s x := by
  rw [(hasDerivAt_saw m).deriv]

/-- `saw 1` is a saw-tooth function -/
lemma saw_one {x : ℝ} : saw 1 x = Int.fract x - 1 / 2 := by
  simp only [saw, Nat.factorial_one, Nat.cast_one, inv_one, bernoulliPoly_one, one_div, smul_eq_mul,
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
        apply Ico_mem_nhdsWithin_Iio
        simp only [Int.cast_sub, Int.cast_one, sub_add_cancel, mem_Ioc, sub_lt_self_iff,
          zero_lt_one, le_refl, and_self]
      · nth_rw 2 [← sub_add_cancel (a : ℝ) 1]
        rw [saw_int, ← Int.cast_one (R := ℝ), ← Int.cast_sub, Int.cast_one, presaw_coe_succ]
    · apply ContinuousWithinAt.congr_of_eventuallyEq (f := presaw (s + 2) a)
      · exact contDiff_presaw.continuous.continuousWithinAt
      · apply saw_eqOn.eventuallyEq_of_mem
        apply Ico_mem_nhdsWithin_Ioi
        simp only [Int.cast_add, Int.cast_one, mem_Ico, le_refl, lt_add_iff_pos_right, zero_lt_one,
          and_self]
      · simp only [saw_int, presaw_coe_same]
  · apply ContinuousAt.congr_of_eventuallyEq (f := presaw (s + 2) a)
    · exact contDiff_presaw.continuous.continuousAt
    · apply saw_eqOn.eventuallyEq_of_mem
      apply Ico_mem_nhds
      · exact (Ne.symm xa).lt_of_le (Int.floor_le x)
      · simp only [Int.cast_add, Int.cast_one, Int.lt_floor_add_one, a]

/-!
### Euler-Maclaurin for a single `[a, a + 1]` interval
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → E} {t : Set ℝ} {a b c : ℤ} {n : ℕ}

lemma intervalIntegrable_presaw_smul (fc : ContDiffOn ℝ n f t) {a b : ℝ} (ab : a ≤ b)
    (u : UniqueDiffOn ℝ t) (abt : Icc a b ⊆ t) {s : ℕ} :
    IntervalIntegrable (fun x ↦ presaw s c x • iteratedDerivWithin n f t x) volume a b := by
  refine (contDiff_presaw.continuous.continuousOn.smul ?_).intervalIntegrable
  simp only [uIcc_of_le ab]
  exact (fc.continuousOn_iteratedDerivWithin (le_refl _) u).mono abt

lemma integral_saw_eq_integral_presaw :
    ∫ x : ℝ in a..a + 1, saw s x • iteratedDerivWithin s f t x =
    ∫ x : ℝ in a..a + 1, presaw s a x • iteratedDerivWithin s f t x := by
  apply intervalIntegral.integral_congr_ae
  have e : Ι (a : ℝ) (a + 1)  =ᵐ[volume] Ioo a (a + 1) := by
    rw [uIoc_of_le]
    · exact MeasureTheory.Ioo_ae_eq_Ioc.symm
    · simp only [Int.cast_le, (lt_add_one _).le]
  simp only [← MeasureTheory.ae_restrict_iff' measurableSet_uIoc,
    MeasureTheory.ae_restrict_congr_set e, MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
  filter_upwards
  intro x m
  rw [saw_eqOn (a := a)]
  exact Ioo_subset_Ico_self m

/-- The key integration by parts identity, `presaw` version -/
lemma presaw_smul_iteratedDeriv_by_parts [CompleteSpace E] (fc : ContDiffOn ℝ (s+1) f t)
    (u : UniqueDiffOn ℝ t) (abt : Icc (a : ℝ) (a + 1) ⊆ t) :
    ∫ x in a..(a + 1), presaw s c x • iteratedDerivWithin s f t x =
      presaw (s+1) c (a + 1) • iteratedDerivWithin s f t (a + 1) -
      presaw (s+1) c a • iteratedDerivWithin s f t a -
      ∫ x in a..(a + 1), presaw (s+1) c x • iteratedDerivWithin (s+1) f t x := by
  have i0 := intervalIntegrable_presaw_smul (s := s) (c := c) fc.of_succ (by linarith) u abt
  have i1 := intervalIntegrable_presaw_smul (s := s + 1) (c := c) fc (by linarith) u abt
  rw [eq_sub_iff_add_eq, ← intervalIntegral.integral_add i0 i1]
  set g := fun x ↦ presaw (s + 1) c x • iteratedDerivWithin s f t x
  set g' := fun x ↦ presaw s c x • iteratedDerivWithin s f t x +
    presaw (s + 1) c x • iteratedDerivWithin (s + 1) f t x
  have df : ∀ x ∈ Ioo (a : ℝ) (a + 1) \ ∅, HasDerivAt g (g' x) x := by
    intro x m
    simp only [diff_empty] at m
    simp only [g, g', add_comm (presaw s c _ • _) _]
    apply HasDerivAt.smul
    · exact hasDerivAt_presaw
    · have mt := abt (Ioo_subset_Icc_self m)
      apply HasDerivWithinAt.hasDerivAt
      · rw [iteratedDerivWithin_succ, hasDerivWithinAt_derivWithin_iff]
        · apply (fc.contDiffWithinAt mt).differentiableWithinAt_iteratedDerivWithin
          · simp only [← Nat.cast_add_one, Nat.cast_lt, Nat.lt_add_one]
          · simp only [mt, insert_eq_of_mem, u]
        · exact u x mt
      · exact Filter.monotone_mem (subset_trans Ioo_subset_Icc_self abt) (isOpen_Ioo.mem_nhds m)
  refine Eq.trans (MeasureTheory.integral_eq_of_hasDerivWithinAt_off_countable_of_le
    (f := g) (f' := g') (Hd := df) (by linarith) countable_empty ?_ ?_) ?_
  · apply contDiff_presaw.continuous.continuousOn.smul
    exact (fc.continuousOn_iteratedDerivWithin le_self_add u).mono abt
  · exact i0.add i1
  · simp only [g, smul_sub]

/-- Iterated integration by parts, `presaw` version -/
lemma presaw_iterated_by_parts [CompleteSpace E] (fc : ContDiffOn ℝ (s+1) f t)
    (u : UniqueDiffOn ℝ t) (abt : Icc (a : ℝ) (a + 1) ⊆ t) :
    ∫ x in a..a + 1, f x = (2⁻¹ : ℝ) • (f a + f (a + 1)) -
      ∑ m ∈ Finset.range s, (-1 : ℝ) ^ m • saw (m + 2) 0 •
        (iteratedDerivWithin (m + 1) f t (a + 1) - iteratedDerivWithin (m + 1) f t a) -
      (-1 : ℝ) ^ s • ∫ x in a..a + 1, presaw (s+1) a x • iteratedDerivWithin (s+1) f t x := by
  induction' s with s h
  · simpa only [zero_add, presaw_one_coe_succ, presaw_coe_same, saw_one_zero, neg_smul,
      sub_neg_eq_add, one_div, iteratedDerivWithin_zero, presaw_zero, smul_add, Finset.range_zero,
      Finset.sum_empty, sub_zero, ← smul_add, Int.reduceNeg, pow_zero, one_smul, Int.cast_add,
      Int.cast_one, add_comm _ (f a)] using presaw_smul_iteratedDeriv_by_parts fc u abt (c := a)
  · refine (h fc.of_succ).trans ?_
    clear h
    have z : (-1 : ℝ) ^ s ≠ 0 := by
      simp only [ne_eq, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and, not_false_eq_true]
    simp only [sub_sub, add_left_cancel_iff, sub_right_inj, Finset.sum_range_succ, add_assoc,
      ← smul_smul, pow_succ, ← smul_add, neg_smul, ← sub_eq_add_neg, one_smul, smul_right_inj z]
    refine (presaw_smul_iteratedDeriv_by_parts fc u abt (c := a)).trans ?_
    simp only [(by omega : s + 1 + 1 = s + 2), presaw_coe_same, Nat.reduceAdd, sub_left_inj,
      presaw_coe_succ, ← smul_sub]

/-!
### The full Euler-Maclaurin formula
-/

variable {n : ℕ}

/-- Trapezoidal sum: the trapezoidal rule for integer step size on `[a, a + n]` -/
def trapezoid_sum (f : ℝ → E) (a : ℤ) : ℕ → E
  | 0 => 0
  | n + 1 => trapezoid_sum f a n + (2⁻¹ : ℝ) • (f (a + n) + f (a + n + 1))

-- Definitions as accessible lemmas
@[simp] lemma trapezoid_sum_zero : trapezoid_sum f a 0 = 0 := rfl
lemma trapezoid_sum_succ :
    trapezoid_sum f a (n + 1) = trapezoid_sum f a n + (2⁻¹ : ℝ) • (f (a + n) + f (a + n + 1)) :=
  rfl

lemma ae_ne {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) [MeasureTheory.NoAtoms μ]
    (x : α) : ∀ᵐ y ∂μ, y ≠ x := by
  simp only [Filter.Eventually, ne_eq, MeasureTheory.mem_ae_iff, compl_ne_eq_singleton,
    MeasureTheory.measure_singleton]

lemma intervalIntegrable_saw_smul (fc : ContDiffOn ℝ s f t) (u : UniqueDiffOn ℝ t)
    (abt : Icc (a : ℝ) (a + n) ⊆ t) :
    IntervalIntegrable (fun x ↦ saw s x • iteratedDerivWithin s f t x)
      volume a (a + n) := by
  induction' n with n h
  · simp
  · simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
    refine (h (subset_trans (Icc_subset_Icc (by rfl) (by simp)) abt)).trans ?_
    have ab1 : Icc ((a + n : ℤ) : ℝ) ((a + n : ℤ) + 1) ⊆ t := by
      refine subset_trans (Icc_subset_Icc ?_ ?_) abt
      all_goals simp [← add_assoc]
    have i := intervalIntegrable_presaw_smul (s := s) (c := a + n) fc (by simp) u ab1
    simp only [Int.cast_add, Int.cast_natCast, intervalIntegrable_iff, le_add_iff_nonneg_right,
      zero_le_one, uIoc_of_le] at i ⊢
    apply i.congr
    simp only [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, Filter.EventuallyEq]
    filter_upwards [ae_ne volume (a + n + 1 : ℝ)]
    intro x ne m
    rw [saw_eqOn (a := a + n)]
    simp only [mem_Ioc, ne_eq, Int.cast_add, Int.cast_natCast, mem_Ico] at m ne ⊢
    exact ⟨m.1.le, Ne.lt_of_le ne m.2⟩

/-- The Euler-Maclaurin formula -/
theorem sum_eq_integral_add [CompleteSpace E] (fc : ContDiffOn ℝ (s + 1) f t)
    (u : UniqueDiffOn ℝ t) (abt : Icc (a : ℝ) (a + n) ⊆ t) :
    trapezoid_sum f a n = (∫ x in a..a + n, f x) +
      ∑ m ∈ Finset.range s, (-1 : ℝ) ^ m • saw (m + 2) 0 •
        (iteratedDerivWithin (m + 1) f t (a + n) - iteratedDerivWithin (m + 1) f t a) +
      (-1 : ℝ) ^ s • ∫ x in a..a + n, saw (s+1) x • iteratedDerivWithin (s+1) f t x := by
  induction' n with n h
  · simp only [trapezoid_sum_zero, CharP.cast_eq_zero, add_zero, integral_same, sub_self,
      smul_zero, Finset.sum_const_zero]
  · generalize hb : a + n = b
    have hb' : (a + n : ℝ) = b := by simp [← hb]
    have ab0 : Icc (a : ℝ) (a + n) ⊆ t := subset_trans (Icc_subset_Icc (by rfl) (by simp)) abt
    have ab1 : Icc (a + n : ℝ) (a + n + 1) ⊆ t :=
      subset_trans (Icc_subset_Icc (by simp) (by simp [add_assoc])) abt
    simp only [hb', Nat.cast_add, Nat.cast_one, ← add_assoc] at ab0 ab1 h ⊢
    simp only [trapezoid_sum_succ, ← add_assoc, Nat.cast_add_one, Int.cast_add,
      Int.cast_natCast, Int.cast_one]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := a + n),
      ← intervalIntegral.integral_add_adjacent_intervals (a := a) (b := b) (c := b + 1), h ab0]
    · simp only [presaw_iterated_by_parts (a := b) fc u ab1, ← integral_saw_eq_integral_presaw,
        smul_sub, smul_add, Finset.sum_sub_distrib, hb']
      abel
    · rw [← hb']
      exact intervalIntegrable_saw_smul (by simpa) u (by simpa only [hb'])
    · rw [← Nat.cast_one (R := ℝ)]
      exact intervalIntegrable_saw_smul (by simpa) u (by simpa only [Nat.cast_one])
    · exact (fc.continuousOn.mono (by simpa only [hb'])).intervalIntegrable_of_Icc (by linarith)
    · exact (fc.continuousOn.mono (by simpa only [hb'])).intervalIntegrable_of_Icc (by linarith)
