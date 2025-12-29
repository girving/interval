import Interval.EulerMaclaurin.DerivUnderIntegral
import Interval.EulerMaclaurin.IteratedDerivArith
import Interval.EulerMaclaurin.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Cases

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

/-- Bernoulli polys have mean `n = 0` -/
lemma mean_bernoulliFun (s : ℕ) :
    ∫ x in (0 : ℝ)..1, bernoulliFun s x = if s = 0 then 1 else 0 := by
  induction' s with s _
  · simp only [bernoulliFun_zero, integral_const, sub_zero, smul_eq_mul, mul_one, ↓reduceIte]
  · apply integral_bernoulliFun_eq_zero
    omega

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

@[simp] lemma bernoulli_odd_eq_zero {s : ℕ} (s0 : s ≠ 0) : bernoulli (2 * s + 1) = 0 := by
  rw [bernoulli, bernoulli'_eq_zero_of_odd]
  all_goals simp; try omega

/-- The values at 0 and 1 match for `2 ≤ s` -/
lemma bernoulliPoly_one_eq_zero (s : ℕ) : bernoulliFun (s + 2) 1 = bernoulliFun (s + 2) 0 := by
  simp only [bernoulliFun_eval_one, bernoulliFun_eval_zero, Nat.reduceEqDiff, ↓reduceIte, add_zero]

/-!
### Multiplication theorem
-/

lemma integrable_bernoulliFun {s : ℕ} {a b : ℝ} :
    IntervalIntegrable (bernoulliFun s) volume a b := by
  apply (contDiff_bernoulliFun _).continuous.intervalIntegrable

lemma integrable_bernoulliFun_comp_add_right {s : ℕ} {a b c : ℝ} :
    IntervalIntegrable (fun x ↦ bernoulliFun s (x + c)) volume a b := by
  apply Continuous.intervalIntegrable
  continuity

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
  exact ((contDiff_bernoulliFun _).comp (contDiff_id.sub contDiff_const)).const_smul _

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
  obtain ⟨z, m, r⟩ := exists_hasDerivAt_eq_zero xy
      (contDiff_bernoulliFun _).continuous.continuousOn e
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
  refine add_le_add_left ?_ _
  refine le_trans (Set.encard_union_le _ _) ?_
  refine add_le_add_right ?_ _
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
      refine pres_eq_zero (by norm_num) r ?_ (bernoulliFun_eval_half_eq_zero _)
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
