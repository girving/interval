module

public import Interval.EulerMaclaurin.Bernoulli
public import Interval.EulerMaclaurin.Formula

/-!
# Euler-Maclaurin formula

This lets us approximate finite sums of `C^k` functions with integrals, with known bounds on the
remainder.

The general formula, for real end points and a family of successive derivatives, is
`EulerMaclaurin.sum_Ioc_eq_integral_add_of_hasDerivWithinAt` in `Interval.EulerMaclaurin.Formula`,
stated with Mathlib's `periodizedBernoulli`. Here it is specialised to `trapezoid_sum`, the
trapezoidal rule with integer step size, and written with `saw`.
-/

@[expose] public section

open Set
open MeasureTheory (volume)
open Metric (closedBall)
open scoped Real
open scoped Topology
open intervalIntegral
noncomputable section
namespace EulerMaclaurin

/-!
### Euler-Maclaurin for a single `[a, a + 1]` interval
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → E} {t : Set ℝ} {a b c : ℤ} {s n : ℕ}

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
  have e : uIoc (a : ℝ) (a + 1) =ᵐ[volume] Ioo a (a + 1) := by
    rw [uIoc_of_le]
    · exact MeasureTheory.Ioo_ae_eq_Ioc.symm
    · simp only [(lt_add_one _).le]
  rw [← MeasureTheory.ae_restrict_iff' measurableSet_uIoc,
    MeasureTheory.Measure.restrict_congr_set e, MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with x m
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
  have i1 : IntervalIntegrable (fun x ↦ presaw (s + 1) c x •
      iteratedDerivWithin (s + 1) f t x) volume (↑a) (a + 1) :=
    intervalIntegrable_presaw_smul (s := s + 1) (c := c) fc (by linarith) u abt
  rw [eq_sub_iff_add_eq, ← intervalIntegral.integral_add i0 i1]
  set g := fun x ↦ presaw (s + 1) c x • iteratedDerivWithin s f t x
  set g' := fun x ↦ presaw s c x • iteratedDerivWithin s f t x +
    presaw (s + 1) c x • iteratedDerivWithin (s + 1) f t x
  have df : ∀ x ∈ Ioo (a : ℝ) (a + 1) \ ∅, HasDerivAt g (g' x) x := by
    intro x m
    simp only [sdiff_empty] at m
    simp only [g, g', add_comm (presaw s c _ • _) _]
    apply HasDerivAt.smul
    · exact hasDerivAt_presaw
    · have mt := abt (Ioo_subset_Icc_self m)
      apply HasDerivWithinAt.hasDerivAt
      · rw [iteratedDerivWithin_succ, hasDerivWithinAt_derivWithin_iff]
        apply (fc.contDiffWithinAt mt).differentiableWithinAt_iteratedDerivWithin
        · simp only [← Nat.cast_add_one, Nat.cast_lt, Nat.lt_add_one]
        · simp only [mt, insert_eq_of_mem, u]
      · exact Filter.monotone_mem (subset_trans Ioo_subset_Icc_self abt) (isOpen_Ioo.mem_nhds m)
  refine Eq.trans (MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (f := g) (f' := g') (Hd := df) (by linarith) countable_empty ?_ ?_) ?_
  · apply contDiff_presaw.continuous.continuousOn.smul
    exact (fc.continuousOn_iteratedDerivWithin le_self_add u).mono abt
  · exact i0.add i1
  · simp only [g]

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
    simp only [(by omega : s + 1 + 1 = s + 2), presaw_coe_same, Nat.reduceAdd, presaw_coe_succ, ←
      smul_sub]

end EulerMaclaurin

/-!
### The full Euler-Maclaurin formula
-/

open EulerMaclaurin
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → E} {t : Set ℝ} {a b c : ℤ} {s n : ℕ}

/-- `saw s` is Mathlib's periodized Bernoulli polynomial divided by `s !` -/
lemma saw_eq_periodizedBernoulli (s : ℕ) (x : ℝ) :
    saw s x = (s.factorial : ℝ)⁻¹ * periodizedBernoulli s x := by
  simp only [saw, periodizedBernoulli_coe, smul_eq_mul]

/-- Trapezoidal sum: the trapezoidal rule for integer step size on `[a, a + n]` -/
def trapezoid_sum (f : ℝ → E) (a : ℤ) : ℕ → E
  | 0 => 0
  | n + 1 => trapezoid_sum f a n + (2⁻¹ : ℝ) • (f (a + n) + f (a + n + 1))

-- Definitions as accessible lemmas
@[simp] lemma trapezoid_sum_zero : trapezoid_sum f a 0 = 0 := rfl
lemma trapezoid_sum_succ :
    trapezoid_sum f a (n + 1) = trapezoid_sum f a n + (2⁻¹ : ℝ) • (f (a + n) + f (a + n + 1)) :=
  rfl

/-- The trapezoidal sum is the sum over the integers in `(a, a + n]`, corrected by half the
difference of the values at the end points -/
lemma trapezoid_sum_eq_sum_Ioc (f : ℝ → E) (a : ℤ) (n : ℕ) :
    trapezoid_sum f a n = ∑ i ∈ Finset.Ioc a (a + n), f i - (2⁻¹ : ℝ) • (f (a + n) - f a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hI : Finset.Ioc a (a + ((n + 1 : ℕ) : ℤ)) = insert (a + n + 1) (Finset.Ioc a (a + n)) := by
      ext i
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have e1 : (a : ℝ) + ((n + 1 : ℕ) : ℝ) = (a : ℝ) + n + 1 := by push_cast; ring
    have e2 : ((a + n + 1 : ℤ) : ℝ) = (a : ℝ) + n + 1 := by push_cast; ring
    have hn : a + n + 1 ∉ Finset.Ioc a (a + n) := by
      simp only [Finset.mem_Ioc]
      omega
    rw [trapezoid_sum_succ, ih, hI, Finset.sum_insert hn, e1, e2]
    module

lemma ae_ne {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    [MeasureTheory.NullSingletonClass μ] (x : α) : ∀ᵐ y ∂μ, y ≠ x := by
  simp only [Filter.Eventually, ne_eq, MeasureTheory.mem_ae_iff, compl_ne_eq_singleton,
    MeasureTheory.measure_singleton]

lemma intervalIntegrable_saw_smul (fc : ContDiffOn ℝ s f t) (u : UniqueDiffOn ℝ t)
    (abt : Icc (a : ℝ) (a + n) ⊆ t) :
    IntervalIntegrable (fun x ↦ saw s x • iteratedDerivWithin s f t x)
      volume a (a + n) := by
  have hc : IntervalIntegrable (iteratedDerivWithin s f t) volume a (a + n) :=
    ((fc.continuousOn_iteratedDerivWithin le_rfl u).mono abt).intervalIntegrable_of_Icc (by simp)
  simpa only [Pi.smul_def, saw_eq_periodizedBernoulli, mul_smul] using
    (hc.periodizedBernoulli_smul (k := s)).smul ((s.factorial : ℝ)⁻¹)

/-- The Euler-Maclaurin formula for a family of successive derivatives: `F (k + 1)` is a derivative
of `F k` within `[a, a + n]` for `k ≤ s`, and `F (s + 1)` is interval integrable -/
theorem trapezoid_sum_eq_integral_add_of_hasDerivWithinAt [CompleteSpace E] {F : ℕ → ℝ → E}
    (hF : ∀ k < s + 1, ∀ x ∈ Icc (a : ℝ) (a + n),
      HasDerivWithinAt (F k) (F (k + 1) x) (Icc (a : ℝ) (a + n)) x)
    (hFs : IntervalIntegrable (F (s + 1)) volume a (a + n)) :
    trapezoid_sum (F 0) a n = (∫ x in a..a + n, F 0 x) +
      ∑ m ∈ Finset.range s, (-1 : ℝ) ^ m • saw (m + 2) 0 • (F (m + 1) (a + n) - F (m + 1) a) +
      (-1 : ℝ) ^ s • ∫ x in a..a + n, saw (s + 1) x • F (s + 1) x := by
  -- Start from the formula for integer end points, which is stated with `periodizedBernoulli`
  have hF' : ∀ k < s + 1, ∀ x ∈ Icc (a : ℝ) ((a + n : ℤ) : ℝ),
      HasDerivWithinAt (F k) (F (k + 1) x) (Icc (a : ℝ) ((a + n : ℤ) : ℝ)) x := by
    simpa only [Int.cast_add, Int.cast_natCast] using hF
  have hFs' : IntervalIntegrable (F (s + 1)) volume (a : ℝ) ((a + n : ℤ) : ℝ) := by
    simpa only [Int.cast_add, Int.cast_natCast] using hFs
  have h := EulerMaclaurin.sum_Ioc_int_eq_integral_add_of_hasDerivWithinAt (p := s + 1) (a := a)
    (b := a + n) (Nat.succ_ne_zero s) (by omega) hF' hFs'
  simp only [Int.cast_add, Int.cast_natCast] at h
  -- The term `k = 0` of the boundary sum cancels the correction in `trapezoid_sum_eq_sum_Ioc`,
  -- and the term `k = m + 1` is the term `m` of the sum over `saw`
  have hsum : ∑ k ∈ Finset.range (s + 1),
        ((bernoulli' (k + 1) : ℝ) / ((k + 1).factorial : ℝ)) • (F k (a + n) - F k a) =
      ∑ m ∈ Finset.range s, (-1 : ℝ) ^ m • saw (m + 2) 0 • (F (m + 1) (a + n) - F (m + 1) a) +
        (2⁻¹ : ℝ) • (F 0 (a + n) - F 0 a) := by
    rw [Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl fun m _ ↦ ?_
      have hc : ((bernoulli' (m + 1 + 1) : ℝ) / ((m + 1 + 1).factorial : ℝ)) =
          (-1 : ℝ) ^ m * saw (m + 2) 0 := by
        rw [show m + 2 = m + 1 + 1 from rfl, saw_eval_zero, bernoulli'_eq_bernoulli]
        push_cast
        ring
      rw [hc, mul_smul]
    · have h2 : ((bernoulli' 1 : ℚ) : ℝ) = 2⁻¹ := by norm_num [bernoulli'_one]
      simp only [zero_add, h2, Nat.factorial_one, Nat.cast_one, div_one]
  -- The remainder: `saw (s + 1)` is `periodizedBernoulli (s + 1)` divided by `(s + 1) !`
  have hrem : ∫ x in (a : ℝ)..a + n, saw (s + 1) x • F (s + 1) x =
      ((s + 1).factorial : ℝ)⁻¹ •
        ∫ t in (a : ℝ)..a + n, periodizedBernoulli (s + 1) t • F (s + 1) t := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    simp only [saw_eq_periodizedBernoulli, mul_smul]
  have hT := trapezoid_sum_eq_sum_Ioc (F 0) a n
  linear_combination (norm := module) hT + h + hsum - (-1 : ℝ) ^ s • hrem

/-- The Euler-Maclaurin formula -/
theorem trapezoid_sum_eq_integral_add [CompleteSpace E] (fc : ContDiffOn ℝ (s + 1) f t)
    (u : UniqueDiffOn ℝ t) (abt : Icc (a : ℝ) (a + n) ⊆ t) :
    trapezoid_sum f a n = (∫ x in a..a + n, f x) +
      ∑ m ∈ Finset.range s, (-1 : ℝ) ^ m • saw (m + 2) 0 •
        (iteratedDerivWithin (m + 1) f t (a + n) - iteratedDerivWithin (m + 1) f t a) +
      (-1 : ℝ) ^ s • ∫ x in a..a + n, saw (s+1) x • iteratedDerivWithin (s+1) f t x := by
  have fc' : ContDiffOn ℝ ((s + 1 : ℕ) : WithTop ℕ∞) f t := fc
  have h := trapezoid_sum_eq_integral_add_of_hasDerivWithinAt (s := s) (a := a) (n := n)
    (F := fun k ↦ iteratedDerivWithin k f t)
    (fun k hk x hx ↦
      (fc'.hasDerivWithinAt_iteratedDerivWithin (by exact_mod_cast hk) u (abt hx)).mono abt)
    (((fc'.continuousOn_iteratedDerivWithin le_rfl u).mono abt).intervalIntegrable_of_Icc
      (by simp))
  simpa only [iteratedDerivWithin_zero] using h
