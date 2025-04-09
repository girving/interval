import Interval.EulerMaclaurin.Bernoulli

/-!
# Euler-Maclaurin formula

This lets us approximate finite sums of `C^k` functions with integrals, with known bounds on the
remainder.
-/

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
  have i1 : IntervalIntegrable (fun x ↦ presaw (s + 1) c x •
      iteratedDerivWithin (s + 1) f t x) volume (↑a) (a + 1) :=
    intervalIntegrable_presaw_smul (s := s + 1) (c := c) fc (by linarith) u abt
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
        apply (fc.contDiffWithinAt mt).differentiableWithinAt_iteratedDerivWithin
        · simp only [← Nat.cast_add_one, Nat.cast_lt, Nat.lt_add_one]
        · simp only [mt, insert_eq_of_mem, u]
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

end EulerMaclaurin

/-!
### The full Euler-Maclaurin formula
-/

open EulerMaclaurin
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → E} {t : Set ℝ} {a b c : ℤ} {s n : ℕ}

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
theorem trapezoid_sum_eq_integral_add [CompleteSpace E] (fc : ContDiffOn ℝ (s + 1) f t)
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
