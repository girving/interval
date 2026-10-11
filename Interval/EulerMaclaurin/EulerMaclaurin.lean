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

/-!
### The full Euler-Maclaurin formula
-/

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
