import Interval.Floating.Log2
import Interval.Interval.Log2
import Interval.Interval.Scale
import Interval.Interval.Series

/-!
## Interval logarithm
-/

open Set
open scoped Real

/-!
### `log (1 + x)` for small `x` via series

Our series for `log (1 + x)` is not very good: see
https://en.wikipedia.org/wiki/Natural_logarithm#Series for a better one with exponent
`(x / (x + 2)) ^ 2`.  We can switch to that later if desired.
-/

/-- `log1p_div_series` will be accurate on `[-1/3 - ε, 1/3 + ε]` -/
def log_series_radius : ℚ := 1/3 + 1/10000

/-- `log (1 + x) / x`, with the singularity removed -/
noncomputable def log1p_div (x : ℝ) : ℝ := if x = 0 then 1 else Real.log (1 + x) / x

/-- The defining property of `log1p_div` -/
@[simp] lemma mul_log1p_div {x : ℝ} : x * log1p_div x = Real.log (1 + x) := by
  simp only [log1p_div]
  by_cases x0 : x = 0
  · simp only [x0, add_zero, Real.log_one, div_zero, ite_true, mul_one]
  · simp only [x0, ite_false, mul_div_cancel₀ _ x0]

/-- Exact precision series for `log1p_div` -/
lemma log1p_div_bound {x : ℝ} (x1 : |x| < 1) (n : ℕ) :
    |log1p_div x - ∑ k in Finset.range n, (-1)^k / (k + 1) * x^k| ≤ |x| ^ n / (1 - |x|) := by
  by_cases x0 : x = 0
  · simp only [log1p_div, x0, add_zero, Real.log_one, div_zero, ite_true, abs_zero, sub_zero,
      div_one]
    induction' n with n _
    · simp only [Nat.zero_eq, Finset.range_zero, Finset.sum_empty, sub_zero, abs_one, pow_zero,
        le_refl]
    · simp only [Finset.sum_range_succ', Nat.cast_add, Nat.cast_one, ne_eq, add_eq_zero,
        one_ne_zero, and_false, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero,
        pow_zero, CharP.cast_eq_zero, zero_add, div_self, mul_one, sub_self, abs_zero,
        Nat.succ_ne_zero, le_refl]
  · have n1 : |-x| < 1 := by simpa only [abs_neg] using x1
    have h := Real.abs_log_sub_add_sum_range_le n1 n
    have e : Real.log (1 + x) = x * log1p_div x := by
      simp only [log1p_div, x0, ite_false, mul_comm x, div_mul_cancel₀ _ x0]
    simp only [pow_succ, neg_mul, neg_div] at h
    simp only [mul_comm, neg_mul, neg_div, mul_div_assoc, Finset.sum_neg_distrib, sub_neg_eq_add,
      add_comm _ (Real.log _), ←sub_eq_add_neg, abs_neg] at h
    rw [←Finset.mul_sum] at h
    simp only [e, ←mul_sub, abs_mul, mul_le_mul_iff_of_pos_left (abs_pos.mpr x0), neg_pow x] at h
    simpa only [mul_comm_div, ←mul_div_assoc]

/-- A power series approximation for `log1p_div` -/
@[irreducible] def log1p_div_series (n : ℕ) : Series where
  radius := .ofRat log_series_radius false
  coeffs := (Array.range n).map (fun n : ℕ ↦ .ofRat ((-1)^n / (n + 1)))
  error := .ofRat (log_series_radius ^ n / (1 - log_series_radius)) true

/-- Our power series for `log1p_div` is correct -/
lemma approx_log1p_div_series (n : ℕ) : log1p_div ∈ approx (log1p_div_series n) := by
  have nn : (log1p_div_series n).coeffs.size = n := by
    rw [log1p_div_series, Array.size_map, Array.size_range]
  have r0 : 0 ≤ log_series_radius := by rw [log_series_radius]; norm_num
  have r1 : 0 < 1 - (log_series_radius : ℝ) := by rw [log_series_radius]; norm_num
  apply (log1p_div_series n).approx_of_taylor (a := fun n ↦ (-1)^n / (n + 1))
      (b := log_series_radius ^ n / (1 - log_series_radius))
  · intro rn x xr
    rw [log1p_div_series] at xr rn; simp only at xr
    have xr' : |x| ≤ log_series_radius := le_trans xr (Floating.ofRat_le rn)
    have x1 : |x| < 1 := by
      simp only [log_series_radius] at xr'
      exact lt_of_le_of_lt xr' (by norm_num)
    simp only [nn]
    exact le_trans (log1p_div_bound x1 n) (by gcongr)
  · intro ⟨k,kn⟩
    have e : (-1 : ℝ) ^ k / (k + 1) = ↑((-1) ^ k / (↑k + 1) : ℚ) := by
      simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_add,
        Rat.cast_natCast]
    simp only [log1p_div_series, Array.getElem_map, Array.range_getElem, e]
    apply Interval.approx_ofRat
  · intro en
    simp only [log1p_div_series] at en ⊢
    refine le_trans (le_of_eq ?_) (Floating.le_ofRat en)
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_one]

/-- `approx` friendly version of `approx_log1p_div_series` -/
@[approx] lemma mem_approx_log1p_div_series {a : ℝ} {x : Interval} (ax : a ∈ approx x) {n : ℕ} :
    log1p_div a ∈ approx ((log1p_div_series n).eval x) :=
  approx_log1p_div_series n a x ax

/-- The series for `log1p_div` converges very slowly, so we need ~38 terms -/
@[irreducible] def log1p_div_series_38 := log1p_div_series 38

/-!
### `log x` for arbitrary `x`, via argument reduction

We choose `n` s.t. `x = (1 + y) * 2^n` has `y ∈ [-1/3, 1/3]`.  Then `log x = log y + n log 2`,
and we can compute `log (1 + y)` via our series.  The surprisingly awkward part is the final
addition, since `n` might be big.  For now, we choose extreme laziness and require the user to
set the final precision.
-/

/-- Untrusted 4/3 approximation -/
@[irreducible] def untrusted_four_thirds : Floating := .ofRat (4/3) false

/-- Choose `n` s.t. `x * 2^-n ∈ [2/3, 4/3]`.  We don't trust the output of this routine for
    our conservativeness results. -/
@[irreducible] def Floating.untrusted_log_shift (x : Floating) : Fixed 0 :=
  -- we make an initial guess that puts us in [1,2], then add 1 if we're not small enough
  let g := x.log2
  let y := x.scaleB' (-g)
  bif y ≤ untrusted_four_thirds then g else g+1

/-- `log x` for arbitrary `x`, via argument reduction -/
@[irreducible] def Floating.log (x : Floating) : Interval :=
  bif x ≤ 0 then nan else
  let n := x.untrusted_log_shift
  let y := ((x : Interval).scaleB' (-n)) - 1
  y * log1p_div_series_38.eval y + Interval.log_two.mul_float n

/-- `log x` for arbitrary `x`, via argument reduction -/
@[irreducible] def Interval.log (x : Interval) : Interval :=
  x.lo.log ∪ x.hi.log

/-- `Floating.log` is conservative -/
@[approx] lemma Floating.mem_approx_log {x : Floating} {x' : ℝ} (xm : x' ∈ approx x) :
    Real.log x' ∈ approx x.log := by
  rw [Floating.log, log1p_div_series_38]
  generalize x.untrusted_log_shift = n
  simp only [bif_eq_if]
  by_cases x0 : x.val ≤ 0
  · simp only [val_le_val, val_zero, x0, decide_true, ite_true, Interval.approx_nan, mem_univ]
  simp only [val_le_val, val_zero, x0, decide_false, ite_false, Bool.false_eq_true]
  simp only [not_le] at x0
  simp only [approx_eq_singleton (Floating.ne_nan_of_nonneg x0.le), mem_singleton_iff] at xm
  simp only [xm]; clear xm x'
  generalize hy : (x : Interval).scaleB' (-n) - 1 = y
  generalize hy' : x.val * 2^(-n.val) - 1 = y'
  have e : Real.log x.val = y' * log1p_div y' +  Real.log 2 * n.val := by
    simp only [← hy', mul_log1p_div, add_sub_cancel]
    rw [Real.log_mul x0.ne' (Real.rpow_pos_of_pos (by norm_num) _).ne', Real.log_rpow (by norm_num)]
    ring
  have ym : y' ∈ approx y := by
    rw [←hy, ←hy']
    approx
  rw [e]
  approx

/-- `Floating.log` turns nonpositives to `nan` -/
@[simp] lemma Floating.log_nonpos {x : Floating} (x0 : x.val ≤ 0) : x.log = nan := by
  rw [Floating.log]
  simp only [val_le_val, val_zero, Bool.cond_decide, ite_eq_left_iff, not_le, not_lt.mpr x0,
    IsEmpty.forall_iff]

/-- `Floating.log` propagates `nan` -/
@[simp] lemma Floating.log_nan : (nan : Floating).log = nan :=
  log_nonpos val_nan_lt_zero.le

/-- `Interval.log` is conservative (`⊆` version) -/
@[approx] lemma Interval.approx_log {x : Interval} : Real.log '' approx x ⊆ approx x.log := by
  rw [Interval.log]
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ x.lo.val ≤ 0
  · rcases n with n | n | n; repeat simp [n]
  simp only [not_or, not_le, Ne] at n
  rcases n with ⟨ln,hn,l0⟩
  have e : approx x = Icc x.lo.val x.hi.val := by simp only [approx, ln, hn, false_or, if_false]
  have le : Real.log '' Icc x.lo.val x.hi.val ⊆ Icc (Real.log x.lo.val) (Real.log x.hi.val) := by
    simp only [image_subset_iff]
    intro a ⟨m0,m1⟩
    simp only [mem_preimage, mem_Icc]
    exact ⟨Real.log_le_log l0 m0, Real.log_le_log (by linarith) m1⟩
  rw [e]
  refine subset_trans le (Icc_subset_approx ?_ ?_)
  · apply Interval.approx_union_left; approx
  · apply Interval.approx_union_right; approx

/-- `Interval.log` is conservative (`∈` version) -/
@[approx] lemma Interval.mem_approx_log {x : Interval} {a : ℝ} (ax : a ∈ approx x) :
    Real.log a ∈ approx x.log :=
  Interval.approx_log (mem_image_of_mem _ ax)

/-- `Interval.log` turns nonpositives to `nan` -/
@[simp] lemma Interval.log_nonpos {x : Interval} {a : ℝ} (a0 : a ≤ 0) (ax : a ∈ approx x) :
    x.log = nan := by
  rw [Interval.log]
  by_cases n : x.lo = nan ∨ x.hi = nan
  · rcases n with n | n; repeat simp [n]
  · rcases not_or.mp n with ⟨n0,n1⟩
    simp only [approx, ne_eq, neg_neg, n0, not_false_eq_true, n1, or_self, ite_false, mem_Icc] at ax
    have l0 : x.lo.val ≤ 0 := by linarith
    simp only [Floating.log_nonpos l0, Interval.nan_union]
