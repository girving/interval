import Interval.Floating.Floor
import Interval.Interval.Log2
import Interval.Interval.Scale
import Interval.Interval.Series

/-!
## Interval exponential function
-/

open Set
open scoped Real

variable {x : Interval} {x' : ℝ}

/-!
### `exp x` for small `x` via series
-/

/-- `exp_series` will be accurate on `[-r,r]` for `r` slightly larger than `log 2 / 2`. -/
def exp_series_radius : ℚ := 0.346574

/-- A power series approximation for `exp` -/
@[irreducible] def exp_series (n : ℕ) : Series where
  radius := .ofRat exp_series_radius false
  coeffs := (Array.range n).map (fun n ↦ (((Nat.factorial n)⁻¹ : ℚ) : Interval))
  error := bif n == 0 then nan
           else .ofRat (exp_series_radius ^ n * ((n + 1) / (Nat.factorial n * n))) true

/-- Our power series for `exp` is correct -/
lemma approx_exp_series (n : ℕ) : approx (exp_series n) Real.exp := by
  have nn : (exp_series n).coeffs.size = n := by rw [exp_series, Array.size_map, Array.size_range]
  by_cases n0 : n = 0
  · intro a x _
    have e : (exp_series 0).error = nan := by
      rw [exp_series]
      simp only [beq_self_eq_true, pow_zero, CharP.cast_eq_zero, zero_add, Nat.factorial_zero,
        Nat.cast_one, mul_zero, div_zero, cond_true]
    simp only [n0, Series.eval, Floating.val_lt_val, e, Interval.grow_nan, taylor_sum_nan,
      Bool.cond_self, approx_nan]
  · apply (exp_series n).approx_of_taylor
    · intro rn x xr
      rw [exp_series] at xr rn; simp only at xr
      have xr' : |x| ≤ exp_series_radius := le_trans xr (Floating.ofRat_le rn)
      have x1 : |x| ≤ 1 := by simp only [exp_series_radius] at xr'; exact le_trans xr' (by norm_num)
      simp only [nn]
      have h := Real.exp_bound x1 (Nat.pos_iff_ne_zero.mpr n0)
      simp only [div_eq_inv_mul] at h
      exact le_trans h (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) xr' _)
        (by positivity))
    · intro k
      have e : (Nat.factorial k : ℝ)⁻¹ = (Nat.factorial k : ℚ)⁻¹ := by
        simp only [Rat.cast_inv, Rat.cast_natCast]
      simp only [exp_series, Array.getElem_map, Array.getElem_range, e]
      approx
    · intro en
      simp only [mul_inv_rev, Nat.cast_succ]
      rw [exp_series, bif_eq_if] at en ⊢
      simp only [beq_iff_eq, ne_eq, n0, if_false] at en ⊢
      refine le_trans (le_of_eq ?_) (Floating.le_ofRat en)
      simp only [div_eq_inv_mul, mul_inv, mul_comm _ ((n:ℚ)⁻¹), Rat.cast_mul, Rat.cast_pow,
        Rat.cast_inv, Rat.cast_natCast, Rat.cast_add, Rat.cast_one]

/-- `approx` friendly version of `approx_exp_series` -/
@[approx] lemma mem_approx_exp_series (ax : approx x x') {n : ℕ} :
    approx ((exp_series n).eval x) (Real.exp x') :=
  approx_exp_series n x' x ax

/-- 16 terms are about enough for 64 bits of precision -/
@[irreducible] def exp_series_16 := exp_series 16

/-!
### `exp x` for arbitrary `x`, via argument reduction

To compute `exp x`, we choose `n` s.t. `y = x - n log 2 ∈ [-log 2 / 2, log 2 / 2]`, compute `exp y`
via Taylor series, and form `exp x = exp (y + n log 2) = exp y * 2^n` via shifting.
-/

/-- `exp x` for potentially large `x`, via argument reduction -/
@[irreducible] def Floating.exp (x : Floating) : Interval :=
  bif x == nan then nan else
  -- We want
  --   `x - n log 2 ∈ [-log 2 / 2, log 2 / 2]`
  --   `x / log 2 - n ∈ [-1/2, 1/2]`
  --   `n ∈ x/log 2 + [-1/2, 1/2]`
  --   `n = floor(x/log 2 + 1/2)`
  let n := ((x.mul Floating.inv_log_two false).add (.ofRat (1/2) false) false).floor
  let y : Interval := x - Interval.log_two.mul_float n
  (exp_series_16.eval y).scaleB' n

/-- `exp x` for potentially large `x`, via argument reduction -/
@[irreducible] def Interval.exp (x : Interval) : Interval :=
  x.lo.exp ∪ x.hi.exp

/-- `Floating.exp` is conservative -/
@[approx] lemma Floating.mem_approx_exp {x : Floating} (xm : approx x x') :
    approx x.exp (Real.exp x') := by
  rw [Floating.exp]
  generalize hn : floor ((mul x Floating.inv_log_two false).add (ofRat (1 / 2) false) false) = n
  simp only [bif_eq_if, beq_iff_eq]
  by_cases xn : x = nan
  · simp only [xn, ↓reduceIte, approx_nan]
  simp only [xn, ite_false]
  have e : Real.exp x' = Real.exp (x' - Real.log 2 * n.val) * 2 ^ n.val := by
    rw [Real.exp_sub, Real.exp_mul, Real.exp_log (by norm_num),
      div_mul_cancel₀ _ (Real.rpow_pos_of_pos (by norm_num) _).ne']
  rw [e, exp_series_16]
  approx

/-- `Floating.exp` propagates `nan` -/
@[simp] lemma Floating.exp_nan : (nan : Floating).exp = nan := by
  rw [Floating.exp, exp_series_16]
  simp only [beq_self_eq_true, nan_mul, cond_true]

/-- `Interval.exp` is conservative (`⊆` version) -/
@[approx] lemma Interval.approx_exp (ax : approx x x') : approx x.exp (Real.exp x') := by
  rw [Interval.exp]
  by_cases xn : x = nan
  · simp only [xn, approx_nan, lo_nan, Floating.exp_nan, hi_nan, union_nan]
  apply approx_of_mem_Icc (a := x.lo.val.exp) (c := x.hi.val.exp)
  · apply Interval.approx_union_left; approx
  · apply Interval.approx_union_right; approx
  · simpa [mem_Icc, Real.exp_le_exp, approx, xn] using ax

/-- `Interval.exp` propagates `nan` -/
@[simp] lemma Interval.exp_nan : (nan : Interval).exp = nan := by
  rw [Interval.exp]
  simp only [lo_nan, Floating.exp_nan, hi_nan, Interval.union_nan]
