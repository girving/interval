import Interval.Interval.Mul
import Interval.Misc.Array

/-!
## Function approximation via `Interval` power series
-/

open BigOperators
open Set
open scoped Real

/-!
### Sums of Taylor series
-/

/-- Sum an `Interval` Taylor series, spitting out `x^n` and the result.
    For now, we use a slow linear loop. We add smaller terms together first to improve precision. -/
def taylor_sum' (c : Array Interval) (x p e : Interval) (offset steps : ℕ)
    (_ : offset + steps ≤ c.size) : Interval :=
  match steps with
  | 0 => e
  | steps+1 => c[offset]'(by omega) * p + taylor_sum' c x (p * x) e (offset+1) steps (by omega)

/-- Sum an `Interval` Taylor series -/
@[irreducible] def taylor_sum (c : Array Interval) (x e : Interval) : Interval :=
  taylor_sum' c x 1 e 0 c.size (by omega)

/-- `taylor_sum'` is conservative -/
lemma approx_taylor_sum' (c : Array Interval) (c' : ℕ → ℝ) (x p e : Interval) (x' p' e' : ℝ)
    (offset steps : ℕ) (os : offset + steps ≤ c.size)
    (ac : ∀ k : Fin c.size, approx c[k] (c' k))
    (xx : approx x x') (pp : approx p p') (ee : approx e e') :
    approx (taylor_sum' c x p e offset steps os)
      (∑ k ∈ Finset.range steps, c' (offset + k) * p' * x' ^ k + e') := by
  induction' steps with steps h generalizing p p' offset
  · simp only [Finset.range_zero, Finset.sum_empty, taylor_sum', zero_add]
    approx
  · simp only [Finset.sum_range_succ', pow_zero, mul_one, add_zero, add_comm (Finset.sum _ _), ←
    add_assoc, pow_succ, add_right_comm _ _ (1 : ℕ), taylor_sum']
    simp only [add_assoc _ _ e']
    apply approx_add (approx_mul (ac ⟨offset, by omega⟩) pp)
    specialize h (p * x) (p' * x') (offset + 1) (by omega) (by approx)
    simp only [mul_assoc, mul_comm (x' ^ _)] at h ⊢
    exact h

/-- `taylor_sum` is conservative -/
lemma approx_taylor_sum (c : Array Interval) (c' : ℕ → ℝ) (x e : Interval) (x' e' : ℝ)
    (ac : ∀ k : Fin c.size, approx c[k] (c' k)) (xx : approx x x') (ee : approx e e') :
    approx (taylor_sum c x e) (∑ k ∈ Finset.range c.size, c' k * x' ^ k + e') := by
  have h := approx_taylor_sum' c c' x 1 e x' 1 e' 0 c.size (by omega) ac xx (by approx) ee
  simp only [zero_add, mul_one] at h
  rw [taylor_sum]
  exact h

/-- `taylor_sum'` propagates `nan` -/
@[simp] lemma taylor_sum_nan' (c : Array Interval) (x p : Interval) (offset steps : ℕ)
    (h : offset + steps ≤ c.size) : taylor_sum' c x p nan offset steps h = nan := by
  induction' steps with steps n generalizing p offset
  · simp [taylor_sum']
  · rw [taylor_sum', n _ _ (by omega), Interval.add_nan]

/-- `taylor_sum` propagates `nan` -/
@[simp] lemma taylor_sum_nan (c : Array Interval) (x : Interval) : taylor_sum c x nan = nan := by
  rw [taylor_sum]; simp

/-!
### Generic `Series` machinery
-/

/-- A power series approximation within an interval `[-r,r]` around `0` -/
structure Series where
  /-- Lower bound on the radius of accuracy -/
  radius : Floating
  /-- Power series coefficients -/
  coeffs : Array Interval
  /-- Upper bound on the error within `[-r,r]` -/
  error : Floating

/-- Evaluation of a `Series` at a point.  For now, we use a slow linear loop. -/
@[irreducible] def Series.eval (p : Series) (x : Interval) : Interval :=
  let a := x.abs
  bif a.hi == nan || p.radius < a.hi then nan else
  taylor_sum p.coeffs x ((0 : Interval).grow p.error)

/-- `Series` objects approximate functions -/
instance : Approx Series (ℝ → ℝ) where
  approx p f := ∀ (x : ℝ) (y : Interval), approx y x → approx (p.eval y) (f x)

/-- `Series.eval` propagates `nan` -/
@[simp] lemma Series.eval_nan {p : Series} : p.eval (nan : Interval) = nan := by
  rw [Series.eval]
  simp only [Interval.abs_nan, Interval.hi_nan, beq_self_eq_true, Bool.true_or, cond_true]

/-- `Approx` proof given an effective Taylor series bound -/
lemma Series.approx_of_taylor' (p : Series) (f : ℝ → ℝ) (a : ℕ → ℝ) (b : ℝ) (x : ℝ) (y : Interval)
    (pf : p.radius ≠ nan → |x| ≤ p.radius.val →
      |f x - ∑ n ∈ Finset.range p.coeffs.size, a n * x ^ n| ≤ b)
    (ac : ∀ n : Fin p.coeffs.size, approx p.coeffs[n.1] (a n))
    (be : p.error ≠ nan → b ≤ p.error.val)
    (xy : approx y x) :
    approx (p.eval y) (f x) := by
  by_cases n : y.abs = nan ∨ p.radius < y.abs.hi
  · rw [Series.eval]
    rcases n with yn | ry
    · simp only [yn, Interval.hi_nan, BEq.rfl, Floating.val_lt_val, Floating.not_lt_nan_val,
        decide_false, Bool.or_false, cond_true, approx_nan]
    · simp only [ry, decide_true, Bool.or_true, cond_true, approx_nan]
  simp only [not_or, not_lt, Floating.val_le_val] at n
  rcases n with ⟨yn, ry⟩
  have yn' : y ≠ nan := by simpa only [ne_eq, Interval.abs_eq_nan] using yn
  have rn : p.radius ≠ nan := Floating.ne_nan_of_le (y.abs.hi_ne_nan yn) ry
  have xa : |x| ≤ p.radius.val := by
    have a := Interval.approx_abs xy
    simp only [approx, Interval.lo_eq_nan, yn, false_or] at a
    exact le_trans a.2 ry
  specialize pf rn xa
  simp only [eval, bif_eq_if, Floating.val_lt_val, not_lt.mpr ry, decide_false, Bool.or_false,
    beq_iff_eq, Interval.hi_eq_nan, Interval.abs_eq_nan, yn', ite_false]
  rw [← add_sub_cancel (∑ n ∈ Finset.range p.coeffs.size, a n * x ^ n) (f x)]
  apply approx_taylor_sum _ _ _ _ _ _ ac xy
  rw [← sub_zero (f x - ∑ n ∈ Finset.range p.coeffs.size, a n * x ^ n)] at pf
  exact Interval.approx_grow pf be (by approx)

/-- `Approx` proof given an effective Taylor series bound -/
lemma Series.approx_of_taylor (p : Series) (f : ℝ → ℝ) (a : ℕ → ℝ) (b : ℝ)
    (pf : p.radius ≠ nan → ∀ x : ℝ,
      |x| ≤ p.radius.val → |f x - ∑ n ∈ Finset.range p.coeffs.size, a n * x ^ n| ≤ b)
    (ac : ∀ n : Fin p.coeffs.size, approx p.coeffs[n.1] (a n))
    (be : p.error ≠ nan → b ≤ p.error.val) :
    approx p f := by
  intro x y xy
  exact approx_of_taylor' p f a b x y (fun n ↦ pf n x) ac be xy
