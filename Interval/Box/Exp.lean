import Interval.Box.Basic
import Interval.Interval.Exp
import Interval.Interval.Sincos

/-!
## `Box` exponential and friends
-/

open Pointwise
open Set
open scoped Real

variable {z : Box} {z' : ℂ}
variable {t : Interval} {t' : ℝ}

/-- `exp (t * I)` -/
@[irreducible] def Interval.cis (t : Interval) : Box := ⟨t.cos, t.sin⟩

/-- `exp z` -/
@[irreducible] def Box.exp (z : Box) : Box := z.re.exp • z.im.cis

/-- `sin z` -/
@[irreducible] def Box.sin (z : Box) : Box :=
  let a := z.im.exp
  let b := (-z.im).exp
  ⟨z.re.sin * (a + b).div2, z.re.cos * (a - b).div2⟩

/-- `cos z` -/
@[irreducible] def Box.cos (z : Box) : Box :=
  let a := z.im.exp
  let b := (-z.im).exp
  ⟨z.re.cos * (a + b).div2, -z.re.sin * (a - b).div2⟩

-- Hyperbolic `sin` and `cos`
@[irreducible] def Box.sinh (z : Box) : Box := z.div_I.sin.mul_I
@[irreducible] def Box.cosh (z : Box) : Box := z.mul_I.cos

@[approx] lemma Interval.approx_cis (m : approx t t') : approx t.cis (t' * Complex.I).exp := by
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos, Interval.cis]
  rw [Box.approx_iff_ext]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  approx

@[approx] lemma Box.approx_exp (m : approx z z') : approx z.exp z'.exp := by
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos, exp, Interval.cis]
  rw [approx_iff_ext] at m ⊢
  simp [Complex.exp_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  approx

@[approx] lemma Box.approx_sin (m : approx z z') : approx z.sin z'.sin := by
  rw [Complex.sin_eq, sin, Complex.cosh, Complex.sinh]
  rw [approx_iff_ext] at m ⊢
  simp only [Complex.add_re, Complex.mul_re, Complex.sin_ofReal_re, Complex.div_ofNat_re,
    Complex.exp_ofReal_re, Complex.sin_ofReal_im, Complex.div_ofNat_im, Complex.add_im,
    Complex.exp_ofReal_im, zero_add, zero_mul, sub_zero, Complex.cos_ofReal_re, Complex.sub_re,
    Complex.cos_ofReal_im, Complex.sub_im, Complex.I_re, mul_zero, Complex.mul_im, add_zero,
    Complex.I_im, mul_one, ← Complex.ofReal_neg, zero_div]
  approx

@[approx] lemma Box.approx_cos (m : approx z z') : approx z.cos z'.cos := by
  rw [Complex.cos_eq, cos, Complex.cosh, Complex.sinh]
  rw [approx_iff_ext] at m ⊢
  simp only [Complex.add_re, Complex.mul_re, Complex.sin_ofReal_re, Complex.div_ofNat_re,
    Complex.exp_ofReal_re, Complex.sin_ofReal_im, Complex.div_ofNat_im, Complex.add_im,
    Complex.exp_ofReal_im, zero_mul, sub_zero, Complex.cos_ofReal_re, Complex.sub_re,
    Complex.cos_ofReal_im, Complex.sub_im, zero_sub, Complex.I_re, mul_zero, Complex.mul_im,
    add_zero, Complex.I_im, mul_one, ← Complex.ofReal_neg, zero_div, ← neg_mul]
  approx

@[approx] lemma Box.approx_sinh (m : approx z z') : approx z.sinh z'.sinh := by
  have e : z' = z' / Complex.I * Complex.I := by simp [mul_assoc]
  rw [e, Complex.sinh_mul_I, sinh]; approx

@[approx] lemma Box.approx_cosh (m : approx z z') : approx z.cosh z'.cosh := by
  rw [← Complex.cos_mul_I, cosh]; approx

@[simp] lemma Interval.cis_nan : (nan : Interval).cis = ⟨pm1, pm1⟩ := by
  rw [cis]; simp
