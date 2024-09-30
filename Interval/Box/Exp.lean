import Interval.Box.Basic
import Interval.Interval.Exp
import Interval.Interval.Sincos

/-!
## `Box` exponential
-/

open Pointwise
open Set
open scoped Real

variable {w : ℂ} {z : Box}

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

@[approx] lemma Interval.mem_approx_cis {s : ℝ} {t : Interval} (st : s ∈ approx t) :
    (s * Complex.I).exp ∈ approx t.cis := by
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos, Interval.cis]
  rw [Box.mem_approx_iff_ext]
  simp [Complex.exp_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  approx

@[approx] lemma Box.mem_approx_exp (wz : w ∈ approx z) : w.exp ∈ approx z.exp := by
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos, exp, Interval.cis]
  rw [mem_approx_iff_ext] at wz ⊢
  simp [Complex.exp_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  approx

@[approx] lemma Box.mem_approx_sin (wz : w ∈ approx z) : w.sin ∈ approx z.sin := by
  rw [Complex.sin_eq, sin, Complex.cosh, Complex.sinh]
  rw [mem_approx_iff_ext] at wz ⊢
  simp only [Complex.add_re, Complex.mul_re, Complex.sin_ofReal_re, Complex.div_ofNat_re,
    Complex.exp_ofReal_re, Complex.sin_ofReal_im, Complex.div_ofNat_im, Complex.add_im,
    Complex.exp_ofReal_im, zero_add, zero_mul, sub_zero, Complex.cos_ofReal_re, Complex.sub_re,
    Complex.cos_ofReal_im, Complex.sub_im, zero_sub, Complex.I_re, mul_zero, Complex.mul_im,
    add_zero, Complex.I_im, mul_one, ← Complex.ofReal_neg, zero_div]
  approx

@[approx] lemma Box.mem_approx_cos (wz : w ∈ approx z) : w.cos ∈ approx z.cos := by
  rw [Complex.cos_eq, cos, Complex.cosh, Complex.sinh]
  rw [mem_approx_iff_ext] at wz ⊢
  simp only [Complex.add_re, Complex.mul_re, Complex.sin_ofReal_re, Complex.div_ofNat_re,
    Complex.exp_ofReal_re, Complex.sin_ofReal_im, Complex.div_ofNat_im, Complex.add_im,
    Complex.exp_ofReal_im, zero_add, zero_mul, sub_zero, Complex.cos_ofReal_re, Complex.sub_re,
    Complex.cos_ofReal_im, Complex.sub_im, zero_sub, Complex.I_re, mul_zero, Complex.mul_im,
    add_zero, Complex.I_im, mul_one, ← Complex.ofReal_neg, zero_div, ← neg_mul]
  approx

@[approx] lemma Box.mem_approx_sinh (wz : w ∈ approx z) : w.sinh ∈ approx z.sinh := by
  have e : w = w / Complex.I * Complex.I := by simp [mul_assoc]
  rw [e, Complex.sinh_mul_I, sinh]; approx

@[approx] lemma Box.mem_approx_cosh (wz : w ∈ approx z) : w.cosh ∈ approx z.cosh := by
  rw [← Complex.cos_mul_I, cosh]; approx

@[simp] lemma Interval.cis_nan : (nan : Interval).cis = ⟨pm1, pm1⟩ := by
  rw [cis]; simp
