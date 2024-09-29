import Interval.Box.Basic
import Interval.Interval.Exp
import Interval.Interval.Sincos

/-!
## `Box` exponential
-/

open Pointwise
open Set
open scoped Real

/-- `exp (t * I)` -/
@[irreducible] def Interval.cis (t : Interval) : Box := ⟨t.cos, t.sin⟩

/-- `exp z` -/
@[irreducible] def Box.exp (z : Box) : Box := z.re.exp.mul_box z.im.cis

@[approx] lemma Interval.mem_approx_cis {s : ℝ} {t : Interval} (st : s ∈ approx t) :
    (s * Complex.I).exp ∈ approx t.cis := by
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos, Interval.cis]
  rw [Box.mem_approx_iff_ext]
  simp [Complex.exp_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  approx

@[approx] lemma Box.mem_approx_exp {w : ℂ} {z : Box} (wz : w ∈ approx z) :
    w.exp ∈ approx z.exp := by
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos, exp, Interval.cis]
  rw [mem_approx_iff_ext] at wz ⊢
  simp [Complex.exp_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  approx

@[simp] lemma Interval.cis_nan : (nan : Interval).cis = ⟨pm1, pm1⟩ := by
  rw [cis]; simp
