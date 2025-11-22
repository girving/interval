import Interval.Approx.NormSq
import Interval.Interval.Conversion
import Interval.Interval.Division
import Interval.Interval.Mul
import Interval.Interval.Scale

/-!
## `Interval` also approximates `ℂ`, along the real line
-/

open Set
open Complex (I)
open scoped Real
namespace Interval

/-- `Interval` approximates `ℂ` along the real line -/
instance instApproxComplex : Approx Interval ℂ where
  approx x x' := approx x x'.re ∧ x'.im = 0

@[local simp] lemma approx_complex_iff {x : Interval} {x' : ℂ} :
    approx x x' ↔ approx x x'.re ∧ x'.im = 0 := by simp [instApproxComplex]

/-- `Interval` are real, so norm is just `sqr` -/
instance : NormSq Interval where
  normSq x := x.sqr

lemma normSq_def {x : Interval} : NormSq.normSq x = x.sqr := rfl

instance : ApproxField Interval ℂ where
  approx_zero := by simp
  approx_one := by simp
  approx_neg := by simp
  approx_add := by approx_simp
  approx_sub := by approx_simp
  approx_mul := by approx_simp
  approx_div {x y x' y'} ax ay := by
    simp only [approx_complex_iff] at ax ay ⊢
    simp only [Complex.div_re, Complex.normSq_apply, ay, mul_zero, add_zero, ax, zero_div,
      Complex.div_im, zero_mul, sub_self, and_true]
    field_simp
    approx

instance : ApproxZeroIff Interval ℂ where
  approx_zero_imp x a := by induction' x; aesop

instance : ApproxNatCast Interval ℂ where
  approx_natCast := by approx_simp

instance : ApproxDiv2 Interval ℂ where
  approx_div2 {x x'} a := by
    simp only [approx_complex_iff] at a
    simp only [div2_eq_mul, approx_complex_iff, Complex.mul_re, Complex.inv_re, Complex.re_ofNat,
      Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im, Complex.im_ofNat, neg_zero,
      zero_div, a, mul_zero, sub_zero, Complex.mul_im, zero_mul, add_zero, and_true]
    simp only [← div2_eq_mul]
    approx

instance : ApproxNormSq Interval ℂ where
  approx_normSq {x x'} a := by
    simp only [approx_complex_iff] at a
    simp [Complex.sq_norm, Complex.normSq_apply, a, normSq_def, ← pow_two]
    approx
