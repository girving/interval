module

public import Interval.Approx.Dyadic
public import Interval.Approx.Rat
public import Mathlib.Analysis.Complex.Basic

/-!
# Squared norms for series scalars
-/

@[expose] public section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

class NormSq (α : Type) where
  normSq : α → α

instance Rat.instNormSq : NormSq ℚ where normSq x := x ^ 2
instance Dyadic.instNormSq : NormSq Dyadic where normSq x := x ^ 2
lemma Rat.normSq_eq_sq (x : ℚ) : NormSq.normSq x = x ^ 2 := rfl
lemma Dyadic.normSq_eq_sq (x : Dyadic) : NormSq.normSq x = x ^ 2 := rfl

class ApproxNormSq (α 𝕜 : Type) [NormSq α] [NontriviallyNormedField 𝕜] [Approx α 𝕜]
    [Approx α ℝ] where
  approx_normSq {x : α} {x' : 𝕜} (ax : approx x x') : approx (NormSq.normSq x) (‖x'‖ ^ 2)

export ApproxNormSq (approx_normSq)
attribute [approx] approx_normSq

instance Rat.instApproxNormSq : ApproxNormSq ℚ ℂ where
  approx_normSq {x x'} ax := by
    simp only [approx] at ax
    simp only [normSq_eq_sq, ← ax, Complex.norm_ratCast, sq_abs, approx, cast_pow]

instance Dyadic.instApproxNormSq : ApproxNormSq Dyadic ℂ where
  approx_normSq {x x'} ax := by
    simp only [approx] at ax
    simp only [normSq_eq_sq, ← ax, Complex.norm_ratCast, ← abs_mul, approx, pow_two,
      Dyadic.toRat_mul]
    simp only [← pow_two, Rat.cast_pow, abs_pow, sq_abs]
