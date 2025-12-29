import Interval.Interval.Conversion
import Interval.Interval.Scale

/-!
# Conversion between `Dyadic` and `Interval`
-/

def Interval.ofDyadic : Dyadic → Interval
  | .zero => 0
  | .ofOdd n k _ => (n : Interval).scaleB' (-.ofInt0 k)

@[approx] lemma Interval.approx_ofDyadic (x : Dyadic) :
    approx (Interval.ofDyadic x) (x.toRat : ℝ) := by
  simp only [Interval.ofDyadic]
  cases x with
  | zero => simp
  | ofOdd n k _ =>
    have two : (2 : ℚ) = (2 : ℝ) := by norm_num
    simp only [Dyadic.ofOdd_eq_ofIntWithPrec, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow,
      Rat.cast_mul, Rat.cast_intCast, Rat.cast_zpow, two, ← Real.rpow_intCast, Int.cast_neg]
    approx
