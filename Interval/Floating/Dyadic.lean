import Interval.Floating.Basic

/-!
# Conversion between `Dyadic` and `Floating`
-/

/-- The exact `Dyadic` that a `Floating` represents -/
def Floating.vald (x : Floating) : Dyadic :=
  Dyadic.ofIntWithPrec x.n (2 ^ 63 - x.s.toInt)

@[simp] lemma Floating.toRat_vald (x : Floating) : x.vald.toRat = x.valq := by
  simp only [vald, valq, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, neg_sub]
