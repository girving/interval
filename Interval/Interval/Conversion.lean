import Interval.Floating.Conversion
import Interval.Interval.Basic

open Classical
open Pointwise

/-!
## Conversion to `Interval` from `ℕ`, `ℤ`, `ℚ`, and `ofScientific`
-/

open Set
open scoped Real
namespace Interval

/-- `ℕ` converts to `Interval` -/
@[coe, irreducible] def ofNat (n : ℕ) : Interval :=
  mix (.ofNat n false) (.ofNat n true) (fun _ ↦ Floating.ofNat_le_ofNat)

/-- `ℤ` converts to `Interval` -/
@[coe, irreducible] def ofInt (n : ℤ) : Interval :=
  mix (.ofInt n false) (.ofInt n true) (fun _ ↦ Floating.ofInt_le_ofInt)

/-- `ℚ` converts to `Interval` -/
@[coe, irreducible] def ofRat (x : ℚ) : Interval :=
  mix (.ofRat x false) (.ofRat x true) (fun _ ↦ Floating.ofRat_le_ofRat)

instance instNatCast : NatCast Interval where natCast := Interval.ofNat
instance instIntCast : IntCast Interval where intCast := Interval.ofInt
instance instRatCast : RatCast Interval where ratCast := Interval.ofRat
lemma natCast_def (n : ℕ) : (n : Interval) = Interval.ofNat n := rfl
lemma intCast_def (n : ℤ) : (n : Interval) = Interval.ofInt n := rfl
lemma ratCast_def (x : ℚ) : (x : Interval) = Interval.ofRat x := rfl

/-- Conversion from `ofScientific`.
    Warning: This is slow for large exponents, as it builds large `ℚ` values. -/
instance : OfScientific Interval where
  ofScientific x u t := .ofRat (OfScientific.ofScientific x u t)

/-- Conversion from `Float` -/
@[irreducible] def ofFloat (x : Float) : Interval :=
  mix (.ofFloat x false) (.ofFloat x true) Floating.ofFloat_le_ofFloat

/-- Conversion from `ℕ` literals to `Interval` -/
instance {n : ℕ} [n.AtLeastTwo] : OfNat Interval n := ⟨.ofNat n⟩

/-- `.ofNat` is conservative -/
instance : ApproxNatCast Interval ℝ where
  approx_natCast := by
    simp only [approx, or_iff_not_imp_left, natCast_def, Interval.ofNat]
    intro n m
    simp only [lo_eq_nan] at m
    simp only [lo_mix m, hi_mix m]
    simp only [mix_eq_nan, not_or] at m
    exact ⟨Floating.ofNat_le m.1, Floating.le_ofNat m.2⟩

/-- `approx_ofNat` for integer literals.
`no_index` is required because of https://github.com/leanprover/lean4/issues/2867. -/
@[approx] lemma ofNat_approx_ofNat {n : ℕ} [n.AtLeastTwo] :
    approx (Interval.ofNat (no_index (OfNat.ofNat n))) (no_index (OfNat.ofNat n) : ℝ) :=
  approx_natCast (A := Interval) (R := ℝ) (n := n)

/-- `approx_ofNat` for integer literals.
`no_index` is required because of https://github.com/leanprover/lean4/issues/2867. -/
@[approx] lemma ofNat_approx_ofNat' {n : ℕ} [n.AtLeastTwo] :
    approx (no_index (OfNat.ofNat n : Interval)) (no_index (OfNat.ofNat n) : ℝ) :=
  approx_natCast (A := Interval) (R := ℝ) (n := n)

/-- `.ofInt` is conservative -/
instance : ApproxIntCast Interval ℝ where
  approx_intCast := by
    simp only [approx, or_iff_not_imp_left, intCast_def, Interval.ofInt]
    intro n m
    simp only [lo_eq_nan] at m
    simp only [lo_mix m, hi_mix m]
    simp only [mix_eq_nan, not_or] at m
    exact ⟨Floating.ofInt_le m.1, Floating.le_ofInt m.2⟩

/-- `.ofRat` is conservative -/
instance : ApproxRatCast Interval ℝ where
  approx_ratCast := by
    simp only [approx, or_iff_not_imp_left, ratCast_def, Interval.ofRat]
    intro n m
    simp only [lo_eq_nan] at m
    simp only [lo_mix m, hi_mix m]
    simp only [mix_eq_nan, not_or] at m
    exact ⟨Floating.ofRat_le m.1, Floating.le_ofRat m.2⟩

/-- `approx_ofRat` for rational literals `a / b`.
`no_index` is required because of https://github.com/leanprover/lean4/issues/2867. -/
@[approx] lemma ofNat_div_approx_ofRat {a b : ℕ} [a.AtLeastTwo] [b.AtLeastTwo] :
    approx (Interval.ofRat (no_index (OfNat.ofNat a) / no_index (OfNat.ofNat b)))
      (no_index (OfNat.ofNat a) / no_index (OfNat.ofNat b) : ℝ) := by
  convert approx_ratCast (A := Interval) (R := ℝ) (x := a / b)
  simp only [Rat.cast_div, Rat.cast_natCast]
  rfl

/-- `approx_ofRat` for rational literals `1 / b`.
`no_index` is required because of https://github.com/leanprover/lean4/issues/2867. -/
@[approx] lemma one_div_ofNat_approx_ofRat {b : ℕ} [b.AtLeastTwo] :
    approx (Interval.ofRat (1 / no_index (OfNat.ofNat b))) (1 / no_index (OfNat.ofNat b) : ℝ) := by
  convert approx_ratCast (A := Interval) (R := ℝ) (x := 1 / b)
  simp only [one_div, Rat.cast_inv, Rat.cast_natCast]
  rfl

/-- `ofRat` conversion is conservative -/
@[approx] lemma approx_ofScientific (x : ℕ) (u : Bool) (t : ℕ) :
    approx (OfScientific.ofScientific x u t : Interval) (OfScientific.ofScientific x u t : ℝ) := by
  simp only [OfScientific.ofScientific]
  apply approx_ratCast

/-- `n.lo ≤ n` -/
lemma ofNat_le (n : ℕ) : (ofNat n).lo.val ≤ n := by
  by_cases m : ofNat n = nan
  · simp only [m, lo_nan]
    exact le_trans Floating.val_nan_lt_zero.le (Nat.cast_nonneg _)
  · have h := approx_natCast (A := Interval) (R := ℝ) (n := n)
    simp only [approx, lo_eq_nan, m, false_or, natCast_def] at h
    exact h.1

/-- `n ≤ n.hi` unless we're `nan` -/
lemma le_ofNat (n : ℕ) (m : ofNat n ≠ nan) : n ≤ (ofNat n).hi.val := by
  have h := approx_natCast (A := Interval) (R := ℝ) (n := n)
  simp only [approx, lo_eq_nan, m, false_or, natCast_def] at h
  exact h.2
