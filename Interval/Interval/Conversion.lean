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
@[irreducible] def ofNat (n : ℕ) : Interval :=
  mix (.ofNat n false) (.ofNat n true)
    (fun n0 n1 ↦ le_trans (Floating.ofNat_le n0) (Floating.le_ofNat n1))

instance instNatCastInterval : NatCast Interval where
  natCast := Interval.ofNat

/-- `ℤ` converts to `Interval` -/
@[irreducible] def ofInt (n : ℤ) : Interval :=
  mix (.ofInt n false) (.ofInt n true)
    (fun n0 n1 ↦ le_trans (Floating.ofInt_le n0) (Floating.le_ofInt n1))

instance instIntCastInterval : IntCast Interval where
  intCast := Interval.ofInt

/-- `ℚ` converts to `Interval` -/
@[irreducible] def ofRat (x : ℚ) : Interval :=
  mix (.ofRat x false) (.ofRat x true)
    (fun n0 n1 ↦ le_trans (Floating.ofRat_le n0) (Floating.le_ofRat n1))

instance instCoeRatInterval : Coe ℚ Interval where
  coe := Interval.ofRat

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
@[approx] lemma approx_ofNat (n : ℕ) : ↑n ∈ approx (Interval.ofNat n) := by
  rw [ofNat]; simp only [approx, mem_ite_univ_left, mem_Icc]
  intro m; simp only [lo_eq_nan] at m
  simp only [lo_mix m, hi_mix m]
  simp only [mix_eq_nan, not_or] at m
  exact ⟨Floating.ofNat_le m.1, Floating.le_ofNat m.2⟩

/-- `approx_ofNat` for integer literals.
`no_index` is required because of https://github.com/leanprover/lean4/issues/2867. -/
@[approx] lemma ofNat_mem_approx_ofNat {n : ℕ} [n.AtLeastTwo] :
    no_index (OfNat.ofNat n) ∈ approx (Interval.ofNat (no_index (OfNat.ofNat n))) := approx_ofNat _

/-- `approx_ofNat` for integer literals.
`no_index` is required because of https://github.com/leanprover/lean4/issues/2867. -/
@[approx] lemma ofNat_mem_approx_ofNat' {n : ℕ} [n.AtLeastTwo] :
    no_index (OfNat.ofNat n) ∈ approx (no_index (OfNat.ofNat n : Interval)) := approx_ofNat _

/-- `.ofInt` is conservative -/
@[approx] lemma approx_ofInt (n : ℤ) : ↑n ∈ approx (Interval.ofInt n) := by
  rw [ofInt]; simp only [approx, mem_ite_univ_left, mem_Icc]
  intro m; simp only [lo_eq_nan] at m
  simp only [lo_mix m, hi_mix m]
  simp only [mix_eq_nan, not_or] at m
  exact ⟨Floating.ofInt_le m.1, Floating.le_ofInt m.2⟩

/-- `.ofRat` is conservative -/
@[approx] lemma approx_ofRat (x : ℚ) : ↑x ∈ approx (Interval.ofRat x) := by
  rw [ofRat]; simp only [approx, mem_ite_univ_left, mem_Icc]
  intro m; simp only [lo_eq_nan] at m
  simp only [lo_mix m, hi_mix m]
  simp only [mix_eq_nan, not_or] at m
  exact ⟨Floating.ofRat_le m.1, Floating.le_ofRat m.2⟩

/-- `approx_ofRat` for rational literals `a / b`.
`no_index` is required because of https://github.com/leanprover/lean4/issues/2867. -/
@[approx] lemma ofNat_div_mem_approx_ofRat {a b : ℕ} [a.AtLeastTwo] [b.AtLeastTwo] :
    no_index (OfNat.ofNat a) / no_index (OfNat.ofNat b) ∈
      approx (Interval.ofRat (no_index (OfNat.ofNat a) / no_index (OfNat.ofNat b))) := by
  convert approx_ofRat _; simp only [Rat.cast_div, Rat.cast_ofNat]

/-- `approx_ofRat` for rational literals `1 / b`.
`no_index` is required because of https://github.com/leanprover/lean4/issues/2867. -/
@[approx] lemma one_div_ofNat_mem_approx_ofRat {b : ℕ} [b.AtLeastTwo] :
    1 / no_index (OfNat.ofNat b) ∈ approx (Interval.ofRat (1 / no_index (OfNat.ofNat b))) := by
  convert approx_ofRat _; simp only [one_div, Rat.cast_inv, Rat.cast_ofNat]

/-- `ofRat` conversion is conservative -/
@[approx] lemma approx_ofScientific (x : ℕ) (u : Bool) (t : ℕ) :
    OfScientific.ofScientific x u t ∈
      approx (OfScientific.ofScientific x u t : Interval) := by
  simp only [OfScientific.ofScientific]
  apply approx_ofRat

/-- `n.lo ≤ n` -/
lemma ofNat_le (n : ℕ) : (ofNat n).lo.val ≤ n := by
  by_cases m : ofNat n = nan
  · simp only [m, lo_nan]
    exact le_trans Floating.val_nan_lt_zero.le (Nat.cast_nonneg _)
  · have h := approx_ofNat n
    simp only [approx, lo_eq_nan, m, ite_false, mem_Icc] at h
    exact h.1

/-- `n ≤ n.hi` unless we're `nan` -/
lemma le_ofNat (n : ℕ) (m : ofNat n ≠ nan) : n ≤ (ofNat n).hi.val := by
  have h := approx_ofNat n
  simp only [approx, lo_eq_nan, m, ite_false, mem_Icc] at h
  exact h.2
