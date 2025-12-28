import Interval.Approx.Div2
import Interval.Floating.Standardization

open Pointwise

/-!
## Floating point scaling by changing the exponent
-/

open Set
open scoped Real
namespace Floating

variable {x : Floating} {x' : ℝ}

/-- Scale by changing the exponent -/
@[irreducible] def scaleB (x : Floating) (t : Int64) : Floating :=
  bif x == 0 then 0 else
  if t < 0 then
    let t := (-t).toUInt64
    bif x.s < t then nan else of_ns x.n (x.s - t)
  else
    bif .max - t.toUInt64 < x.s then nan else of_ns x.n (x.s + t.toUInt64)

/-- Scale by changing the exponent -/
@[irreducible] def scaleB' (x : Floating) (t : Fixed 0) : Floating :=
  bif t == nan then nan else scaleB x t.n

/-- `scaleB` is conservative -/
@[approx] lemma approx_scaleB {x : Floating} (t : Int64) (xm : approx x x') :
    approx (x.scaleB t) (x' * 2^(t : ℤ)) := by
  rw [scaleB]
  have t0 : 0 < (2 : ℝ) := by norm_num
  simp only [bif_eq_if, decide_eq_true_eq, beq_iff_eq]
  by_cases xn : x = nan
  · simp [xn]
  simp only [approx_eq_singleton xn] at xm
  split_ifs with x0 t0 st st
  · simp only [← xm, x0, val_zero, zero_mul, ne_eq, zero_ne_nan, not_false_eq_true,
      approx_eq_singleton]
  · simp
  · simp only [approx, Int64.toUInt64_neg, UInt64.sub_neg, of_ns_eq_nan_iff,
      val_of_ns (x.n_ne_min xn)]
    right
    rw [← xm, val, mul_assoc, ← zpow_add₀ (by norm_num)]
    refine congr_arg₂ _ rfl (congr_arg₂ _ rfl ?_)
    generalize x.s = s at st
    induction' s using UInt64.induction_nat with s sb
    induction' t using Int64.induction_nat with t tb
    simp only [to_omega] at st t0 ⊢
    split_ifs at st t0 ⊢
    all_goals omega
  · simp only [approx_nan]
  · simp only [approx, of_ns_eq_nan_iff, val_of_ns (x.n_ne_min xn)]
    right
    rw [← xm, val, mul_assoc, ← zpow_add₀ (by norm_num)]
    refine congr_arg₂ _ rfl (congr_arg₂ _ rfl ?_)
    generalize x.s = s at st
    induction' s using UInt64.induction_nat with s sb
    induction' t using Int64.induction_nat with t tb
    simp only [to_omega] at st t0 ⊢
    split_ifs at st t0 ⊢
    all_goals omega

/-- `scaleB _ _` is exact if not `nan` -/
lemma val_scaleB {x : Floating} {t : Int64} (n : x.scaleB t ≠ nan) :
    (x.scaleB t).val = x.val * 2^(t : ℤ) := by
  simpa [approx, n, ↓reduceIte] using approx_scaleB t (approx_val (x := x))

/-- `scaleB` propagates `nan` -/
@[simp] lemma nan_scaleB {t : Int64} : (nan : Floating).scaleB t = nan := by
  rw [scaleB]
  simp only [bif_eq_if, s_nan, decide_eq_true_eq, n_nan, of_ns_nan, ite_self, beq_iff_eq,
    nan_ne_zero, ↓reduceIte]

/-- `scaleB` propagates `nan` -/
@[simp] lemma ne_nan_of_scaleB {x : Floating} {t : Int64} (n : x.scaleB t ≠ nan) : x ≠ nan := by
  contrapose n
  simp only [n, nan_scaleB]

@[simp] lemma scaleB_zero {t : Int64} : (0 : Floating).scaleB t = 0 := by
  rw [scaleB]
  simp

/-!
### Dividing by two
-/

@[irreducible] def div2 (x : Floating) : Floating := x.scaleB (-1)

instance : Div2 Floating where
  div2 := Floating.div2

lemma div2_def (x : Floating) : Div2.div2 x = Floating.div2 x := rfl

/-- `div2` is conservative -/
@[approx] lemma approx_div2 (xm : approx x x') : approx x.div2 (x' / 2) := by
  have e : x' / 2 = x' * 2^(-1 : ℤ) := by
    simp only [div_eq_mul_inv, Int.reduceNeg, zpow_neg, zpow_one]
  rw [e, div2]
  exact approx_scaleB _ xm

instance : ApproxDiv2 Floating ℝ where
  approx_div2 {x x'} a := by
    rw [div2_def, div2_eq_mul, ← div_eq_inv_mul]
    approx

/-- `div2` is exact if not `nan` -/
lemma val_div2 {x : Floating} (n : x.div2 ≠ nan) : x.div2.val = x.val / 2 := by
  simpa [approx, n] using approx_div2 (approx_val (x := x))

/-- `div2` propagates `nan` -/
@[simp] lemma nan_div2 : (nan : Floating).div2 = nan := by
  rw [div2]; simp only [nan_scaleB]

/-- `div2` propagates `nan` -/
@[simp] lemma ne_nan_of_div2 {x : Floating} (n : x.div2 ≠ nan) : x ≠ nan := by
  rw [div2] at n; exact ne_nan_of_scaleB n

instance : Div2Zero Floating where
  div2_zero := by simp [div2_def, div2]
