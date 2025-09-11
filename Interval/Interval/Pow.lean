import Interval.Interval.Division
import Interval.Interval.Exp
import Interval.Interval.Log

/-!
## Interval powers

These are easy on top of `exp` and `log`.
-/

open Classical
open Set
open scoped Real

variable {x y : Interval} {x' y' : ℝ} {n : ℕ}

/-- `x^y = exp (x.log * y)` -/
@[irreducible] def Interval.pow (x : Interval) (y : Interval) : Interval :=
  (x.log * y).exp

instance : Pow Interval Interval := ⟨Interval.pow⟩

lemma Interval.pow_def {x y : Interval} : x ^ y = (x.log * y).exp := by
  trans x.pow y
  · rfl
  · rw [Interval.pow]

/-- `Interval.pow` is conservative -/
@[approx] lemma Interval.mem_approx_pow (xm : approx x x') (ym : approx y y') :
    approx (x ^ y) (x' ^ y') := by
  rw [pow_def]
  by_cases x0 : 0 < x'
  · rw [Real.rpow_def_of_pos x0]; approx
  · simp only [not_lt] at x0
    rw [Interval.log_nonpos x0 xm, Interval.nan_mul, Interval.exp_nan]
    simp only [approx_nan]

/-- `Interval.pow` is conservative for `ℕ` powers -/
@[approx] lemma Interval.mem_approx_pow_nat (xm : approx x x') :
    approx (x ^ (n : Interval)) (x' ^ n) := by
  simp only [← Real.rpow_natCast]
  approx

/-- `Interval.pow` propagates `nan` -/
@[simp] lemma Interval.nan_pow {y : Interval} : (nan : Interval) ^ y = nan := by
  simp only [pow_def, nan_log, nan_mul, exp_nan]

/-- `Interval.pow` propagates `nan` -/
@[simp] lemma Interval.pow_nan {x : Interval} : x ^ (nan : Interval) = nan := by
  simp only [pow_def, mul_nan, exp_nan]

/-!
### `Interval ^ ℕ` powers
-/

/-- For use within `Interval.powNat` for large `n` (not very optimised) -/
@[irreducible] def Floating.powNatSlow (x : Floating) (n : ℕ) : Interval :=
  bif n == 0 then 1 else
  let p := (x.abs : Interval) ^ (n : Interval)
  bif n % 2 == 1 ∧ x < 0 then -p else p

/-- Special case low powers, and use `Floating.powNatSlow` for larger `n` -/
@[irreducible] def Interval.powNat (x : Interval) (n : ℕ) : Interval := match n with
  | 0 => 1
  | 1 => x
  | 2 => x.sqr
  | 3 => x.sqr * x
  | 4 => x.sqr.sqr
  | n =>
    let p := x.lo.powNatSlow n ∪ x.hi.powNatSlow n
    bif x.lo < 0 && 0 ≤ x.hi && n % 2 = 0 then 0 ∪ p else p

instance : Pow Interval ℕ := ⟨Interval.powNat⟩
lemma Interval.powNat_def {x : Interval} {n : ℕ} : x ^ n = x.powNat n := rfl

/-- `Floating.powNatSlow` is conservative -/
@[approx] lemma Floating.mem_approx_powNatSlow {x : Floating} (xm : approx x x') (n : ℕ) :
    approx (x.powNatSlow n) (x' ^ n) := by
  rw [powNatSlow]
  simp only [to_if]
  by_cases n0 : n = 0
  · simp only [n0, ↓reduceIte, Interval.approx_one, pow_zero]
  simp only [n0, ↓reduceIte, val_lt_val, val_zero]
  by_cases xn : x = nan
  · simp [xn]
  simp only [approx, xn, false_or] at xm
  simp only [← xm]
  have am : approx ((x.abs : Interval) ^ Interval.ofNat n) (|x.val| ^ n) := by
    apply Interval.mem_approx_pow_nat
    approx
  by_cases x0 : x.val < 0
  · rcases Nat.even_or_odd' n with ⟨k, e | e⟩
    · simpa [e, pow_mul] using am
    · simpa [e, x0, pow_mul, pow_succ' _ (2 * k), ← neg_mul, abs_of_neg x0] using am
  · simp only [x0, and_false, ↓reduceIte]
    simp only [Floating.abs_of_nonneg (not_lt.mp x0)]
    approx

@[simp] lemma Floating.nan_powNatSlow {n : ℕ} (n0 : n ≠ 0) :
    (nan : Floating).powNatSlow n = nan := by
  rw [powNatSlow]
  simp [to_if, n0]

/-- `Interval ^ ℕ` is conservative -/
@[approx] lemma Interval.mem_approx_powNat (xm : approx x x') : approx (x ^ n) (x' ^ n) := by
  rw [powNat_def]
  unfold Interval.powNat
  by_cases n0 : n = 0; · simp only [n0, approx_one, pow_zero]
  by_cases n1 : n = 1; · simp only [n1, pow_one, xm]
  by_cases n2 : n = 2; · simp only [n2]; approx
  by_cases n3 : n = 3; · simp only [n3, pow_succ _ 2]; approx
  by_cases n4 : n = 4; · simp only [n4, (by norm_num : 4 = 2 * 2), pow_mul]; approx
  simp only [to_if, decide_eq_true_eq]
  by_cases xn : x = nan; · simp [xn, n0]
  by_cases ln : x.lo.powNatSlow n = nan; · simp [ln]
  by_cases hn : x.hi.powNatSlow n = nan; · simp [hn]
  have alo := Floating.mem_approx_powNatSlow (Floating.approx_val (x := x.lo)) n
  have ahi := Floating.mem_approx_powNatSlow (Floating.approx_val (x := x.hi)) n
  simp only [approx, lo_eq_nan, xn, ln, hn, or_iff_not_imp_left, not_false_iff,
    true_imp_iff] at xm alo ahi ⊢
  intro rn
  generalize x.lo.powNatSlow n = lp at alo ln rn
  generalize x.hi.powNatSlow n = hp at ahi hn rn
  have vm := Floating.val_max (lp.hi_ne_nan ln) (hp.hi_ne_nan hn)
  rcases Nat.even_or_odd n with ⟨k, e⟩ | e
  · simp only [← two_mul] at e
    simp only [e, pow_mul, Nat.mul_mod_right, and_true] at alo ahi ⊢
    clear n0 n1 n2 n3 n4 e rn
    rcases x.sign_cases with ⟨xls,xhs⟩ | ⟨xls,xhs⟩ | ⟨xls,xhs⟩
    · simp only [Floating.val_lt_val, Floating.val_zero, Floating.val_le_val, not_le.mpr xhs,
        and_false, ↓reduceIte, lo_union, Floating.val_min, inf_le_iff, hi_union, vm, le_sup_iff]
      constructor
      · exact .inr (le_trans ahi.1 (pow_le_pow_left₀ (by bound) (by nlinarith) _))
      · exact .inl (le_trans (pow_le_pow_left₀ (by bound) (by nlinarith) _) alo.2)
    · simp only [Floating.val_lt_val, Floating.val_zero, not_lt.mpr xls, Floating.val_le_val, xhs,
        and_true, ↓reduceIte, lo_union, Floating.val_min, inf_le_iff, hi_union, vm, le_sup_iff]
      constructor
      · exact .inl (le_trans alo.1 (pow_le_pow_left₀ (by bound) (by nlinarith) _))
      · exact .inr (le_trans (pow_le_pow_left₀ (by bound) (by nlinarith) _) ahi.2)
    · simp only [Floating.val_lt_val, Floating.val_zero, xls, Floating.val_le_val, xhs, and_self,
        ↓reduceIte, lo_union, lo_zero, Floating.val_min, inf_le_iff, hi_union, hi_zero]
      constructor
      · left
        bound
      · rw [Floating.val_max (by simp) (Floating.max_ne_nan.mpr ⟨lp.hi_ne_nan ln, hp.hi_ne_nan hn⟩)]
        simp only [Floating.val_zero, le_sup_iff, vm]
        right
        by_cases s : x' < 0
        · exact .inl (le_trans (pow_le_pow_left₀ (by bound) (by nlinarith) _) alo.2)
        · exact .inr (le_trans (pow_le_pow_left₀ (by bound) (by nlinarith) _) ahi.2)
  · have n2 : n % 2 ≠ 0 := by simp only [Odd] at e; omega
    simp only [n2, and_false, ↓reduceIte, lo_union, Floating.val_min, inf_le_iff, hi_union]
    constructor
    · exact .inl (le_trans alo.1 (by simp only [e.pow_le_pow, xm.1]))
    · simp only [Floating.val_max (lp.hi_ne_nan ln) (hp.hi_ne_nan hn), le_max_iff]
      exact .inr (le_trans (by simp only [e.pow_le_pow, xm.2]) ahi.2)

/-!
### `Interval ^ ℤ` powers
-/

@[irreducible] def Interval.powInt (x : Interval) (n : ℤ) : Interval :=
  let p := x ^ n.natAbs
  bif n < 0 then p.inv else p

instance : Pow Interval ℤ := ⟨Interval.powInt⟩
lemma Interval.powInt_def {x : Interval} {n : ℤ} : x ^ n = x.powInt n := rfl

/-- `Interval.powInt` is conservative -/
@[approx] lemma Interval.mem_approx_powInt {n : ℤ} (xm : approx x x') :
    approx (x ^ n) (x' ^ n) := by
  rw [powInt_def, Interval.powInt]
  simp only [bif_eq_if, decide_eq_true_eq]
  have a : approx (x ^ n.natAbs) (x' ^ n.natAbs) := mem_approx_powNat xm
  by_cases n0 : n < 0
  · simp only [n0, ↓reduceIte]
    nth_rw 2 [Int.eq_neg_natAbs_of_nonpos n0.le]
    simp only [zpow_neg, zpow_natCast]
    exact approx_inv a
  · simp only [n0, ↓reduceIte]
    simp only [not_lt] at n0
    nth_rw 2 [Int.eq_natAbs_of_nonneg n0]
    simp only [zpow_natCast, a]
