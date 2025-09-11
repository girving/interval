import Interval.Floating.Mul
import Interval.Interval.Basic
import Interval.Interval.Preinterval

open Classical
open Pointwise

/-!
## Interval arithmetic multiplication
-/

open Set
open scoped Real
namespace Interval

variable {x y : Interval} {x' y' : ℝ}

/-!
### Definition, without correctness proof
-/

/-- Multiply two intervals, producing a not necessarily correct interval.
    We define this, prove it correct, then wrap it in `Mul Interval` below. -/
@[irreducible, inline] def premul (x : Interval) (y : Interval) : Preinterval :=
  bif x.lo.n.isNeg != x.hi.n.isNeg && y.lo.n.isNeg != x.hi.n.isNeg then  -- x,y have mixed sign
    ⟨min (x.lo.mul y.hi false) (x.hi.mul y.lo false),
     (x.lo.mul y.lo true).max (x.hi.mul y.hi true)⟩
  else -- At least one of x,y has constant sign, so we can save multiplications
    let (a,b,c,d) := match (x.lo.n.isNeg, x.hi.n.isNeg, y.lo.n.isNeg, y.hi.n.isNeg) with
      | (false, _, false, _)    => (x.lo, x.hi, y.lo, y.hi)  -- 0 ≤ x, 0 ≤ y
      | (false, _, true, false) => (x.hi, x.hi, y.lo, y.hi)  -- 0 ≤ x, 0 ∈ y
      | (false, _, _, true)     => (x.hi, x.lo, y.lo, y.hi)  -- 0 ≤ x, y ≤ 0
      | (true, false, false, _) => (x.lo, x.hi, y.hi, y.hi)  -- 0 ∈ x, 0 ≤ y
      | (true, false, _, _)     => (x.hi, x.lo, y.lo, y.lo)  -- 0 ∈ x, y ≤ 0 (0 ∈ y is impossible)
      | (_, true, false, _)     => (x.lo, x.hi, y.hi, y.lo)  -- x ≤ 0, 0 ≤ y
      | (_, true, true, false)  => (x.lo, x.lo, y.hi, y.lo)  -- x ≤ 0, 0 ∈ y
      | (_, true, _, true)      => (x.hi, x.lo, y.hi, y.lo)  -- x ≤ 0, y ≤ 0
    ⟨a.mul c false, b.mul d true⟩

/-!
### Correctness proof
-/

/-- `premul` propagates `x = nan` -/
@[simp] lemma nan_premul {y : Interval} : (nan : Interval).premul y = nan := by
  rw [premul]
  simp only [lo_nan, Floating.n_nan, Int64.isNeg_min, hi_nan, bne_self_eq_false, Floating.isNeg_iff,
    Bool.false_and, Floating.nan_mul, min_self, bif_eq_if, ite_false, Bool.false_eq_true,
    Int64.isNeg]
  rcases y.sign_cases with ⟨ls,hs⟩ | ⟨ls,hs⟩ | ⟨ls,hs⟩
  all_goals try simp only [not_lt.mpr ls]
  all_goals try simp only [not_lt.mpr hs]
  all_goals simp only [ls, hs, decide_true, decide_false, Floating.nan_mul, ← Preinterval.nan_def]

/-- `premul` propagates `y = nan` -/
@[simp] lemma premul_nan {x : Interval} : x.premul nan = nan := by
  rw [premul]
  simp only [Floating.isNeg_iff, lo_nan, Floating.n_nan, Int64.isNeg_min, hi_nan, Floating.mul_nan,
    min_self, bif_eq_if, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_decide, Int64.isNeg]
  rcases x.sign_cases with ⟨ls,hs⟩ | ⟨ls,hs⟩ | ⟨ls,hs⟩
  all_goals try simp only [not_lt.mpr ls]
  all_goals try simp only [not_lt.mpr hs]
  all_goals simp only [ls, hs, decide_true, decide_false, Floating.mul_nan, not_true, ite_self, ←
    Preinterval.nan_def, false_and, true_iff, not_false_iff, true_and, Floating.max_nan]

/-- `mul` respects `approx` -/
@[approx] lemma approx_premul (ax : approx x x') (ay : approx y y') :
    approx (x.premul y) (x' * y') := by
  -- Discard nans
  by_cases n : x = nan ∨ y = nan
  · rcases n with n | n
    all_goals simp only [n, nan_premul, premul_nan, approx_nan]
  rcases not_or.mp n with ⟨xn,yn⟩; clear n
  rw [premul]
  simp only [bif_eq_if, Floating.isNeg_iff, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_decide,
    Int64.isNeg]
  -- Record Floating.mul bounds
  generalize mll0 : x.lo.mul y.lo false = ll0
  generalize mlh0 : x.lo.mul y.hi false = lh0
  generalize mhl0 : x.hi.mul y.lo false = hl0
  generalize mhh0 : x.hi.mul y.hi false = hh0
  generalize mll1 : x.lo.mul y.lo true = ll1
  generalize mlh1 : x.lo.mul y.hi true = lh1
  generalize mhl1 : x.hi.mul y.lo true = hl1
  generalize mhh1 : x.hi.mul y.hi true = hh1
  have ill0 : ll0 ≠ nan → ll0.val ≤ x.lo.val * y.lo.val := by rw [←mll0]; exact Floating.mul_le
  have ilh0 : lh0 ≠ nan → lh0.val ≤ x.lo.val * y.hi.val := by rw [←mlh0]; exact Floating.mul_le
  have ihl0 : hl0 ≠ nan → hl0.val ≤ x.hi.val * y.lo.val := by rw [←mhl0]; exact Floating.mul_le
  have ihh0 : hh0 ≠ nan → hh0.val ≤ x.hi.val * y.hi.val := by rw [←mhh0]; exact Floating.mul_le
  have ill1 : ll1 ≠ nan → x.lo.val * y.lo.val ≤ ll1.val := by rw [←mll1]; exact Floating.le_mul
  have ilh1 : lh1 ≠ nan → x.lo.val * y.hi.val ≤ lh1.val := by rw [←mlh1]; exact Floating.le_mul
  have ihl1 : hl1 ≠ nan → x.hi.val * y.lo.val ≤ hl1.val := by rw [←mhl1]; exact Floating.le_mul
  have ihh1 : hh1 ≠ nan → x.hi.val * y.hi.val ≤ hh1.val := by rw [←mhh1]; exact Floating.le_mul
  have xle := x.le
  have yle := y.le
  -- Split on signs
  rcases x.sign_cases with ⟨xls,xhs⟩ | ⟨xls,xhs⟩ | ⟨xls,xhs⟩
  all_goals try simp only [not_lt.mpr xls]
  all_goals try simp only [not_lt.mpr xhs]
  all_goals rcases y.sign_cases with ⟨yls,yhs⟩ | ⟨yls,yhs⟩ | ⟨yls,yhs⟩
  all_goals try simp only [not_lt.mpr yls]
  all_goals try simp only [not_lt.mpr yhs]
  all_goals simp only [xls, xhs, yls, yhs, not_true, false_and, if_false, decide_true,
    decide_false, true_iff, not_false_iff, true_and, if_true, mll0, mlh0, mhl0, mhh0, mll1,
    mlh1, mhl1, mhh1]
  all_goals clear mll0 mlh0 mhl0 mhh0 mll1 mlh1 mhl1 mhh1
  all_goals simp only [approx, x.lo_ne_nan xn, y.lo_ne_nan yn, and_imp, Floating.min_eq_nan,
    Floating.max_eq_nan, mem_Icc, Floating.val_min, min_le_iff, or_iff_not_imp_left, not_false_iff,
    true_imp_iff, not_imp_iff_and_not] at ax ay ⊢
  -- Dispatch everything with nlinarith
  · intro m0 m1; specialize ihh0 m0; specialize ill1 m1
    exact ⟨by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ilh0 m0; specialize ihl1 m1
    exact ⟨by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ilh0 m0; specialize ill1 m1
    exact ⟨by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ihl0 m0; specialize ilh1 m1
    exact ⟨by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ill0 m0; specialize ihh1 m1
    exact ⟨by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ihl0 m0; specialize ihh1 m1
    exact ⟨by nlinarith, by nlinarith⟩
  · intro m0 m1 m2 m3
    specialize ilh0 m0; specialize ihl0 m1; specialize ill1 m2; specialize ihh1 m3
    simp only [Floating.val_max m2 m3, le_max_iff, ← or_iff_not_imp_right]
    constructor
    all_goals left; nlinarith
  · intro m0 m1; specialize ilh0 m0; specialize ihh1 m1
    exact ⟨by nlinarith, by nlinarith⟩
  · intro m0 m1 m2 m3
    specialize ilh0 m0; specialize ihl0 m1; specialize ill1 m2; specialize ihh1 m3
    simp only [Floating.val_max m2 m3, le_max_iff, ← or_iff_not_imp_right]
    constructor
    all_goals rcases nonpos_or_nonneg x' with x0' | x0'
    all_goals try left; nlinarith
    all_goals right; nlinarith

/-!
### Final definition
-/

/-- Multiply two intervals -/
@[irreducible] def mul (x : Interval) (y : Interval) : Interval :=
  (x.premul y).mix' (approx_premul x.lo_mem y.lo_mem)

/-- `* = mul` -/
instance : Mul Interval where
  mul (x y : Interval) := x.mul y

/-- `*` definition -/
lemma mul_def {x y : Interval} : x * y = x.mul y := rfl

/-- `Interval` multiplication approximates `ℝ` -/
instance : ApproxMul Interval ℝ where
  approx_mul x y := by
    rw [mul_def, mul, Preinterval.approx_mix']
    approx

/-- `Interval` approximates `ℝ` as a ring -/
instance : ApproxRing Interval ℝ where

/-- `mul` propagates `x = nan` -/
@[simp] lemma nan_mul {y : Interval} : nan * y = nan := by
  rw [mul_def, mul]; simp only [nan_premul, lo_nan, Preinterval.mix_nan']

/-- `mul` propagates `y = nan` -/
@[simp] lemma mul_nan {x : Interval} : x * nan = nan := by
  rw [mul_def, mul]; simp only [premul_nan, lo_nan, Preinterval.mix_nan']

/-- `mul` arguments are `≠ nan` if the result is -/
lemma ne_nan_of_mul {x : Interval} {y : Interval} (n : x * y ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose n
  simp only [not_and_or, not_not] at n ⊢
  rcases n with n | n
  all_goals simp only [n, nan_mul, mul_nan]

/-!
### `Floating * Floating`, but conservative
-/

/-- Multiply two `Floating`s, producing an `Interval -/
@[irreducible] def float_mul_float (x : Floating) (y : Floating) : Interval :=
  mix (x.mul y false) (x.mul y true)
    (fun n0 n1 ↦ le_trans (Floating.mul_le n0) (Floating.le_mul n1))

/-- `float_mul_float` respects `approx` -/
@[approx] lemma approx_float_mul_float {x y : Floating} (ax : approx x x') (ay : approx y y') :
    approx (float_mul_float x y) (x' * y') := by
  rw [float_mul_float]
  simp only [approx, lo_eq_nan, mix_eq_nan] at ax ay ⊢
  by_cases n : x = nan ∨ y = nan ∨ Floating.mul x y false = nan ∨ Floating.mul x y true = nan
  · rcases n with n | n | n | n; repeat simp [n]
  simp only [not_or] at n
  rcases n with ⟨n0,n1,n2,n3⟩
  simp only [n0, false_or, n1, n2, n3, or_self, ne_eq, mix_eq_nan, not_false_eq_true, lo_mix,
    hi_mix] at ax ay ⊢
  simp only [← ax, ← ay]
  exact ⟨Floating.mul_le n2, Floating.le_mul n3⟩

/-- `float_mul_float _ nan _ = nan` -/
@[simp] lemma float_mul_float_nan_right {x : Floating} :
    float_mul_float x (nan : Floating) = nan := by
  simp only [float_mul_float, Floating.mul_nan, mix_self, coe_nan]

/-- `float_mul_float nan _ _ = nan` -/
@[simp] lemma float_mul_float_nan_left {x : Floating} :
    float_mul_float (nan : Floating) x = nan := by
  simp only [float_mul_float, Floating.nan_mul, mix_self, coe_nan]

/-- `float_mul_float` arguments are `≠ nan` if the result is -/
lemma ne_nan_of_float_mul_float {x : Floating} {y : Floating}
    (n : (float_mul_float x y).lo ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose n
  simp only [not_and_or, not_not] at n ⊢
  rcases n with n | n; repeat simp [n]

/-!
### `Interval * Floating`
-/

/-- Multiply times a `Floating` -/
@[irreducible] def mul_float (x : Interval) (y : Floating) : Interval :=
  let t := bif y.n.isNeg then (x.hi, x.lo) else (x.lo, x.hi)
  mix (t.1.mul y false) (t.2.mul y true) (by
    intro n0 n1
    refine le_trans (Floating.mul_le n0) (le_trans ?_ (Floating.le_mul n1))
    clear n0 n1
    simp only [t, bif_eq_if, Floating.isNeg_iff, decide_eq_true_eq, Int64.isNeg]
    by_cases y0 : y.val < 0
    · simp only [y0, ite_true, mul_le_mul_right_of_neg, le]
    · simp only [y0, ite_false]; exact mul_le_mul_of_nonneg_right x.le (not_lt.mp y0))

/-- `mul_float` respects `approx` -/
@[approx] lemma approx_mul_float {y : Floating} (ax : approx x x') (ay : approx y y') :
    approx (x.mul_float y) (x' * y') := by
  -- Handle special cases
  rw [mul_float]
  simp only [Floating.isNeg_iff, bif_eq_if, decide_eq_true_eq, Int64.isNeg]
  by_cases n : x = nan ∨ y = nan
  · rcases n with n | n; repeat simp [n]
  simp only [not_or] at n
  rcases n with ⟨n0,n1⟩
  simp only [approx, lo_eq_nan, n0, false_or, n1] at ax ay
  have xle : x.lo.val ≤ x.hi.val := x.le
  -- Record Floating.mul bounds
  generalize ml0 : x.lo.mul y false = l0
  generalize mh0 : x.hi.mul y false = h0
  generalize ml1 : x.lo.mul y true = l1
  generalize mh1 : x.hi.mul y true = h1
  have il0 : l0 ≠ nan → l0.val ≤ x.lo.val * y.val := by rw [←ml0]; exact Floating.mul_le
  have ih0 : h0 ≠ nan → h0.val ≤ x.hi.val * y.val := by rw [←mh0]; exact Floating.mul_le
  have il1 : l1 ≠ nan → x.lo.val * y.val ≤ l1.val := by rw [←ml1]; exact Floating.le_mul
  have ih1 : h1 ≠ nan → x.hi.val * y.val ≤ h1.val := by rw [←mh1]; exact Floating.le_mul
  -- Split on signs
  by_cases ys : y.val < 0
  all_goals simp only [ys, ite_true, ite_false, approx, ml0, mh0, ml1, mh1, or_iff_not_imp_left,
    ← ay]
  all_goals intro m
  all_goals simp only [lo_eq_nan] at m
  all_goals simp only [lo_mix m, hi_mix m]
  all_goals simp only [mix_eq_nan, not_or] at m
  -- Handle each case
  · specialize ih0 m.1; specialize il1 m.2
    exact ⟨by nlinarith, by nlinarith⟩
  · have le : x.lo.val * y.val ≤ x.hi.val * y.val := by nlinarith
    specialize il0 m.1; specialize ih1 m.2
    exact ⟨by nlinarith, by nlinarith⟩

@[simp] lemma mul_float_nan {x : Interval} : x.mul_float nan = nan := by
  rw [mul_float]; simp

@[simp] lemma nan_mul_float {x : Floating} : (nan : Interval).mul_float x = nan := by
  rw [mul_float]; simp

/-!
### Interval squaring
-/

/-- Tighter than `mul x x` -/
@[irreducible] def sqr (x : Interval) : Interval :=
  if m : x.lo.n.isNeg != x.hi.n.isNeg then  -- x has mixed sign
    mix 0 ((x.lo.mul x.lo true).max (x.hi.mul x.hi true)) (by
      intro _ n
      simp only [ne_eq, Floating.max_eq_nan, not_or] at n
      simp only [bne_iff_ne, ne_eq] at m
      simp only [Floating.val_zero, Floating.val_max n.1 n.2, le_max_iff]
      left
      exact le_trans (by nlinarith) (Floating.le_mul n.1))
  else if x0 : x.lo.n.isNeg then
    mix (x.hi.mul x.hi false) (x.lo.mul x.lo true) (by
      intro n0 n1
      simp only [Floating.isNeg_iff, bne_iff_ne, ne_eq, decide_eq_decide, not_not,
        decide_eq_true_eq, Int64.isNeg] at m x0
      have le := x.le
      have h0 := m.mp x0
      exact le_trans (Floating.mul_le n0) (le_trans (by nlinarith) (Floating.le_mul n1)))
  else
    mix (x.lo.mul x.lo false) (x.hi.mul x.hi true) (by
      intro n0 n1
      simp only [Floating.isNeg_iff, bne_iff_ne, ne_eq, decide_eq_decide, not_not,
        decide_eq_true_eq, Int64.isNeg] at m x0
      have le := x.le
      exact le_trans (Floating.mul_le n0) (le_trans (by nlinarith) (Floating.le_mul n1)))

/-- `sqr` respects `approx` -/
@[approx] lemma approx_sqr (ax : approx x x') : approx x.sqr (x' ^ 2) := by
  -- Record Floating.mul bounds
  generalize mll0 : x.lo.mul x.lo false = ll0
  generalize mll1 : x.lo.mul x.lo true = ll1
  generalize mhh0 : x.hi.mul x.hi false = hh0
  generalize mhh1 : x.hi.mul x.hi true = hh1
  have ill0 : ll0 ≠ nan → ll0.val ≤ x.lo.val * x.lo.val := by rw [←mll0]; exact Floating.mul_le
  have ill1 : ll1 ≠ nan → x.lo.val * x.lo.val ≤ ll1.val := by rw [←mll1]; exact Floating.le_mul
  have ihh0 : hh0 ≠ nan → hh0.val ≤ x.hi.val * x.hi.val := by rw [←mhh0]; exact Floating.mul_le
  have ihh1 : hh1 ≠ nan → x.hi.val * x.hi.val ≤ hh1.val := by rw [←mhh1]; exact Floating.le_mul
  -- Handle special cases
  simp only [sqr, Floating.isNeg_iff, bne_iff_ne, ne_eq, decide_eq_decide, decide_eq_true_eq,
    dite_not, Int64.isNeg]
  by_cases n : x = nan
  · simp only [n, approx_nan, lo_nan, Floating.val_nan_lt_zero, hi_nan, Floating.mul_nan, mix_self,
    coe_nan, dite_eq_ite, ite_self, Floating.max_nan, mix_nan]
  simp only [approx, lo_eq_nan, n, false_or] at ax
  -- Split on signs
  rcases x.sign_cases with ⟨xls,xhs⟩ | ⟨xls,xhs⟩ | ⟨xls,xhs⟩
  all_goals try simp only [not_lt.mpr xls]
  all_goals try simp only [not_lt.mpr xhs]
  all_goals simp only [xls, xhs, dite_false, dite_true, approx, mll0, mhh0, mll1, mhh1, lo_eq_nan,
    true_iff, or_iff_not_imp_left]
  all_goals intro m
  all_goals simp only [lo_mix m, hi_mix m]
  all_goals simp only [mix_eq_nan, not_or, Floating.max_eq_nan] at m
  -- Dispatch everything with nlinarith
  · specialize ihh0 m.1; specialize ill1 m.2
    exact ⟨by nlinarith, by nlinarith⟩
  · specialize ill0 m.1; specialize ihh1 m.2
    exact ⟨by nlinarith, by nlinarith⟩
  · specialize ill1 m.2.1; specialize ihh1 m.2.2
    simp only [Floating.val_zero, Floating.val_max m.2.1 m.2.2, le_max_iff]
    constructor
    · nlinarith
    · by_cases x' < 0
      · left; nlinarith
      · right; nlinarith

@[simp] lemma sqr_nan : (nan : Interval).sqr = nan := by
  rw [sqr]; simp
