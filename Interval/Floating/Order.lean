import Interval.Floating.Neg

/-!
## Floating point ordering

We choose to make `Floating` a linear order with `∀ x, nan ≤ x`, though unfortunately this means
`max` can't propagate `nan`.  We provide an `Floating.max` version which does.
-/

open Set
open scoped Real
namespace Floating

/-- Unlike `Float`, we don't worry about `nan` for our comparisons -/
@[irreducible] def blt (x y : Floating) : Bool :=
  let xn := x.n.isNeg
  let yn := y.n.isNeg
  xn > yn || (xn == yn &&
    ((bif xn then x.s > y.s else x.s < y.s) || (x.s == y.s && x.n.toUInt64 < y.n.toUInt64)))

/-- Unlike `Float`, we don't worry about `nan` for our comparisons -/
@[irreducible] def ble (x y : Floating) : Bool := !(y.blt x)

-- Ordering instances
instance : LT Floating where lt x y := x.blt y
instance : LE Floating where le x y := x.ble y
instance : DecidableRel (α := Floating) (· < ·) | a, b => by dsimp [LT.lt]; infer_instance
instance : DecidableRel (α := Floating) (· ≤ ·) | a, b => by dsimp [LE.le]; infer_instance
instance : Min Floating where min x y := bif x.ble y then x else y

/-- We define `max` so that `Floating` is a `LinearOrder`, though unfortunately this means
    that it does not propagate `nan` correctly.  `Floating.max` works better. -/
instance : Max Floating where max x y := bif x.ble y then y else x

/-- A version of `max` that propagates `nan` -/
@[irreducible] def max (x y : Floating) : Floating :=
  -min (-x) (-y)

/-- Turn `blt` into `<` -/
lemma blt_eq_lt {x y : Floating} : x.blt y = decide (x < y) := by simp only [LT.lt, Bool.decide_coe]

/-- Turn `ble` into `<` -/
lemma ble_eq_le {x y : Floating} : x.ble y = decide (x ≤ y) := by simp only [LE.le, Bool.decide_coe]

/-- `min` in terms of `≤` -/
lemma min_def (x y : Floating) : min x y = if x ≤ y then x else y := by
  simp only [min, ble_eq_le, bif_eq_if, decide_eq_true_eq]

/-- `max` in terms of `≤` -/
lemma max_def (x y : Floating) : Max.max x y = if x ≤ y then y else x := by
  simp only [Max.max, ble_eq_le, Bool.cond_decide]

/-- `<` in more mathematical terms -/
lemma lt_def {x y : Floating} : x < y ↔ (x.n.isNeg > y.n.isNeg ∨
    (x.n.isNeg = y.n.isNeg ∧ (
      (if x.n.isNeg then x.s > y.s else x.s < y.s) ∨
      (x.s = y.s ∧ x.n.toUInt64 < y.n.toUInt64)))) := by
  have e : x < y ↔ x.blt y := by simp only [LT.lt]
  rw [e, blt]
  simp only [gt_iff_lt, bif_eq_if, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    Bool.ite_eq_true_distrib]

/-- `≤` in terms of `<` -/
lemma le_def {x y : Floating} : x ≤ y ↔ ¬(y < x) := by
  have e0 : y < x ↔ y.blt x := by simp only [LT.lt]
  have e1 : x ≤ y ↔ x.ble y := by simp only [LE.le]
  rw [e0, e1, ble, Bool.not_eq_true', Bool.not_eq_true]

/-- `<` respects `-` -/
@[simp] lemma neg_lt_neg {x y : Floating} (xm : x ≠ nan) (ym : y ≠ nan) :
    (-x) < (-y) ↔ y < x := by
  simp only [lt_def, n_neg, gt_iff_lt, s_neg, Bool.lt_iff]
  have flip : x ≠ 0 → y ≠ 0 →
      ((-x.n).toUInt64 < (-y.n).toUInt64 ↔ y.n.toUInt64 < x.n.toUInt64) := by
    intro x0 y0
    simp only [ne_eq, ← Floating.n_eq_zero_iff, Int64.eq_zero_iff_n_eq_zero,
      UInt64.eq_zero_iff_toNat_eq_zero] at x0 y0
    simp only [Int64.neg_def, UInt64.lt_iff_toNat_lt, UInt64.toNat_neg, UInt64.toUInt64_toInt64,
      UInt64.size]
    have xs := x.n.toUInt64.toNat_lt_2_pow_64
    have ys := y.n.toUInt64.toNat_lt_2_pow_64
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    all_goals omega
  by_cases x0 : x = 0
  · simp only [x0, n_zero, _root_.neg_zero, s_zero, Int64.n_zero]
    by_cases y0 : y = 0
    · simp only [y0, n_zero, _root_.neg_zero, and_false, s_zero, lt_self_iff_false, Int64.n_zero]
    · simp only [Int64.isNeg, Int64.isNeg_neg (y.n_ne_zero y0) (y.n_ne_min ym),
        decide_eq_false_iff_not, not_le, lt_self_iff_false, decide_false, Bool.false_eq_true,
        and_false, false_eq_decide_iff, ↓reduceIte, false_or, decide_eq_true_eq, true_and, not_lt]
      by_cases yn : y.n < 0
      · simp only [yn, UInt64.pos_iff_ne_zero, Ne, eq_comm (a := (0 : UInt64)), ←
          Int64.ne_zero_iff_n_ne_zero, neg_eq_zero, y.n_ne_zero y0, not_false_eq_true, and_true,
          ne_or_eq, and_self, ↓reduceIte, true_or]
      · simp only [yn, false_and, ↓reduceIte, false_or, false_iff, not_and, not_or, not_lt,
          UInt64.nonneg, implies_true, and_self]
  · by_cases y0 : y = 0
    · simp only [y0, n_zero, _root_.neg_zero, s_zero, Int64.n_zero]
      by_cases xn : x.n < 0
      · simp only [Int64.isNeg, lt_self_iff_false, decide_false,
          Int64.isNeg_neg (x.n_ne_zero x0) (x.n_ne_min xm), not_le.mpr xn, Bool.false_eq_true,
          and_false, ↓reduceIte, true_and, false_or, xn, decide_true, Bool.true_eq_false, and_self,
          false_and, or_self, iff_false, not_or, not_lt, UInt64.nonneg, not_and, implies_true]
      · simp only [Int64.isNeg, lt_self_iff_false, decide_false,
          Int64.isNeg_neg (x.n_ne_zero x0) (x.n_ne_min xm), not_lt.mp xn, decide_true, and_self,
          Bool.true_eq_false, ↓reduceIte, UInt64.pos_iff_ne_zero, Ne, false_and, or_false, xn,
          Bool.false_eq_true, and_false, eq_comm (a := (0 : UInt64)), ← Int64.ne_zero_iff_n_ne_zero,
          x.n_ne_zero x0, not_false_eq_true, and_true, ne_or_eq, or_true]
    · simp only [Int64.isNeg, Int64.isNeg_neg (y.n_ne_zero y0) (y.n_ne_min ym),
        decide_eq_false_iff_not, Int64.isNeg_neg (x.n_ne_zero x0) (x.n_ne_min xm), decide_eq_true_eq,
        decide_eq_decide, ← not_lt, not_not]
      by_cases xn : x.n < 0
      · by_cases yn : y.n < 0
        · simp only [yn, xn, not_true_eq_false, and_false, ↓reduceIte, eq_comm (a := x.s),
            flip x0 y0, true_and, false_or, and_true]
        · simp only [yn, xn, not_true_eq_false, and_self, not_false_eq_true, iff_true, ↓reduceIte,
            false_and, or_self]
      · by_cases yn : y.n < 0
        · simp only [yn, xn, not_false_eq_true, and_self, not_true_eq_false, iff_false, ↓reduceIte,
            false_and, or_false]
        · simp only [yn, xn, not_false_eq_true, and_true, ↓reduceIte, eq_comm (a := x.s),
            flip x0 y0, true_and, false_or, and_false]

/-- `≤` respects `-` -/
@[simp] lemma neg_le_neg {x y : Floating} (xm : x ≠ nan) (ym : y ≠ nan) :
    (-x) ≤ (-y) ↔ y ≤ x := by
  simp only [le_def, neg_lt_neg ym xm]

/-- `nan` appears negative -/
@[simp] lemma nan_lt_zero : (nan : Floating) < 0 := by simp only [nan, LT.lt, blt]; decide

/-- Our ordering is antireflexive -/
lemma not_lt_self (x : Floating) : ¬x < x := by
  simp only [lt_def, lt_self_iff_false, ite_self, and_false, or_self, not_false_eq_true]

/-- `<` is antisymmetric -/
lemma not_lt_of_lt {x y : Floating} (xy : x < y) : ¬(y < x) := by
  simp only [lt_def] at xy ⊢
  by_cases xn : x.n.isNeg
  · by_cases yn : y.n.isNeg
    · simp only [xn, yn, gt_iff_lt, lt_self_iff_false, ite_true, true_and, false_or, not_or,
        not_lt, not_and] at xy ⊢
      rcases xy with h | h
      · simp only [h.le, h.ne, IsEmpty.forall_iff, and_self]
      · simp only [h.1, le_refl, h.2.le, forall_true_left, and_self]
    · simp only [yn, xn, gt_iff_lt, Bool.false_eq_true, ↓reduceIte, false_and, or_false, not_lt,
        Bool.le_true]
  · by_cases yn : y.n.isNeg
    · simp only [xn, yn, gt_iff_lt, not_lt.mpr (Bool.false_le _), Bool.false_eq_true, ↓reduceIte,
        false_and, or_self] at xy
    · simp only [xn, yn, gt_iff_lt, lt_self_iff_false, true_and, false_or, not_or, not_lt,
        not_and] at xy ⊢
      rcases xy with h | h
      · simp only [Bool.false_eq_true, ↓reduceIte, not_lt, h.le, h.ne', false_implies, and_self]
      · simp only [Bool.false_eq_true, ↓reduceIte, h.1, lt_self_iff_false, not_false_eq_true,
          h.2.le, imp_self, and_self]

/-- `≤` is antisymmetric -/
lemma le_antisymm' {x y : Floating} (xy : x ≤ y) (yx : y ≤ x) : x = y := by
  simp only [le_def, lt_def] at xy yx
  simp only [ext_iff]
  by_cases xn : x.n.isNeg
  · by_cases yn : y.n.isNeg
    · simp only [xn, yn, lt_self_iff_false, ite_true, true_and, false_or, not_or, not_lt,
        not_and] at xy yx
      simp only [le_antisymm xy.1 yx.1, le_refl, forall_true_left, true_and, and_true] at xy yx ⊢
      simp only [Int64.ext_iff, le_antisymm xy yx]
    · simp only [yn, xn, gt_iff_lt, Bool.false_eq_true, ↓reduceIte, false_and, or_false, not_lt,
        Bool.le_true, Bool.false_lt_true, Bool.true_eq_false, not_true_eq_false] at xy yx
  · by_cases yn : y.n.isNeg
    · simp only [yn, xn, gt_iff_lt, Bool.false_lt_true, Bool.true_eq_false, ↓reduceIte, false_and,
        or_false, not_true_eq_false] at xy yx
    · simp only [xn, yn, lt_self_iff_false, ite_false, true_and, false_or, not_or, not_lt,
        not_and, Bool.false_eq_true] at xy yx
      simp only [le_antisymm xy.1 yx.1, le_refl, forall_true_left, true_and, and_true] at xy yx ⊢
      simp only [Int64.ext_iff, le_antisymm xy yx]

 /-- `x.n.isNeg` determines negativity -/
lemma isNeg_iff' {x : Floating} : x.n < 0 ↔ x < 0 := by
  by_cases xn : x.n < 0
  · simp only [xn, lt_def, Int64.isNeg, decide_true, n_zero, lt_self_iff_false, decide_false,
      Bool.false_lt_true, Bool.true_eq_false, ↓reduceIte, s_zero, Int64.n_zero, false_and, or_false]
  · simp only [xn, lt_def, Int64.isNeg, decide_false, n_zero, lt_self_iff_false,
    Bool.false_eq_true, ↓reduceIte, s_zero, Int64.n_zero, not_lt.mpr x.n.toUInt64.nonneg, and_false,
    or_false, true_and, false_or, false_iff, not_lt, UInt64.nonneg]

/-- Strict upper bound for `↑↑x.n`, if we're normalized and positive -/
@[simp] lemma le_coe_coe_n {x : Floating} (s0 : x.s ≠ 0) (xn : 0 ≤ x.n) :
    2^62 ≤ ((x.n : ℤ) : ℝ) := by
  by_cases x0 : x = 0
  · simp only [x0, s_zero, ne_eq, not_true_eq_false] at s0
  have xm : x.n ≠ .minValue := by
    contrapose xn
    simp only [ne_eq, not_not] at xn
    simp only [xn]
    decide
  have e : (2^62 : ℝ) = (2^62 : ℤ) := by norm_num
  simp only [e, Int.cast_le, ← Int64.uabs_eq_self xn, UInt64.toInt]
  simpa only [UInt64.le_iff_toNat_le, up62, ← Nat.cast_le (α := ℤ), Nat.cast_pow,
    Nat.cast_ofNat] using x.norm' x0 (UInt64.ne_zero_iff_toNat_ne_zero.mp s0)

/-- Strict upper bound for `↑↑x.n` -/
@[simp] lemma coe_coe_n_lt {x : Floating} : ((x.n : ℤ) : ℝ) < 2^63 := by
  have e : (2^63 : ℝ) = (2^63 : ℤ) := by norm_num
  simp only [e, Int.cast_lt, x.n.coe_lt_pow]

/-- Strict upper bound for `-↑↑x.n` -/
@[simp] lemma neg_coe_coe_n_lt {x : Floating} (n : x ≠ nan) : -((x.n : ℤ) : ℝ) < 2^63 := by
  rw [neg_lt]
  have me : (-2 ^ 63 : ℝ) = (Int64.minValue : ℤ) := by
    simp only [Int64.coe_min', Int.cast_neg, Int.cast_pow, Int.cast_ofNat]
  rw [me, Int.cast_lt, Int64.coe_lt_coe]
  exact Ne.lt_of_le (x.n_ne_min n).symm x.n.min_le

/-- Upper bound for `-↑↑x.n` -/
@[simp] lemma neg_coe_coe_n_le (x : Floating) : -((x.n : ℤ) : ℝ) ≤ 2^63 := by
  by_cases n : x = nan
  · simp only [n, n_nan, Int64.coe_min', Int.cast_neg, Int.cast_pow, Int.cast_ofNat, neg_neg,
      le_refl]
  · exact (neg_coe_coe_n_lt n).le

 /-- `nan` is the unique minimum -/
@[simp] lemma nan_lt {x : Floating} (n : x ≠ nan) : nan < x := by
  simp only [lt_def, n_nan, gt_iff_lt, s_nan, Int64.n_min]
  by_cases xn : x.n < 0
  · simp only [Int64.isNeg, xn, decide_true, Int64.isNeg_min, lt_self_iff_false, ↓reduceIte,
    UInt64.lt_iff_toNat_lt, UInt64.toNat_max, UInt64.toNat_2_pow_63, true_and, false_or]
    simp only [Int64.isNeg_eq_le] at xn
    contrapose n
    simp only [not_or, not_lt, tsub_le_iff_right, not_and, not_not] at n ⊢
    have se : x.s = .max := by
      simp only [UInt64.eq_iff_toNat_eq, UInt64.toNat_max]
      have h := x.s.toNat_le_pow_sub_one
      omega
    simp only [se, UInt64.toNat_max, forall_true_left] at n
    simp only [ext_iff, n_nan, Int64.ext_iff, Int64.n_min, UInt64.eq_iff_toNat_eq,
      UInt64.toNat_2_pow_63, se, s_nan, and_true]
    omega
  · simp only [Int64.isNeg, xn, decide_false, Int64.isNeg_min, decide_true, Bool.false_lt_true,
      Bool.true_eq_false, ↓reduceIte, false_and, or_false]

/-- `nan` is the minimum -/
@[simp] lemma nan_le (x : Floating) : nan ≤ x := by
  simp only [le_def, lt_def, Int64.isNeg, n_nan, Int64.isNeg_min, decide_true, gt_iff_lt,
    decide_eq_true_eq, s_nan, Int64.n_min, not_or, not_lt, Bool.le_true, not_and, true_and]
  by_cases xn : x.n < 0
  · simp only [xn, ↓reduceIte, not_lt, UInt64.le_iff_toNat_le, UInt64.toNat_max,
      UInt64.toNat_2_pow_63, forall_const]
    simp only [Int64.isNeg_eq_le] at xn
    simp only [UInt64.toNat_le_pow_sub_one, true_and, xn, implies_true]
  · simp only [xn, ↓reduceIte, not_lt, IsEmpty.forall_iff]

/-- `nan` is the unique minimum, `val` version -/
@[simp] lemma val_nan_lt {x : Floating} (n : x ≠ nan) : (nan : Floating).val < x.val := by
  rw [val, val]
  simp only [n_nan, Int64.coe_min', Int.cast_neg, Int.cast_pow, Int.cast_ofNat, s_nan, neg_mul,
    UInt64.toInt, UInt64.toNat_max]
  rw [neg_lt, ←neg_mul]
  refine lt_of_lt_of_le (b := 2^63 * 2 ^ ((x.s.toNat : ℤ) - 2 ^ 63)) ?_ ?_
  · rw [mul_lt_mul_iff_of_pos_right two_zpow_pos]
    exact neg_coe_coe_n_lt n
  · refine mul_le_mul_of_nonneg_left ?_ two_pow_pos.le
    apply zpow_le_zpow_right₀ (by norm_num)
    have h := x.s.toNat_le_pow_sub_one
    omega

/-- `nan` is the minimum, `val` version -/
@[simp] lemma val_nan_le (x : Floating) : (nan : Floating).val ≤ x.val := by
  by_cases n : x = nan
  · simp only [n, le_refl]
  · exact (val_nan_lt n).le

/-- `nan` is the minimum -/
@[simp] lemma not_lt_nan (x : Floating) : ¬x < nan := by
  simpa only [le_def] using nan_le x

/-- `nan` is the minimum -/
@[simp] lemma not_lt_nan_val (x : Floating) : ¬x.val < (nan : Floating).val := by
  simp only [not_lt, val_nan_le]

/-- `x.n.isNeg` determines negativity, `val` version -/
@[simp] lemma isNeg_iff {x : Floating} : x.n < 0 ↔ x.val < 0 := by
  rw [val]; symm
  by_cases xn : x.n < 0
  · simp only [xn, ← not_le, mul_nonneg_iff_of_pos_right (two_zpow_pos (𝕜 := ℝ)), iff_true]
    simpa only [Int.cast_nonneg, not_le, Int64.coe_lt_zero_iff]
  · simp only [xn, not_lt, two_zpow_pos, mul_nonneg_iff_of_pos_right, Int.cast_nonneg,
      Int64.coe_nonneg_iff, iff_false, not_lt.mp xn]

/-- `0 ≤ x.n` determines nonnegativity, `val` version -/
@[simp] lemma n_nonneg_iff {x : Floating} : 0 ≤ x.n ↔ 0 ≤ x.val := by
  simp only [← not_lt, isNeg_iff]

 /-- The order is consistent with `.val`, nonnegative case -/
lemma val_lt_val_of_nonneg {x y : Floating} (xn : 0 ≤ x.n) (yn : 0 ≤ y.n) :
    x.val < y.val ↔ x < y := by
  simp only [val, UInt64.toInt, lt_def, Int64.isNeg, isNeg_iff, Bool.lt_iff,
    decide_eq_false_iff_not, two_zpow_pos, decide_eq_true_eq, decide_eq_decide, mul_neg_iff,
    Int.cast_pos, Int64.coe_pos_iff, and_true, Int.cast_lt_zero]
  simp only [two_zpow_not_neg, and_false, Int64.coe_neg_iff, isNeg_iff, val, false_or, not_lt,
    two_zpow_pos, Int.cast_nonneg, Int64.coe_nonneg_iff, yn, true_and, gt_iff_lt, mul_neg_iff,
    and_true]
  simp only [Int.cast_lt_zero, Int64.coe_neg_iff, not_lt.mpr xn, false_or, if_false, not_lt.mpr yn,
    true_and]
  have en : x.n.toUInt64 < y.n.toUInt64 ↔ x.n < y.n := by
    simp only [UInt64.lt_iff_toNat_lt, ← Int64.coe_lt_coe, Int64.coe_of_nonneg, xn, yn,
      Nat.cast_lt]
  by_cases se : x.s = y.s
  · simp only [se, two_zpow_pos, mul_lt_mul_right, Int.cast_lt, Int64.coe_lt_coe,
      lt_self_iff_false, en, true_and, false_or]
  simp only [se, false_and, or_false]
  by_cases xys : x.s < y.s
  · simp only [Int.reducePow, xys, iff_true]
    have ys0 : y.s ≠ 0 := (trans x.s.nonneg xys).ne'
    refine lt_of_lt_of_le (mul_lt_mul_of_pos_right coe_coe_n_lt two_zpow_pos) ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_coe_coe_n ys0 yn) two_zpow_pos.le)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_mul_zpow, Nat.cast_ofNat]
    apply zpow_le_zpow_right₀ (by norm_num)
    simp only [UInt64.lt_iff_toNat_lt] at xys
    omega
  · simp only [Int.reducePow, xys, iff_false, not_lt]
    replace xys := (Ne.symm se).lt_of_le (not_lt.mp xys)
    have xs0 : x.s ≠ 0 := (trans y.s.nonneg xys).ne'
    refine le_trans (mul_le_mul_of_nonneg_right coe_coe_n_lt.le two_zpow_pos.le) ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_coe_coe_n xs0 xn) two_zpow_pos.le)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_mul_zpow, Nat.cast_ofNat]
    apply zpow_le_zpow_right₀ (by norm_num)
    simp only [UInt64.lt_iff_toNat_lt] at xys
    omega

/-- The order is consistent with `.val` -/
@[simp] lemma val_lt_val {x y : Floating} : x < y ↔ x.val < y.val := by
  symm
  by_cases xn : x.n < 0
  · by_cases yn : y.n < 0
    · by_cases xm : x = nan
      · by_cases ym : y = nan
        · simp only [xm, ym, lt_self_iff_false, not_lt_nan]
        · simp only [xm, ne_eq, ym, not_false_eq_true, val_nan_lt, nan_lt]
      · by_cases ym : y = nan
        · simp only [ym, not_lt_nan, iff_false, not_lt, val_nan_le]
        · by_cases x0 : x = 0
          · simp only [x0, val_zero]
            have h0 : y < 0 := by simpa only [isNeg_iff', decide_eq_true_eq] using yn
            have h1 : y.val < 0 := by simpa only [isNeg_iff, decide_eq_true_eq] using yn
            simp only [not_lt.mpr h1.le, not_lt_of_lt h0]
          · by_cases y0 : y = 0
            · simp only [y0, val_zero]
              have h0 : x < 0 := by simpa only [isNeg_iff', decide_eq_true_eq] using xn
              have h1 : x.val < 0 := by simpa only [isNeg_iff, decide_eq_true_eq] using xn
              simp only [h1, h0]
            · rw [←neg_lt_neg ym xm, ←neg_lt_neg_iff, ←val_neg xm, ←val_neg ym]
              apply val_lt_val_of_nonneg
              · simpa only [n_neg, Int64.isNeg_neg (y.n_ne_zero y0) (y.n_ne_min ym),
                  Bool.not_eq_false', ← not_lt, not_not]
              · simpa only [n_neg, Int64.isNeg_neg (x.n_ne_zero x0) (x.n_ne_min xm),
                  Bool.not_eq_false', ← not_lt, not_not]
    · simp only at yn
      trans True
      · simp only [isNeg_iff, not_lt] at xn yn
        simp only [iff_true]
        linarith
      · simp only [lt_def, Int64.isNeg, xn, decide_true, yn, decide_false, gt_iff_lt,
          Bool.false_lt_true, Bool.true_eq_false, ↓reduceIte, false_and, or_false]
  · by_cases yn : y.n < 0
    · simp only at xn
      trans False
      · simp only [isNeg_iff, not_lt] at xn yn
        simp only [iff_false, not_lt]
        linarith
      · simp only [lt_def, Int64.isNeg, xn, decide_false, yn, decide_true, gt_iff_lt,
          Bool.false_eq_true, ↓reduceIte, false_and, or_false, false_iff, not_lt, Bool.le_true]
    · simp only at xn yn
      exact val_lt_val_of_nonneg (not_lt.mp xn) (not_lt.mp yn)

/-- The order is consistent with `.val` -/
@[simp] lemma val_le_val {x y : Floating} : x ≤ y ↔ x.val ≤ y.val := by
  rw [←not_lt, le_def, not_iff_not, val_lt_val]

@[bound] lemma val_le_val_of_le {x y : Floating} (le : x ≤ y) : x.val ≤ y.val := by
  simpa only [val_le_val] using le

/-- `Floating` is a partial order -/
instance : LinearOrder Floating where
  le_refl x := by simp only [val_le_val, le_refl]
  le_trans x y z := by simp only [val_le_val]; apply le_trans
  le_antisymm x y := le_antisymm'
  le_total x y := by simp only [val_le_val]; apply le_total
  lt_iff_le_not_ge x y := by
    simp only [val_lt_val, val_le_val]; apply lt_iff_le_not_ge
  toDecidableLE x y := by infer_instance
  min_def x y := by simp only [min, ble_eq_le, bif_eq_if, decide_eq_true_eq]
  max_def x y := by simp only [Max.max, ble_eq_le, bif_eq_if, decide_eq_true_eq]

/-- `val` is injective -/
@[simp] lemma val_inj {x y : Floating} : x.val = y.val ↔ x = y := by
  constructor
  · intro h; apply le_antisymm
    all_goals simp only [val_le_val, h, le_refl]
  · intro h; simp only [h]

@[simp] lemma lt_zero_iff {x : Floating} : x < 0 ↔ x.val < 0 := by
  rw [←val_zero]; exact val_lt_val

@[simp] lemma nonneg_iff {x : Floating} : 0 ≤ x ↔ 0 ≤ x.val := by
  rw [←val_zero]; exact val_le_val

@[simp] lemma not_nan_nonneg : ¬0 ≤ (nan : Floating).val := by
  simpa only [val_lt_val, val_zero, not_le] using nan_lt_zero

@[simp] lemma not_nan_pos : ¬0 < (nan : Floating).val := by
  simpa only [val_le_val, val_zero, not_lt] using nan_lt_zero.le

lemma ne_nan_of_nonneg {x : Floating} (n : 0 ≤ x.val) : x ≠ nan := by
  contrapose n; simp only [ne_eq, not_not] at n; simp only [n, not_nan_nonneg, not_false_eq_true]

lemma ne_nan_of_le {x y : Floating} (n : x ≠ nan) (le : x.val ≤ y.val) : y ≠ nan := by
  contrapose n
  simp only [ne_eq, not_not, ←val_inj] at n ⊢
  simp only [n] at le
  exact le_antisymm le (val_nan_le _)

/-- If we're positive, `n` is small -/
lemma n_lt_of_nonneg {x : Floating} (x0 : 0 ≤ x.val) : x.n.toUInt64.toNat < 2^63 := by
  have h : 0 ≤ x.n := by simpa only [n_nonneg_iff] using x0
  simpa only [Int64.isNeg_eq_le, decide_eq_false_iff_not, ← not_lt, not_not] using h

/-!
### Facts about `min` and `max`
-/

/-- `min` propagates `nan` -/
@[simp] lemma min_nan (x : Floating) : min x nan = nan := by
  simp only [min, bif_eq_if, ite_eq_right_iff]
  intro le; exact le_antisymm le (nan_le x)

/-- `min` propagates `nan` -/
@[simp] lemma nan_min (x : Floating) : min nan x = nan := by
  simp only [min, ble_eq_le, nan_le, decide_true, cond_true]

/-- `min` propagates `nan` -/
lemma ne_nan_of_min {x y : Floating} (n : min x y ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose n; simp only [ne_eq, not_and_or, not_not] at n ⊢
  rcases n with n | n; repeat simp only [n, min_nan, nan_min]

/-- `min` never produces new `nan`s -/
lemma eq_nan_of_min {x y : Floating} (n : min x y = nan) : x = nan ∨ y = nan := by
  rw [min_def] at n; split_ifs at n; repeat simp only [n, true_or, or_true]

/-- `Floating.max` propagates `nan` (`Max.max` does not) -/
@[simp] lemma max_nan (x : Floating) : x.max nan = nan := by
  rw [max]; simp only [neg_nan, nan_le, min_eq_right]

/-- `Floating.max` propagates `nan` (`Max.max` does not) -/
@[simp] lemma nan_max (x : Floating) : (nan : Floating).max x = nan := by
  rw [max]; simp only [neg_nan, nan_le, min_eq_left]

/-- `Floating.min` propagates `nan` (`Max.max` does not) -/
lemma ne_nan_of_max {x y : Floating} (n : x.max y ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose n; simp only [ne_eq, not_and_or, not_not] at n ⊢
  rcases n with n | n; repeat simp only [n, nan_max, max_nan]

/-- `Floating.max` never produces new `nan`s -/
lemma eq_nan_of_max {x y : Floating} (n : x.max y = nan) : x = nan ∨ y = nan := by
  rw [max] at n; simp only [neg_eq_nan_iff] at n
  rcases eq_nan_of_min n with n | n
  repeat { simp only [neg_eq_nan_iff] at n; simp only [n, true_or, or_true] }

/-- `min` is `nan` if an argument is -/
@[simp] lemma min_eq_nan {x y : Floating} : min x y = nan ↔ x = nan ∨ y = nan := by
  refine ⟨eq_nan_of_min, ?_⟩
  intro n; rcases n with n | n; repeat simp only [n, min_nan, nan_min]

/-- `Floating.max` is `nan` if an argument is -/
@[simp] lemma max_eq_nan {x y : Floating} : x.max y = nan ↔ x = nan ∨ y = nan := by
  refine ⟨eq_nan_of_max, ?_⟩
  intro n; rcases n with n | n; repeat simp only [n, max_nan, nan_max]

/-- `max` is `nan` if both arguments are -/
@[simp] lemma max_eq_nan' {x y : Floating} : Max.max x y = nan ↔ x = nan ∧ y = nan := by
  rw [max_def]
  by_cases xn : x = nan; · simp [xn]
  by_cases yn : y = nan; · simp [xn, yn]
  split_ifs
  all_goals simp [xn, yn]

/-- `Floating.max` is `nan` if an argument is -/
@[simp] lemma max_ne_nan {x y : Floating} : x.max y ≠ nan ↔ x ≠ nan ∧ y ≠ nan := by
  simp only [ne_eq, max_eq_nan, not_or]

/-- `min` commutes with `val` -/
@[simp] lemma val_min {x y : Floating} : (min x y).val = min x.val y.val := by
  simp only [LinearOrder.min_def, apply_ite (f := Floating.val), val_le_val]

/-- `Floating.max` commutes with `val` away from `nan` -/
@[simp] lemma val_max {x y : Floating} (xn : x ≠ nan) (yn : y ≠ nan) :
    (x.max y).val = Max.max x.val y.val := by
  rw [max]
  simp only [min_def, neg_le_neg xn yn, apply_ite (f := fun x : Floating ↦ (-x).val), neg_neg,
    LinearOrder.max_def, val_le_val]
  by_cases xy : x.val ≤ y.val
  · simp [xy, ite_eq_right_iff]
    intro yx; simp only [le_antisymm xy yx, ←val_inj]
  · simp only [not_le] at xy
    simp only [xy.le, ite_true, not_le.mpr xy, ite_false]

/-- `Floating.max` commutes with `val` away from `nan` -/
@[simp] lemma val_max' {x y : Floating} (n : x.max y ≠ nan) :
    (x.max y).val = Max.max x.val y.val := by
  simp only [max_ne_nan] at n; exact val_max n.1 n.2

@[simp] lemma max_self (x : Floating) : x.max x = x := by
  simp only [max, min_self, neg_neg]

/-- `Floating.max` is commutative -/
lemma max_comm (x y : Floating) : x.max y = y.max x := by
  simp only [max, min_comm]

/-- `Floating.max` is associative -/
lemma max_assoc (x y z : Floating) : (x.max y).max z = x.max (y.max z) := by
  simp only [max, min_assoc, neg_neg]

/-- `max_eq_left` for `Floating.max`, if we're not `nan` -/
@[simp] lemma max_eq_left {x y : Floating} (yx : y.val ≤ x.val) (yn : y ≠ nan) : x.max y = x := by
  rw [max, min_eq_left]
  · simp only [neg_neg]
  · by_cases xn : x = nan
    · simp only [xn, neg_nan, val_le_val, val_nan_le]
    · simp only [val_le_val, ne_eq, xn, not_false_eq_true, val_neg, yn, neg_le_neg_iff, yx]

/-- `max_eq_right` for `Floating.max`, if we're not `nan` -/
@[simp] lemma max_eq_right {x y : Floating} (xy : x.val ≤ y.val) (xn : x ≠ nan) : x.max y = y := by
  rw [max_comm, max_eq_left xy xn]

@[simp] lemma val_nan_lt_zero : (nan : Floating).val < 0 := by
  simp only [←lt_zero_iff, nan_lt_zero]

/-!
### Additional facts about "naive" min and max (discarding single nans)

`Min.min` propagates nans, and `Max.max` is already naive, so we only need to define `naive_min`.
-/

/-- `min` that discards single `nan`s -/
def naive_min (x y : Floating) : Floating := -Max.max (-x) (-y)

lemma naive_min_eq_nan {x y : Floating} : naive_min x y = nan ↔ x = nan ∧ y = nan := by
  simp only [naive_min, neg_eq_nan_iff, max_eq_nan']

lemma naive_max_eq_nan {x y : Floating} : Max.max x y = nan ↔ x = nan ∧ y = nan := max_eq_nan'

@[simp] lemma nan_naive_min {x : Floating} : naive_min nan x = x := by simp [naive_min]
@[simp] lemma naive_min_nan {x : Floating} : naive_min x nan = x := by simp [naive_min]
@[simp] lemma nan_naive_max {x : Floating} : Max.max nan x = x := by simp
@[simp] lemma naive_max_nan {x : Floating} : Max.max x nan = x := by simp

/-- `Max.max` commutes with `val` -/
@[simp] lemma val_naive_max {x y : Floating} : (Max.max x y).val = Max.max x.val y.val := by
  simp only [LinearOrder.max_def, apply_ite (f := Floating.val), val_le_val]

/-- `naive_min` commutes with `val` if neither argument is `nan` -/
@[simp] lemma val_naive_min {x y : Floating} (xn : x ≠ nan) (yn : y ≠ nan) :
    (naive_min x y).val = min x.val y.val := by
  simp [naive_min, xn, yn, max_neg_neg]
