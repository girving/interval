import Batteries.Lean.Float
import Mathlib.Data.Int.Bitwise
import Mathlib.Data.Real.Basic
import Interval.Approx.Approx
import Interval.Int64
import Interval.UInt128
import Interval.Misc.Int
import Interval.Misc.Real

/-!
## 64-bit fixed point numbers
-/

open Pointwise
open Set
open scoped Real

variable {α : Type}
variable {s t : Int64}
variable {a : ℝ}

/-!
### `Fixed` definitions and basics
-/

/-- A 64-bit fixed point number, corresponding to either
    1. `n * 2^s`, if `n ≠ Int64.min`
    2. Arbitrary, if `n = Int64.min` -/
@[unbox] structure Fixed (s : Int64) where
  n : Int64
  deriving DecidableEq, BEq

/-- Sentinel value, indicating we don't know what the number is -/
instance : Nan (Fixed s) where
  nan := ⟨.minValue⟩

/-- Reduce `Fixed s` equality to `Int64` equality -/
@[to_bitvec] lemma Fixed.ext_iff (x y : Fixed s) : x = y ↔ x.n = y.n := by
  induction' x with x; induction' y with y; simp only [mk.injEq]

/-- `Fixed s` has nice equality -/
instance : LawfulBEq (Fixed s) where
  eq_of_beq {x y} e := by
    simp only [BEq.beq] at e
    rw [Fixed.ext_iff, Int64.ext_iff]
    rw [eq_of_beq e]
  rfl {x} := beq_self_eq_true' x.n

/-- The `ℝ` that a `Fixed` represents, if it's not `nan` -/
noncomputable def Fixed.val (x : Fixed s) :=
  ((x.n : ℤ) : ℝ) * (2 : ℝ)^(s : ℤ)

/-- Approximate `Fixed s` by a `Float` -/
def Fixed.toFloat (x : Fixed s) :=
  bif x == nan then Float.nan else x.n.toFloat.scaleB s

/-- We print `Fixed s` as an approximate floating point number -/
instance : Repr (Fixed s) where
  reprPrec x _ := x.toFloat.toStringFull

/-- `0` is easy regardless of `s` -/
instance : Zero (Fixed s) where
  zero := ⟨0⟩

lemma Fixed.zero_def : (0 : Fixed s) = ⟨0⟩ := rfl
lemma Fixed.nan_def : (nan : Fixed s) = ⟨Int64.minValue⟩ := rfl
@[simp] lemma Fixed.zero_n : (0 : Fixed s).n = 0 := rfl
@[simp] lemma Fixed.nan_n : (nan : Fixed s).n = Int64.minValue := rfl

@[simp] lemma Fixed.val_zero : (0 : Fixed s).val = 0 := by
  simp only [val, zero_def, Int64.coe_zero, Int.cast_zero, zero_mul]

lemma Fixed.val_of_s0 {x : Fixed 0} : x.val = ↑x.n := by
  simp only [val, Int64.coe_zero, zpow_zero, mul_one]

@[simp] lemma Fixed.isNeg_nan : (nan : Fixed s).n < 0 := by
  rw [nan_n]; rfl

@[simp] lemma Fixed.zero_ne_nan : 0 ≠ (nan : Fixed s) := by
  simp only [nan, ne_eq, Fixed.ext_iff, Fixed.zero_n, Int64.ext_iff, Int64.n_zero, Int64.n_min]
  decide +kernel

lemma Fixed.val_eq_val {x y : Fixed s} : x.val = y.val ↔ x = y := by
  rw [val, val]
  simp only [mul_eq_mul_right_iff, Int.cast_inj, Int64.coe_eq_coe, ext_iff, or_iff_left_iff_imp]
  intro z
  replace z := eq_zero_of_zpow_eq_zero z
  norm_num at z

/-!
### Additive group operations: `add, sub, neg`
-/

/-- `Fixed` negation -/
def Fixed.neg (x : Fixed s) : Fixed s := ⟨-x.n⟩
instance : Neg (Fixed s) where neg x := x.neg
lemma Fixed.neg_def (x : Fixed s) : -x = x.neg := rfl

/-- `-nan = nan` -/
@[simp] lemma Fixed.neg_nan : -(nan : Fixed s) = nan := by
  simp only [nan, neg_def, neg, Int64.neg_def, ext_iff]
  decide +kernel

/-- The contrapose of `-nan = nan` -/
@[simp] lemma Fixed.ne_nan_of_neg {x : Fixed s} (h : -x ≠ nan) : x ≠ nan := by
  contrapose h
  simp only [h, neg_nan]

/-- `Fixed` addition saturates to `nan` -/
@[irreducible] def Fixed.add (x y : Fixed s) :=
  let z : Fixed s := ⟨x.n + y.n⟩
  bif x == nan || y == nan || (x.n.isNeg == y.n.isNeg && x.n.isNeg != z.n.isNeg) then nan else z
instance : Add (Fixed s) where add x y := x.add y
lemma Fixed.add_def (x y : Fixed s) : x + y = x.add y := rfl

/-- `Fixed` subtraction saturates to `nan` -/
@[irreducible] def Fixed.sub (x y : Fixed s) :=
  let z : Fixed s := ⟨x.n - y.n⟩
  bif x == nan || y == nan || (x.n.isNeg != y.n.isNeg && x.n.isNeg != z.n.isNeg) then nan else z
instance : Sub (Fixed s) where sub x y := x.sub y
lemma Fixed.sub_def (x y : Fixed s) : x - y = x.sub y := rfl

/-- `Fixed` addition with fewer bools -/
lemma Fixed.add_as_eq (x y : Fixed s) : x + y = (
    let z : Fixed s := ⟨x.n + y.n⟩
    if x = nan ∨ y = nan ∨ (x.n.isNeg = y.n.isNeg ∧ x.n.isNeg ≠ z.n.isNeg) then nan else z) := by
  rw [Fixed.add_def, add, bif_eq_if]
  simp only [bne, Bool.or_assoc, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq]

/-- `-(-x) = x` -/
instance : InvolutiveNeg (Fixed s) where
  neg_neg x := by induction' x with x; simp only [Fixed.neg_def, Fixed.neg, _root_.neg_neg]

/-- Negation preserves `nan` -/
@[simp] lemma Fixed.neg_eq_nan {x : Fixed s} : (-x) = nan ↔ x = nan := by
  have i : ∀ {x : Fixed s}, x = nan → (-x) = nan := by
    intro x h
    simp only [h, nan, neg_def, neg, Int64.neg_def, mk.injEq]
    decide +kernel
  by_cases a : x = nan
  · simp only [a, neg_nan]
  · by_cases b : (-x) = nan
    · rw [b, ←neg_neg x, i b]
    · simp only [a, b]

/-- Negation preserves `nan` -/
@[simp] lemma Fixed.neg_ne_nan {x : Fixed s} : (-x) ≠ nan ↔ x ≠ nan := by
  simp only [ne_eq, neg_eq_nan]

 /-- Negation preserves `nan` -/
@[simp] lemma Fixed.neg_beq_nan {x : Fixed s} : ((-x) == nan) = (x == nan) := by
  simp only [Bool.beq_eq_decide_eq', neg_eq_nan]

/-- Negation flips `isNeg` unless we're `0` or `nan` -/
lemma Fixed.isNeg_neg {x : Fixed s} (x0 : x.n ≠ 0) (xn : x ≠ nan) : (-x.n).isNeg = !x.n.isNeg := by
  simp only [Int64.isNeg, decide_eq_not_decide, decide_eq_true_iff, not_lt]
  apply Int64.isNeg_neg x0
  simp only [Ne, Fixed.ext_iff] at xn
  exact xn

/-- `x - y = x + (-y)` -/
lemma Fixed.sub_eq_add_neg (x y : Fixed s) : x - y = x + (-y) := by
  rw [sub_def, sub, add_def, add]
  simp only [Bool.cond_eq_ite, Bool.beq_eq_decide_eq', Bool.or_eq_true,
    decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq, neg_eq_nan]
  by_cases nx : x = nan
  · simp only [nx, true_or, ite_true]
  by_cases ny : y = nan
  · simp only [ny, or_true, true_or, ite_true, neg_nan]
  simp only [nx, ny, neg_def, neg]
  by_cases y0 : y.n = 0
  · simp only [y0, sub_zero, not_true, and_false, or_self, ite_false, neg_zero, add_zero]
  · simp only [_root_.sub_eq_add_neg, false_or, Fixed.isNeg_neg y0 ny, Bool.beq_not_iff_ne, ne_eq]

lemma Fixed.add_comm (x y : Fixed s) : x + y = y + x := by
  simp only [Fixed.add_as_eq, _root_.add_comm]
  refine if_congr ?_ rfl rfl
  by_cases xn : x = nan
  · by_cases yn : y = nan
    · simp only [xn, yn, ne_eq, true_and, true_or, or_self]
    · simp only [xn, ne_eq, true_or, or_true]
  · by_cases yn : y = nan
    · simp only [yn, ne_eq, true_or, or_true]
    · simp only [xn, yn, ne_eq, false_or]
      by_cases x0 : x.n.isNeg; repeat {
        by_cases y0 : y.n.isNeg
        repeat simp only [x0, y0, true_and, false_and, Bool.true_eq_false, Bool.false_eq_true] }

-- Addition and subtraction propagate nans
@[simp] lemma Fixed.nan_add {x : Fixed s} : nan + x = nan := by
  simp only [add_def, add, beq_self_eq_true, Bool.true_or, cond_true]
@[simp] lemma Fixed.add_nan {x : Fixed s} : x + nan = nan := by
  rw [Fixed.add_comm, Fixed.add_def, Fixed.add]; rfl
@[simp] lemma Fixed.nan_sub {x : Fixed s} : nan - x = nan := by simp only [sub_eq_add_neg, nan_add]
@[simp] lemma Fixed.sub_nan {x : Fixed s} : x - nan = nan := by
  simp only [sub_eq_add_neg, neg_nan, add_nan]

/-- If `x + y ≠ nan`, neither `x` or `y` are `nan` -/
lemma Fixed.ne_nan_of_add {x y : Fixed s} (h : x + y ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose h; simp only [not_and_or, not_not] at h
  cases' h with h h
  · simp only [h, nan_add]
  · simp only [h, add_nan]

/-- If `x - y ≠ nan`, neither `x` or `y` are `nan` -/
lemma Fixed.ne_nan_of_sub {x y : Fixed s} (h : x - y ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose h; simp only [not_and_or, not_not] at h
  cases' h with h h
  · simp only [h, nan_sub]
  · simp only [h, sub_nan]

/-- `Fixed.val` commutes with negation, except at `nan` -/
lemma Fixed.val_neg {x : Fixed s} (xn : x ≠ nan) : (-x).val = -x.val := by
  simp only [Ne, Fixed.ext_iff, nan] at xn
  simp only [val, neg_def, neg, Int64.coe_neg' xn, Int.cast_neg, neg_mul]

/-- `Fixed.val` commutes with add if `isNeg` matches the left argument -/
lemma Fixed.val_add_eq {x y : Fixed s} (h : (x.n + y.n).isNeg = x.n.isNeg) :
    (⟨x.n + y.n⟩ : Fixed s).val = x.val + y.val := by
  simp only [Int64.isNeg, decide_eq_decide] at h
  simp only [val, Int64.coe_add_eq h, Int.cast_add, add_mul]

/-- `Fixed.val` commutes with add if the two arguments have different `isNeg`s -/
lemma Fixed.val_add_ne {x y : Fixed s} (h : x.n.isNeg ≠ y.n.isNeg) :
    (⟨x.n + y.n⟩ : Fixed s).val = x.val + y.val := by
  simp only [Int64.isNeg, ne_eq, decide_eq_decide] at h
  simp only [val, Int64.coe_add_ne h, Int.cast_add, add_mul]

/-- `Fixed` approximates `ℝ` -/
instance : Approx (Fixed s) ℝ where
  approx x a := x = nan ∨ x.val = a

instance : ApproxNan (Fixed s) ℝ where
  approx_nan a := by simp only [approx, true_or]

@[simp] lemma Fixed.approx_nan : approx (nan : Fixed s) a := by
  simp only [approx, nan, true_or]

@[approx] lemma Fixed.approx_val (x : Fixed s) : approx x x.val := by
  simp only [approx, or_true]

@[simp] lemma Fixed.approx_zero_iff : approx (0 : Fixed s) a ↔ a = 0 := by
  simp only [approx, nan, ext_iff, zero_n, Int64.zero_def, Int64.ext_iff, Int64.n_min, val_zero,
    eq_comm (a := a)]
  simp only [UInt64.toInt64_ofNat, Int64.n_zero, or_iff_right_iff_imp]
  intro h; contrapose h; clear h; decide +kernel

instance : ApproxZero (Fixed s) ℝ where
  approx_zero := by simp only [approx, Fixed.val_zero, or_true]

instance : ApproxZeroIff (Fixed s) ℝ where
  approx_zero_imp x a := by simpa only [Fixed.approx_zero_iff] using a

/-- If we're not `nan`, `approx` is a singleton -/
@[simp] lemma Fixed.approx_eq_singleton {x : Fixed s} (n : x ≠ nan) : approx x a ↔ x.val = a := by
  simp only [approx, n, false_or]

/-- `Fixed` negation respects `approx` -/
instance : ApproxNeg (Fixed s) ℝ where
  approx_neg {x a} m := by
    simp only [approx, Fixed.neg_eq_nan, Fixed.neg_eq_nan] at m ⊢
    by_cases h : x = nan
    · simp only [h, Fixed.neg_nan, true_or]
    · simpa only [h, Fixed.val_neg h, neg_inj, false_or] using m

/-- For `Fixed`, `-` and `approx` commute -/
@[simp] lemma Fixed.approx_neg (x : Fixed s) : approx (-x) (-a) ↔ approx x a := by
  by_cases n : x = nan
  · simp only [n, neg_nan, approx_nan]
  · simp only [approx_eq_singleton (neg_ne_nan.mpr n), val_neg n, neg_inj, approx_eq_singleton n]

/-- `Fixed` addition respects `approx` -/
instance : ApproxAdd (Fixed s) ℝ where
  approx_add {x y} {a b} xa yb := by
    simp only [Fixed.add_as_eq, approx] at xa yb ⊢
    by_cases xn : x = nan
    · simp only [xn, true_or, Fixed.nan_n, ne_eq, ↓reduceIte]
    · by_cases yn : y = nan
      · simp only [yn, true_or, Fixed.nan_n, ne_eq, or_true, ↓reduceIte]
      · simp only [xn, yn, ne_eq, false_or, ite_eq_left_iff, not_and, not_not] at xa yb ⊢
        by_cases x0 : x.n.isNeg
        · by_cases z0 : (x.n + y.n).isNeg
          · simp only [x0, Bool.true_eq, z0, implies_true, forall_const, not_true_eq_false,
              and_false, ↓reduceIte, Fixed.val_add_eq (z0.trans x0.symm), xa, yb, or_true]
          · by_cases y0 : y.n.isNeg
            · simp only [x0, y0, z0, Bool.true_eq_false, imp_false, not_true_eq_false,
                IsEmpty.forall_iff, not_false_eq_true, and_self, ↓reduceIte, true_or]
            · simp only [x0, y0, Bool.true_eq, Bool.false_eq_true, IsEmpty.forall_iff,
                forall_const, Bool.not_eq_true, false_and, ↓reduceIte,
                Fixed.val_add_ne (x0.trans_ne (Ne.symm y0)), xa, yb, or_true]
        · by_cases y0 : y.n.isNeg
          · simp [x0, y0, IsEmpty.forall_iff, false_and, Fixed.val_add_ne (Ne.trans_eq x0 y0.symm),
              Bool.false_eq_true, xa, yb]
          · by_cases z0 : (x.n + y.n).isNeg
            · simp only [x0, y0, z0, Bool.false_eq_true, imp_false, not_true_eq_false,
                IsEmpty.forall_iff, not_false_eq_true, and_self, ↓reduceIte, true_or]
            · simp only [Bool.not_eq_true] at x0 z0
              simp only [x0, y0, z0, imp_self, forall_const, not_true_eq_false, and_false,
                ↓reduceIte, Fixed.val_add_eq (z0.trans x0.symm), xa, yb, or_true]

/-- `Fixed.val` commutes with add if the result isn't `nan` -/
lemma Fixed.val_add {x y : Fixed s} (n : x + y ≠ nan) : (x + y).val = x.val + y.val := by
  have h := approx_add (approx_val x) (approx_val y)
  simp only [approx, n, false_or] at h
  rw [h]

/-- `Fixed` subtraction respects `approx` -/
instance : ApproxSub (Fixed s) ℝ where
  approx_sub {x y} {a b} xa yb := by
    simp only [Fixed.sub_eq_add_neg, sub_eq_add_neg]
    exact approx_add xa (approx_neg yb)

/-- `Fixed.val` commutes with sub if the result isn't `nan` -/
lemma Fixed.val_sub {x y : Fixed s} (n : x - y ≠ nan) : (x - y).val = x.val - y.val := by
  have h := approx_sub (approx_val x) (approx_val y)
  simp only [approx, n, false_or] at h
  rw [h]

/-- `neg_add` for `Fixed s` -/
lemma Fixed.neg_add {x y : Fixed s} : -(x + y) = -y + -x := by
  simp only [add_as_eq, ext_iff, nan_n, ne_eq, neg_def, neg, apply_ite (f := fun x : Fixed s ↦ x.n),
    Int64.neg_eq_min]
  by_cases xn : x.n = .minValue
  · simp only [xn, true_or, ite_true, or_true]
    rfl
  by_cases yn : y.n = .minValue
  · simp only [yn, true_or, or_true, ite_true]
    rfl
  simp only [xn, yn, false_or]
  by_cases x0 : x.n = 0
  · simp only [x0, zero_add, and_not_self, ite_false, neg_zero, add_zero, not_true_eq_false,
    and_false]
  by_cases y0 : y.n = 0
  · simp only [y0, zero_add, and_not_self, ite_false, neg_zero, add_zero, not_true_eq_false,
    and_false]
  simp only at xn yn
  have e : -y.n + -x.n = -(x.n + y.n) := by ring
  simp only [Int64.isNeg_neg y0 yn, Int64.isNeg_neg x0 xn, apply_ite (f := fun x : Int64 ↦ -x), e,
    Int64.isNeg, decide_eq_decide, not_iff, ← not_lt, not_iff_not, not_not]
  by_cases xyn : x.n.isNeg = y.n.isNeg
  · simp only [Int64.isNeg, decide_eq_decide] at xyn
    simp only [xyn, true_and]
    by_cases xym : x.n + y.n = .minValue
    · simp only [not_lt, xym, Int64.isNeg_min, iff_true, Int64.neg_min, ite_self]
    · have xy0 : x.n + y.n ≠ 0 := by
        contrapose xyn
        simp only [eq_neg_iff_add_eq_zero.mpr xyn, Int64.isNeg_neg y0 yn, ← not_le, iff_not_self,
          not_false_eq_true]
      simp only [Int64.isNeg_neg xy0 xym, ite_not, ← not_iff]
      by_cases y0 : y.n < 0
      · simp only [y0, true_iff, neg_add_rev, Int64.neg_min, ← not_lt, ite_not]
      · simp only [y0, false_iff, neg_add_rev, Int64.neg_min, ite_not, ← not_lt, Decidable.not_not]
  · simp only [Int64.isNeg, decide_eq_decide] at xyn
    simp only [xyn, false_and, if_false, iff_comm (b := x.n < 0)]

/-- `neg_sub` for `Fixed s` -/
lemma Fixed.neg_sub {x y : Fixed s} : -(x - y) = y - x := by
  simp only [sub_eq_add_neg, Fixed.neg_add, neg_neg]

/-- `Fixed` approximates `ℝ` as an additive group -/
instance : ApproxAddGroup (Fixed s) ℝ where

lemma Fixed.rounds_iff {x : Fixed s} {up : Bool} :
    Rounds x a up ↔ (x ≠ nan → if up then a ≤ x.val else x.val ≤ a) := by
  simp only [Rounds, approx]
  constructor
  · aesop
  · intro h
    by_cases n : x = nan
    · use a
      simp only [n, true_or, le_refl, ite_self, and_self]
    · aesop

/-!
### Order operations on `Fixed`: min, max, abs
-/

lemma Fixed.val_lt_zero {x : Fixed s} : x.val < 0 ↔ x.n < 0 := by
  simp only [val, mul_neg_iff, Int.cast_pos, two_zpow_not_neg, and_false, Int.cast_lt_zero,
    Int64.coe_lt_zero_iff, two_zpow_pos, and_true, false_or]

lemma Fixed.val_nonneg {x : Fixed s} : 0 ≤ x.val ↔ ¬x.n < 0 := by
  rw [←not_iff_not]; simp only [not_le, val_lt_zero, not_not]

lemma Fixed.val_nonpos {x : Fixed s} : x.val ≤ 0 ↔ x.n ≤ 0 := by
  simp only [val, mul_nonpos_iff, two_zpow_pos.le, and_true, two_zpow_not_nonpos,
    and_false, false_or, Int.cast_nonpos, Int64.coe_nonpos_iff]

lemma Fixed.val_pos {x : Fixed s} : 0 < x.val ↔ 0 < x.n := by
  simp only [val, two_zpow_pos, mul_pos_iff_of_pos_right, Int.cast_pos, Int64.coe_pos_iff]

lemma Fixed.isNeg_eq {x : Fixed s} : x.n < 0 ↔ x.val < 0 := by
  by_cases n : x.n < 0
  · simp only [n, true_iff]; rwa [val_lt_zero]
  · simp only at n; simp only [n, false_iff, not_lt]; rwa [val_nonneg]

/-- `x.val = 0` iff `x = 0` is -/
lemma Fixed.val_eq_zero_iff {x : Fixed s} : x.val ≠ 0 ↔ x ≠ 0 := by
  have z : (2:ℝ) ≠ 0 := by norm_num
  simp only [val, ne_eq, mul_eq_zero, Int.cast_eq_zero, Int64.coe_eq_zero, zpow_ne_zero _ z,
    or_false, ext_iff, zero_n]

/-- `x.val` is nonzero iff `x` is -/
lemma Fixed.val_ne_zero_iff {x : Fixed s} : x.val ≠ 0 ↔ x ≠ 0 := by
  simp only [val_eq_zero_iff]

instance : Min (Fixed s) where
  min x y := ⟨min x.n y.n⟩

/-- `Max.max` can't propagate `nan` sincde it needs to be order consistent -/
instance : Max (Fixed s) where
  max x y := ⟨max x.n y.n⟩

/-- `Fixed.max` propagates `nan` -/
@[irreducible] def Fixed.max (x y : Fixed s) : Fixed s :=
  -min (-x) (-y)  -- Use `min` so that `nan` propagates

/-- Unfortunately we can't use `|x|`, since that notation can't use our own implementation.-/
def Fixed.abs (x : Fixed s) : Fixed s :=
  ⟨x.n.uabs.toInt64⟩

lemma Fixed.min_def {x y : Fixed s} : min x y = ⟨min x.n y.n⟩ := rfl
lemma Fixed.max_def' {x y : Fixed s} : Max.max x y = ⟨Max.max x.n y.n⟩ := rfl
lemma Fixed.max_def {x y : Fixed s} : x.max y = -min (-x) (-y) := by rw [max]
lemma Fixed.abs_def {x : Fixed s} : x.abs = ⟨x.n.uabs.toInt64⟩ := rfl

@[simp] lemma Fixed.min_nan {x : Fixed s} : min x nan = nan := by
  simp only [nan, min_def, Int64.min_le, min_eq_right]

@[simp] lemma Fixed.nan_min {x : Fixed s} : min nan x = nan := by
  simp only [nan, min_def, Int64.min_le, min_eq_left]

@[simp] lemma Fixed.max_nan {x : Fixed s} : max x nan = nan := by
  simp only [max_def, neg_nan, min_nan]

@[simp] lemma Fixed.nan_max {x : Fixed s} : max nan x = nan := by
  simp only [max_def, neg_nan, nan_min]

@[simp] lemma Fixed.abs_nan : abs (nan : Fixed s) = nan := by
  simp only [abs, ext_iff, Int64.ext_iff, nan]
  decide

@[simp] lemma Fixed.abs_zero : abs (0 : Fixed s) = 0 := by
  simp only [abs, zero_n]; rfl

@[simp] lemma Fixed.abs_eq_nan {x : Fixed s} : abs x = nan ↔ x = nan := by
  simp only [abs, Int64.uabs, nan, ext_iff, Int64.ext_iff, Int64.n_min, UInt64.eq_iff_toNat_eq,
    UInt64.toNat_2_pow_63, UInt64.toUInt64_toInt64]
  by_cases n : x.n < 0
  · simp only [n, UInt64.toNat_neg, if_true]
    generalize x.n.toUInt64 = n
    by_cases n0 : n = 0
    · simp only [n0, UInt64.toNat_zero, tsub_zero]
      rfl
    · simp only [UInt64.size, Nat.reducePow]
      omega
  · simp only [n, if_false]

@[simp] lemma Fixed.abs_ne_nan {x : Fixed s} : abs x ≠ nan ↔ x ≠ nan := by
  simp only [ne_eq, abs_eq_nan]

@[simp] lemma Fixed.isNeg_abs {x : Fixed s} : (abs x).n < 0 ↔ x = nan := by
  rw [← val_lt_zero]
  simp only [val, abs, mul_neg_iff, Int.cast_pos, two_zpow_not_neg, and_false,
    Int.cast_lt_zero, Int64.uabs_lt_zero, two_zpow_pos, and_true, false_or, nan, ext_iff]

lemma Fixed.val_abs {x : Fixed s} (n : x ≠ nan) : (abs x).val = |x.val| := by
  simp only [val, abs_mul, abs_zpow, abs_two, mul_eq_mul_right_iff]
  left
  simp only [nan, ne_eq, ext_iff] at n
  simp only [abs_def, ← Int.cast_abs, Int64.coe_uabs' n]

lemma Fixed.approx_abs_eq {x : Fixed s} (n : x ≠ nan) : approx (abs x) a ↔ |x.val| = a := by
  simp only [approx, ne_eq, neg_neg, abs_eq_nan, n, not_false_eq_true, ne_nan_of_neg,
    Fixed.val_abs n, false_or]

lemma Fixed.approx_abs {x : Fixed s} (m : approx x a) : approx (abs x) (|a|) := by
  by_cases n : x = nan
  · simp only [approx, n, abs_nan, true_or]
  · simp only [approx, n, false_or] at m
    simp only [approx, ne_eq, neg_neg, abs_eq_nan, n, not_false_eq_true, ne_nan_of_neg, val_abs n,
      m, or_true]

@[simp] lemma Fixed.min_eq_nan {x y : Fixed s} : min x y = nan ↔ x = nan ∨ y = nan := by
  simp only [min, nan, ext_iff, Int64.eq_min_iff_min_lt]
  split_ifs with xy
  · constructor
    · intro h; exact Or.inl h
    · intro h; cases' h with h h
      · exact h
      · exact le_trans xy.le h
  · simp only [not_lt] at xy
    constructor
    · intro h; exact Or.inr h
    · intro h; cases' h with h h
      · exact le_trans xy h
      · exact h

@[simp] lemma Fixed.max_eq_nan {x y : Fixed s} : max x y = nan ↔ x = nan ∨ y = nan := by
  simp only [max, neg_eq_nan, min_eq_nan]

lemma Fixed.val_lt_val {x y : Fixed s} : x.val < y.val ↔ x.n < y.n := by
  rw [val, val, mul_lt_mul_iff_left₀ two_zpow_pos]
  simp only [Int.cast_lt, Int64.coe_lt_coe]

lemma Fixed.val_le_val {x y : Fixed s} : x.val ≤ y.val ↔ x.n ≤ y.n := by
  rw [val, val, mul_le_mul_iff_left₀ two_zpow_pos]
  simp only [Int.cast_le, Int64.coe_le_coe]

@[simp] lemma Fixed.val_min {x y : Fixed s} : (min x y).val = min x.val y.val := by
  simp only [min_def]
  by_cases h : x.n ≤ y.n
  · simp only [h, inf_of_le_left, val_le_val]
  · simp only [not_le] at h
    simp only [min_eq_right, h.le, val_le_val]

lemma Fixed.val_max {x y : Fixed s} (nx : x ≠ nan) (ny : y ≠ nan) :
    (x.max y).val = Max.max x.val y.val := by
  have n : min (-x) (-y) ≠ nan := by
    simp only [ne_eq, min_eq_nan, neg_eq_nan, nx, ny, or_self, not_false_eq_true]
  simp only [max, val_neg n, val_min, val_neg nx, val_neg ny, min_neg_neg, neg_neg]

lemma Fixed.min_comm {x y : Fixed s} : min x y = min y x := by
  simp only [min]
  split_ifs with l r r
  · simp only [not_lt.mpr r.le] at l
  · rfl
  · rfl
  · simp only [not_lt, Fixed.ext_iff] at l r ⊢
    exact le_antisymm l r

lemma Fixed.max_comm {x y : Fixed s} : max x y = max y x := by
  simp only [max, min_comm]

/-!
### Order lemmas about `nan`
-/

/-- `nan.val` is very negative -/
lemma Fixed.val_nan : (nan : Fixed s).val = -(2:ℝ) ^ (s + 63 : ℤ) := by
  simp only [nan, val]
  rw [Int64.coe_min']
  have e : (2:ℝ) ^ (63 : ℕ) = (2:ℝ) ^ (63 : ℤ) := rfl
  simp only [Int.cast_neg, Int.cast_pow, Int.cast_ofNat, neg_mul, neg_inj, e]
  rw [Int.add_comm, zpow_add₀]; norm_num

/-- `nan.val < 0` -/
@[simp] lemma Fixed.val_nan_neg : (nan : Fixed s).val < 0 := by
  simp only [val_nan, Left.neg_neg_iff, two_zpow_pos]

/-- ¬`0 ≤ nan.val` -/
@[simp] lemma Fixed.not_val_nan_nonneg : ¬0 ≤ (nan : Fixed s).val := not_le.mpr val_nan_neg

/-- ¬`0 < nan.val` -/
@[simp] lemma Fixed.not_val_nan_pos : ¬0 < (nan : Fixed s).val := not_lt.mpr val_nan_neg.le

/-- Positive `Fixed`s are `≠ nan` -/
lemma Fixed.ne_nan_of_pos {x : Fixed s} (h : 0 < x.val) : x ≠ nan := by
  contrapose h; simp only [not_lt, h, val_nan_neg.le]

/-!
### `Fixed` multiplication, rounding up or down
-/

/-- Cast a `UInt128` to `Fixed s`, ignoring `s`.  Too large values become `nan`. -/
def Fixed.of_raw_uint128 (n : UInt128) : Fixed s :=
  bif n.hi != 0 || n.lo.toInt64.isNeg then nan else ⟨n.lo.toInt64⟩

/-- If `of_raw_uint128 ≠ nan`, the input is small -/
lemma Fixed.lt_of_of_raw_uint128_ne_nan {n : UInt128} {s : Int64}
    (h : (of_raw_uint128 n : Fixed s) ≠ nan) : n.toNat < 2^63 := by
  simp only [of_raw_uint128, Int64.isNeg, Nat.reducePow, bif_eq_if, Bool.or_eq_true, bne_iff_ne,
    ne_eq, decide_eq_true_eq, ite_eq_left_iff, not_or, Decidable.not_not, not_le, and_imp,
    Classical.not_imp, Int64.isNeg_eq_le, UInt64.toUInt64_toInt64] at h
  rw [UInt128.toNat_def, h.1]
  simp only [UInt64.toNat_zero, zero_mul, zero_add]
  omega

/-- Multiply two positive, non-nan `Fixed`s -/
@[irreducible] def Fixed.mul_of_pos (x : Fixed s) (y : Fixed t) (u : Int64) (up : Bool) : Fixed u :=
  let d : Fixed 0 := ⟨s⟩ + ⟨t⟩ - ⟨u⟩
  bif d == nan then nan else
  let z := mul128 x.n.toUInt64 y.n.toUInt64
  of_raw_uint128 (bif d.n.isNeg then
    z.shiftRightRound (-d.n).toUInt64 up else z.shiftLeftSaturate d.n.toUInt64)

/-- Multiply, changing `s` and rounding up or down.  We have
  `z = x * y`
  `z.n * 2^u = x.n * y.n * 2^(s + t)`
  `z.n = x.n * y.n * 2^(s + t - u)` -/
@[irreducible] def Fixed.mul (x : Fixed s) (y : Fixed t) (u : Int64) (up : Bool) : Fixed u :=
  bif x == nan || y == nan then nan else
  let p := x.n.isNeg != y.n.isNeg
  let z := mul_of_pos (abs x) (abs y) u (up.xor p)
  bif p then -z else z

lemma Fixed.of_raw_uint128_val {n : UInt128} (h : (of_raw_uint128 n : Fixed s) ≠ nan) :
    (of_raw_uint128 n : Fixed s).val = (n : ℝ) * (2:ℝ)^(s : ℤ) := by
  simp only [of_raw_uint128, bif_eq_if, Bool.or_eq_true, bne_iff_ne, ne_eq, ite_eq_left_iff, not_or,
    not_not, Bool.not_eq_true, and_imp, not_forall, exists_prop, Int64.isNeg,
    decide_eq_false_iff_not, Int64.isNeg_eq_le] at h
  simp only [val, Int64.toInt_eq_if, of_raw_uint128, h.1, bne_self_eq_false, h.2.1, bif_eq_if,
    ite_false, CharP.cast_eq_zero, sub_zero, Nat.cast_ite, Nat.cast_pow, Nat.cast_ofNat,
    UInt128.toReal, UInt128.toNat_def, UInt64.toNat_zero, Bool.false_or, zero_mul, zero_add,
    Int.cast_natCast, Int.reducePow, Int64.isNeg, decide_eq_true_eq, Int64.isNeg_eq_le]
  simp only [UInt64.toUInt64_toInt64, UInt64.natCast_toNat, Nat.reducePow]

/-- If we're not `nan`, `shiftLeftSaturate` is nice -/
lemma Fixed.toNat_shiftLeftSaturate_of_ne_nan {x : UInt128} {s : UInt64} {t : Int64}
    (h : (of_raw_uint128 (x.shiftLeftSaturate s) : Fixed t) ≠ nan) :
    (x.shiftLeftSaturate s).toNat = x.toNat * 2 ^ s.toNat := by
  replace h := Fixed.lt_of_of_raw_uint128_ne_nan h
  simp only [UInt128.shiftLeftSaturate_eq, UInt128.toNat_ofNat, UInt128.toNat_max] at h ⊢
  generalize hn : x.toNat * 2 ^ s.toNat = n
  rw [hn] at h
  clear hn t s x
  have lt : min n (2 ^ 128 - 1) < 2^128 := min_lt_of_right_lt (by norm_num)
  simp only [ge_iff_le, Nat.mod_eq_of_lt lt, min_lt_iff, min_eq_left_iff] at h ⊢
  norm_num at h
  exact le_trans h.le (by norm_num)

/-- `Fixed.mul nan _ _ _ = nan` -/
@[simp] lemma Fixed.nan_mul {y : Fixed t} {u : Int64} {up : Bool} :
    Fixed.mul (nan : Fixed s) y u up = nan := by
  simp only [mul, beq_self_eq_true, Bool.true_or, abs_nan, cond_true]

/-- `Fixed.mul nan _ _ _ = nan` -/
@[simp] lemma Fixed.mul_nan {x : Fixed s} {u : Int64} {up : Bool} :
    Fixed.mul x (nan : Fixed t) u up = nan := by
  simp only [mul, beq_self_eq_true, Bool.or_true, abs_nan, cond_true]

lemma extract_exists_cond {c : Prop} {y : α} {e : α → Prop} :
    (∃ x, (c → x = y) ∧ e x) ↔ ite c (h := Classical.dec c) (e y) (∃ x, e x) := by
  by_cases h : c
  all_goals simp [h]

/-- `Fixed.mul_of_pos` respects `approx` -/
lemma Fixed.approx_mul_of_pos {x : Fixed s} {y : Fixed t} {u : Int64} {up : Bool}
    (xn : x ≠ nan) (yn : y ≠ nan) (xp : ¬x.n < 0) (yp : ¬y.n < 0)
    {x' y' : ℝ} (ax : approx x x') (ay : approx y y') :
    Rounds (mul_of_pos x y u up) (x' * y') up := by
  simp only [approx, xn, false_or, yn] at ax ay
  simp only [← ax, ← ay]
  clear x' y' ax ay
  have two0 : (2 : ℝ) ≠ 0 := by norm_num
  have twop : ∀ {x : ℤ}, (2:ℝ)^x ≠ 0 := fun {_} ↦ zpow_ne_zero _ (by norm_num)
  rw [mul_of_pos]
  simp only [bif_eq_if, beq_iff_eq, Int64.isNeg, decide_eq_true_eq]
  generalize hd : (⟨s⟩ + ⟨t⟩ - ⟨u⟩ : Fixed 0) = d
  generalize hw : (x.n.toUInt64.toNat : ℝ) * y.n.toUInt64.toNat = w
  have wa : (mul128 x.n.toUInt64 y.n.toUInt64 : ℝ) = w := by
    simp only [UInt128.toReal, toNat_mul128, Nat.cast_mul, hw]
  by_cases dn : d = nan
  · simp only [dn, ↓reduceIte, rounds_nan]
  · simp only [dn, ite_false]
    have de : (d.n : ℤ) = ↑s + ↑t - ↑u := by
      have e : d.val = s + t - u := by
        simp only [←hd] at dn
        by_cases stn : (⟨s⟩ + ⟨t⟩ : Fixed 0) = nan
        · simp only [stn, nan_sub, not_true] at dn
        · simp only [← hd, Fixed.val_sub dn, Fixed.val_add stn]
          simp only [val, Int64.coe_zero, zpow_zero, mul_one]
      simpa only [val, Int64.coe_zero, zpow_zero, mul_one, ←Int.cast_add, ←Int.cast_sub,
        Int.cast_inj] using e
    by_cases ds : d.n < 0
    · have dn : (2:ℝ) ^ (-d.n).toUInt64.toNat = (2:ℝ) ^ ((u:ℤ) - ↑s - ↑t) := by
        suffices h : ↑(-d.n).toUInt64.toNat = -(d.n : ℤ) by
          rw [←zpow_natCast, h, de, _root_.neg_sub, sub_add_eq_sub_sub]
        by_cases z : d.n = 0
        · simp only [z, Int64.isNeg_zero] at ds
        · simp only [Int64.zero_def, Int64.ext_iff, UInt64.eq_iff_toNat_eq] at z
          simp only [Int64.zero_undef, UInt64.toInt64_ofNat, Int64.n_zero, UInt64.toNat_zero] at z
          simp only [Int64.neg_def, UInt64.toNat_neg, Int64.toInt_eq_if, ds, Nat.cast_pow,
            Nat.cast_ofNat, if_true, UInt64.toUInt64_toInt64, UInt64.size]
          rw [Nat.mod_eq_of_lt]
          · simp
          · omega
      generalize hz : (mul128 x.n.toUInt64 y.n.toUInt64).shiftRightRound (-d.n).toUInt64 up = z
      have za := UInt128.approx_shiftRightRound
        (mul128 x.n.toUInt64 y.n.toUInt64) (-d.n).toUInt64 up
      simp only [hz, wa, dn] at za
      clear hz
      simp only [ds, ite_true, rounds_iff]
      intro zn
      simp only [Fixed.of_raw_uint128_val zn]
      simp only [Fixed.val, ← mul_assoc, mul_comm _ ((2:ℝ)^(t : ℤ))]
      simp only [←mul_assoc, mul_comm _ ((2:ℝ)^(s : ℤ)), Int64.toReal_toInt (not_lt.mp xp),
        Int64.toReal_toInt (not_lt.mp yp)]
      simp only [mul_assoc, hw]
      induction up
      · simp only [ite_false, Bool.false_eq_true, rounds_same] at za ⊢
        refine le_trans (mul_le_mul_of_nonneg_right za (zpow_nonneg (by norm_num) _)) (le_of_eq ?_)
        simp only [zpow_sub₀ two0, div_eq_mul_inv, mul_assoc, mul_inv_rev, inv_inv,
          inv_mul_cancel₀ twop, mul_one]
        ring
      · simp only [rounds_same, ↓reduceIte] at za ⊢
        refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right za (zpow_nonneg (by norm_num) _))
        simp only [zpow_sub₀ two0, div_eq_mul_inv, mul_assoc, mul_inv_rev, inv_inv,
          inv_mul_cancel₀ twop, mul_one]
        ring
    · have dn : (2:ℝ) ^ d.n.toUInt64.toNat = (2:ℝ) ^ ((s:ℤ) + ↑t - ↑u) := by
        suffices h : ↑d.n.toUInt64.toNat = (d.n : ℤ) by rw [←zpow_natCast, h, de]
        simp only [Int64.toInt_eq_if, ds, Nat.reducePow, CharP.cast_eq_zero, sub_zero, if_false]
      simp only [ite_false, ds, rounds_iff]
      intro zn
      simp only [UInt128.toReal] at wa
      simp only [Fixed.of_raw_uint128_val zn, UInt128.toReal, Nat.cast_mul,
        Fixed.toNat_shiftLeftSaturate_of_ne_nan zn, wa, Nat.cast_pow, Nat.cast_two]
      simp only [Fixed.val, ←mul_assoc, mul_comm _ ((2:ℝ)^(t : ℤ))]
      simp only [←mul_assoc, mul_comm _ ((2:ℝ)^(s : ℤ)), Int64.toReal_toInt (not_lt.mp xp),
        Int64.toReal_toInt (not_lt.mp yp)]
      simp only [mul_assoc, hw, dn, zpow_add₀ two0, zpow_sub₀ two0, div_mul_cancel₀ _ twop]
      simp only [←mul_assoc, mul_comm _ w, le_refl, ite_self]

/-- `Fixed.mul` respects `approx` -/
lemma Fixed.approx_mul (x : Fixed s) (y : Fixed t) (u : Int64) (up : Bool) {x' y' : ℝ}
    (ax : approx x x') (ay : approx y y') : Rounds (x.mul y u up) (x' * y') up := by
  rw [mul]
  simp only [bif_eq_if, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ite_not, Int64.isNeg,
    decide_eq_decide]
  by_cases n : x = nan ∨ y = nan
  · simp only [n, ite_true, rounds_nan]
  · simp only [n, ite_false]
    simp only [not_or] at n
    by_cases p : x.n < 0 ↔ y.n < 0
    · have e : x' * y' = |x'| * |y'| := by
        simp only [approx, n, false_or] at ax ay
        simp only [← val_lt_zero, ax, ay] at p
        by_cases n : x' < 0
        · simp only [abs_of_neg n, abs_of_neg (p.mp n), mul_neg, neg_mul, neg_neg]
        · simp only [abs_of_nonneg (not_lt.mp n), abs_of_nonneg (not_lt.mp (p.not.mp n))]
      simp only [p, bne_self_eq_false, Bool.xor_false, ite_true, e]
      refine approx_mul_of_pos ?_ ?_ ?_ ?_ (approx_abs ax) (approx_abs ay)
      all_goals simp [n]
    · have p' : ¬x.n < 0 ↔ y.n < 0 := by simpa only [not_iff] using p
      simp only [p, ite_false]
      apply rounds_neg
      have e : -(x' * y') = |x'| * |y'| := by
        simp only [approx, n, false_or] at ax ay
        simp only [← val_lt_zero, ax, ay, not_iff, not_iff_comm (a := x' < 0),
          not_lt (a := y')] at p
        by_cases n : x' < 0
        · simp only [← neg_mul, abs_of_neg n, abs_of_nonneg (p.mpr n)]
        · simp only [← mul_neg, abs_of_nonneg (not_lt.mp n), abs_of_neg (not_le.mp (p.not.mpr n))]
      have eu : (decide (x.n < 0) != decide (y.n < 0)) = true := by aesop
      simp only [eu, Bool.bne_true, e]
      refine approx_mul_of_pos ?_ ?_ ?_ ?_ (approx_abs ax) (approx_abs ay)
      all_goals simp [n]

/-- `Fixed.approx_mul` in plainer form (down version) -/
lemma Fixed.mul_le {x : Fixed s} {y : Fixed t} {u : Int64} (n : Fixed.mul x y u false ≠ nan) :
    (Fixed.mul x y u false).val ≤ x.val * y.val := by
  simpa only [rounds_iff, ne_eq, n, not_false_eq_true, Bool.false_eq_true, ↓reduceIte,
    forall_const] using approx_mul x y u false (approx_val x) (approx_val y)

/-- `Fixed.approx_mul` in plainer form (up version) -/
lemma Fixed.le_mul {x : Fixed s} {y : Fixed t} {u : Int64} (n : Fixed.mul x y u true ≠ nan) :
    x.val * y.val ≤ (Fixed.mul x y u true).val := by
  simpa only [rounds_iff, ne_eq, n, not_false_eq_true, Bool.false_eq_true, ↓reduceIte,
    forall_const] using approx_mul x y u true (approx_val x) (approx_val y)

/-!
## Conversion from `ℕ`, `ℤ`, `ℚ`, `Float`
-/

/-- Conversion from `ℕ` literals to `Fixed s`, rounding up or down -/
@[irreducible] def Fixed.ofNat (n : ℕ) (up : Bool) : Fixed s :=
  let t : ℤ := s
  bif t < 0 then
    let u := (-t).toNat
    bif n != 0 && (63 ≤ u || 63-u ≤ n.log2) then nan
    else ⟨n <<< u⟩
  else
    let u := t.toNat
    let k := (bif up then n + (1 <<< u) - 1 else n) >>> u
    bif k.log2 < 63 then ⟨k⟩ else nan

/-- Conversion from `ℕ` literals to `Fixed 0`, not rounding -/
@[irreducible] def Fixed.ofNat0 (n : ℕ) : Fixed 0 :=
  bif n.log2 < 63 then ⟨n⟩ else nan

/-- We use the general `.ofNat` routine even for `1`, to handle overflow,
    rounding down arbitrarily -/
instance Fixed.instOne : One (Fixed s) := ⟨.ofNat 1 false⟩

/-- Conversion from `ℕ` literals to `Fixed s` -/
instance {n : ℕ} [n.AtLeastTwo] : OfNat (Fixed s) n := ⟨.ofNat n false⟩

/-- Conversion from `ℤ` -/
@[irreducible] def Fixed.ofInt (n : ℤ) (up : Bool) : Fixed s :=
  bif n < 0 then -.ofNat (-n).toNat !up else .ofNat n.toNat up

/-- Conversion from `ℚ`, rounding up or down -/
@[irreducible] def Fixed.ofRat (x : ℚ) (up : Bool) : Fixed s :=
  -- Our rational is `x = a / b`.  The `Int64` result `y` should satisfy
  --   `y * 2^s ≈ a / b`
  -- We can do this via an exact integer division if we merge `2^s` into either `a` or `b`.
  -- This might be expensive if `s` is large, but we can worry about that later.
  let (a, b) := bif s.isNeg then (x.num >>> ↑s, x.den) else (x.num, x.den <<< s.toUInt64.toNat)
  let d := a.rdiv b up
  bif |d| < 2^63 then ⟨d⟩ else nan

/-- Convert a `Float` to `Fixed s` -/
@[irreducible] def Fixed.ofFloat (x : Float) : Fixed s :=
  let xs := x.abs.scaleB (-s)
  bif xs ≤ 0.5 then 0 else
  let y := xs.toUInt64.toInt64
  bif y == 0 || y.isNeg then nan else
  ⟨bif x < 0 then -y else y⟩

/-- `Fixed.ofNat` rounds the desired way -/
lemma Fixed.approx_ofNat (n : ℕ) (up : Bool) : Rounds (.ofNat n up : Fixed s) (n : ℝ) up := by
  have t0 : (2:ℝ) ≠ 0 := by norm_num
  by_cases nn : (.ofNat n up : Fixed s) = nan
  · simp only [nn, rounds_nan]
  rw [ofNat] at nn ⊢
  simp only [bif_eq_if, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq,
    Bool.or_eq_true] at nn ⊢
  generalize ht : (s : ℤ) = t at nn
  by_cases tn : t < 0
  · simp only [tn, ite_true, ite_eq_left_iff, not_and, not_forall, exists_prop] at nn
    by_cases n0 : n = 0
    · simp only [Rounds, tn, ↓reduceIte, n0, not_true_eq_false, Nat.log2_zero, nonpos_iff_eq_zero,
        false_and, Nat.zero_shiftLeft, Nat.cast_zero, CharP.cast_eq_zero]
      use 0
      simp only [approx, val, Int64.coe_zero, Int.cast_zero, zero_mul, or_true, le_refl, ite_self,
        and_self]
    simp only [rounds_iff, tn, n0, not_false_eq_true, nn, and_false, ite_false, ite_true, Fixed.val,
      ht, ne_eq, true_imp_iff]
    replace nn := nn.1
    simp only [n0, not_false_eq_true, not_or, not_le, forall_true_left] at nn
    simp only [Nat.shiftLeft_eq]
    have lt : n * 2 ^ Int.toNat (-t) < 2^63 := by
      have lt := (Nat.log2_lt n0).mp nn.2
      refine lt_of_lt_of_le ((mul_lt_mul_iff_left₀ (pow_pos (by norm_num) _)).mpr lt) ?_
      simp only [←pow_add, Nat.sub_add_cancel nn.1.le, le_refl]
    have e : (Int.toNat (-t) : ℤ) = -t := Int.toNat_of_nonneg (by omega)
    simp only [Int64.toInt_ofNat'' lt, Nat.cast_mul (α := ℤ), Int.cast_pow, Nat.cast_two,
      Int.cast_mul, Int.cast_ofNat, Nat.cast_pow, mul_assoc]
    simp only [←zpow_natCast, ←zpow_add₀ t0, e, neg_add_cancel, zpow_zero,
      mul_one, le_refl, ite_self, Int.cast_natCast]
  · have tp := not_lt.mp tn
    have tz : (2:ℝ) ^ t = ↑(2 ^ t.toNat : ℕ) := by
      generalize hu : t.toNat = u
      have tu : (t : ℤ) = u := by rw [←hu]; exact (Int.toNat_of_nonneg tp).symm
      simp only [tu, zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    simp only [tn, tsub_le_iff_right, ite_false, ite_eq_right_iff, not_forall, exists_prop] at nn
    induction up
    · simp only [Bool.false_eq_true, ↓reduceIte] at nn
      simp only [tn, ↓reduceIte, Bool.false_eq_true, nn, rounds_iff, ne_eq, not_false_eq_true, val,
        forall_const]
      replace nn := nn.1
      simp only [Nat.shiftRight_eq_div_pow, ht] at nn ⊢
      by_cases n0 : n / 2^t.toNat = 0
      · simp only [n0, Nat.cast_zero, Int64.coe_zero, Int.cast_zero, zero_mul, Nat.cast_nonneg]
      simp only [Nat.log2_lt n0] at nn
      simp only [Int64.toInt_ofNat'' nn, tz, ← Nat.cast_mul, Int.cast_natCast, ← Nat.cast_mul]
      simp only [Nat.cast_le]
      apply Nat.div_mul_le_self
    · simp only [ite_true] at nn
      simp only [rounds_iff, tn, tsub_le_iff_right, ite_true, ite_false, Fixed.val, ht, tz, nn,
        ne_eq, not_false_iff, true_imp_iff]
      simp only [Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq_div_pow] at nn ⊢
      by_cases np : n = 0
      · simp only [np, zero_add, Nat.two_pow_sub_one_div_two_pow, le_refl, tsub_eq_zero_of_le,
          pow_zero, Nat.cast_zero, Int64.coe_zero, Int.cast_zero, zero_mul]
      rw [←Ne, ←Nat.pos_iff_ne_zero] at np
      have n0'' : 0 < n + 2 ^ Int.toNat t - 1 := by
        have le : 1 ≤ 2 ^ Int.toNat t := Nat.one_le_two_pow
        simp only [Nat.add_sub_assoc le]
        exact lt_of_lt_of_le np (by omega)
      by_cases zero : (n + 2 ^ Int.toNat t - 1) / 2 ^ Int.toNat t = 0
      · simp only [zero, Nat.cast_zero, Int64.coe_zero, Int.cast_zero, zero_mul]
        rw [←Nat.cast_zero, Nat.cast_le]
        simp only [Nat.div_eq_zero_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq,
          Int.toNat_eq_zero, not_le, false_and, false_or] at zero
        omega
      · simp only [Int64.toInt_ofNat'' ((Nat.log2_lt zero).mp nn.1), ← Nat.cast_mul, Nat.cast_le,
        Int.cast_natCast]
        exact Nat.le_add_div_mul (Nat.pow_pos (by norm_num))

lemma Real.cast_natCast (n : ℤ) (n0 : 0 ≤ n) : (n : ℝ) = (n.toNat : ℝ) := by
  conv => left; rw [←Int.toNat_of_nonneg n0]
  rw [Int.cast_natCast]

/-- `Fixed.ofNat0` is conservative -/
@[approx] lemma Fixed.approx_ofNat0 (n : ℕ) : approx (ofNat0 n) (n : ℝ) := by
  by_cases nn : (ofNat0 n) = nan
  · simp only [nn, approx_nan]
  rw [ofNat0] at nn ⊢
  simp only [bif_eq_if, decide_eq_true_eq, ite_eq_right_iff, not_forall, exists_prop] at nn ⊢
  simp only [approx, nn, ite_true, val, Int64.coe_zero, zpow_zero, mul_one]
  replace nn := nn.1
  by_cases n0 : n = 0
  · simp only [n0, Nat.cast_zero, Int64.coe_zero, Int.cast_zero, CharP.cast_eq_zero, or_true]
  simp only [Nat.log2_lt n0] at nn
  simp only [Int64.toInt_ofNat'' nn, Int.cast_natCast, or_true]

/-- `Fixed.approx_ofNat`, down version -/
lemma Fixed.ofNat_le {n : ℕ} (h : (.ofNat n false : Fixed s) ≠ nan) :
    (.ofNat n false : Fixed s).val ≤ n := by
  simpa [rounds_iff, h] using Fixed.approx_ofNat n false (s := s)

/-- `Fixed.approx_ofNat`, up version -/
lemma Fixed.le_ofNat {n : ℕ} (h : (.ofNat n true : Fixed s) ≠ nan) :
    n ≤ (.ofNat n true : Fixed s).val := by
  simpa [rounds_iff, h] using Fixed.approx_ofNat n true (s := s)

/-- `Fixed.ofInt` rounds the desired way -/
lemma Fixed.approx_ofInt (n : ℤ) (up : Bool) : Rounds (.ofInt n up : Fixed s) (n : ℝ) up := by
  rw [Fixed.ofInt]
  by_cases n0 : n < 0
  · have e : (n : ℝ) = -↑(-n).toNat := by
      rw [←Real.cast_natCast (-n) (by omega)]
      simp only [Int.cast_neg, neg_neg]
    simpa only [e, n0, decide_true, cond_true, approx_neg, rounds_neg, Bool.not_not, mem_neg,
      neg_neg] using (approx_ofNat (-n).toNat (!up) (s := s)).neg
  · simp only [Real.cast_natCast n (by omega), n0, decide_false, cond_false, approx_ofNat]

/-- `Fixed.approx_ofInt`, down version -/
lemma Fixed.ofInt_le {n : ℤ} (h : (.ofInt n false : Fixed s) ≠ nan) :
    (.ofInt n false : Fixed s).val ≤ n := by
  simpa [rounds_iff, h] using Fixed.approx_ofInt n false (s := s)

/-- `Fixed.approx_ofInt`, up version -/
lemma Fixed.le_ofInt {n : ℤ} (h : (.ofInt n true : Fixed s) ≠ nan) :
    n ≤ (.ofInt n true : Fixed s).val := by
  simpa [rounds_iff, h] using Fixed.approx_ofInt n true (s := s)

/-- `Fixed.ofRat` rounds the desired way -/
lemma Fixed.approx_ofRat (x : ℚ) (up : Bool) :
    Rounds (.ofRat x up : Fixed s) (x : ℝ) up := by
  by_cases n : (ofRat x up : Fixed s) = nan
  · simp only [n, rounds_nan]
  simp only [rounds_iff, ne_eq, n, not_false_eq_true, forall_const]
  rw [ofRat]
  by_cases sn : s < 0
  · simp only [Bool.cond_decide, sn, Int64.isNeg, if_true]
    by_cases dn : |Int.rdiv (x.num >>> ↑s) ↑x.den up| < 2 ^ 63
    · simp only [dn, ite_true, Int64.toInt_ofInt' dn, val]
      rw [← Int64.coe_lt_zero_iff] at sn
      generalize (s : ℤ) = s at sn dn
      have e : s = -(-s).toNat := by rw [Int.toNat_of_nonneg (by omega), neg_neg]
      rw [e] at dn ⊢; clear e sn
      generalize (-s).toNat = s at dn
      simp only [Int.shiftRight_neg, Int.shiftLeft_eq_mul_pow, zpow_neg, Nat.cast_pow,
        Nat.cast_ofNat, zpow_natCast] at dn ⊢
      nth_rw 3 [← Rat.num_div_den x]
      --simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
      induction up
      · simp only [Bool.false_eq_true, ↓reduceIte, mul_inv_le_iff₀ (two_pow_pos (R := ℝ))]
        refine le_trans Int.rdiv_le ?_
        simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, mul_div_right_comm,
          Field.ratCast_def, le_refl]
      · simp only [↓reduceIte, ← div_eq_mul_inv, le_div_iff₀ (G₀ := ℝ) two_pow_pos]
        refine le_trans (le_of_eq ?_) Int.le_rdiv
        simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, ← Field.ratCast_def, Rat.cast_eq_id,
          id_eq, mul_div_right_comm]
    · rw [ofRat, Int64.isNeg, bif_eq_if] at n
      simp only [bif_eq_if, decide_eq_true_eq, sn, if_true] at n
      simp only [dn, ite_false, not_true_eq_false] at n
  · simp only [Bool.cond_decide, sn, val, Int64.isNeg, if_false]
    simp only at sn
    by_cases dn : |Int.rdiv x.num (x.den <<< s.toUInt64.toNat) up| < 2 ^ 63
    · simp only [dn, Int64.coe_of_nonneg (not_lt.mp sn), ↓reduceIte]
      rw [Int64.toInt_ofInt' dn, Nat.shiftLeft_eq]
      generalize s.toUInt64.toNat = s; clear dn
      induction up
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine le_trans (mul_le_mul_of_nonneg_right Int.rdiv_le two_pow_pos.le) (le_of_eq ?_)
        simp only [div_eq_mul_inv, Nat.cast_mul, mul_inv, Nat.cast_pow, Nat.cast_two, mul_assoc,
          inv_mul_cancel₀ (two_pow_pos (R := ℝ)).ne', mul_one, zpow_natCast]
        nth_rw 3 [←Rat.num_div_den x]
        simp only [← div_eq_mul_inv, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
      · simp only
        refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right Int.le_rdiv two_pow_pos.le)
        simp only [div_eq_mul_inv, Nat.cast_mul, mul_inv, Nat.cast_pow, Nat.cast_two,  mul_assoc,
          inv_mul_cancel₀ (two_pow_pos (R := ℝ)).ne', mul_one, zpow_natCast]
        nth_rw 1 [←Rat.num_div_den x]
        simp only [← div_eq_mul_inv, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    · simp only [ofRat, Int64.isNeg] at n
      simp only [sn, decide_false, bif_eq_if, Bool.false_eq_true, ↓reduceIte, dn, not_true] at n

/-- `Fixed.approx_ofRat`, down version -/
lemma Fixed.ofRat_le {x : ℚ} (h : (.ofRat x false : Fixed s) ≠ nan) :
    (.ofRat x false : Fixed s).val ≤ x := by
  simpa [rounds_iff, h] using Fixed.approx_ofRat x false (s := s)

/-- `Fixed.approx_ofRat`, up version -/
lemma Fixed.le_ofRat {x : ℚ} (h : (.ofRat x true : Fixed s) ≠ nan) :
    x ≤ (.ofRat x true : Fixed s).val := by
  simpa [rounds_iff, h] using Fixed.approx_ofRat x true (s := s)

@[simp] lemma Fixed.val_one_of_s0 : (1 : Fixed 0).val = 1 := by
  rw [val]
  simp only [Int64.coe_zero, zpow_zero, mul_one, Int.cast_eq_one]
  trans ↑(Fixed.ofNat 1 false : Fixed 0).n
  · rfl
  · rw [Fixed.ofNat]
    simp [to_if]

/-!
### `2^n` and `log2`
-/

/-- Find `n` s.t. `2^n ≤ x.val < 2^(n+1)`, or `nan` -/
@[irreducible] def Fixed.log2 (x : Fixed s) : Fixed 0 :=
  bif x.n ≤ 0 then nan else ⟨x.n.toUInt64.log2.toInt64⟩ + ⟨s⟩

/-- `2^n : Fixed s`, rounded up or down -/
@[irreducible] def Fixed.two_pow (n : Fixed 0) (up : Bool) : Fixed s :=
  -- In the end, we'll have `⟨⟨x⟩⟩ : Fixed s` with `.val = x * 2^s`.
  -- We want `x * 2^s = s^n`, so `x = 2^(n - s)`.
  let k := n - ⟨s⟩
  bif k == nan || 63 ≤ k.n then nan else
  bif k.n.isNeg then bif up then ⟨1⟩ else 0 else
  ⟨(1 <<< k.n.toUInt64).toInt64⟩

/-- `x.log2` gives us a bracketing interval of two powers around `x.val` -/
lemma Fixed.val_mem_log2 {x : Fixed s} (h : x.log2 ≠ nan) :
    x.val ∈ Ico (2^(x.log2.n : ℤ)) (2^(x.log2.n + 1 : ℤ)) := by
  rw [Fixed.log2] at h ⊢
  have t0 : (2:ℝ) ≠ 0 := by norm_num
  have tp : ∀ n : ℕ, (2:ℝ) ^ n = (2^n : ℕ) := fun n ↦ by rw [Nat.cast_pow, Nat.cast_two]
  by_cases x0 : x.n ≤ 0
  · simp only [x0, decide_true, bif_eq_if, ite_true, ne_eq, not_true_eq_false] at h
  · simp only [val, x0, decide_false, cond_false, mem_Ico, ← div_le_iff₀ (G₀ := ℝ) two_zpow_pos,
      ← lt_div_iff₀ (two_zpow_pos (𝕜 := ℝ)), ←zpow_sub₀ t0] at h ⊢
    have v := Fixed.val_add h
    simp only [val, Int64.coe_zero, zpow_zero, mul_one, ←Int.cast_add, Int.cast_inj] at v
    simp only [v]; ring_nf
    simp only [not_le] at x0
    rw [Int64.coe_log2, UInt64.toNat_log2, ← Nat.cast_one (R := ℤ), ←Nat.cast_add, zpow_natCast,
      zpow_natCast, Nat.add_comm, Int64.toReal_toInt x0.le, tp, tp, Nat.cast_le, Nat.cast_lt]
    refine ⟨Nat.log2_self_le ?_, Nat.lt_log2_self⟩
    simp only [←UInt64.ne_zero_iff_toNat_ne_zero, ←Int64.ne_zero_iff_n_ne_zero]
    exact x0.ne'

/-- `Fixed.two_pow` is correctly rounded -/
lemma Fixed.approx_two_pow (n : Fixed 0) (up : Bool) :
    Rounds (.two_pow n up : Fixed s) (2 ^ (n.n : ℤ) : ℝ) up := by
  generalize hk : n - ⟨s⟩ = k
  rw [two_pow]
  simp only [rounds_iff, bif_eq_if, hk, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  by_cases h : k = nan ∨ 63 ≤ k.n
  · simp only [h, ↓reduceIte, ne_eq, not_true_eq_false, IsEmpty.forall_iff]
  · simp only [h, ite_false]
    simp only [not_or] at h
    by_cases kn : k.n < 0
    · simp only [Int64.isNeg, kn, decide_true, ↓reduceIte, ne_eq]
      induction up
      · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, neg_neg, zero_ne_nan, not_false_eq_true,
          ne_nan_of_neg, val_zero, two_zpow_pos.le, imp_self]
      · simp only [↓reduceIte, val, Int64.coe_one, Int.cast_one, one_mul, Nat.one_lt_ofNat,
          zpow_le_zpow_iff_right₀, Int64.coe_le_coe]
        simp only [← hk, not_le, isNeg_eq] at h kn
        simp only [Fixed.val_sub h.1, sub_neg] at kn
        simp only [val, Int64.coe_zero, zpow_zero, mul_one, Int.cast_lt, Int64.coe_lt_coe] at kn
        simp only [kn.le, implies_true]
    · simp only at kn
      simp only [val]
      have k63 : k.n.toUInt64.toNat < 63 := by
        have e : ((63 : Int64) : ℤ) = ((63 : ℕ) : ℤ) := rfl
        simp only [not_le, ←Int64.coe_lt_coe, Int64.coe_of_nonneg (not_lt.mp kn), e,
          Nat.cast_lt] at h
        exact h.2
      have k64 : k.n.toUInt64.toNat < 64 := by omega
      have e1 : 1 % 2 ^ (64 - k.n.toUInt64.toNat) = 1 :=
        Nat.mod_eq_of_lt (one_lt_pow₀ (by norm_num) (by omega))
      have lt : (1 <<< k.n.toUInt64).toInt64.toUInt64.toNat < 2 ^ 63 := by
        simp only [UInt64.toNat_shiftLeft, UInt64.toNat_one, one_mul, Nat.shiftLeft_eq_mul_pow,
          Nat.mod_eq_of_lt k64, UInt64.toUInt64_toInt64]
        rw [Nat.mod_eq_of_lt]
        · exact pow_lt_pow_right₀ (by norm_num) k63
        · exact pow_lt_pow_right₀ (by norm_num) k64
      have e : (2:ℝ) ^ k.n.toUInt64.toNat * 2 ^ (s : ℤ) = 2 ^ (n.n : ℤ) := by
        rw [pow_mul_zpow (by norm_num)]; apply congr_arg₂ _ rfl
        rw [←hk] at h
        have v := Fixed.val_sub h.1
        simp only [hk, val, Int64.coe_of_nonneg (not_lt.mp kn), Int64.coe_zero, zpow_zero,
          mul_one, ←Int.cast_sub, Int.cast_inj] at v
        linarith
      simp only [Int64.toInt_eq_toNat_of_lt lt, UInt64.toNat_shiftLeft''' k64, UInt64.toNat_one, e1,
        one_mul, Nat.cast_pow, Nat.cast_ofNat, Int.cast_pow, e, le_refl, ite_self, Int.cast_ofNat,
        Int64.isNeg, kn, decide_false, Bool.false_eq_true, ↓reduceIte, implies_true,
        UInt64.toUInt64_toInt64]

/-- `Fixed.log2 = nan` if we're nonpos -/
@[simp] lemma Fixed.log2_eq_nan_of_nonpos {x : Fixed s} (x0 : x.val ≤ 0) : x.log2 = nan := by
  simp only [val_nonpos] at x0
  rw [log2]
  simp only [x0, decide_true, cond_true]

/-- `Fixed.log2` propagates `nan` -/
@[simp] lemma Fixed.log2_nan : (nan : Fixed s).log2 = nan := by
  rw [log2]
  simp only [Bool.cond_decide, ite_eq_left_iff, not_le, ← val_pos, not_val_nan_pos,
    IsEmpty.forall_iff]

/-- `Fixed.two_pow` propagates `nan` -/
@[simp] lemma Fixed.two_pow_nan {up : Bool} : (two_pow nan up : Fixed s) = nan := by
  rw [two_pow]
  simp only [nan_sub, beq_self_eq_true, Bool.true_or, cond_true]

/-- `Fixed.two_pow ≠ nan` implies the argument `≠ nan` -/
@[simp] lemma Fixed.ne_nan_of_two_pow {n : Fixed 0} {up : Bool}
    (h : (two_pow n up : Fixed s) ≠ nan) : n ≠ nan := by
  contrapose h
  simp only [h, two_pow_nan]

/-- `Fixed.approx_two_pow`, down version -/
lemma Fixed.two_pow_le {n : Fixed 0} (h : (.two_pow n false : Fixed s) ≠ nan) :
    (.two_pow n false : Fixed s).val ≤ 2 ^ (n.n : ℤ) := by
  simpa [rounds_iff, h] using Fixed.approx_two_pow n false (s := s)

/-- `Fixed.approx_ofNat`, up version -/
lemma Fixed.le_two_pow {n : Fixed 0} (h : (.two_pow n true : Fixed s) ≠ nan) :
    2 ^ (n.n : ℤ) ≤ (.two_pow n true : Fixed s).val := by
  simpa [rounds_iff, h] using Fixed.approx_two_pow n true (s := s)

/-!
### Exponent changes: `Fixed s → Fixed t`
-/

/-- Change `Fixed s` to `Fixed t`, rounding up or down as desired -/
@[irreducible] def Fixed.repoint (x : Fixed s) (t : Int64) (up : Bool) : Fixed t :=
  -- We want `y : Int64` s.t. `y = x * 2^(s-t)`
  let k : Fixed 0 := ⟨s⟩ - ⟨t⟩
  bif k == nan || x == nan then nan else
  bif t ≤ s then
    bif 63 ≤ k.n.toUInt64 && x.n != 0 then nan
    else bif x.n.uabs >>> (63 - k.n.toUInt64) != 0 then nan
    else ⟨x.n <<< k.n.toUInt64⟩
  else
    ⟨x.n.shiftRightRound (-k).n.toUInt64 up⟩

/-- `Fixed.repoint` propagates `nan` -/
@[simp] lemma Fixed.repoint_nan (t : Int64) (up : Bool) : (nan : Fixed s).repoint t up = nan := by
  rw [Fixed.repoint]
  simp only [beq_self_eq_true, Bool.or_true, Bool.cond_true]

/-- Special case of `pow_sub` involving `UInt64`s -/
lemma two_pow_coe_sub {s t : Int64} {k : Fixed 0} (st : s ≤ t) (e : ⟨t⟩ - ⟨s⟩ = k) (kn : k ≠ nan) :
    (2:ℝ) ^ (t:ℤ) / 2 ^ (s:ℤ) = (2^k.n.toUInt64.toNat : ℤ) := by
  rw [←zpow_sub₀ (by norm_num)]
  rw [←e] at kn
  have h := Fixed.val_sub kn
  simp only [Fixed.val, Int64.coe_zero, zpow_zero, mul_one, ←Int.cast_sub, Int.cast_inj, e] at h
  simp only [← h, Int.cast_pow]
  rw [Int64.coe_of_nonneg, zpow_natCast]
  · norm_num
  · rwa [←Int64.coe_le_coe, Int64.coe_zero, h, sub_nonneg, Int64.coe_le_coe]

/-- `Fixed.repoint` is conservative -/
lemma Fixed.approx_repoint (x : Fixed s) (t : Int64) (up : Bool) {x' : ℝ} (ax : approx x x') :
    Rounds (x.repoint t up) x' up := by
  by_cases xn : x = nan
  · simp only [xn, repoint_nan, rounds_nan]
  rw [Fixed.repoint]
  by_cases kn : (⟨s⟩ - ⟨t⟩ : Fixed 0) = nan
  · simp only [kn, BEq.rfl, Bool.true_or, nan_n, Int64.toUInt64_neg, sub_neg_eq_add, neg_nan,
      Bool.cond_decide, cond_true, rounds_nan]
  simp only [ne_eq, xn, not_false_eq_true, approx_eq_singleton, bif_eq_if, Bool.and_eq_true,
    bne_iff_ne, ite_not, beq_iff_eq, ite_false, Bool.or_eq_true, kn, false_or] at ax ⊢
  generalize hk : (⟨s⟩ - ⟨t⟩ : Fixed 0) = k at kn
  by_cases ts : t ≤ s
  · simp only [ts, ite_true, decide_true]
    by_cases k63 : 63 ≤ k.n.toUInt64
    · by_cases x0 : x.n = 0
      · simp only [rounds_iff, k63, x0, not_true_eq_false, and_false, Int64.uabs_zero,
          UInt64.zero_shiftRight, ite_true, ite_false, ← ax]
        split_ifs
        · simp [val, x0]
        · simp [val, Int64.zero_shiftLeft', Int64.coe_zero, Int.cast_zero, zero_mul, x0, le_refl]
      · simp only [k63, decide_true, x0, not_false_eq_true, and_self, ↓reduceIte, rounds_nan]
    · simp only [k63, decide_false]
      simp only [not_le] at k63
      have e62 : (62 : UInt64).toNat = 62 := rfl
      have e63 : (63 : UInt64).toNat = 63 := rfl
      have st62 : k.n.toUInt64 ≤ 62 := by
        simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, e62, e63] at k63 ⊢; omega
      have st63 : k.n.toUInt64 ≤ 63 := by
        simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, e63] at k63 ⊢; omega
      have st62' : k.n.toUInt64.toNat ≤ 62 := by rwa [UInt64.le_iff_toNat_le, e62] at st62
      have lt : 63 - k.n.toUInt64.toNat < 64 := by omega
      simp only [UInt64.eq_iff_toNat_eq, UInt64.toNat_shiftRight', UInt64.toNat_sub'' st63, e63,
        Nat.mod_eq_of_lt lt, UInt64.toNat_zero, Nat.div_eq_zero_iff]
      by_cases lt : x.n.uabs.toNat < 2 ^ (63 - k.n.toUInt64.toNat)
      · by_cases xn : (⟨x.n <<< k.n.toUInt64⟩ : Fixed t) = nan
        · simp only [Bool.false_eq_true, false_and, ↓reduceIte, Nat.pow_eq_zero,
            OfNat.ofNat_ne_zero, ne_eq, lt, or_true, xn, rounds_nan]
        · have pst : (2:ℝ) ^ (s:ℤ) / 2 ^ (t:ℤ) = (2^k.n.toUInt64.toNat : ℤ) :=
            two_pow_coe_sub ts hk kn
          have r : ((x.n <<< k.n.toUInt64 : Int64) : ℤ) = ↑x.n * 2^k.n.toUInt64.toNat :=
            Int64.coe_shiftLeft (by omega) lt
          simp only [Bool.false_eq_true, false_and, ↓reduceIte, Nat.pow_eq_zero,
            OfNat.ofNat_ne_zero, ne_eq, lt, or_true, ← ax, val, rounds_iff, xn, not_false_eq_true,
            r, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
            ← div_le_iff₀ (G₀ := ℝ) (two_zpow_pos (n := t)), mul_div_assoc, pst, le_refl,
            ← le_div_iff₀ (G₀ := ℝ) (two_zpow_pos (n := t)), ite_self, imp_self]
      · simp only [Bool.false_eq_true, false_and, ↓reduceIte, Nat.pow_eq_zero, OfNat.ofNat_ne_zero,
          ne_eq, lt, or_self, rounds_nan]
  · simp only [ts, decide_false]
    simp only [not_le] at ts
    by_cases sn : (⟨Int64.shiftRightRound x.n (-k).n.toUInt64 up⟩ : Fixed t) = nan
    · simp only [Bool.false_eq_true, ↓reduceIte, sn, rounds_nan]
    · have pts : (2:ℝ) ^ (t:ℤ) / 2 ^ (s:ℤ) = (2^(-k.n).toUInt64.toNat : ℤ) := by
        apply two_pow_coe_sub ts.le
        · rw [←Fixed.neg, ←Fixed.neg_def, ←hk, Fixed.neg_sub]
        · rw [←Fixed.neg_eq_nan, Fixed.neg_def, Fixed.neg] at kn
          exact kn
      simp only [val, rounds_iff, ← div_le_iff₀ (G₀ := ℝ) (two_zpow_pos (n := s)), mul_div_assoc,
        pts, ← le_div_iff₀ (G₀ := ℝ) (two_zpow_pos (n := s)), Bool.false_eq_true, if_false, ne_eq,
        sn, not_false_iff, true_imp_iff, ← ax]
      simp only [← Int.cast_mul, Int.cast_le, Int64.coe_shiftRightRound]
      induction up
      · simp only [Int.rdiv, Nat.cast_pow, Nat.cast_ofNat, cond_false]
        exact Int.ediv_mul_le _ (by positivity)
      · simp only [Int.rdiv, Nat.cast_pow, Nat.cast_ofNat, cond_true, neg_mul, le_neg]
        exact Int.ediv_mul_le _ (by positivity)

/-- `Fixed.repoint _ _ false` rounds down -/
lemma Fixed.repoint_le {x : Fixed s} {t : Int64} (n : x.repoint t false ≠ nan) :
    (x.repoint t false).val ≤ x.val := by
  simpa [rounds_iff, n] using Fixed.approx_repoint x t false (approx_val x)

/-- `Fixed.repoint _ _ true` rounds up -/
lemma Fixed.le_repoint {x : Fixed s} {t : Int64} (n : x.repoint t true ≠ nan) :
    x.val ≤ (x.repoint t true).val := by
  simpa [rounds_iff, n] using Fixed.approx_repoint x t true (approx_val x)

/-!
### Ordering on `Fixed s`
-/

@[irreducible] def Fixed.ble (x y : Fixed s) : Bool := x.n ≤ y.n
@[irreducible] def Fixed.blt (x y : Fixed s) : Bool := x.n < y.n

instance Fixed.instLE : LE (Fixed s) where le x y := x.ble y
instance Fixed.instLT : LT (Fixed s) where lt x y := x.blt y

lemma Fixed.le_def (x y : Fixed s) : (x ≤ y) ↔ (x.n ≤ y.n) := by
  nth_rw 1 [LE.le]
  simp only [instLE, ble, decide_eq_true_eq, ge_iff_le]

lemma Fixed.lt_def (x y : Fixed s) : (x < y) ↔ (x.n < y.n) := by
  nth_rw 1 [LT.lt]
  simp only [instLT, blt, decide_eq_true_eq, gt_iff_lt]

instance Fixed.decidableLT : @DecidableRel (Fixed s) (Fixed s) (· < ·)
  | a, b => by dsimp [LT.lt]; infer_instance

instance Fixed.decidableLE : @DecidableRel (Fixed s) (Fixed s) (· ≤ ·)
  | a, b => by dsimp [LE.le]; infer_instance

lemma Fixed.blt_eq_decide_lt (x y : Fixed s) : x.blt y = decide (x < y) := by
  simp only [blt, lt_def]

lemma Fixed.ble_eq_decide_le (x y : Fixed s) : x.ble y = decide (x ≤ y) := by
  simp only [ble, le_def]

/-- The order is consistent with `.val` -/
@[simp] lemma Fixed.le_iff {x y : Fixed s} : x ≤ y ↔ x.val ≤ y.val := by
  simp only [le_def, val_le_val]

/-- The order is consistent with `.val` -/
@[simp] lemma Fixed.lt_iff {x y : Fixed s} : x < y ↔ x.val < y.val := by
  simp only [lt_def, val_lt_val]

instance : LinearOrder (Fixed s) where
  le_refl x := by simp only [Fixed.le_iff, le_refl]
  le_trans x y z := by simp only [Fixed.le_iff]; apply le_trans
  le_antisymm x y a b := by
    simp only [Fixed.le_iff] at a b
    simpa [Fixed.val, zpow_ne_zero, Fixed.ext_iff] using le_antisymm a b
  le_total x y := by simp only [Fixed.le_iff]; apply le_total
  lt_iff_le_not_ge x y := by simp only [Fixed.lt_iff, Fixed.le_iff]; apply lt_iff_le_not_ge
  toDecidableLE := by infer_instance
  toDecidableLT := by infer_instance
  toDecidableEq := by infer_instance
  min_def x y := by simp only [Fixed.min_def, Fixed.le_def, min_def]; aesop
  max_def x y := by simp only [Fixed.max_def', Fixed.le_def, max_def]; aesop

@[simp] lemma Fixed.nan_le (x : Fixed s) : (nan : Fixed s) ≤ x := by
  simp only [le_def, nan, Int64.min_le]

@[simp] lemma Fixed.val_nan_le (x : Fixed s) : (nan : Fixed s).val ≤ x.val := by
  simp only [← le_iff, nan_le]
