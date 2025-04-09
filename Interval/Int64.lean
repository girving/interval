import Mathlib.Data.Real.Basic
import Interval.Misc.Bool
import Interval.Misc.BitVec
import Interval.Misc.Int
import Interval.Tactic.Decide
import Interval.UInt64

/-!
## 64-bit two's complement integers

Arithmetic wraps, so beware (not really, our uses are formally checked).
-/

open Set
open scoped UInt64.CommRing

def Int64.min : Int64 := ⟨1 <<< 63⟩

attribute [coe] Int64.toInt

/-- The `ℤ` that an `Int64` represents -/
instance : Coe Int64 ℤ where
  coe x := x.toInt

/-- The `ZMod (2^64)` that an `Int64` represents -/
noncomputable instance : Coe Int64 (ZMod (2^64)) where
  coe x := x.toUInt64.toNat

/-- Reduce `Int64` equality to `UInt64` equality -/
lemma Int64.ext_iff (x y : Int64) : x = y ↔ x.toUInt64 = y.toUInt64 := by
  induction' x with x; induction' y with y; simp only [mk.injEq]

-- Arithmetic definition lemmas
lemma Int64.zero_def : (0 : Int64) = ⟨0⟩ := rfl
lemma Int64.one_def : (1 : Int64) = ⟨1⟩ := rfl
lemma Int64.neg_def (x : Int64) : -x = ⟨-x.toUInt64⟩ := rfl
lemma Int64.add_def (x y : Int64) : x + y = ⟨x.toUInt64 + y.toUInt64⟩ := rfl
lemma Int64.sub_def (x y : Int64) : x - y = ⟨x.toUInt64 - y.toUInt64⟩ := rfl
lemma Int64.mul_def (x y : Int64) : x * y = ⟨x.toUInt64 * y.toUInt64⟩ := rfl

-- Simplification lemmas
@[simp] lemma Int64.n_zero : (0 : Int64).toUInt64 = 0 := rfl
@[simp] lemma Int64.toInt_zero : ((0 : Int64) : ℤ) = 0 := rfl
@[simp] lemma Int64.isNeg_zero : ¬((0 : Int64) < 0) := of_decide_eq_false rfl
@[simp] lemma Int64.n_min : Int64.min.toUInt64 = 2^63 := rfl
@[simp] lemma Int64.toNat_min : Int64.min.toUInt64.toNat = 2^63 := rfl
@[simp] lemma Int64.toInt_min : Int64.min.toInt = -2^63 := rfl
@[simp] lemma Int64.toBitVec_min : Int64.min.toBitVec = 2^63 := rfl
@[simp] lemma Int64.isNeg_min : Int64.min < 0 := rfl
@[simp] lemma Int64.neg_min : -Int64.min = .min := rfl
@[simp] lemma Int64.toBitVec_zero : (0 : Int64).toBitVec = 0 := rfl
@[simp] lemma Int64.zero_undef : (⟨0⟩ : Int64) = 0 := rfl

/-- Fast conversion from `ℕ` -/
instance : NatCast Int64 where
  natCast n := ⟨(n : UInt64)⟩

/-- Fast conversion from `ℤ` -/
instance : IntCast Int64 where
  intCast n := ⟨(n : UInt64)⟩

@[simp] lemma Int64.toBitVec_ofNat {n : ℕ} : (n : Int64).toBitVec = (n : BitVec 64) := rfl
@[simp] lemma Int64.toBitVec_ofInt {n : ℤ} : (n : Int64).toBitVec = (n : BitVec 64) := rfl

-- Expand the definition of < and ≤
lemma Int64.lt_def (x y : Int64) : x < y ↔ x.toBitVec.slt y.toBitVec := by
  simp only [LT.lt, Int64.lt]
lemma Int64.le_def (x y : Int64) : x ≤ y ↔ x.toBitVec.sle y.toBitVec := by
  simp only [LE.le, Int64.le]

/-- `Int64` is a commutative ring.
    We don't use `CommRing.ofMinimalAxioms, since we want our own `Sub` instance. -/
instance : CommRing Int64 where
  add_zero x := by simp only [Int64.add_def, Int64.zero_def, add_zero]
  zero_add x := by simp only [Int64.add_def, Int64.zero_def, zero_add]
  add_comm x y := by simp only [Int64.add_def, add_comm]
  add_assoc x y z := by simp only [Int64.add_def, add_assoc]
  neg_add_cancel x := by
    simp only [Int64.neg_def, Int64.add_def, neg_add_cancel, Int64.zero_def]
  mul_assoc x y z := by simp only [Int64.mul_def, mul_assoc]
  mul_comm x y := by simp only [Int64.mul_def, mul_comm]
  zero_mul x := by simp only [Int64.mul_def, Int64.zero_def, zero_mul]
  mul_zero x := by simp only [Int64.mul_def, Int64.zero_def, mul_zero]
  one_mul x := by simp only [Int64.mul_def, Int64.one_def, one_mul]
  mul_one x := by simp only [Int64.mul_def, Int64.one_def, mul_one]
  left_distrib x y z := by simp only [Int64.add_def, Int64.mul_def, left_distrib]
  right_distrib x y z := by simp only [Int64.add_def, Int64.mul_def, right_distrib]
  sub_eq_add_neg x y := by simp only [Int64.sub_def, Int64.add_def, Int64.neg_def, sub_eq_add_neg]
  natCast_zero := rfl
  natCast_succ := by
    intro n
    simp only [NatCast.natCast, Nat.cast_add, Nat.cast_one, Int64.one_def, Int64.add_def]
  intCast_ofNat := by
    intro n
    simp only [IntCast.intCast, Int.cast_ofNat, Int64.ext_iff, UInt64.eq_iff_toNat_eq]
    rfl
  intCast_negSucc := by
    intro n
    simp only [IntCast.intCast, Int.cast_negSucc, Int64.ext_iff, UInt64.eq_iff_toNat_eq]
    rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- `Int64` < is decidable -/
instance decidableLT : @DecidableRel Int64 Int64 (· < ·)
  | a, b => by dsimp [LT.lt, Int64.lt]; infer_instance

/-- `Int64` ≤ is decidable -/
instance decidableLE : @DecidableRel Int64 Int64 (· ≤ ·)
  | a, b => by dsimp [LE.le, Int64.le]; infer_instance

/-- Negation preserves `min` -/
@[simp] lemma Int64.neg_eq_min {x : Int64} : (-x) = min ↔ x = min := by
  have i : ∀ {x : Int64}, x = min → (-x) = min := by
    intro x h; simp only [h, neg_def, n_min]; decide
  by_cases a : x = min
  · simp only [a, neg_min]
  · by_cases b : (-x) = min
    · rw [b, ←neg_neg x, i b]
    · simp only [a, b]

/-- `min ≠ 0` -/
@[simp] lemma Int64.min_ne_zero : Int64.min ≠ 0 := by decide

/-- `0 ≠ min` -/
@[simp] lemma Int64.zero_ne_min : 0 ≠ Int64.min := by decide

-- Consequences of the sign bit being true or false
lemma Int64.coe_of_nonneg {x : Int64} (h : 0 ≤ x) : (x : ℤ) = x.toUInt64.toNat := by
  simp only [le_def, BitVec.sle, toBitVec_zero, BitVec.ofNat_eq_ofNat, BitVec.toInt_zero,
    decide_eq_true_eq] at h
  simp only [BitVec.toInt, toBitVec, UInt64.toNat_toBitVec, Nat.cast_ofNat, toInt] at h ⊢
  have lt := x.toUInt64.toNat_lt_2_pow_64
  omega
lemma Int64.coe_of_neg {x : Int64} (h : x < 0) : (x : ℤ) = x.toUInt64.toNat - ((2^64 : ℕ) : ℤ) := by
  have b := x.toUInt64.toNat_lt_2_pow_64
  simp only [lt_def, BitVec.slt, BitVec.toInt, toBitVec, UInt64.toNat_toBitVec, Nat.reducePow,
    Nat.cast_ofNat, n_zero, UInt64.toBitVec_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, mul_zero,
    Nat.ofNat_pos, ↓reduceIte, CharP.cast_eq_zero, decide_eq_true_eq] at h
  simp only [cond_true, Nat.cast_zero, sub_zero, Int64.toInt, UInt64.toNat,
    Int64.toBitVec, Int64.toBitVec, BitVec.toInt] at h ⊢
  omega

/-- `isNeg` in terms of `≤` over `ℕ` -/
lemma Int64.isNeg_eq_le (x : Int64) : x < 0 ↔ 2^63 ≤ x.toUInt64.toNat := by
  have b := x.toUInt64.toNat_lt_2_pow_64
  simp only [lt_def, BitVec.slt, BitVec.toInt, toBitVec, UInt64.toNat_toBitVec, Nat.reducePow,
    Nat.cast_ofNat, n_zero, UInt64.toBitVec_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, mul_zero,
    Nat.ofNat_pos, ↓reduceIte, CharP.cast_eq_zero, decide_eq_true_eq]
  rw [UInt64.toNat]
  omega

/-- The ordering is consistent with `ℤ` -/
@[simp] lemma Int64.coe_lt_coe (x y : Int64) : (x : ℤ) < (y : ℤ) ↔ x < y := by
  simp only [toInt, lt_def, BitVec.slt, decide_eq_true_eq]

/-- Converting to `ℤ` is under `2^63` -/
@[simp] lemma Int64.coe_lt_pow (x : Int64) : (x : ℤ) < 2^63 := by
  have h := x.toUInt64.toNat_lt_2_pow_64
  simp only [toInt, UInt64.toNat, BitVec.toInt] at h ⊢
  omega

/-- Converting to `ℤ` is at least `-2^63` -/
@[simp] lemma Int64.pow_le_coe (x : Int64) : -2^63 ≤ (x : ℤ) := by
  simp only [toInt, BitVec.toInt]
  omega

@[simp] lemma Int64.coe_min' : ((.min : Int64) : ℤ) = -(2:ℤ)^63 := rfl

/-- The ordering is consistent with `ℤ` -/
@[simp] lemma Int64.coe_le_coe (x y : Int64) : (x : ℤ) ≤ (y : ℤ) ↔ x ≤ y := by
  simp [← not_lt, coe_lt_coe, lt_def, le_def, BitVec.slt, BitVec.sle]

/-- We print `Int64`s as signed integers -/
instance : Repr Int64 where
  reprPrec x p := Repr.reprPrec (x : ℤ) p

/-- Approximate `Int64` by a `Float` -/
def Int64.toFloat (x : Int64) :=
  if x < 0 then -(-x.toUInt64).toFloat else x.toUInt64.toFloat

-- An `Int64` is zero iff its inner `UInt64` is -/
lemma Int64.eq_zero_iff_n_eq_zero (x : Int64) : x = 0 ↔ x.toUInt64 = 0 := by
  simp only [Int64.ext_iff, Int64.zero_def]

-- An `Int64` is not zero iff its inner `UInt64` is -/
lemma Int64.ne_zero_iff_n_ne_zero (x : Int64) : x ≠ 0 ↔ x.toUInt64 ≠ 0 := by
  simp only [Ne, Int64.eq_zero_iff_n_eq_zero]

/-- Expand negation into something `omega` can handle -/
lemma Int64.coe_neg {x : Int64} :
    ((-x : Int64) : ℤ) = if (x : ℤ) = -2^63 then -2^63 else -(x : ℤ) := by
  have neg := x.toUInt64.toNat_neg
  have xu := x.toUInt64.toNat_lt_2_pow_64
  simp only [neg_def, toInt, BitVec.toInt, Int64.toBitVec, UInt64.toNat, UInt64.size,
    UInt64.eq_iff_toNat_eq, UInt64.toBitVec_zero, BitVec.toNat_zero] at neg xu ⊢
  generalize x.toUInt64.toBitVec.toNat = a at neg xu
  generalize (-x.toUInt64).toBitVec.toNat = b at neg
  by_cases a0 : a = 0
  all_goals simp only [a0, if_true, if_false, mul_zero] at neg ⊢
  · omega
  · omega

/-- Expand addition into something `omega` can handle -/
lemma Int64.coe_add {x y : Int64} :
    ((x + y : Int64) : ℤ) =
      let s := (x : ℤ) + y
      if s < -2^63 then s + 2^64 else if 2^63 ≤ s then s - 2^64 else s := by
  have add := UInt64.toNat_add x.toUInt64 y.toUInt64
  have au := x.toUInt64.toNat_lt_2_pow_64
  have bu := y.toUInt64.toNat_lt_2_pow_64
  simp only [UInt64.toNat] at add au bu
  simp only [add_def, toInt, BitVec.toInt, Int64.toBitVec, add]
  omega

/-- Expand subtraction into something `omega` can handle -/
lemma Int64.coe_sub {x y : Int64} :
    ((x - y : Int64) : ℤ) =
      let s := (x : ℤ) - y
      if s < -2^63 then s + 2^64 else if 2^63 ≤ s then s - 2^64 else s := by
  simp only [sub_eq_add_neg, coe_add, coe_neg]
  have x0 := x.pow_le_coe
  have x1 := x.coe_lt_pow
  have y0 := y.pow_le_coe
  have y1 := y.coe_lt_pow
  omega

-- Lemmas about `coe : Int64 → ℤ`
@[simp] lemma Int64.coe_zero : ((0 : Int64) : ℤ) = 0 := rfl
@[simp] lemma Int64.coe_one : ((1 : Int64) : ℤ) = 1 := rfl

/-- Equality is consistent with `ℤ` -/
@[simp] lemma Int64.coe_eq_coe (x y : Int64) : (x : ℤ) = (y : ℤ) ↔ x = y := by
  simp only [toInt, UInt64.le_iff_toNat_le, ext_iff, UInt64.eq_iff_toNat_eq,
    BitVec.toInt, UInt64.toNat, Int64.toBitVec]
  omega

/-- Equality is consistent with `ℤ` -/
@[simp] lemma Int64.coe_ne_coe (x y : Int64) : (x : ℤ) ≠ (y : ℤ) ↔ x ≠ y := by
  simp only [ne_eq, coe_eq_coe]

@[simp] lemma Int64.coe_eq_zero (x : Int64) : (x : ℤ) = 0 ↔ x = 0 := by
  rw [←coe_zero, coe_eq_coe]

/-- Converting to `ℤ` is more than `-2^63` if we're not `min` -/
@[simp] lemma Int64.pow_lt_coe {x : Int64} (n : x ≠ min) : -2^63 < (x : ℤ) := by
  refine Ne.lt_of_le ?_ (pow_le_coe x)
  rw [Ne, ←coe_min', coe_eq_coe]
  exact n.symm

/-- Negation flips `.isNeg`, except at `0` and `.min` -/
lemma Int64.isNeg_neg {x : Int64} (x0 : x ≠ 0) (xn : x ≠ .min) : (-x) < 0 ↔ 0 ≤ x := by
  simp only [← coe_le_coe, toInt_zero, ← coe_lt_coe, coe_neg]
  simp only [ne_eq, ← coe_eq_zero] at x0
  simp only [← coe_ne_coe, toInt_min] at xn
  omega

/-!
### Conditions for `ℤ` conversion to commute with arithmetic
-/

/-- `Int64.neg` usually commutes with `ℤ` conversion -/
lemma Int64.coe_neg' {x : Int64} (xn : x ≠ .min) : ((-x : Int64) : ℤ) = -x := by
  simp only [← coe_ne_coe, toInt_min] at xn
  simp only [← coe_eq_coe, coe_neg, xn, if_false]

/-- `ℤ` conversion commutes with add if `isNeg` matches the left argument -/
lemma Int64.coe_add_eq {x y : Int64} (h : x + y < 0 ↔ x < 0) :
    ((x + y : Int64) : ℤ) = x + y := by
  simp only [← coe_lt_coe, coe_zero, coe_add] at h
  simp only [coe_add]
  have := x.coe_lt_pow
  have := y.coe_lt_pow
  have := x.pow_le_coe
  have := y.pow_le_coe
  omega

/-- `ℤ` conversion commutes with add if `isNeg` matches the right argument -/
lemma Int64.coe_add_eq' {x y : Int64} (h : x + y < 0 ↔ y < 0) :
    ((x + y : Int64) : ℤ) = x + y := by
  simp only [add_comm x, add_comm (x : ℤ)] at h ⊢
  apply Int64.coe_add_eq h

/-- `ℤ` conversion commutes with add if the two arguments have different `isNeg`s -/
lemma Int64.coe_add_ne {x y : Int64} (h : ¬(x < 0 ↔ y < 0)) : ((x + y : Int64) : ℤ) = x + y := by
  simp only [← coe_lt_coe, coe_zero, coe_add] at h
  simp only [coe_add]
  have := x.coe_lt_pow
  have := y.coe_lt_pow
  have := x.pow_le_coe
  have := y.pow_le_coe
  omega

/-- `ℤ` conversion commutes with sub if the result is positive -/
lemma Int64.coe_sub_of_le_of_pos {x y : Int64} (yx : y ≤ x) (h : 0 ≤ x - y) :
    ((x - y : Int64) : ℤ) = x - y := by
  simp only [← coe_le_coe, coe_zero, coe_sub] at h yx
  simp only [coe_sub]
  have := x.coe_lt_pow
  have := y.coe_lt_pow
  have := x.pow_le_coe
  have := y.pow_le_coe
  omega

/-- Conversion to `ℤ` is the same as via `ℕ` if we're nonnegative -/
lemma Int64.toReal_toInt {x : Int64} (h : 0 ≤ x) : ((x : ℤ) : ℝ) = x.toUInt64.toNat := by
  simp only [coe_of_nonneg h, Int.cast_natCast]

/-- Conversion from `ℕ` is secretly the same as conversion to `UInt64` -/
@[simp] lemma Int64.ofNat_eq_coe (n : ℕ) : (n : Int64).toUInt64 = n := by
  induction' n with n h
  · simp only [Nat.zero_eq, Nat.cast_zero, n_zero]
  · simp only [Nat.cast_succ, Int64.add_def, h]; rfl

/-- Conversion `ℕ → Int64 → ℤ` is the same as direct if we're small -/
lemma Int64.toInt_ofNat {n : ℕ} (h : n < 2^63) : ((n : Int64) : ℤ) = n := by
  simp only [toInt, BitVec.toInt, toBitVec_ofNat, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    OfNat.ofNat_ne_zero]
  omega


/-- Conversion `ℤ → Int64 → ℤ` is the same as direct if we're small -/
lemma Int64.toInt_ofInt {n : ℤ} (h : |n| < 2^63) : ((n : Int64) : ℤ) = n := by
  simp only [toInt, BitVec.toInt, toBitVec_ofInt, Nat.reducePow, Nat.cast_ofNat,
    BitVec.toNat_intCast, Int.abs_def] at h ⊢
  omega

/-- Conversion to `ℤ` is the same as the underlying `toNat` if we're small -/
lemma Int64.toInt_eq_toNat_of_lt {x : Int64} (h : x.toUInt64.toNat < 2^63) :
    (x : ℤ) = ↑x.toUInt64.toNat := by
  apply Int64.coe_of_nonneg
  simp only [le_def, BitVec.sle, BitVec.toInt, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
    decide_eq_true_eq, UInt64.toNat, Int64.toBitVec, n_zero, UInt64.toBitVec_zero] at h ⊢
  omega

/-- `UInt64.log2` converts to `ℤ` as `toNat` -/
@[simp] lemma Int64.coe_log2 (n : UInt64) : ((⟨n.log2⟩ : Int64) : ℤ) = n.log2.toNat := by
  rw [Int64.toInt_eq_toNat_of_lt]
  simp only [UInt64.toNat_log2]
  exact lt_trans (UInt64.log2_lt_64 _) (by norm_num)

/-- Adding `2^63` and converting via `UInt64` commutes -/
@[simp] lemma Int64.toNat_add_pow_eq_coe (n : Int64) :
    ((n + 2^63).toUInt64.toNat : ℤ) = (n : ℤ) + 2^63 := by
  have add := coe_add (x := n) (y := 2^63)
  generalize n + 2 ^ 63 = z at add
  have be : ∀ z : Int64, z.toBitVec.toNat = z.toUInt64.toNat := fun _ ↦ rfl
  have pe : (2 ^ 63 : Int64).toUInt64.toNat = 2 ^ 63 := by fast_decide
  simp only [toInt, BitVec.toInt, Nat.cast_ofNat,
    Int.reduceNeg, be, pe] at add ⊢
  have zu := z.toUInt64.toNat_lt_2_pow_64
  have nu := n.toUInt64.toNat_lt_2_pow_64
  omega

/-!
### Order lemmas
-/

/-- `Int64` `min` (must be defined before `LinearOrder`) -/
instance : Min Int64 where
  min x y := if x < y then x else y

/-- `Int64` `max` (must be defined before `LinearOrder`) -/
instance : Max Int64 where
  max x y := if x < y then y else x

/-- `Int64` is a linear order (though not an ordered algebraic structure) -/
instance : LinearOrder Int64 where
  le_refl x := by simp only [←Int64.coe_le_coe, le_refl]
  le_trans x y z := by simp only [←Int64.coe_le_coe]; apply le_trans
  le_antisymm x y := by
    simp only [←Int64.coe_le_coe, ←Int64.coe_eq_coe]; apply le_antisymm
  le_total x y := by simp only [←Int64.coe_le_coe]; apply le_total
  lt_iff_le_not_le x y := by
    simp only [←Int64.coe_lt_coe, ←Int64.coe_le_coe]; apply lt_iff_le_not_le
  decidableLE x y := by infer_instance
  min_def x y := by
    simp only [min, bif_eq_if, decide_eq_true_eq]
    split_ifs
    · rfl
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]; linarith
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]; linarith
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]
  max_def x y := by
    simp only [max, bif_eq_if, decide_eq_true_eq]
    split_ifs
    · rfl
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]; linarith
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]; linarith
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]

/-- `Int64.min` is the smallest element -/
@[simp] lemma Int64.min_le (x : Int64) : .min ≤ x := by
  simp only [← Int64.coe_le_coe, toInt_min]
  simp only [Int64.toInt, BitVec.toInt]
  omega

/-- `Int64.min` is the smallest element -/
lemma Int64.eq_min_iff_min_lt (x : Int64) : x = .min ↔ x ≤ .min := by
  have h := min_le x
  constructor
  · intro h; simp only [h, le_refl]
  · intro h; apply le_antisymm; repeat assumption

lemma Int64.coe_nonneg {x : Int64} (h : 0 ≤ x) : 0 ≤ (x : ℤ) := by
  rwa [← Int64.coe_zero, Int64.coe_le_coe]

@[simp] lemma Int64.coe_nonpos_iff {x : Int64} : (x : ℤ) ≤ 0 ↔ x ≤ 0 := by
  rw [← Int64.coe_zero, coe_le_coe]

lemma Int64.coe_lt_zero {x : Int64} (h : x < 0) : (x : ℤ) < 0 := by
  rwa [← Int64.coe_zero, Int64.coe_lt_coe]

lemma Int64.coe_lt_zero_iff {x : Int64} : (x : ℤ) < 0 ↔ x < 0 := by
  rw [← Int64.coe_zero, coe_lt_coe]

@[simp] lemma Int64.coe_nonneg_iff {x : Int64} : 0 ≤ (x : ℤ) ↔ 0 ≤ x := by
  rw [← Int64.coe_zero, coe_le_coe]

@[simp] lemma Int64.coe_neg_iff {x : Int64} : (x : ℤ) < 0 ↔ x < 0 := by
  rw [← Int64.coe_zero, coe_lt_coe]

@[simp] lemma Int64.coe_pos_iff {x : Int64} : 0 < (x : ℤ) ↔ 0 < x := by
  simpa only [coe_zero] using coe_lt_coe 0 x

@[simp] lemma Int64.natAbs_lt_pow_iff {x : Int64} : (x : ℤ).natAbs < 2^63 ↔ x ≠ min := by
  simp only [Int.natAbs_def, ← coe_ne_coe, toInt_min]
  have := x.coe_lt_pow
  have := x.pow_le_coe
  split_ifs
  all_goals omega

/-- A sufficient condition for subtraction to decrease the value -/
lemma Int64.sub_le {x y : Int64} (h : min + y ≤ x) : x - y ≤ x := by
  simp only [← coe_le_coe, ← coe_ne_coe, toInt_min, coe_add, coe_sub] at h ⊢
  have := x.coe_lt_pow
  have := x.pow_le_coe
  have := y.coe_lt_pow
  have := y.pow_le_coe
  omega

/-!
### Shims for proof backwards compatibility
-/

/-- I now use `x < 0` directly in most places, but we record this for backwards compatibility -/
def Int64.isNeg (x : Int64) : Bool := x < 0

/-- Show that `Int64 → ℤ` is the same as we used to define it -/
lemma Int64.toInt_eq_if (x : Int64) :
    (x : ℤ) = (x.toUInt64.toNat : ℤ) - ((if x < 0 then 2^64 else 0) : ℕ) := by
  have u := x.toUInt64.toNat_lt_2_pow_64
  simp only [toInt, Nat.reducePow, apply_ite, Nat.cast_ofNat, CharP.cast_eq_zero, sub_zero,
    BitVec.toInt, Int64.toBitVec, UInt64.toNat, lt_def, BitVec.slt] at u ⊢
  simp only [n_zero, UInt64.toBitVec_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    mul_zero, Nat.ofNat_pos, ↓reduceIte, CharP.cast_eq_zero,
    decide_eq_true_eq, ite_eq_right_iff]
  generalize x.toUInt64.toBitVec.toNat = a at u
  by_cases lt : 2 * a < 18446744073709551616
  · simp_all only [ite_true, forall_const, if_true_right, isEmpty_Prop, not_lt, Nat.cast_nonneg,
      IsEmpty.forall_iff]
  · simp_all only [not_lt, isEmpty_Prop, IsEmpty.forall_iff, if_true_left]
    omega

/-!
### Order operations: min, abs
-/

/-- Almost absolute value (maps `Int64.min → Int64.min`) -/
def Int64.abs (x : Int64) : UInt64 :=
  if x < 0 then -x.toUInt64 else x.toUInt64

@[simp] lemma Int64.abs_zero : (0 : Int64).abs = 0 := rfl
@[simp] lemma Int64.abs_min : Int64.min.abs = Int64.min := rfl

/-- `.abs` is absolute value (`ℕ` version) )-/
lemma Int64.toNat_abs {x : Int64} : x.abs.toNat = (x : ℤ).natAbs := by
  have u := x.toUInt64.toNat_lt_2_pow_64
  simp only [abs, apply_ite, UInt64.toNat_neg, Int.natAbs_def, UInt64.size_eq_pow,
    UInt64.eq_iff_toNat_eq, ← coe_lt_zero_iff, UInt64.toNat_zero, coe_lt_zero_iff, isNeg_eq_le]
  generalize ha : x.toUInt64.toNat = a at u
  by_cases a0 : 2 ^ 63 ≤ a
  all_goals by_cases a1 : a = 0
  all_goals simp only [a0, toInt, BitVec.toInt, Int64.toBitVec, UInt64.toNat_toBitVec, ha, a1,
    apply_ite (f := fun k : ℤ ↦ (-k).toNat), apply_ite (f := fun k : ℤ ↦ k.toNat), if_true,
    if_false, Nat.reducePow, Int.toNat_neg_nat, Nat.cast_ofNat, neg_sub, Int.toNat_sub',
      Int.reduceToNat]
  · simp
  · split_ifs
    all_goals omega
  · simp
  · split_ifs
    all_goals omega

/-- `.abs` is absolute value (`ℤ` version) -/
lemma Int64.coe_abs {x : Int64} : x.abs.toInt = |(x : ℤ)| := by
  simp only [UInt64.toInt, toNat_abs, Int.natCast_natAbs]

/-- `abs` preserves 0 -/
@[simp] lemma Int64.abs_eq_zero_iff {x : Int64} : x.abs = 0 ↔ x = 0 := by
  simp only [← coe_eq_coe, UInt64.eq_iff_toNat_eq, UInt64.toNat_zero, toInt_zero, toNat_abs,
    Int.natAbs_eq_zero]

/-- `abs` preserves 0 -/
@[simp] lemma Int64.abs_ne_zero_iff {x : Int64} : x.abs ≠ 0 ↔ x ≠ 0 := by
  simp only [Ne, Int64.abs_eq_zero_iff]

/-- `.abs` doesn't change if nonneg -/
lemma Int64.abs_eq_self' {x : Int64} (h : 0 ≤ x) : x.abs = x.toUInt64 := by
  have h1 := coe_of_nonneg h
  simp only [← coe_nonneg_iff] at h
  simp only [UInt64.eq_iff_toNat_eq, toNat_abs, Int.natAbs_def, not_lt.mpr h, if_false]
  simp only [h1, Int.toNat_ofNat]

/-- `.abs` doesn't change if nonneg -/
lemma Int64.abs_eq_self {x : Int64} (h : 0 ≤ x) : x.abs.toInt = x := by
  simp only [← coe_nonneg_iff] at h
  simp only [coe_abs, abs_of_nonneg h]

/-- `.abs` negates if negative -/
lemma Int64.abs_eq_neg' {x : Int64} (n : x < 0) : x.abs = (-x).toUInt64 := by
  have h := coe_lt_zero n
  simp only [UInt64.eq_iff_toNat_eq, toNat_abs, neg_def, UInt64.toNat_neg, UInt64.toNat_zero,
    UInt64.size_eq_pow, Int.natAbs_def, h, if_true]
  simp only [toInt, Int64.toBitVec, BitVec.toInt, UInt64.toNat_toBitVec,
    apply_ite (f := fun x : ℤ ↦ (-x).toNat)] at h ⊢
  have := x.toUInt64.toNat_lt_2_pow_64
  generalize x.toUInt64.toNat = a at h
  by_cases c0 : 2 * a < 2 ^ 64
  all_goals by_cases c1 : a = 0
  all_goals simp only [c0, c1, if_true, if_false]
  all_goals omega

/-- `.abs` negates if negative -/
lemma Int64.abs_eq_neg {x : Int64} (n : x < 0) : x.abs.toInt = -x := by
  rw [coe_abs, abs_of_neg (coe_lt_zero n)]

/-- `.min` commutes  with `coe` -/
lemma Int64.coe_min {x y : Int64} : (Min.min (α := Int64) x y : ℤ) = Min.min (x : ℤ) y := by
  simp only [LinearOrder.min_def, coe_le_coe]
  by_cases xy : x ≤ y
  · simp only [xy, ite_true]
  · simp only [xy, ite_false]

/-- `.max` commutes  with `coe` -/
lemma Int64.coe_max {x y : Int64} : (Max.max (α := Int64) x y : ℤ) = Max.max (x : ℤ) y := by
  simp only [LinearOrder.max_def, coe_le_coe]
  by_cases xy : x ≤ y
  · simp only [xy, ite_true]
  · simp only [xy, ite_false]

/-- If we turn `abs` back into an `Int64`, it's abs except at `.min` -/
lemma Int64.coe_abs' {x : Int64} (n : x ≠ .min) : ((⟨x.abs⟩ : Int64) : ℤ) = |(x : ℤ)| := by
  generalize ha : (x : ℤ) = a
  have ha' : x.toUInt64.toBitVec.toInt = a := by rw [← ha]; rfl
  have e : (-x.toUInt64).toBitVec.toInt = (-x : Int64) := rfl
  simp only [← coe_ne_coe, toInt_min, ha] at n
  simp only [abs, ← coe_ne_coe, toInt_min, ha, toInt, ← coe_lt_zero_iff,
    apply_ite (fun x : UInt64 ↦ x.toBitVec.toInt), ha', Int64.toBitVec]
  simp only [e, coe_neg, ha, n, if_false, Int.abs_def]

/-- If we turn `abs` back into an `Int64`, it's negative only at `.min` -/
lemma Int64.abs_lt_zero {x : Int64} : ((⟨x.abs⟩ : Int64) : ℤ) < 0 ↔ x = .min := by
  by_cases e : x = .min
  · simp only [e, abs_min]; decide
  · simp only [coe_abs' e, e, iff_false, not_lt, abs_nonneg]

/-- `(-x).abs = x.abs` away from `min` -/
@[simp] lemma Int64.abs_neg {x : Int64} : (-x).abs = x.abs := by
  by_cases z : x = 0
  · simp only [z, neg_zero, abs_zero]
  by_cases m : x = min
  · simp only [m, neg_min, abs_min, coe_min', Int.cast_neg, Int.cast_pow,
      AddGroupWithOne.intCast_ofNat]
  rw [Int64.abs, Int64.abs]
  simp only [isNeg_neg z m, bif_eq_if, Bool.not_eq_true']
  simp only [neg_def, neg_neg]
  by_cases h : x < 0
  all_goals simp only [h, ite_false, ite_true, Bool.true_eq_false, Bool.false_eq_true, ← not_lt,
    not_true, not_false_iff]

/-- `(-t).n.toNat = t` when converting negatives to `ℤ` -/
@[simp] lemma Int64.toNat_neg {x : Int64} (n : x < 0) : ((-x).toUInt64.toNat : ℤ) = -x := by
  simp only [toInt_eq_if]
  by_cases x0 : x = 0
  · simp only [x0, isNeg_zero, Bool.false_eq_true] at n
  · simp only [ext_iff, n_zero] at x0
    simp only [neg_def, UInt64.toNat_neg, x0, ↓reduceIte, UInt64.size_eq_pow, Nat.reducePow,
      UInt64.le_size, Nat.cast_sub, Nat.cast_ofNat, n, neg_sub]

@[simp] lemma Int64.abs_eq_pow_iff {x : Int64} : x.abs = 2^63 ↔ x = min := by
  rw [abs]
  by_cases n : x < 0
  · simp only [n, if_true]
    have e : -x.toUInt64 = (-x).toUInt64 := rfl
    rw [e, ←n_min, ←ext_iff, neg_eq_min]
  · simp only [n, ite_false, ext_iff, n_min, Bool.false_eq_true]

@[simp] lemma Int64.abs_abs {x : Int64} : (⟨x.abs⟩ : Int64).abs = x.abs := by
  rw [abs, abs]
  by_cases x0 : x = 0
  · simp only [x0, isNeg_zero, n_zero, neg_zero, Bool.cond_self, if_false]
    rfl
  by_cases m : x = min
  · simp only [m, abs_min, coe_min', Int.cast_neg, Int.cast_pow, AddGroupWithOne.intCast_ofNat]
    decide
  by_cases n : x < 0
  · simp only [n, cond_true, ← neg_def, isNeg_neg x0 m, Bool.not_true, neg_neg, cond_false, if_true,
      not_le.mpr n, if_false]
  · simp only [Bool.not_eq_true] at n
    have e : (⟨x.toUInt64⟩ : Int64) = x := rfl
    simp only [n, cond_false, e, if_false]

@[simp] lemma Int64.isNeg_abs {x : Int64} (m : x ≠ min) : 0 ≤ (⟨x.abs⟩ : Int64) := by
  rw [abs]
  by_cases x0 : x = 0
  · simp only [x0, isNeg_zero, n_zero, neg_zero, Bool.cond_self, ← zero_def, if_false, le_refl]
  by_cases n : x < 0
  · simp only [n, cond_true, ← neg_def, isNeg_neg x0 m, Bool.not_true, if_true]
    simp only [← coe_le_coe, ← coe_lt_coe, coe_zero, coe_neg' m] at n ⊢
    omega
  · have e : (⟨x.toUInt64⟩ : Int64) = x := rfl
    simp only [n, cond_false, e, if_false]
    exact not_lt.mp n

/-!
### Left shift
-/

/-- Shifting left is shifting the inner `UInt64` left -/
instance : HShiftLeft Int64 UInt64 Int64 where
  hShiftLeft x s := ⟨x.toUInt64 <<< s⟩

lemma Int64.shiftLeft_def (x : Int64) (s : UInt64) : x <<< s = ⟨x.toUInt64 <<< s⟩ := rfl

/-- Shifting left is multiplying by a power of two, in nice cases -/
lemma Int64.coe_shiftLeft {x : Int64} {s : UInt64} (s64 : s.toNat < 64)
    (xs : x.abs.toNat < 2 ^ (63 - s.toNat)) : ((x <<< s) : ℤ) = x * 2^s.toNat := by
  have e : ((1 <<< 63 : ℕ) : UInt64).toNat = 2^63 := by rfl
  simp only [isNeg_eq_le, Int64.shiftLeft_def, Int64.toInt_eq_if, UInt64.le_iff_toNat_le, e,
    UInt64.toNat_shiftLeft', Nat.mod_eq_of_lt s64, Int64.abs] at xs ⊢
  by_cases x0 : x.toUInt64 = 0
  · simp only [x0, n_zero, UInt64.toNat_zero, Nat.zero_mod, zero_mul, CharP.cast_eq_zero,
      Nat.reducePow, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero, ↓reduceIte, sub_self]
  by_cases le : 2 ^ 63 ≤ x.toUInt64.toNat
  · generalize hy : 2^64 - x.toUInt64.toNat = y at xs
    have xy : x.toUInt64.toNat = 2^64 - y := by
      rw [←hy]
      have h := x.toUInt64.toNat_lt_2_pow_64
      omega
    simp only [isNeg_eq_le, le, decide_true, if_true, UInt64.toNat_neg, x0, UInt64.size_eq_pow, hy,
      ite_false] at xs
    have y0 : 0 < y := by have h := x.toUInt64.toNat_lt_2_pow_64; omega
    have xm : x.toUInt64.toNat % 2 ^ (64 - s.toNat) = 2 ^ (64 - s.toNat) - y := by
      have e : 2^64 - y = (2^(64 - s.toNat) * (2^s.toNat - 1) + (2^(64 - s.toNat) - y)) := by
        simp only [mul_tsub, ← pow_add, Nat.sub_add_cancel s64.le, mul_one]
        have h0 : 2^(64 - s.toNat) ≤ 2^64 := pow_le_pow_right₀ (by norm_num) (by omega)
        have h1 : y ≤ 2 ^ (64 - s.toNat) :=
          le_trans xs.le (pow_le_pow_right₀ (by norm_num) (by omega))
        omega
      rw [xy, e, Nat.mul_add_mod, Nat.mod_eq_of_lt]
      exact Nat.sub_lt (by positivity) y0
    have y63 : y * 2 ^ s.toNat ≤ 2^63 := by
      refine le_trans (Nat.mul_le_mul_right _ xs.le) ?_
      rw [←pow_add]
      have le : 63 - s.toNat + s.toNat ≤ 63 := by omega
      exact le_trans (pow_le_pow_right₀ (by norm_num) le) (by norm_num)
    have yle : 2 ^ 63 ≤ 2 ^ 64 - y * 2 ^ s.toNat := by
      apply Nat.le_sub_of_add_le
      rw [add_comm, ←Nat.le_sub_iff_add_le (by norm_num)]
      exact y63
    simp only [isNeg_eq_le, le, xm, decide_true, if_true, tsub_mul, ←pow_add,
      Nat.sub_add_cancel s64.le]
    simp only [yle, decide_true, ite_true, Nat.cast_pow, Nat.cast_ofNat, xy]
    rw [Nat.cast_sub, Nat.cast_sub]
    · simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, sub_sub_cancel_left, neg_mul]
    · rw [←hy]; omega
    · exact le_trans y63 (by norm_num)
  · simp only [isNeg_eq_le, le, decide_false, ite_false] at xs
    have lt : x.toUInt64.toNat < 2 ^ (64 - s.toNat) :=
      lt_of_lt_of_le xs (Nat.pow_le_pow_of_le_right (by norm_num) (by omega))
    simp only [Nat.mod_eq_of_lt lt, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, decide_eq_true_eq,
      Nat.cast_ite, CharP.cast_eq_zero, le, decide_false, ite_false, sub_zero, sub_eq_self,
      ite_eq_right_iff, Nat.zero_lt_succ, pow_eq_zero_iff, OfNat.ofNat_ne_zero, imp_false, not_le,
      Bool.false_eq_true, isNeg_eq_le]
    intro le; contrapose le; clear le; simp only [not_le]
    refine lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right xs (pow_pos (by norm_num) _)) ?_
    simp only [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- `0 <<< s = 0` -/
@[simp] lemma Int64.zero_shiftLeft (s : UInt64) : (0 : Int64) <<< s = 0 := by
  simp only [shiftLeft_def, n_zero, UInt64.zero_shiftLeft]; rfl

/-!
### Right shift, rounding up or down
-/

/-- Shift right, rounding up or down -/
@[irreducible] def Int64.shiftRightRound (x : Int64) (s : UInt64) (up : Bool) : Int64 :=
  if x < 0 then
    -- We need arithmetic shifting, which is easiest to do by taking bitwise complement.
    -- However, this fails if `x = min`, so we handle that case separately.
    bif x == min then
      bif 64 ≤ s then bif up then 0 else -1
      else -⟨1 <<< (63 - s)⟩
    else
      -⟨(-x).toUInt64.shiftRightRound s !up⟩
  else
    ⟨x.toUInt64.shiftRightRound s up⟩

/-- `0.shiftRightRound = 0` -/
@[simp] lemma Int64.zero_shiftRightRound (s : UInt64) (up : Bool) :
    (0 : Int64).shiftRightRound s up = 0 := by
  rw [shiftRightRound]
  simp only [lt_self_iff_false, ↓reduceIte, n_zero, UInt64.zero_shiftRightRound, zero_undef]

/-- `Int64.isNeg` for powers of two -/
lemma Int64.isNeg_one_shift {s : UInt64} (s64 : s.toNat < 64) :
    (⟨1 <<< s⟩ : Int64) < 0 ↔ s.toNat = 63 := by
  simp only [isNeg_eq_le, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat,
    UInt64.le_iff_toNat_le, UInt64.toNat_2_pow_63, UInt64.toNat_shiftLeft', UInt64.toNat_one,
    Nat.mod_eq_of_lt s64, decide_eq_decide]
  rw [Nat.mod_eq_of_lt, one_mul, pow_le_pow_iff_right₀ (by omega)]
  · constructor; intro; omega; intro; omega
  · exact one_lt_pow₀ (by norm_num) (by omega)

/-- `ℤ` conversion for `UInt64` powers of two -/
lemma Int64.coe_one_shift {s : UInt64} (s63 : s.toNat < 63) :
    ((⟨1 <<< s⟩ : Int64) : ℤ) = 2^s.toNat := by
  have s64 : s.toNat < 64 := by omega
  have e : (1 <<< s : UInt64).toNat = 2^s.toNat := by
    simp only [UInt64.toNat_shiftLeft', UInt64.toNat_one, Nat.mod_eq_of_lt s64, ne_eq,
      pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true, mul_eq_right₀]
    exact Nat.mod_eq_of_lt (one_lt_pow₀ (by norm_num) (by omega))
  simp only [toInt_eq_if, e, Nat.cast_pow, Nat.cast_ofNat, isNeg_one_shift s64, s63.ne, ↓reduceIte,
    CharP.cast_eq_zero, sub_zero]

/-- `ℤ` conversion for negated `Int64` powers of two -/
lemma Int64.coe_neg_one_shift {s : UInt64} (s63 : s.toNat < 63) :
    ((-⟨1 <<< s⟩ : Int64) : ℤ) = -2^s.toNat := by
  rw [Int64.coe_neg, Int64.coe_one_shift s63]
  have p : 0 < (2 : ℤ) ^ s.toNat := pow_pos (by norm_num) _
  simp only [ite_eq_right_iff]
  omega

/-- Negated `ℤ` conversion for `UInt64` values -/
lemma Int64.coe_eq_toNat_of_lt {n : UInt64} (h : n.toNat < 2^63) :
    ((⟨n⟩ : Int64) : ℤ) = n.toNat := by
  simp only [toInt_eq_if, neg_def, UInt64.toNat_neg, UInt64.size_eq_pow, Nat.cast_ite,
    CharP.cast_eq_zero, isNeg_eq_le, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat,
    UInt64.le_iff_toNat_le, UInt64.toNat_2_pow_63, bif_eq_if, decide_eq_true_eq]
  split_ifs with h0
  · omega
  · simp only [sub_zero]

/-- Negated `ℤ` conversion for `UInt64` values -/
lemma Int64.coe_neg_eq_neg_toNat_of_lt {n : UInt64} (h : n.toNat < 2^63) :
    ((-⟨n⟩ : Int64) : ℤ) = -n.toNat := by
  simp only [toInt_eq_if, neg_def, UInt64.toNat_neg, UInt64.size_eq_pow, Nat.cast_ite,
    CharP.cast_eq_zero, isNeg_eq_le, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat,
    UInt64.le_iff_toNat_le, UInt64.toNat_2_pow_63, bif_eq_if, decide_eq_true_eq]
  split_ifs with h0 h1 h2
  · omega
  · simp only [sub_self, h0, UInt64.toNat_zero, CharP.cast_eq_zero, neg_zero]
  · omega
  · contrapose h2; clear h2
    simp only [not_le, not_lt]
    exact le_trans (by norm_num) (Nat.sub_le_sub_left h.le _)

/-- `Int64.shiftRightRound` rounds correctly -/
lemma Int64.coe_shiftRightRound (x : Int64) (s : UInt64) (up : Bool) :
    (x.shiftRightRound s up : ℤ) = (x : ℤ).rdiv (2^s.toNat) up := by
  rw [shiftRightRound, Int.rdiv]
  have t0 : (2 : ℤ) ≠ 0 := by decide
  have e1 : ((-1 : Int64) : ℤ) = -1 := rfl
  have e63 : (63 : UInt64).toNat = 63 := rfl
  have e64 : (64 : UInt64).toNat = 64 := rfl
  simp only [bif_eq_if, decide_eq_true_eq, beq_iff_eq, ← coe_lt_zero_iff,
    apply_ite (fun x : Int64 ↦ (x : ℤ)), coe_zero, e1, Nat.cast_pow, Nat.cast_ofNat]
  by_cases x0 : (x : ℤ) < 0
  · simp only [x0, if_true]
    by_cases xm : x = .min
    · have me : ((.min : Int64) : ℤ) = -(2:ℤ)^63 := by decide
      simp only [xm, if_true, me]
      by_cases s64 : 64 ≤ s
      · simp only [s64, ite_true]
        simp only [UInt64.le_iff_toNat_le, e64] at s64
        induction up
        · simp only [ite_false, neg_neg, Nat.cast_pow, Nat.cast_ofNat, cond_false,
            Bool.false_eq_true]
          rw [Int.ediv_eq_neg_one (by positivity)]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        · simp only [ite_true, neg_neg, Nat.cast_pow, Nat.cast_ofNat, cond_true,
            zero_eq_neg]
          apply Int.ediv_eq_zero_of_lt (by positivity)
          exact pow_lt_pow_right₀ (by norm_num) (by omega)
      · simp only [s64, ite_false, neg_neg]
        simp only [UInt64.le_iff_toNat_le, e64, not_le] at s64
        have s63 : s.toNat ≤ 63 := by omega
        have es : (63 - s).toNat = 63 - s.toNat := by
          rw [UInt64.toNat_sub'', e63]
          simp only [UInt64.le_iff_toNat_le, e63]; omega
        by_cases s0 : s = 0
        · simp only [s0, sub_zero, UInt64.toNat_zero, pow_zero, Int.ediv_one, ite_self]; decide
        · simp only [UInt64.eq_iff_toNat_eq, UInt64.toNat_zero] at s0
          rw [Int64.coe_neg_one_shift, es]
          · simp only [Int.ediv_pow_of_le t0 s63, Int.neg_ediv_pow_of_le t0 s63, ite_self]
          · rw [es]; omega
    · simp only [xm, ite_false]
      have xnn : ¬-x < 0 := by
        simp only [← Int64.coe_lt_coe, coe_zero, coe_neg, ← coe_min', coe_eq_coe, xm, if_false]
        linarith
      have ult : ((-x).toUInt64.shiftRightRound s !up).toNat < 2 ^ 63 := by
        rw [isNeg_eq_le, not_le] at xnn
        exact lt_of_le_of_lt UInt64.shiftRightRound_le_self xnn
      rw [coe_neg_eq_neg_toNat_of_lt ult, UInt64.toNat_shiftRightRound']
      induction up
      · simp only [Bool.not_false, ite_true, Int.cast_neg_ceilDiv_eq_ediv, Nat.cast_pow,
          Nat.cast_ofNat, ite_false]
        refine congr_arg₂ _ ?_ rfl
        rw [← coe_of_nonneg, coe_neg' xm, neg_neg]
        simp only [not_lt.mp xnn, not_false_eq_true]
      · simp only [Bool.not_true, ite_false, Int.ofNat_ediv, Nat.cast_pow, Nat.cast_ofNat,
          ite_true, neg_inj, Bool.false_eq_true]
        rw [← coe_of_nonneg, coe_neg' xm]
        simp only [not_lt.mp xnn, not_false_eq_true]
  · simp only [x0, ite_false]
    have xn : ¬x < 0 := by
      rw [←Int64.coe_lt_coe, coe_zero]
      linarith
    have xsn : ¬(⟨UInt64.shiftRightRound x.toUInt64 s up⟩ : Int64) < 0 := by
      simp only [isNeg_eq_le, Nat.reducePow, not_le] at xn ⊢
      exact lt_of_le_of_lt (UInt64.shiftRightRound_le_self) xn
    rw [coe_of_nonneg (not_lt.mp xsn), UInt64.toNat_shiftRightRound']
    induction up
    · simp only [ite_false, Int.ofNat_ediv, Nat.cast_pow, Nat.cast_ofNat,
        coe_of_nonneg (not_lt.mp xn), Bool.false_eq_true]
    · simp only [ite_true, Int.cast_ceilDiv_eq_neg_ediv, Nat.cast_pow, Nat.cast_ofNat,
        coe_of_nonneg (not_lt.mp xn)]

/-- `Int64.shiftRightRound` reduces `abs` -/
lemma Int64.abs_shiftRightRound_le (x : Int64) (s : UInt64) (up : Bool) :
    |(x.shiftRightRound s up : ℤ)| ≤ |(x : ℤ)| := by
  simp only [ne_eq, coe_shiftRightRound, Nat.cast_pow, Nat.cast_ofNat, Int.abs_rdiv_le]

/-- `Int64.shiftRightRound` never produces `min` from scratch -/
lemma Int64.shiftRightRound_ne_min {x : Int64} (n : x ≠ min) (s : UInt64) (up : Bool) :
    x.shiftRightRound s up ≠ min := by
  contrapose n
  simp only [ne_eq, not_not] at n ⊢
  have h := abs_shiftRightRound_le x s up
  simp only [n, coe_min', _root_.abs_neg, abs_pow, abs_two, le_abs] at h
  rcases h with h | h
  · linarith [coe_lt_pow x]
  · rw [←coe_eq_coe, coe_min']
    apply le_antisymm
    · linarith
    · exact pow_le_coe _

/-!
### `natFloor`: An `ℕ` trying to be less than an `Int64`
-/

/-- The greatest natural `≤ n` (that is, `max 0 n`) -/
def Int64.natFloor (n : Int64) : ℕ :=
  if n < 0 then 0 else n.toUInt64.toNat

/-- `natFloor` in terms of `n : ℤ` -/
lemma Int64.natFloor_eq (n : Int64) : n.natFloor = ⌊(n : ℤ)⌋₊ := by
  rw [natFloor]
  by_cases neg : n < 0
  · simp [neg, coe_of_neg neg]
  · simp only [neg, Bool.false_eq_true, ↓reduceIte, Nat.floor_int]
    simp only [Bool.not_eq_true] at neg
    simp only [coe_of_nonneg (not_lt.mp neg), Int.toNat_ofNat]
