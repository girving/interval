import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Interval.Misc.Bool
import Interval.Misc.BitVec
import Interval.Misc.Int
import Interval.Tactic.Decide
import Interval.Tactic.Init
import Interval.UInt64

/-!
## 64-bit two's complement integers

Arithmetic wraps, so beware (not really, our uses are formally checked).
-/

open Set

attribute [coe] Int64.toInt

/-- The `ℤ` that an `Int64` represents -/
instance : Coe Int64 ℤ where
  coe x := x.toInt

/-- The `ZMod (2^64)` that an `Int64` represents -/
noncomputable instance : Coe Int64 (ZMod (2^64)) where
  coe x := x.toUInt64.toNat

/-- Reduce `Int64` equality to `UInt64` equality -/
@[to_bitvec] lemma Int64.ext_iff (x y : Int64) : x = y ↔ x.toUInt64 = y.toUInt64 := by
  induction' x with x; induction' y with y; simp

-- Arithmetic definition lemmas
lemma Int64.zero_def : (0 : Int64) = UInt64.toInt64 0 := rfl
lemma Int64.one_def : (1 : Int64) = UInt64.toInt64 1 := rfl
lemma Int64.neg_def (x : Int64) : -x = (-x.toUInt64).toInt64 := rfl
lemma Int64.add_def (x y : Int64) : x + y = (x.toUInt64 + y.toUInt64).toInt64 := rfl
lemma Int64.sub_def (x y : Int64) : x - y = (x.toUInt64 - y.toUInt64).toInt64 := rfl
lemma Int64.mul_def (x y : Int64) : x * y = (x.toUInt64 * y.toUInt64).toInt64 := rfl

-- Simplification lemmas
@[simp] lemma Int64.n_zero : (0 : Int64).toUInt64 = 0 := rfl
@[simp] lemma Int64.isNeg_zero : ¬((0 : Int64) < 0) := of_decide_eq_false rfl
@[simp] lemma Int64.n_min : Int64.minValue.toUInt64 = 2^63 := by fast_decide
@[simp] lemma Int64.toNat_min : Int64.minValue.toUInt64.toNat = 2^63 := rfl
@[simp] lemma Int64.toInt_min : Int64.minValue.toInt = -2^63 := rfl
@[simp] lemma Int64.toBitVec_min : Int64.minValue.toBitVec = 2^63 := by fast_decide
@[simp] lemma Int64.isNeg_min : Int64.minValue < 0 := rfl
@[simp] lemma Int64.neg_min : -Int64.minValue = .minValue := rfl
@[simp] lemma Int64.zero_undef : (UInt64.toInt64 0 : Int64) = 0 := rfl

/-- Fast conversion from `ℕ` -/
instance : NatCast Int64 where
  natCast n := UInt64.toInt64 (UInt64.ofNat n)

/-- Fast conversion from `ℤ` -/
instance : IntCast Int64 where
  intCast n := Int64.ofInt n

@[to_bitvec, to_omega] lemma Int64.toBitVec_natCast (n : ℕ) : (n : Int64).toBitVec = n := rfl
@[to_bitvec, to_omega] lemma Int64.toBitVec_intCast (n : ℤ) : (n : Int64).toBitVec = n := by rfl
@[to_omega, to_bitvec] lemma Int64.apply_ite_toInt (c : Prop) {d : Decidable c} (x y : Int64) :
    (((if c then x else y) : Int64) : ℤ) = if c then (x : ℤ) else (y : ℤ) := by apply apply_ite
@[to_omega] lemma Int64.toUInt64_natCast (n : ℕ) : (n : Int64).toUInt64 = .ofNat n := rfl

lemma Int64.induction_bitvec {p : Int64 → Prop} (h : ∀ x : BitVec 64, p (.ofBitVec x))
    (x : Int64) : p x :=
  h x.toBitVec

@[to_bitvec] lemma Int64.toBitVec_ofUInt64 (x : UInt64) :
    (UInt64.toInt64 x).toBitVec = x.toBitVec := rfl

@[simp, to_omega] lemma Int64.toInt64_ofNat (n : ℕ) : (UInt64.ofNat n).toInt64 = .ofNat n := by
  simp only [to_bitvec, toBitVec_ofNat']

@[to_omega] lemma Int64.toInt_natCast (n : ℕ) :
    ((n : Int64) : ℤ) = if 2 * (n % 2^64) < 2^64 then (n : ℤ) % 2^64 else (n : ℤ) % 2^64 - 2^64 := by
  have e : (n : ℕ) = Int64.ofNat n := rfl
  simp only [toInt, BitVec.toInt, Int64.toBitVec, e]
  simp only [toUInt64_ofNat', UInt64.toNat_toBitVec, UInt64.toNat_ofNat', Nat.reducePow,
    Int.natCast_emod, Nat.cast_ofNat, Int.reducePow]

@[to_omega] lemma Int64.coe_ofNat (n : ℕ) : (Int64.ofNat n).toInt = (n : ℤ).bmod size :=
  Int64.toInt_ofNat

@[simp, to_bitvec] lemma BitVec.ofNat_mod_64 (n : ℕ) :
    BitVec.ofNat 64 (n % 2 ^ 64) = BitVec.ofNat 64 n := by
  simp only [Nat.reducePow, toNat_eq, toNat_ofNat, dvd_refl, Nat.mod_mod_of_dvd]

/-- `Int64` is a commutative ring.
    We don't use `CommRing.ofMinimalAxioms, since we want our own `Sub` instance. -/
instance : CommRing Int64 where
  add_zero x := Int64.add_zero x
  zero_add x := Int64.zero_add x
  add_comm x y := Int64.add_comm x y
  add_assoc x y z := Int64.add_assoc x y z
  neg_add_cancel x := Int64.add_left_neg x
  mul_assoc x y z := Int64.mul_assoc x y z
  mul_comm x y := Int64.mul_comm x y
  zero_mul x := Int64.zero_mul
  mul_zero x := Int64.mul_zero
  one_mul x := Int64.one_mul x
  mul_one x := Int64.mul_one x
  left_distrib x y z := Int64.mul_add
  right_distrib x y z := Int64.add_mul
  sub_eq_add_neg x y := Int64.sub_eq_add_neg x y
  natCast_zero := rfl
  natCast_succ n := by simp only [to_bitvec]
  intCast_ofNat n := rfl
  intCast_negSucc n := by simp only [to_bitvec, Int.negSucc_eq]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- `Int64` < is decidable -/
instance decidableLT : @DecidableRel Int64 Int64 (· < ·)
  | a, b => by dsimp [LT.lt, Int64.lt]; infer_instance

/-- `Int64` ≤ is decidable -/
instance decidableLE : @DecidableRel Int64 Int64 (· ≤ ·)
  | a, b => by dsimp [LE.le, Int64.le]; infer_instance

/-- Negation preserves `min` -/
@[simp] lemma Int64.neg_eq_min {x : Int64} : (-x) = minValue ↔ x = minValue := by
  have i : ∀ {x : Int64}, x = minValue → (-x) = minValue := by
    intro x h; simp only [h, neg_def]; decide
  by_cases a : x = minValue
  · simp only [a, neg_min]
  · by_cases b : (-x) = minValue
    · rw [b, ←neg_neg x, i b]
    · simp only [a, b]

/-- `minValue ≠ 0` -/
@[simp] lemma Int64.min_ne_zero : Int64.minValue ≠ 0 := by decide

/-- `0 ≠ minValue` -/
@[simp] lemma Int64.zero_ne_min : 0 ≠ Int64.minValue := by decide

-- Consequences of the sign bit being true or false
lemma Int64.coe_of_nonneg {x : Int64} (h : 0 ≤ x) : (x : ℤ) = x.toUInt64.toNat := by
  simp only [Int64.le_iff_toBitVec_sle, BitVec.sle, toBitVec_zero, BitVec.toInt_zero,
    decide_eq_true_eq] at h
  simp only [BitVec.toInt, toBitVec, UInt64.toNat_toBitVec, toInt] at h ⊢
  have lt := x.toUInt64.toNat_lt_2_pow_64
  omega
lemma Int64.coe_of_neg {x : Int64} (h : x < 0) : (x : ℤ) = x.toUInt64.toNat - ((2^64 : ℕ) : ℤ) := by
  have b := x.toUInt64.toNat_lt_2_pow_64
  simp only [Int64.lt_iff_toBitVec_slt, BitVec.slt, BitVec.toInt, toBitVec, UInt64.toNat_toBitVec,
    Nat.reducePow, Nat.cast_ofNat, n_zero, UInt64.toBitVec_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    CharP.cast_eq_zero, decide_eq_true_eq] at h
  simp only [Int64.toInt, UInt64.toNat, Int64.toBitVec, Int64.toBitVec, BitVec.toInt] at h ⊢
  omega

lemma Int64.neg_natCast (n : ℕ) : -(n : Int64) = (-(n : ℤ) : ℤ) := by
  apply Int64.neg_ofNat

@[to_omega] lemma Int64.toUInt64_intCast (n : ℤ) : (n : Int64).toUInt64 = .ofInt n := by
  simp only [UInt64.eq_iff_toBitVec_eq, toBitVec_toUInt64, toBitVec_intCast, UInt64.ofInt,
    Int.reducePow]
  refine Eq.trans ?_ (UInt64.toBitVec_ofNat (n % 18446744073709551616).toNat)
  simp only [UInt64.toBitVec_ofNat, BitVec.toNat_eq, BitVec.toNat_intCast, BitVec.toNat_ofNat]
  omega

/-- `isNeg` in terms of `≤` over `ℕ` -/
lemma Int64.isNeg_eq_le (x : Int64) : x < 0 ↔ 2^63 ≤ x.toUInt64.toNat := by
  have b := x.toUInt64.toNat_lt_2_pow_64
  simp only [Int64.lt_iff_toBitVec_slt, BitVec.slt, BitVec.toInt, toBitVec, UInt64.toNat_toBitVec,
    Nat.reducePow, Nat.cast_ofNat, n_zero, UInt64.toBitVec_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    CharP.cast_eq_zero, decide_eq_true_eq]
  rw [UInt64.toNat]
  omega

/-- The ordering is consistent with `ℤ` -/
@[simp] lemma Int64.coe_lt_coe (x y : Int64) : (x : ℤ) < (y : ℤ) ↔ x < y := by
  simp only [toInt, Int64.lt_iff_toBitVec_slt, BitVec.slt, decide_eq_true_eq]

/-- Converting to `ℤ` is under `2^63` -/
@[simp] lemma Int64.coe_lt_pow (x : Int64) : (x : ℤ) < 2^63 := by
  have h := x.toUInt64.toNat_lt_2_pow_64
  simp only [toInt, UInt64.toNat, BitVec.toInt] at h ⊢
  omega

/-- Converting to `ℤ` is at least `-2^63` -/
@[simp] lemma Int64.pow_le_coe (x : Int64) : -2^63 ≤ (x : ℤ) := by
  simp only [toInt, BitVec.toInt]
  omega

@[simp] lemma Int64.coe_min' : ((.minValue : Int64) : ℤ) = -(2:ℤ)^63 := rfl

/-- The ordering is consistent with `ℤ` -/
@[simp] lemma Int64.coe_le_coe (x y : Int64) : (x : ℤ) ≤ (y : ℤ) ↔ x ≤ y := by
  simp only [← not_lt, coe_lt_coe, Int64.lt_iff_toBitVec_slt, Int64.le_iff_toBitVec_sle, BitVec.slt,
    BitVec.sle]
  simp only [toInt_toBitVec, coe_lt_coe, decide_eq_true_eq, Int64.not_lt]

/-- We print `Int64`s as signed integers -/
instance : Repr Int64 where
  reprPrec x p := Repr.reprPrec (x : ℤ) p

-- An `Int64` is zero iff its inner `UInt64` is -/
lemma Int64.eq_zero_iff_n_eq_zero (x : Int64) : x = 0 ↔ x.toUInt64 = 0 := by
  simp only [ext_iff, n_zero]

-- An `Int64` is not zero iff its inner `UInt64` is -/
lemma Int64.ne_zero_iff_n_ne_zero (x : Int64) : x ≠ 0 ↔ x.toUInt64 ≠ 0 := by
  simp only [Ne, Int64.eq_zero_iff_n_eq_zero]

/-- Expand negation into something `omega` can handle -/
@[to_omega] lemma Int64.coe_neg {x : Int64} :
    ((-x : Int64) : ℤ) = if (x : ℤ) = -2^63 then -2^63 else -(x : ℤ) := by
  have neg := x.toUInt64.toNat_neg
  have xu := x.toUInt64.toNat_lt_2_pow_64
  simp only [neg_def, toInt, BitVec.toInt, Int64.toBitVec, UInt64.toNat, UInt64.size,
    UInt64.toUInt64_toInt64] at neg xu ⊢
  generalize x.toUInt64.toBitVec.toNat = a at neg xu
  generalize (-x.toUInt64).toBitVec.toNat = b at neg
  by_cases a0 : a = 0
  all_goals try simp only [a0] at neg ⊢
  · simp only [tsub_zero, Nat.mod_self] at neg
    simp [neg]
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
  simp only [add_def, toInt, BitVec.toInt, Int64.toBitVec, add, UInt64.toUInt64_toInt64]
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
  simp only [toInt, ext_iff, UInt64.eq_iff_toNat_eq, BitVec.toInt, UInt64.toNat, Int64.toBitVec]
  omega

/-- Equality is consistent with `ℤ` -/
@[simp] lemma Int64.coe_ne_coe (x y : Int64) : (x : ℤ) ≠ (y : ℤ) ↔ x ≠ y := by
  simp only [ne_eq, coe_eq_coe]

@[simp] lemma Int64.coe_eq_zero (x : Int64) : (x : ℤ) = 0 ↔ x = 0 := by
  rw [←coe_zero, coe_eq_coe]

/-- Converting to `ℤ` is more than `-2^63` if we're not `minValue` -/
@[simp] lemma Int64.pow_lt_coe {x : Int64} (n : x ≠ minValue) : -2^63 < (x : ℤ) := by
  refine Ne.lt_of_le ?_ (pow_le_coe x)
  rw [Ne, ←coe_min', coe_eq_coe]
  exact n.symm

/-- Negation flips `.isNeg`, except at `0` and `.minValue` -/
lemma Int64.isNeg_neg {x : Int64} (x0 : x ≠ 0) (xn : x ≠ .minValue) : (-x) < 0 ↔ 0 ≤ x := by
  simp only [← coe_le_coe, toInt_zero, ← coe_lt_coe, coe_neg]
  simp only [ne_eq, ← coe_eq_zero] at x0
  simp only [← coe_ne_coe, toInt_min] at xn
  omega

@[to_omega] lemma UInt64.coe_toInt64 (x : UInt64) :
    (x.toInt64 : ℤ) = if x < 2^63 then x.toInt else x.toInt - 2^64 := by
  induction' x using UInt64.induction_nat with x h
  have e0 : (ofNat x).toInt64 = (x : Int64) := UInt64.toInt64_ofNat
  have e1 : (2 ^ 63 : UInt64).toNat = 2^63 := by fast_decide
  simp only [to_omega, e0, UInt64.lt_iff_toNat_lt, e1] at h ⊢
  omega

/-!
### Conditions for `ℤ` conversion to commute with arithmetic
-/

/-- `Int64.neg` usually commutes with `ℤ` conversion -/
lemma Int64.coe_neg' {x : Int64} (xn : x ≠ .minValue) : ((-x : Int64) : ℤ) = -x := by
  simp only [← coe_ne_coe, toInt_min] at xn
  simp only [coe_neg, xn, if_false]

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
  simp only [← coe_lt_coe, coe_zero] at h
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
@[simp] lemma Int64.ofNat_eq_coe (n : ℕ) : (n : Int64).toUInt64 = .ofNat n := rfl

@[simp] lemma Int64.toNat_toBitVec_natCast (n : ℕ) : (n : Int64).toBitVec.toNat = n % (2 ^ 64) :=
  rfl

@[simp] lemma Int64.toNat_toBitVec_intCast (n : ℤ) :
    (n : Int64).toBitVec.toNat = (n % (2 ^ 64)).toNat := by
  simp only [to_bitvec]

/-- Conversion `ℕ → Int64 → ℤ` is the same as direct if we're small -/
lemma Int64.toInt_ofNat'' {n : ℕ} (h : n < 2^63) : ((n : Int64) : ℤ) = n := by
  simp only [toInt, BitVec.toInt]
  simp only [toNat_toBitVec_natCast, Nat.reducePow, Int.natCast_emod, Nat.cast_ofNat]
  omega

/-- Conversion `ℤ → Int64 → ℤ` is the same as direct if we're small -/
lemma Int64.toInt_ofInt' {n : ℤ} (h : |n| < 2^63) : ((n : Int64) : ℤ) = n := by
  generalize ha : 2 ^ 63 = a
  have ha' : (2 ^ 63 : ℤ) = a := by omega
  have a2 : 2 ^ 64 = 2 * a := by omega
  have a2' : (2 ^ 64 : ℤ) = (2 * a : ℕ) := by omega
  simp only [toInt, BitVec.toInt, toNat_toBitVec_intCast, a2, a2', ha'] at h ⊢
  clear ha ha' a2 a2'
  induction' n using Int.induction_overlap with n n
  all_goals simp only [Nat.abs_cast, Nat.cast_lt, Nat.ofNat_pos, mul_lt_mul_left, Int.ofNat_toNat,
    Int.ofNat_mod_ofNat, Int.toNat_natCast, abs_neg, Nat.abs_cast, Nat.cast_lt] at h ⊢
  · rw [Nat.mod_eq_of_lt]
    · simp only [h, ↓reduceIte]
    · omega
  · by_cases n0 : n = 0
    · simp [n0]
    have d : ¬((2 * a : ℕ) : ℤ) ∣ n := by
      contrapose h
      simp only [Decidable.not_not, not_lt, Int.natCast_dvd, Int.natAbs_natCast] at h ⊢
      linarith [Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr n0) h]
    have lt : n < 2 * a := by omega
    simp only [Int.neg_emod, d, ite_false, Int.ofNat_mod_ofNat]
    simp only [Int.natCast_natAbs, Int.natCast_emod, Int.abs_natCast]
    simp only [Int.ofNat_mod_ofNat, Nat.mod_eq_of_lt lt, ← Nat.cast_sub lt.le, Int.toNat_natCast]
    omega

/-- Conversion to `ℤ` is the same as the underlying `toNat` if we're small -/
lemma Int64.toInt_eq_toNat_of_lt {x : Int64} (h : x.toUInt64.toNat < 2^63) :
    (x : ℤ) = ↑x.toUInt64.toNat := by
  apply Int64.coe_of_nonneg
  simp only [le_iff_toBitVec_sle, BitVec.sle, BitVec.toInt, BitVec.toNat_ofNat, decide_eq_true_eq,
    UInt64.toNat, Int64.toBitVec, n_zero, UInt64.toBitVec_zero] at h ⊢
  omega

/-- `UInt64.log2` converts to `ℤ` as `toNat` -/
@[simp] lemma Int64.coe_log2 (n : UInt64) : (n.log2.toInt64 : ℤ) = n.log2.toNat := by
  rw [Int64.toInt_eq_toNat_of_lt]
  simp only [UInt64.toNat_log2, UInt64.toUInt64_toInt64]
  exact lt_trans (UInt64.log2_lt_64 _) (by norm_num)

/-- Adding `2^63` and converting via `UInt64` commutes -/
@[simp] lemma Int64.toNat_add_pow_eq_coe (n : Int64) :
    ((n + 2^63).toUInt64.toNat : ℤ) = (n : ℤ) + 2^63 := by
  have add := coe_add (x := n) (y := 2^63)
  generalize n + 2 ^ 63 = z at add
  have be : ∀ z : Int64, z.toBitVec.toNat = z.toUInt64.toNat := fun _ ↦ rfl
  have pe : (2 ^ 63 : Int64).toUInt64.toNat = 2 ^ 63 := by fast_decide
  simp only [toInt, BitVec.toInt, be, pe] at add ⊢
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
  lt_iff_le_not_ge x y := by
    simp only [←Int64.coe_lt_coe, ←Int64.coe_le_coe]; apply lt_iff_le_not_ge
  toDecidableLE x y := by infer_instance
  min_def x y := by
    simp only [min]
    split_ifs
    · rfl
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]; linarith
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]; linarith
    · simp_all only [← Int64.coe_lt_coe, ← Int64.coe_le_coe]
  max_def x y := by
    simp only [max]
    split_ifs
    · rfl
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]; linarith
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]; linarith
    · simp_all only [← Int64.coe_lt_coe, ← Int64.coe_le_coe]

/-- `Int64.min` is the smallest element -/
@[simp] lemma Int64.min_le (x : Int64) : .minValue ≤ x := by
  simp only [← Int64.coe_le_coe, toInt_min]
  simp only [Int64.toInt, BitVec.toInt]
  omega

/-- `Int64.min` is the smallest element -/
lemma Int64.eq_min_iff_min_lt (x : Int64) : x = .minValue ↔ x ≤ .minValue := by
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

@[simp] lemma Int64.natAbs_lt_pow_iff {x : Int64} : (x : ℤ).natAbs < 2^63 ↔ x ≠ minValue := by
  simp only [Int.natAbs_def, ← coe_ne_coe, toInt_min]
  have := x.coe_lt_pow
  have := x.pow_le_coe
  split_ifs
  all_goals omega

/-- A sufficient condition for subtraction to decrease the value -/
lemma Int64.sub_le' {x y : Int64} (h : minValue + y ≤ x) : x - y ≤ x := by
  simp only [← coe_le_coe, toInt_min, coe_add, coe_sub] at h ⊢
  have := x.coe_lt_pow
  have := x.pow_le_coe
  have := y.coe_lt_pow
  have := y.pow_le_coe
  omega

@[to_omega] lemma Int64.toNat_toUInt64 (x : Int64) : x.toUInt64.toNat = (x.toInt % 2^64).toNat := by
  induction' x using Int64.induction_bitvec with x
  simp only [toUInt64_ofBitVec, UInt64.toNat_ofBitVec, toInt_ofBitVec, Int.reducePow]
  simp only [BitVec.toInt]
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
    BitVec.toInt, Int64.toBitVec, UInt64.toNat, lt_iff_toBitVec_slt, BitVec.slt] at u ⊢
  simp only [UInt64.toNat_toBitVec] at u
  simp only [n_zero, UInt64.toBitVec_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, Nat.ofNat_pos,
    ↓reduceIte, decide_eq_true_eq, ite_eq_right_iff, Nat.mul_zero, Int64.toBitVec_toUInt64,
    Int64.toNat_toBitVec]
  generalize x.toUInt64.toNat = a at u
  by_cases lt : 2 * a < 18446744073709551616
  · simp_all only [ite_true, forall_const, if_true_right, isEmpty_Prop, not_lt, Nat.cast_nonneg,
      IsEmpty.forall_iff]
  · simp only [lt, ↓reduceIte, sub_neg, Nat.cast_lt_ofNat, u, IsEmpty.forall_iff]

/-- Alternate definition of (almost) absolute value (maps `Int64.min → Int64.min`) -/
lemma Int64.abs_def (x : Int64) : x.abs = if x < 0 then -x else x := by
  simp only [lt_iff_toBitVec_slt, toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.slt_zero_eq_msb,
    apply_ite, eq_iff_toBitVec_eq, Int64.toBitVec_abs, BitVec.abs_eq, toBitVec_neg, ite_eq_left_iff,
    Bool.not_eq_true, ite_eq_right_iff]
  split_ifs with h
  all_goals simp [h]

/-- Prove something about `Int64` via `ℕ` -/
lemma Int64.induction_nat (p : Int64 → Prop)
    (h : ∀ n : ℕ, n < 2^64 → p (n : Int64)) (x : Int64) : p x := by
  convert h x.toUInt64.toNat (UInt64.toNat_lt _)
  have e : ∀ n : ℕ, (n : Int64) = (UInt64.ofNat n).toInt64 := by intro; rfl
  simp only [e, UInt64.cast_toNat, toInt64_toUInt64]

@[to_omega] lemma Int64.toNat_toBitVec' (x : Int64) : x.toBitVec.toNat = ((x : ℤ) % 2^64).toNat := by
  induction' x using Int64.induction_nat with x h
  simp only [to_omega]
  omega

/-!
### Order operations: min, abs
-/

/-- Alterantive abs which is better behaved, by has to change type -/
def Int64.uabs (x : Int64) : UInt64 :=
  if x < 0 then -x.toUInt64 else x.toUInt64

@[simp] lemma Int64.abs_zero : (0 : Int64).abs = 0 := rfl
@[simp] lemma Int64.uabs_zero : (0 : Int64).uabs = 0 := rfl
@[simp] lemma Int64.abs_min : Int64.minValue.abs = Int64.minValue := rfl
@[simp] lemma Int64.uabs_min : Int64.minValue.uabs = 2^63 := by fast_decide

/-- `.abs` is absolute value (`ℕ` version) -/
@[to_omega] lemma Int64.toNat_abs {x : Int64} :
    x.abs.toNatClampNeg = if x = .minValue then 0 else (x : ℤ).natAbs := by
  split_ifs with m
  · simp only [m, abs_min, toNatClampNeg_minValue]
  induction' x using Int64.induction_nat with n h
  simp only [to_omega] at m
  simp only [Int64.abs, toBitVec_natCast, BitVec.natCast_eq_ofNat, toInt_natCast, Nat.reducePow,
    Int.reducePow]
  rw [Int64.toNatClampNeg, Int64.toInt, Int64.toBitVec]
  simp only [BitVec.abs, to_omega, Int.bmod]
  split_ifs
  all_goals omega

/-- `.uabs` is absolute value (`ℕ` version) -/
@[to_omega] lemma Int64.toNat_uabs {x : Int64} : x.uabs.toNat = (x : ℤ).natAbs := by
  induction' x using Int64.induction_nat with n h
  have e0 : (UInt64.ofNat n).toNat = n % 2^64 := by exact UInt64.toNat_ofNat
  have e1 : n % 18446744073709551616 = n := by omega
  simp only [Int64.uabs, toInt_natCast, Nat.reducePow, Int.reducePow, to_omega, e0, e1]
  split_ifs
  all_goals omega

/-- `.abs` is absolute value (`ℤ` version) -/
@[to_omega] lemma Int64.coe_abs {x : Int64} :
    x.abs.toInt = if x = .minValue then -2^63 else |(x : ℤ)| := by
  split_ifs with m
  · simp [m]
  induction' x using Int64.induction_nat with n h
  simp only [to_omega] at m
  simp only [Int64.abs, toBitVec_natCast, BitVec.natCast_eq_ofNat, toInt_natCast, Nat.reducePow,
    Int.reducePow]
  rw [Int64.toInt, Int64.toBitVec]
  simp only [BitVec.abs, to_omega, Int.bmod]
  simp only [Nat.reducePow, Nat.add_one_sub_one, Nat.reduceMod, ge_iff_le, Nat.cast_ofNat,
    Int.reduceAdd, Int.reduceDiv, Int.abs_def,
    apply_ite (f := fun x : ℤ ↦ x % 18446744073709551616), Int.neg_emod] at h m ⊢
  simp only [Int.reduceAbs, Nat.cast_ofNat, dvd_refl, Int.emod_emod_of_dvd, Int.sub_emod_right,
    ite_self]
  omega

/-- `.uabs` is absolute value (`ℤ` version) -/
@[to_omega] lemma Int64.coe_uabs {x : Int64} : x.uabs.toInt = |(x : ℤ)| := by
  induction' x using Int64.induction_nat with n h
  simp only [Int64.uabs, toInt_natCast, Nat.reducePow, Int.reducePow, to_omega, Int.abs_def]
  omega

/-- If we turn `uabs` back into an `Int64`, it's abs except at `.min` -/
lemma Int64.coe_uabs' {x : Int64} (n : x ≠ .minValue) : (x.uabs.toInt64 : ℤ) = |(x : ℤ)| := by
  generalize ha : (x : ℤ) = a
  have ha' : x.toUInt64.toBitVec.toInt = a := by rw [← ha]; rfl
  have e : (-x.toUInt64).toBitVec.toInt = (-x : Int64) := rfl
  simp only [← coe_ne_coe, toInt_min, ha] at n
  simp only [uabs, toInt, ← coe_lt_zero_iff, UInt64.toUInt64_toInt64,
    apply_ite (fun x : UInt64 ↦ x.toBitVec.toInt), ha', Int64.toBitVec]
  simp only [e, coe_neg, ha, n, if_false, Int.abs_def]

/-- `abs` preserves 0 -/
@[simp] lemma Int64.abs_eq_zero_iff {x : Int64} : x.abs = 0 ↔ x = 0 := by
  simp only [abs_def]
  split_ifs with h
  · simp only [neg_eq_zero]
  · simp only

/-- `uabs` preserves 0 -/
@[simp] lemma Int64.uabs_eq_zero_iff {x : Int64} : x.uabs = 0 ↔ x = 0 := by
  simp only [← coe_eq_coe, UInt64.eq_iff_toNat_eq, UInt64.toNat_zero, toInt_zero, toNat_uabs,
    Int.natAbs_eq_zero]

/-- `abs` preserves 0 -/
@[simp] lemma Int64.abs_ne_zero_iff {x : Int64} : x.abs ≠ 0 ↔ x ≠ 0 := by
  simp only [Ne, Int64.abs_eq_zero_iff]

/-- `uabs` preserves 0 -/
@[simp] lemma Int64.uabs_ne_zero_iff {x : Int64} : x.uabs ≠ 0 ↔ x ≠ 0 := by
  simp only [Ne, Int64.uabs_eq_zero_iff]

/-- `.abs` doesn't change if nonneg -/
lemma Int64.abs_eq_self' {x : Int64} (h : 0 ≤ x) : x.abs = x := by
  simp only [abs_def, not_lt.mpr h, ↓reduceIte]

/-- `.uabs` doesn't change if nonneg -/
lemma Int64.uabs_eq_self' {x : Int64} (h : 0 ≤ x) : x.uabs = x.toUInt64 := by
  have h1 := coe_of_nonneg h
  simp only [← coe_nonneg_iff] at h
  simp only [UInt64.eq_iff_toNat_eq, toNat_uabs, Int.natAbs_def, not_lt.mpr h, if_false]
  simp only [h1, Int.toNat_natCast]

lemma Int64.ne_minValue_of_nonneg {x : Int64} (h : 0 ≤ x) : x ≠ .minValue := by aesop

/-- `.abs` doesn't change if nonneg -/
lemma Int64.abs_eq_self {x : Int64} (h : 0 ≤ x) : x.abs.toInt = x := by
  have m := ne_minValue_of_nonneg h
  simp only [← coe_nonneg_iff] at h
  simp only [coe_abs, m, ↓reduceIte, abs_of_nonneg h]

/-- `.uabs` doesn't change if nonneg -/
lemma Int64.uabs_eq_self {x : Int64} (h : 0 ≤ x) : x.uabs.toInt = x := by
  simp only [← coe_nonneg_iff] at h
  simp only [coe_uabs, abs_of_nonneg h]

/-- `.abs` negates if negative -/
lemma Int64.abs_eq_neg' {x : Int64} (n : x < 0) : x.abs = -x := by
  simp only [abs_def, n, ↓reduceIte]

/-- `.uabs` negates if negative -/
lemma Int64.uabs_eq_neg' {x : Int64} (n : x < 0) : x.uabs = (-x).toUInt64 := by
  induction' x using Int64.induction_nat with k h
  simp only [uabs, to_omega, UInt64.eq_iff_toNat_eq, Int64.neg_natCast] at n ⊢
  split_ifs
  all_goals omega

/-- `.uabs` negates if negative -/
lemma Int64.uabs_eq_neg {x : Int64} (n : x < 0) : x.uabs.toInt = -x := by
  rw [coe_uabs, abs_of_neg (coe_lt_zero n)]

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

@[simp, to_omega] lemma Nat.toUInt64_toInt64 (n : ℕ) : n.toInt64.toUInt64 = .ofInt n := by
  simp only [toInt64, Int64.toUInt64_ofNat', UInt64.eq_iff_toNat_eq, UInt64.toNat_ofNat', reducePow,
    UInt64.toNat_ofInt]
  omega

/-- If we turn `uabs` back into an `Int64`, it's negative only at `.min` -/
lemma Int64.uabs_lt_zero {x : Int64} : (x.uabs.toInt64 : ℤ) < 0 ↔ x = .minValue := by
  induction' x using Int64.induction_nat with x h
  simp only [to_omega, Int64.uabs, Int.bmod]
  split_ifs
  all_goals omega

/-- `(-x).uabs = x.uabs` -/
@[simp] lemma Int64.uabs_neg {x : Int64} : (-x).uabs = x.uabs := by
  induction' x using Int64.induction_nat with x h
  simp only [to_omega, Int64.uabs]
  split_ifs
  all_goals omega

/-- `(-t).n.toNat = t` when converting negatives to `ℤ` -/
@[simp] lemma Int64.toNat_neg {x : Int64} (n : x < 0) : ((-x).toUInt64.toNat : ℤ) = -x := by
  induction' x using Int64.induction_nat with x h
  simp only [to_omega] at n ⊢
  omega

@[simp] lemma Int64.uabs_eq_pow_iff {x : Int64} : x.uabs = 2^63 ↔ x = minValue := by
  induction' x using Int64.induction_nat with x h
  simp only [to_omega, Int64.uabs]
  split_ifs
  all_goals omega

@[simp] lemma Int64.uabs_uabs {x : Int64} : x.uabs.toInt64.uabs = x.uabs := by
  induction' x using Int64.induction_nat with x h
  simp only [to_omega, Int64.uabs, Int.bmod]
  split_ifs
  all_goals omega

@[simp] lemma Int64.isNeg_uabs {x : Int64} (m : x ≠ minValue) : 0 ≤ x.uabs.toInt64 := by
  induction' x using Int64.induction_nat with x h
  simp only [to_omega, Int64.uabs, Int.bmod] at m ⊢
  split_ifs
  all_goals omega

/-!
### Left shift
-/

/-- Shifting left is shifting the inner `UInt64` left -/
instance : HShiftLeft Int64 UInt64 Int64 where
  hShiftLeft x s := (x.toUInt64 <<< s).toInt64

lemma Int64.shiftLeft_def (x : Int64) (s : UInt64) : x <<< s = (x.toUInt64 <<< s).toInt64 := rfl

/-- Shifting left is multiplying by a power of two, in nice cases -/
lemma Int64.coe_shiftLeft {x : Int64} {s : UInt64} (s64 : s.toNat < 64)
    (xs : x.uabs.toNat < 2 ^ (63 - s.toNat)) : ((x <<< s) : ℤ) = x * 2^s.toNat := by
  -- Reduce to a statement about bitvecs
  have p : (63 - s.toNat + s.toNat) ≤ 63 := by omega
  rw [BitVec.ofInt_inj_of_lt 64 (by norm_num)]
  rotate_left
  · simp only [Nat.add_one_sub_one, Int.reducePow, Int.reduceNeg]; exact pow_le_coe _
  · simp only [Nat.add_one_sub_one, Int.reducePow]; exact coe_lt_pow _
  · apply neg_le_of_abs_le
    simp only [toNat_uabs] at xs
    simp only [abs_mul, abs_pow, Nat.abs_ofNat, Nat.add_one_sub_one]
    suffices h : (x : ℤ).natAbs * 2 ^ s.toNat ≤ 2 ^ 63 by
      simpa [← Nat.cast_le (α := ℤ)] using h
    refine le_trans (Nat.mul_le_mul_right _ xs.le) ?_
    simp only [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) p
  · apply lt_of_abs_lt
    simp only [toNat_uabs] at xs
    simp only [abs_mul, abs_pow, Nat.abs_ofNat, Nat.add_one_sub_one]
    suffices h : (x : ℤ).natAbs * 2 ^ s.toNat < 2 ^ 63 by
      simpa [← Nat.cast_lt (α := ℤ)] using h
    refine lt_of_lt_of_le ((Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr xs) ?_
    simp only [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) p
  clear xs p
  -- Dispatch the bitvec statement
  induction' x using Int64.induction_bitvec with x
  induction' s using UInt64.induction_bitvec with s
  simp only [to_bitvec, Int64.shiftLeft_def]
  simp only [UInt64.toNat_ofBitVec, BitVec.shiftLeft_eq', BitVec.toNat_umod, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod] at s64 ⊢
  generalize s.toNat = s at s64
  interval_cases s
  all_goals {
    simp only [Nat.reduceMod, Int.reducePow, BitVec.ofInt_ofNat, BitVec.shiftLeft_eq_mul_twoPow]
    apply congr_arg₂ _ rfl
    fast_decide }

/-- `0 <<< s = 0` -/
@[simp] lemma Int64.zero_shiftLeft' (s : UInt64) : (0 : Int64) <<< s = 0 := by
  simp only [shiftLeft_def, n_zero, UInt64.zero_shiftLeft]
  rfl

/-!
### Right shift, rounding up or down
-/

/-- Shift right, rounding up or down -/
@[irreducible] def Int64.shiftRightRound (x : Int64) (s : UInt64) (up : Bool) : Int64 :=
  if x < 0 then
    -- We need arithmetic shifting, which is easiest to do by taking bitwise complement.
    -- However, this fails if `x = min`, so we handle that case separately.
    bif x == minValue then
      bif 64 ≤ s then bif up then 0 else -1
      else -UInt64.toInt64 (1 <<< (63 - s))
    else
      -UInt64.toInt64 ((-x).toUInt64.shiftRightRound s !up)
  else
    UInt64.toInt64 (x.toUInt64.shiftRightRound s up)

/-- `0.shiftRightRound = 0` -/
@[simp] lemma Int64.zero_shiftRightRound (s : UInt64) (up : Bool) :
    (0 : Int64).shiftRightRound s up = 0 := by
  rw [shiftRightRound]
  simp only [lt_self_iff_false, ↓reduceIte, n_zero, UInt64.zero_shiftRightRound, zero_undef]

/-- `Int64.isNeg` for powers of two -/
lemma Int64.isNeg_one_shift {s : UInt64} (s64 : s.toNat < 64) :
    UInt64.toInt64 (1 <<< s) < 0 ↔ s.toNat = 63 := by
  induction' s using UInt64.induction_nat with s h
  simp only [to_omega, Nat.mod_eq_of_lt h] at s64
  by_cases s63 : s = 63
  · simp only [s63, UInt64.reduceOfNat, UInt64.reduceToNat, iff_true]; rfl
  replace s63 : s < 63 := by omega
  have e : 1 % 2 ^ (64 - s) = 1 := by rw [Nat.mod_eq_of_lt]; exact Nat.one_lt_two_pow (by omega)
  have e' : (1 : ℤ) % 2 ^ (64 - s) = 1 := by
    rw [Int.emod_eq_of_lt (by norm_num)]
    exact one_lt_pow₀ (by norm_num) (by omega)
  simp only [to_omega, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt s64, e, e', _root_.one_mul,
    pow_lt_pow_right₀ (a := 2) (by norm_num) s63, s63.ne, ↓reduceIte, iff_false, not_lt,
    Nat.ofNat_nonneg, pow_nonneg]

/-- `ℤ` conversion for `UInt64` powers of two -/
lemma Int64.coe_one_shift {s : UInt64} (s63 : s.toNat < 63) :
    (UInt64.toInt64 (1 <<< s) : ℤ) = 2^s.toNat := by
  have s64 : s.toNat < 64 := by omega
  have e : (1 <<< s : UInt64).toNat = 2^s.toNat := by
    simp only [UInt64.toNat_shiftLeft', UInt64.toNat_one, Nat.mod_eq_of_lt s64, ne_eq,
      pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true, mul_eq_right₀]
    exact Nat.mod_eq_of_lt (one_lt_pow₀ (by norm_num) (by omega))
  simp only [toInt_eq_if, UInt64.toUInt64_toInt64, e, Nat.cast_pow, Nat.cast_ofNat,
    isNeg_one_shift s64, s63.ne, ↓reduceIte, CharP.cast_eq_zero, sub_zero]

/-- `ℤ` conversion for negated `Int64` powers of two -/
lemma Int64.coe_neg_one_shift {s : UInt64} (s63 : s.toNat < 63) :
    ((-UInt64.toInt64 (1 <<< s) : Int64) : ℤ) = -2^s.toNat := by
  rw [Int64.coe_neg, Int64.coe_one_shift s63]
  have p : 0 < (2 : ℤ) ^ s.toNat := pow_pos (by norm_num) _
  simp only [ite_eq_right_iff]
  omega

/-- Negated `ℤ` conversion for `UInt64` values -/
lemma Int64.coe_eq_toNat_of_lt {n : UInt64} (h : n.toNat < 2^63) :
    ((UInt64.toInt64 n : Int64) : ℤ) = n.toNat := by
  simpa only [toInt_eq_if, UInt64.toUInt64_toInt64, isNeg_eq_le, Nat.reducePow, UInt64.size_eq_pow,
    Nat.cast_ite, Nat.cast_ofNat, CharP.cast_eq_zero, sub_eq_self, ite_eq_right_iff,
    OfNat.ofNat_ne_zero, imp_false, not_le] using h

/-- Negated `ℤ` conversion for `UInt64` values -/
lemma Int64.coe_neg_eq_neg_toNat_of_lt {n : UInt64} (h : n.toNat < 2^63) :
    ((-UInt64.toInt64 n : Int64) : ℤ) = -n.toNat := by
  induction' n using UInt64.induction_nat with n _
  have e : (UInt64.ofNat n).toInt64 = Int64.ofNat n := rfl
  simp only [to_omega, e, Int.bmod] at h ⊢
  omega

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
    by_cases xm : x = .minValue
    · have me : ((.minValue : Int64) : ℤ) = -(2:ℤ)^63 := by decide
      simp only [xm, if_true, me]
      by_cases s64 : 64 ≤ s
      · simp only [s64, ite_true]
        simp only [UInt64.le_iff_toNat_le, e64] at s64
        induction up
        · simp only [ite_false, neg_neg, Bool.false_eq_true]
          rw [Int.ediv_eq_neg_one (by positivity)]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        · simp only [ite_true, neg_neg, zero_eq_neg]
          apply Int.ediv_eq_zero_of_lt (by positivity)
          exact pow_lt_pow_right₀ (by norm_num) (by omega)
      · simp only [s64, ite_false, neg_neg]
        simp only [UInt64.le_iff_toNat_le, e64, not_le] at s64
        have s63 : s.toNat ≤ 63 := by omega
        have es : (63 - s).toNat = 63 - s.toNat := by
          rw [UInt64.toNat_sub'', e63]
          simp only [UInt64.le_iff_toNat_le, e63]; omega
        by_cases s0 : s = 0
        · simp only [s0, UInt64.toNat_zero, pow_zero, Int.ediv_one, ite_self]; decide
        · simp only [UInt64.eq_iff_toNat_eq, UInt64.toNat_zero] at s0
          rw [Int64.coe_neg_one_shift, es]
          · simp only [Int.ediv_pow_of_le t0 s63, Int.neg_ediv_pow_of_le t0 s63, ite_self]
          · rw [es]; omega
    · simp only [xm, ite_false]
      have xnn : ¬-x < 0 := by
        rw [← Int64.coe_lt_coe, coe_neg, ← coe_min']
        split_ifs with h
        · rw [coe_eq_coe] at h; trivial
        · simp only [coe_neg_iff, coe_zero, Int.neg_neg_iff_pos, coe_pos_iff, not_lt] at x0 ⊢
          exact x0.le
      have ult : ((-x).toUInt64.shiftRightRound s !up).toNat < 2 ^ 63 := by
        rw [isNeg_eq_le, not_le] at xnn
        exact lt_of_le_of_lt UInt64.shiftRightRound_le_self xnn
      rw [coe_neg_eq_neg_toNat_of_lt ult, UInt64.toNat_shiftRightRound']
      induction up
      · simp only [Bool.not_false, ite_true, Int.cast_neg_ceilDiv_eq_ediv, Nat.cast_pow,
          Nat.cast_ofNat]
        refine congr_arg₂ _ ?_ rfl
        rw [← coe_of_nonneg, coe_neg' xm, neg_neg]
        simp only [not_lt.mp xnn]
      · simp only [Bool.not_true, ite_false, Int.natCast_ediv, Nat.cast_pow, Nat.cast_ofNat,
          ite_true, neg_inj, Bool.false_eq_true]
        rw [← coe_of_nonneg, coe_neg' xm]
        simp only [not_lt.mp xnn]
  · simp only [x0, ite_false]
    have xn : ¬x < 0 := by
      rw [←Int64.coe_lt_coe, coe_zero]
      linarith
    have xsn : ¬(UInt64.shiftRightRound x.toUInt64 s up).toInt64 < 0 := by
      simp only [isNeg_eq_le, Nat.reducePow, not_le] at xn ⊢
      exact lt_of_le_of_lt (UInt64.shiftRightRound_le_self) xn
    rw [coe_of_nonneg (not_lt.mp xsn), UInt64.toUInt64_toInt64, UInt64.toNat_shiftRightRound']
    induction up
    · simp only [ite_false, Int.natCast_ediv, Nat.cast_pow, Nat.cast_ofNat,
        coe_of_nonneg (not_lt.mp xn), Bool.false_eq_true]
    · simp only [ite_true, Int.cast_ceilDiv_eq_neg_ediv, Nat.cast_pow, Nat.cast_ofNat,
        coe_of_nonneg (not_lt.mp xn)]

/-- `Int64.shiftRightRound` reduces `abs` -/
lemma Int64.abs_shiftRightRound_le (x : Int64) (s : UInt64) (up : Bool) :
    |(x.shiftRightRound s up : ℤ)| ≤ |(x : ℤ)| := by
  simp only [coe_shiftRightRound, Int.abs_rdiv_le]

/-- `Int64.shiftRightRound` never produces `min` from scratch -/
lemma Int64.shiftRightRound_ne_min {x : Int64} (n : x ≠ minValue) (s : UInt64) (up : Bool) :
    x.shiftRightRound s up ≠ minValue := by
  contrapose n
  simp only [ne_eq, Decidable.not_not] at n ⊢
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
  · simp only [neg, ↓reduceIte, Nat.floor_int]
    simp only at neg
    simp only [coe_of_nonneg (not_lt.mp neg), Int.toNat_natCast]
