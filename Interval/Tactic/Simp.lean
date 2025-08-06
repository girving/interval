import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Size
import Interval.Tactic.Init

/-!
# Initial simp sets

We add various mathlib lemmas to the simp sets defined in `Interval.Tactic.Init`.
-/

attribute [to_if, to_bitvec, to_omega] Bool.not_not Bool.or_eq_true beq_iff_eq Bool.and_eq_true
  Bool.not_eq_eq_eq_not Bool.not_true bne_iff_ne decide_eq_true_iff ne_eq and_false one_ne_zero

attribute [to_bitvec] NatCast.natCast UInt64.ofNat UInt64.eq_iff_toBitVec_eq BitVec.ofNat_add
  UInt64.ofInt Int64.toUInt64_add UInt64.toBitVec_add Int64.toBitVec_toUInt64 Int64.toBitVec_ofNat
  BitVec.ofNat_eq_ofNat Int64.toBitVec_ofInt IntCast.intCast BitVec.toNat_intCast BitVec.ofInt_neg
  BitVec.ofInt_add BitVec.reduceOfInt Int64.toBitVec_neg BitVec.ofInt_natCast neg_add_rev
  BitVec.reduceNeg Nat.cast_add BitVec.natCast_eq_ofNat Nat.cast_one BitVec.ofNat_eq_ofNat
  Int64.lt_iff_toBitVec_slt UInt64.toBitVec_toInt64 Int64.le_iff_toBitVec_sle
  BitVec.ofInt_int64ToInt BitVec.ofInt_mul Int64.toUInt64_ofBitVec  UInt64.toBitVec_shiftLeft
  Int64.toBitVec_ofBitVec UInt64.lt_iff_toBitVec_lt UInt64.toBitVec_ofNat Int64.toInt64_toUInt64
  UInt64.toInt64_ofNat UInt64.toBitVec_shiftRight UInt64.toBitVec_shiftLeft UInt64.toBitVec_sub
  UInt64.le_iff_toBitVec_le UInt64.add_zero UInt64.toNat_zero UInt64.toBitVec_neg

attribute [to_omega] BitVec.toInt_ofNat BitVec.msb_eq_toNat BitVec.toInt_ofNat' BitVec.toInt_neg
  BitVec.toNat_eq BitVec.toNat_intMin BitVec.toNat_ofNat BitVec.toInt_neg CharP.cast_eq_zero
  Int.zero_bmod UInt64.toNat_neg UInt64.size UInt64.toNat_ofNat Int64.toInt_ofNat
  Int64.eq_iff_toBitVec_eq Int64.toBitVec_minValue Int64.toUInt64_ofNat Int64.lt_iff_toInt_lt
  Int64.lt_iff_toBitVec_slt Int64.size Nat.shiftLeft_eq_mul_pow Nat.add_eq_zero UInt64.add_zero
  UInt64.toNat_zero Nat.zero_mod UInt64.le_iff_toNat_le UInt64.lt_iff_toNat_lt
  Int64.le_iff_toInt_le UInt64.toNat_sub

-- `apply_ite` lemmas
@[to_omega] lemma UInt64.apply_ite_toNat (c : Prop) {d : Decidable c} (x y : UInt64) :
    (if c then x else y).toNat = if c then x.toNat else y.toNat := by apply apply_ite
@[to_omega, to_bitvec] lemma UInt64.apply_ite_toBitVec (c : Prop) {d : Decidable c} (x y : UInt64) :
    (if c then x else y).toBitVec = if c then x.toBitVec else y.toBitVec := by apply apply_ite
@[to_omega, to_bitvec] lemma UInt64.apply_ite_toInt64 (c : Prop) {d : Decidable c} (x y : UInt64) :
    (if c then x else y).toInt64 = if c then x.toInt64 else y.toInt64 := by apply apply_ite
@[to_omega, to_bitvec] lemma Int64.apply_ite_toBitVec (c : Prop) {d : Decidable c} (x y : Int64) :
    (if c then x else y).toBitVec = if c then x.toBitVec else y.toBitVec := by apply apply_ite
@[to_omega] lemma BitVec.apply_ite_toInt (c : Prop) {d : Decidable c} (x y : BitVec 64) :
    (if c then x else y).toInt = if c then x.toInt else y.toInt := by apply apply_ite
@[to_omega] lemma BitVec.apply_ite_toNat (c : Prop) {d : Decidable c} (x y : BitVec 64) :
    (if c then x else y).toNat = if c then x.toNat else y.toNat := by apply apply_ite
@[to_omega] lemma Int.apply_ite_toNat (c : Prop) {d : Decidable c} (x y : ℤ) :
    (if c then x else y).toNat = if c then x.toNat else y.toNat := by apply apply_ite
@[to_omega] lemma BitVec.toNat_natCast (n : ℕ) : (n : BitVec 64).toNat = n % 2^64 :=
  BitVec.toNat_ofNat _ _
@[to_omega] lemma BitVec.neg_eq_op {n : BitVec 64} : n.neg = -n := rfl

lemma BitVec.ofInt_inj_of_lt (n : ℕ) {x y : ℤ} (n0 : 0 < n)
    (x0 : -2^(n-1) ≤ x) (x1 : x < 2^(n-1)) (y0 : -2^(n-1) ≤ y) (y1 : y < 2^(n-1)) :
    x = y ↔ BitVec.ofInt n x = BitVec.ofInt n y := by
  rw [← BitVec.toInt_inj, BitVec.toInt_ofInt_eq_self n0 x0 x1, BitVec.toInt_ofInt_eq_self n0 y0 y1]
