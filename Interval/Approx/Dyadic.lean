import Interval.Approx.Div2
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Cases

/-!
# Dyadic rationals approximate any field

We want to do power series computations over `Dyadic`, where these approximate `ℂ` as a ring.
This works because our `spray` series functions uses only ring operation and `div2` on scalars.
-/

variable {𝕜 : Type}
variable {x y : Dyadic} {x' y' : 𝕜} {s : ℤ} {n : ℕ}

/-!
### Nice printing for dyadic rationals, using binary scientific notation
-/

instance : Repr Dyadic where
  reprPrec x _ := match x with
  | .zero => "0"
  | .ofOdd n 0 _ => toString n
  | .ofOdd n s _ => toString n ++ "p" ++ toString (-s)

/-!
### Dyadic rational basics
-/

instance : Div2 Dyadic where
  div2 x := x >>> 1

instance : Div2Zero Dyadic where
  div2_zero := rfl

lemma Dyadic.natCast_zero : (0 : ℕ) = (0 : Dyadic) := rfl
lemma Dyadic.intCast_zero : (0 : ℤ) = (0 : Dyadic) := rfl
lemma Dyadic.intCast_one : (1 : ℤ) = (1 : Dyadic) := rfl
@[simp] lemma Dyadic.toRat_one : (1 : Dyadic).toRat = 1 := rfl
@[simp] lemma Dyadic.toRat_zero' : zero.toRat = 0 := rfl

@[simp] lemma Dyadic.toRat_shiftRightInt : (x >>> s).toRat = x.toRat / 2 ^ s := by
  induction' x with x t xo
  · simp only [instHShiftRightInt, Dyadic.shiftRight, toRat_zero', zero_div]
  · have two : (2 : ℚ) ≠ 0 := by norm_num
    simp only [instHShiftRightInt, Dyadic.shiftRight, toRat_ofOdd_eq_mkRat, neg_add_rev,
      Int.shiftLeft_eq, Nat.shiftLeft_eq, _root_.one_mul, Rat.mkRat_eq_div, Int.cast_mul,
      Int.cast_pow, Int.cast_ofNat, ← zpow_natCast, Int.ofNat_toNat, Nat.cast_pow, Nat.cast_ofNat,
      mul_div_assoc, ← zpow_sub₀ two, mul_eq_mul_left_iff, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one,
      not_false_eq_true, zpow_right_inj₀, Int.cast_eq_zero]
    omega

@[simp] lemma Dyadic.shiftRight_natCast : x >>> (n : ℤ) = x >>> n := rfl

@[simp] lemma Dyadic.toRat_shiftRightNat : (x >>> n).toRat = x.toRat / 2 ^ n := by
  simp only [← shiftRight_natCast, toRat_shiftRightInt, zpow_natCast]

@[simp] lemma Dyadic.toRat_div2 : (div2 x).toRat = div2 x.toRat := by
  simp only [div2, toRat_shiftRightNat, pow_one, div_eq_inv_mul, smul_eq_mul]

lemma Dyadic.intCast_add (a b : ℤ) : (a + b : ℤ) = (a + b : Dyadic) := by
  simp only [← toRat_inj, toRat_intCast, Int.cast_add, toRat_add]

lemma Dyadic.intCast_add_one : (s + 1 : ℤ) = (s + 1 : Dyadic) := by
  simp only [intCast_add, intCast_one]

lemma Dyadic.natCast_succ (n : ℕ) : (n + 1 : ℕ) = (n + 1 : Dyadic) := by
  simp only [← toRat_inj, toRat_natCast, Nat.cast_add, Nat.cast_one, toRat_add, toRat_one]

lemma Dyadic.intCast_neg (n : ℤ) : (-n : ℤ) = (-n : Dyadic) := by
  trans .ofInt (-n)
  · rfl
  · simp only [ofInt, ← Dyadic.neg_ofIntWithPrec]
    rfl

lemma Dyadic.neg_add (x y : Dyadic) : -(x + y) = -x + -y := by
  simp only [← toRat_inj, toRat_neg, toRat_add, neg_add_rev]
  ring

instance : CommRing Dyadic where
  add_assoc := Dyadic.add_assoc
  zero_add := Dyadic.zero_add
  add_zero := Dyadic.add_zero
  add_comm := Dyadic.add_comm
  left_distrib := Dyadic.mul_add
  right_distrib := Dyadic.add_mul
  zero_mul := Dyadic.zero_mul
  mul_zero := Dyadic.mul_zero
  mul_assoc := Dyadic.mul_assoc
  one_mul := Dyadic.one_mul
  mul_one := Dyadic.mul_one
  mul_comm := Dyadic.mul_comm
  neg_add_cancel := Dyadic.neg_add_cancel
  natCast_succ := Dyadic.natCast_succ
  nsmul n x := n * x
  nsmul_zero x := by rw [Dyadic.natCast_zero, Dyadic.zero_mul]
  nsmul_succ n x := by simp only [Dyadic.natCast_succ, Dyadic.add_mul, Dyadic.one_mul]
  zsmul n x := n * x
  zsmul_zero' x := by rw [Dyadic.intCast_zero, Dyadic.zero_mul]
  zsmul_succ' n x := by simp [Dyadic.intCast_add_one, Dyadic.add_mul, Dyadic.one_mul]
  zsmul_neg' n x := by
    simp only [Int.negSucc_eq, neg_add_rev, Int.reduceNeg, add_comm, Dyadic.intCast_add,
      Dyadic.intCast_neg, Dyadic.intCast_one, Dyadic.add_mul, Dyadic.neg_mul, Dyadic.one_mul,
      Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Dyadic.neg_add]
  intCast_negSucc n := by
    simp only [Dyadic.instIntCast, Int.negSucc_eq, neg_add, Dyadic.intCast_add, Dyadic.natCast_succ,
      Dyadic.neg_add, Dyadic.intCast_neg, Dyadic.intCast_one]
    rfl
  npow n x := x.pow n
  npow_zero x := Dyadic.pow_zero _
  npow_succ x n := Dyadic.pow_succ _ _

@[simp] lemma Dyadic.monoidPow_eq_instPowNat : Monoid.toNatPow = instPowNat := rfl

@[simp] lemma Dyadic.toRat_nonneg (x : Dyadic) : 0 ≤ x.toRat ↔ 0 ≤ x := by
  rw [← Dyadic.toRat_zero, Dyadic.toRat_le_toRat_iff]

@[bound] alias ⟨_, Bound.dyadic_toRat_nonneg⟩ := Dyadic.toRat_nonneg

@[bound] alias ⟨_, Bound.ratCast_nonneg⟩ := Rat.cast_nonneg

@[bound] lemma Dyadic.div2_nonneg (x : Dyadic) (x0 : 0 ≤ x) : 0 ≤ div2 x := by
  simp only [← Dyadic.toRat_le_toRat_iff, Dyadic.toRat_div2, Dyadic.toRat_zero, div2_eq_mul]
  bound

/-!
### Dyadic rationals approximate any field
-/

instance Dyadic.instApproxRing [Field 𝕜] : Approx Dyadic 𝕜 where approx x x' := x.toRat = x'
lemma Dyadic.approx [Field 𝕜] : approx x x' ↔ x.toRat = x' := by rfl

variable [Field 𝕜] [CharZero 𝕜]

instance : ApproxZero Dyadic 𝕜 where approx_zero := by simp [approx]
instance : ApproxZeroIff Dyadic 𝕜 where approx_zero_imp x a := by simpa using a.symm
instance : ApproxOne Dyadic 𝕜 where approx_one := by simp [approx]
instance : ApproxNeg Dyadic 𝕜 where approx_neg := by simp [approx]
instance : ApproxAdd Dyadic 𝕜 where approx_add := by simp [approx]
instance : ApproxSub Dyadic 𝕜 where approx_sub := by simp [approx]
instance : ApproxMul Dyadic 𝕜 where approx_mul := by simp [approx]
instance : ApproxNatCast Dyadic 𝕜 where approx_natCast := by simp [approx]
instance : ApproxIntCast Dyadic 𝕜 where approx_intCast := by simp [approx]
instance : ApproxDiv2 Dyadic 𝕜 where approx_div2 := by simp [approx, div2_eq_mul]
