module

public import Interval.Approx.Div2

/-!
# Rationals approximate any field

We want to do power series computations over `ℚ`, where these approximate `ℂ` via field structure.
This works because our `spray` series functions uses only field operations on scalars.
-/

@[expose] public section

variable {𝕜 : Type}

instance Rat.instApproxField [Field 𝕜] : Approx ℚ 𝕜 where approx x x' := x = x'
lemma Rat.approx [Field 𝕜] {x : ℚ} {x' : 𝕜} : approx x x' ↔ x = x' := by rfl

section Field
variable [Field 𝕜] [CharZero 𝕜]

instance : ApproxZero ℚ 𝕜 where approx_zero := by simp [approx]
instance : ApproxZeroIff ℚ 𝕜 where approx_zero_imp x a := by simpa using a.symm
instance : ApproxOne ℚ 𝕜 where approx_one := by simp [approx]
instance : ApproxNeg ℚ 𝕜 where approx_neg := by simp [approx]
instance : ApproxAdd ℚ 𝕜 where approx_add := by simp [approx]
instance : ApproxSub ℚ 𝕜 where approx_sub := by simp [approx]
instance : ApproxMul ℚ 𝕜 where approx_mul := by simp [approx]
instance : ApproxInv ℚ 𝕜 where approx_inv := by simp [approx]
instance : ApproxDiv ℚ 𝕜 where approx_div := by simp [approx]
instance : ApproxSMul ℚ 𝕜 𝕜 𝕜 where approx_smul := by simp [approx, Rat.smul_def]; aesop
instance : ApproxNatCast ℚ 𝕜 where approx_natCast := by simp [approx]
instance : ApproxIntCast ℚ 𝕜 where approx_intCast := by simp [approx]
instance : ApproxRatCast ℚ 𝕜 where approx_ratCast := by simp [approx]
instance : ApproxDiv2 ℚ 𝕜 where approx_div2 := by simp [approx, div2_eq_mul]
