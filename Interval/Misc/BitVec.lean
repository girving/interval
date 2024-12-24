import Mathlib.Data.BitVec

/-!
## `BitVec` facts
-/

variable {n : ℕ} {i : ℤ}

@[simp] lemma BitVec.toNat_zero : (0 : BitVec n).toNat = 0 := rfl

lemma BitVec.toNat_intCast : (i : BitVec n).toNat = (i % (2 ^ n : ℕ)).toNat := rfl
