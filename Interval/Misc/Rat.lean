module

public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Basic.Real.Basic
public import Interval.Misc.Bool
public import Interval.Misc.Nat
public import Interval.Misc.Real

/-!
## `ℚ` machinery
-/

@[expose] public section

open Set
variable {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

lemma Rat.abs_eq_div {x : ℚ} : |x| = (x.num.natAbs : ℚ) / x.den := by
  nth_rw 1 [←Rat.num_div_den x]
  have d0 : 0 < (x.den : ℚ) := Nat.cast_pos.mpr x.den_pos
  rw [abs_div, abs_of_pos d0, ←Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

lemma Rat.abs_eq_div' {x : ℚ} : (|x| : 𝕜) = (x.num.natAbs : 𝕜) / x.den := by
  nth_rw 1 [←Rat.num_div_den x]
  have d0 : 0 < (x.den : 𝕜) := Nat.cast_pos.mpr x.den_pos
  simp only [cast_div, cast_intCast, cast_natCast, abs_div, abs_of_pos d0, ←Int.cast_abs,
    Int.abs_eq_natAbs, Int.cast_natCast]

/-- `n` s.t. `2^n ≤ |x| < 2^(n+1)` if `n ≠ 0` -/
@[irreducible] def Rat.log2 (x : ℚ) : ℤ :=
  -- Reduce to two possible answers
  let n := x.num.natAbs
  let a := n.log2  -- `2^a ≤ n < 2^(a+1)`
  let b := x.den.log2  -- `2^b ≤ d < 2^(b+1)`
  -- `2^(a-b-1) < n/d < 2^(a+1-b)`, so the answer is either `a-b-1` or `a-b`
  -- If `2^(a-b) ≤ n/d` then `a-b`, otherwise `a-b-1`
  let g : ℤ := a - b
  let good := bif 0 ≤ g then decide (x.den <<< g.toNat ≤ n) else decide (x.den ≤ n <<< (-g).toNat)
  bif good then g else g - 1

lemma Rat.log2_correct {x : ℚ} (x0 : x ≠ 0) : |x| ∈ Ico (2^x.log2) (2^(x.log2 + 1)) := by
  have t0 : (2:ℚ) ≠ 0 := by norm_num
  rw [log2]
  simp only [sub_nonneg, Nat.cast_le, neg_sub, bif_eq_if, decide_eq_true_eq, Nat.shiftLeft_eq]
  generalize hn : x.num.natAbs = n
  generalize ha : n.log2 = a
  generalize hb : x.den.log2 = b
  have n0 : n ≠ 0 := by rwa [←hn, Int.natAbs_ne_zero, Rat.num_ne_zero]
  have d0' : 0 < (x.den : ℚ) := Nat.cast_pos.mpr x.den_pos
  have an := Nat.log2_self_le n0
  have bd := Nat.log2_self_le x.den_nz
  have na := Nat.lt_log2_self (n := n)
  have db := Nat.lt_log2_self (n := x.den)
  simp only [ha, hb] at an bd na db
  have ae : |x| = (n : ℚ) / x.den := by rw [Rat.abs_eq_div, hn]
  have lo : 2^(a - b - 1 : ℤ) ≤ |x| := by
    rw [ae]
    refine le_trans ?_ (div_le_div₀ (by positivity) (Nat.cast_le.mpr an) (by positivity)
      (Nat.cast_le.mpr db.le))
    simp only [sub_sub, zpow_sub₀ t0, zpow_natCast, Nat.cast_pow, Nat.cast_ofNat,
      ← Nat.cast_add_one, le_refl]
  have hi : |x| < 2^(a - b + 1 : ℤ) := by
    rw [ae]
    refine lt_of_lt_of_le ((div_lt_div_iff_of_pos_right d0').mpr (Nat.cast_lt.mpr na)) ?_
    refine le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (Nat.cast_le.mpr bd)) ?_
    simp only [Nat.cast_pow, Nat.cast_ofNat, ← add_sub_right_comm, zpow_sub₀ t0, zpow_natCast,
      ← Nat.cast_add_one, le_refl]
  simp only [← Nat.cast_le (α := ℚ), ← ae, mem_Ico, apply_ite (fun n : ℤ ↦ (2 : ℚ) ^ n),
    apply_ite (fun y : ℚ ↦ y ≤ |x|), apply_ite (fun y : ℚ ↦ |x| < y), apply_ite (fun n : ℤ ↦ n + 1),
    Nat.cast_mul, Nat.cast_pow, Nat.cast_two, mul_comm (x.den : ℚ), ← le_div_iff₀ d0', lo, hi,
    sub_add_cancel]
  by_cases ba : b ≤ a
  · simp only [Nat.cast_le, ba, ite_true, decide_eq_true_eq, ← Nat.cast_sub ba, Int.toNat_natCast,
    zpow_natCast]
    split_ifs with h
    · simp only [h, and_self]
    · simp only [not_le.mp h, and_self]
  · have ab : a ≤ b := (not_le.mp ba).le
    have e : (a : ℤ) - (b : ℤ) = -((b - a : ℕ) : ℤ) := by simp only [Nat.cast_sub ab, neg_sub]
    simp [Nat.cast_le, ba, ↓reduceIte, ← Nat.cast_sub ab, mul_comm _ ((2 : ℚ) ^ _),
      decide_eq_true_eq, e, zpow_neg, zpow_natCast, ae, not_le,
      inv_le_iff_one_le_mul₀ (two_pow_pos (R := ℚ)), ← mul_div_assoc, one_le_div d0',
      div_lt_iff₀ d0', ← div_eq_inv_mul, lt_div_iff₀ (two_pow_pos (R := ℚ)), ite_true_left, and_self]

lemma Rat.log2_self_le {x : ℚ} (x0 : x ≠ 0) : 2 ^ x.log2 ≤ |x| := (Rat.log2_correct x0).1

lemma Rat.lt_log2_self {x : ℚ} : |x| < 2 ^ (x.log2 + 1) := by
  by_cases x0 : x = 0
  · simp only [x0, abs_zero, two_zpow_pos]
  · exact (Rat.log2_correct x0).2
