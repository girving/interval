module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Ring
public import Interval.Misc.Nat

/-!
## `ℤ` facts
-/

@[expose] public section

/-- `Int` division, rounding up or down -/
def Int.rdiv (a : ℤ) (b : ℕ) (up : Bool) : ℤ :=
  bif up then -(-a / b) else a / b

/-- `0 ≤ rdiv a _ _` if `0 ≤ a` -/
lemma Int.rdiv_nonneg {a : ℤ} {b : ℕ} {up : Bool} (a0 : 0 ≤ a) : 0 ≤ a.rdiv b up := by
  simp only [Int.rdiv]
  induction up
  · simp only [Bool.cond_false, Int.ediv_nonneg a0 (Nat.cast_nonneg _)]
  · simp only [Bool.cond_true, Left.nonneg_neg_iff]
    by_cases b0 : b = 0
    · simp only [b0, Nat.cast_zero, Int.ediv_zero, le_refl]
    · apply Int.ediv_le_of_le_mul
      · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero b0)
      · simpa only [zero_mul, Left.neg_nonpos_iff]

/-- `rdiv` rounds down if desired -/
lemma Int.rdiv_le {a : ℤ} {b : ℕ} : (a.rdiv b false : ℝ) ≤ a / b := by
  simp only [rdiv, Bool.cond_false]
  by_cases b0 : b = 0
  · simp only [b0, Nat.cast_zero, Int.ediv_zero, cast_zero, div_zero, le_refl]
  · rw [le_div_iff₀]
    · have e : (b : ℝ) = (b : ℤ) := rfl
      rw [e, ←Int.cast_mul, Int.cast_le]
      exact Int.ediv_mul_le _ (Nat.cast_ne_zero.mpr b0)
    · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero b0)

/-- `rdiv` rounds up if desired -/
lemma Int.le_rdiv {a : ℤ} {b : ℕ} : (a / b : ℝ) ≤ a.rdiv b true := by
  simp only [rdiv, Bool.cond_true, cast_neg]
  by_cases b0 : b = 0
  · simp only [b0, Nat.cast_zero, div_zero, Int.ediv_zero, cast_zero, neg_zero, le_refl]
  · rw [le_neg, ←neg_div, ←Int.cast_neg]
    generalize -a = a
    rw [le_div_iff₀]
    · have e : (b : ℝ) = (b : ℤ) := rfl
      rw [e, ←Int.cast_mul, Int.cast_le]
      exact Int.ediv_mul_le _ (Nat.cast_ne_zero.mpr b0)
    · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero b0)

lemma Int.rdiv_le_rdiv {a : ℤ} {b : ℕ} {u0 u1 : Bool} (u01 : u0 ≤ u1) :
    a.rdiv b u0 ≤ a.rdiv b u1 := by
  induction u0
  · induction u1
    · rfl
    · rw [←Int.cast_le (R := ℝ)]
      exact le_trans Int.rdiv_le Int.le_rdiv
  · simp only [Bool.eq_true_of_true_le u01, le_refl]

@[simp] lemma Int.zero_rdiv {b : ℕ} {up : Bool} : (0 : ℤ).rdiv b up = 0 := by
  induction up; repeat simp only [rdiv, neg_zero, zero_ediv, Bool.cond_self]

/-- `rdiv` by 1 does nothing -/
@[simp] lemma Int.rdiv_one {a : ℤ} {up : Bool} : a.rdiv 1 up = a := by
  induction up; repeat simp only [rdiv, Nat.cast_one, ediv_one, neg_neg, Bool.cond_self]

/-- `rdiv` never rounds up by much -/
lemma Int.rdiv_lt {a : ℤ} {b : ℕ} {up : Bool} : (a.rdiv b up : ℝ) < a / b + 1 := by
  by_cases b0 : b = 0
  · simp only [rdiv, b0, Nat.cast_zero, Int.ediv_zero, neg_zero, Bool.cond_self, cast_zero,
      div_zero, zero_add, zero_lt_one]
  refine lt_of_le_of_lt (Int.cast_le.mpr (Int.rdiv_le_rdiv (Bool.le_true up))) ?_
  simp only [rdiv, Bool.cond_true, cast_neg]
  rw [neg_lt, neg_add, ←lt_sub_iff_add_lt, sub_neg_eq_add]
  have bp : 0 < (b : ℝ) := by positivity
  have e : (((-a / b : ℤ) : ℝ) + 1) * b = ((-a / b + 1) * b : ℤ) := by
    simp only [cast_mul, cast_add, cast_one, cast_natCast]
  rw [←mul_lt_mul_iff_of_pos_right bp, e, neg_mul, div_mul_cancel₀ _ bp.ne', ←Int.cast_neg,
    Int.cast_lt]
  apply Int.lt_ediv_add_one_mul_self
  positivity

/-- `rdiv` reduces `abs` -/
lemma Int.abs_rdiv_le (x : Int) (y : ℕ) (up : Bool) : |(x.rdiv y up : ℤ)| ≤ |(x : ℤ)| := by
  simp only [Int.rdiv]
  induction up
  · simp only [Bool.cond_false]
    apply Int.abs_ediv_le_abs
  · simp only [Bool.cond_true, _root_.abs_neg]
    refine le_trans (Int.abs_ediv_le_abs _ _) ?_
    simp only [_root_.abs_neg, le_refl]

/-- `a.rdiv (b / c)` = `(a * c).rdiv b` if `c | b` -/
lemma Int.rdiv_div {a : ℤ} {b c : ℕ} (bc : c ∣ b) : a.rdiv (b / c) = (a * c).rdiv b := by
  ext up
  by_cases c0 : c = 0
  · induction up; repeat simp [c0, rdiv]
  have cp := Nat.pos_iff_ne_zero.mpr c0
  rcases dvd_def.mp bc with ⟨k, e⟩
  simp only [e, Nat.mul_div_cancel_left _ cp]
  induction up
  repeat simp only [rdiv, Bool.cond_false, Bool.cond_true, Nat.cast_mul, mul_comm (c : ℤ), ← neg_mul,
    Int.mul_ediv_mul_of_pos_left _ _ (Nat.cast_pos.mpr cp)]

@[simp] lemma Int.mul_rdiv_cancel {a : ℤ} {b : ℕ} (b0 : b ≠ 0) {up : Bool} :
    (a * b).rdiv b up = a := by
  induction up
  repeat simp only [rdiv, ne_eq, Nat.cast_eq_zero, b0, not_false_eq_true, mul_ediv_cancel,
    Bool.cond_false, Bool.cond_true, ←neg_mul, neg_neg]

/-- `Int.ediv (-small) big = -1` -/
lemma Int.ediv_eq_neg_one {a b : ℤ} (a0 : 0 < a) (ab : a ≤ b) : -a / b = -1 := by
  refine Eq.trans (Int.ediv_of_neg_of_pos (by omega) (by omega)) ?_
  simp only [neg_neg, neg_add_rev, add_eq_left, neg_eq_zero]
  exact Int.ediv_eq_zero_of_lt (by omega) (by omega)

/-- A sufficient condition for `Int.ediv = -1` -/
lemma Int.ediv_eq_neg_one' {a b : ℤ} (a0 : a < 0) (b0 : 0 < b) (ab : -a < b) : a / b = -1 := by
  generalize hc : a + b = c
  have ca : a = c + (-1) * b := by rw [←hc]; ring
  rw [ca, Int.add_mul_ediv_right _ _ b0.ne', add_eq_right]
  apply Int.ediv_eq_zero_of_lt
  repeat { rw [←hc]; omega }

/-- `-(-a / b)` rounds up if we don't divide -/
lemma Int.neg_ediv_neg {a b : ℤ} (b0 : 0 < b) (ab : ¬b ∣ a) : -(-a / b) = a / b + 1 := by
  rw [←Int.mul_ediv_add_emod a b]
  generalize a / b = x
  generalize hy : a % b = y
  have y0 : 0 < y := by
    rw [←hy]
    rcases emod_pos_of_not_dvd ab with h | h
    · simp only [h, lt_self_iff_false] at b0
    · exact h
  have yb : y < b := by
    rw [← hy]
    convert emod_lt a b0.ne'
    rw [Nat.cast_natAbs, abs_of_pos b0, cast_id]
  have e0 : -(b * x + y) = -y + (-x) * b := by ring
  have e1 : (b * x + y) = y + (x) * b := by ring
  rw [e0, e1]
  simp only [Int.add_mul_ediv_right _ _ b0.ne', ediv_eq_zero_of_lt y0.le yb]
  rw [ediv_eq_neg_one y0 yb.le]
  ring

/-- `a ^ n / a ^ k = a ^ (n - k)` if `k ≤ n` -/
lemma Int.ediv_pow_of_le {a : ℤ} {n k : ℕ} (a0 : a ≠ 0) (kn : k ≤ n) :
    a ^ n / a ^ k = a ^ (n - k) := by
  rw [←Int.cast_inj (α := ℝ), Int.cast_div]
  · simp only [cast_pow]
    rw [pow_sub₀ _ (Int.cast_ne_zero.mpr a0) kn, div_eq_mul_inv]
  · exact pow_dvd_pow _ kn
  · positivity

/-- `-a ^ n / a ^ k = -a ^ (n - k)` if `k ≤ n` -/
lemma Int.neg_ediv_pow_of_le {a : ℤ} {n k : ℕ} (a0 : a ≠ 0) (kn : k ≤ n) :
    -a ^ n / a ^ k = -a ^ (n - k) := by
  rw [Int.neg_ediv_of_dvd, Int.ediv_pow_of_le a0 kn]
  exact pow_dvd_pow _ kn

/-- `ℕ`'s `-ceilDiv` in terms of `Int.ediv` -/
lemma Int.cast_neg_ceilDiv_eq_ediv (a b : ℕ) : -((a ⌈/⌉ b : ℕ) : ℤ) = (-a) / b := by
  simp only [Nat.ceilDiv_eq_add_pred_div, natCast_ediv]
  by_cases b0 : b = 0
  · simp only [b0, add_zero, Nat.cast_zero, Int.ediv_zero, neg_zero]
  have b0' : (b : ℤ) ≠ 0 := by omega
  have b1 : 1 ≤ b := by omega
  rw [←Nat.div_add_mod a b]
  generalize a / b = x
  generalize hy : a % b = y
  have yb : y < b := by rw [←hy]; exact Nat.mod_lt a b1
  rw [mul_comm b]
  by_cases y0 : y = 0
  · simp only [y0, add_zero, Nat.cast_mul, ←Int.neg_mul, Nat.add_sub_assoc b1,
      Int.mul_ediv_cancel _ b0', Nat.cast_add, Nat.cast_mul, neg_inj]
    rw [add_comm, Int.add_mul_ediv_right, add_eq_right]
    · apply Int.ediv_eq_zero_of_lt; omega; omega
    · omega
  · have y1 : 1 ≤ y := by omega
    have e : x * b + y + b - 1 = (x + 1) * b + (y - 1) := by
      rw [Nat.add_assoc, Nat.add_comm y b, ←Nat.add_assoc, ←add_one_mul, ←Nat.add_sub_assoc y1]
    simp only [e, Nat.cast_add, Nat.cast_mul, Nat.cast_one, neg_add_rev, ←neg_mul,
      add_comm ((↑x + 1) * ↑b), Int.add_mul_ediv_right _ _ b0']
    have yb0 : ((y - 1 : ℕ) : ℤ) / b = 0 := by
      rw [Int.ediv_eq_zero_of_lt (by omega)]
      omega
    have yb1 : -(y : ℤ) / b = -1 := by
      have e : -(y : ℤ) = ((b - y) + -1 * b) := by ring_nf
      rw [e, Int.add_mul_ediv_right _ _ b0', Int.ediv_eq_zero_of_lt (by omega) (by omega)]
      norm_num
    simp only [yb0, yb1]
    ring_nf

/-- `ℕ`'s `ceilDiv` in terms of `Int.ediv` -/
lemma Int.cast_ceilDiv_eq_neg_ediv (a b : ℕ) : ((a ⌈/⌉ b : ℕ) : ℤ) = -((-a) / b) := by
  rw [←Int.cast_neg_ceilDiv_eq_ediv, neg_neg]

/-- `natAbs = toNat` if we're nonnegative -/
lemma Int.natAbs_eq_toNat {a : ℤ} (a0 : 0 ≤ a) : a.natAbs = a.toNat := by
  simp only [←Nat.cast_inj (R := ℤ), natCast_natAbs, a0, toNat_of_nonneg, abs_eq_self]

/-- `natAbs = toNat -` if we're nonpositive -/
lemma Int.natAbs_eq_toNat_neg {a : ℤ} (a0 : a ≤ 0) : a.natAbs = (-a).toNat := by
  obtain ⟨_, e⟩ := Int.exists_eq_neg_ofNat a0
  simp [e]

/-- Coercion of `natAbs` to any linearly ordered ring is equal to `a` for nonnegative `a` -/
lemma Int.coe_natAbs_eq_self {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a : ℤ}
    (h : 0 ≤ a) : (a.natAbs : R) = a := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
  simp [Int.natAbs_eq_toNat]

/-- Coercion of `natAbs` to any linearly ordered ring is equal to `-a` for nonpositive `a` -/
lemma Int.coe_natAbs_eq_neg {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a : ℤ}
    (h : a ≤ 0) : (a.natAbs : R) = -a := by
  obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat h
  simp [Int.natAbs_eq_toNat]

lemma Int.emod_mul_eq_mul_emod' (a n m : ℤ) (n0 : 0 ≤ n) (m0 : 0 < m) :
    a * n % (m * n) = a % m * n := by
  generalize hy : n.toNat = y
  generalize hz : m.toNat = z
  replace hy : n = y := by rw [←hy, Int.toNat_of_nonneg n0]
  replace hz : m = z := by rw [←hz, Int.toNat_of_nonneg m0.le]
  have z1 : 1 ≤ z := by omega
  simp only [hy, hz]; clear hy hz n0 m0 n m
  have e : a = a + |a| * z + -|a| * z := by ring
  generalize hx : (a + |a| * z).toNat = x
  replace hx : a + |a| * z = x := by
    rw [←hx, Int.toNat_of_nonneg]
    refine le_trans ?_ (add_le_add_right (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr z1) (abs_nonneg _)) _)
    simp only [Nat.cast_one, mul_one]
    exact add_abs_nonneg a
  rw [e, hx, Int.add_mul_emod_self_right, add_mul, mul_assoc, Int.add_mul_emod_self_right]
  simp only [←Nat.cast_mul, ← Int.natCast_emod, Nat.cast_inj]
  apply Nat.mul_mod_mul_right

lemma Int.emod_mul_eq_mul_emod (a n : ℤ) (n0 : 0 < n) : a * n % n^2 = a % n * n := by
  rw [pow_two, Int.emod_mul_eq_mul_emod' _ _ _ n0.le n0]

/-- `p` is true for all integers if it is true for nonnegative and nonpositive integers.

    This is a slightly nicer induction principle on the integers that covers zero twice
    to reduce notational clutter. -/
theorem Int.induction_overlap {p : ℤ → Prop} (hi : ∀ n : ℕ, p n) (lo : ∀ n : ℕ, p (-n)) :
    ∀ n : ℤ, p n := by intro n; induction' n using Int.rec with n; exact hi n; exact lo (_ + 1)

section ZPow
attribute [bound] zpow_nonneg zpow_pos

variable {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

lemma zpow_anti {a : 𝕜} (a0 : 0 < a) (a1 : a ≤ 1) : Antitone fun n : ℤ ↦ a ^ n := by
  intro n m nm
  by_cases e0 : n = m
  · simp [e0]
  · by_cases e1 : a = 1
    · simp [e1]
    · exact (zpow_right_strictAnti₀ a0 (Ne.lt_of_le e1 a1) (Ne.lt_of_le e0 nm)).le

/-- `bound` lemma for branching on `1 ≤ a ∨ a ≤ 1` when proving `a ^ n ≤ a ^ m` -/
@[bound] lemma Bound.zpow_le_zpow_right_of_le_one_or_one_le {a : 𝕜} {n m : ℤ}
    (h : 1 ≤ a ∧ n ≤ m ∨ 0 < a ∧ a ≤ 1 ∧ m ≤ n) :
    a ^ n ≤ a ^ m := by
  rcases h with ⟨a1, nm⟩ | ⟨a0, a1, mn⟩
  · exact zpow_le_zpow_right₀ a1 nm
  · exact zpow_anti a0 a1 mn

end ZPow

@[simp] lemma Int.natFloor_cast (n : ℤ) : ⌊(n : ℝ)⌋₊ = ⌊n⌋₊ := by
  induction' n using  Int.induction_overlap with n n
  · simp
  · simp only [cast_neg, cast_natCast, Nat.floor_int, toNat_neg_natCast, Nat.floor_eq_zero]
    refine lt_of_le_of_lt ?_ zero_lt_one
    simp only [Left.neg_nonpos_iff, Nat.cast_nonneg]

/-- Turn `|n|` into something `omega` understands -/
lemma Int.abs_def {n : ℤ} : |n| = if n < 0 then -n else n := by
  by_cases h : n < 0
  · simp only [h, ↓reduceIte, abs_eq_neg_self, h.le]
  · simp only [not_lt] at h
    simp only [abs_of_nonneg h]
    omega

/-- Turn `n.natAbs` into something `omega` understands -/
lemma Int.natAbs_def {n : ℤ} : n.natAbs = if n < 0 then (-n).toNat else n.toNat := by
  simp only [natAbs]
  induction' n using Int.rec with n
  · simp only [ofNat_eq_natCast, toNat_neg_natCast, toNat_natCast]
    split_ifs
    all_goals omega
  · simp only [Nat.succ_eq_add_one, negSucc_eq, neg_add_rev, reduceNeg, add_neg_lt_iff_lt_add,
      zero_add, neg_neg, toNat_natCast_add_one]; split_ifs; omega; omega
