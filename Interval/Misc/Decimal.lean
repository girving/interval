import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Bound
import Interval.Approx.Approx
import Interval.Misc.Int
import Interval.Misc.Real

/-!
# Utilities for decimal numbers
-/

open Set

/-!
### `Decimal` basics
-/

/-- `n * 10^s -/
structure Decimal where
  /-- Coefficient -/
  n : ℤ
  /-- Decimal integer exponent -/
  s : ℤ
  deriving DecidableEq

namespace Decimal

instance : Zero Decimal where
  zero := ⟨0, 0⟩

lemma zero_def : (0 : Decimal) = ⟨0,0⟩ := rfl

/-- The obvious instance -/
instance : OfScientific Decimal where
  ofScientific n z s := ⟨n, if z then -s else s⟩

instance (n : ℕ) [n.AtLeastTwo] : OfNat Decimal n where
  ofNat := ⟨n, 0⟩

instance : Neg Decimal where
  neg x := ⟨-x.n, x.s⟩

/-- Negation of a `Decimal` number negates the coefficient -/
lemma neg_eq (x : Decimal) : -x = ⟨-x.n, x.s⟩ := rfl

/-- Convert to `ℝ` -/
@[irreducible] def val (x : Decimal) : ℝ :=
  let y := OfScientific.ofScientific x.n.natAbs (x.s < 0) x.s.natAbs
  bif x.n < 0 then -y else y

/-- Convert to `ℚ` -/
@[irreducible] def valq (x : Decimal) : ℚ :=
  let y := OfScientific.ofScientific x.n.natAbs (x.s < 0) x.s.natAbs
  bif x.n < 0 then -y else y

/-- Convert to `ℝ` -/
instance : CoeTail Decimal ℝ where
  coe x := x.val

lemma Rat.ofScientific_eq (n : ℕ) (neg : Bool) (e : ℕ) :
    (OfScientific.ofScientific n neg e : ℚ) = (n : ℚ) * 10 ^ (if neg then -(e : ℤ) else e) := by
  have en : OfNat.ofNat n = n := rfl
  have ee : OfNat.ofNat e = e := rfl
  simp only [OfScientific.ofScientific, Rat.ofScientific_def, en, ee]
  split_ifs
  · simp [Rat.mkRat_eq_div, div_eq_mul_inv]
  · simp

lemma Real.ofScientific_eq (n : ℕ) (neg : Bool) (e : ℕ) :
    (OfScientific.ofScientific n neg e : ℝ) = (n : ℚ) * 10 ^ (if neg then -(e : ℤ) else e) := by
  trans ((OfScientific.ofScientific n neg e : ℚ) : ℝ)
  · rfl
  · simp only [Rat.ofScientific_eq, pow_ite, zpow_neg, zpow_natCast, mul_ite]
    induction neg
    all_goals simp

/-- `Decimal.val` in simple form -/
lemma val_eq (x : Decimal) : x.val = x.n * 10 ^ x.s := by
  rw [Decimal.val, Real.ofScientific_eq]
  simp only [decide_eq_true_eq, Int.natCast_natAbs, pow_ite, zpow_neg, mul_ite, bif_eq_if]
  by_cases s0 : x.s < 0
  · by_cases n0 : x.n < 0
    · simp only [n0, ↓reduceIte, s0, Int.coe_natAbs_eq_neg n0.le, Rat.cast_neg, Rat.cast_intCast,
        abs_of_neg s0, zpow_neg, inv_inv, ← neg_mul, neg_neg]
    · simp only [n0, ↓reduceIte, s0, Int.coe_natAbs_eq_self (not_lt.mp n0), Rat.cast_intCast,
        abs_of_nonpos s0.le, zpow_neg, inv_inv]
  · by_cases n0 : x.n < 0
    · simp only [n0, ↓reduceIte, s0, Int.coe_natAbs_eq_neg n0.le, Rat.cast_neg, Rat.cast_intCast,
        abs_of_nonneg (not_lt.mp s0), ← neg_mul, neg_neg]
    · simp only [n0, ↓reduceIte, s0, Int.coe_natAbs_eq_self (not_lt.mp n0), Rat.cast_intCast,
        abs_of_nonneg (not_lt.mp s0)]

/-- `Decimal.valq` in simple form -/
lemma valq_eq (x : Decimal) : x.valq = x.n * 10 ^ x.s := by
  rw [Decimal.valq, Rat.ofScientific_eq]
  simp only [decide_eq_true_eq, Int.natCast_natAbs, pow_ite, zpow_neg, mul_ite, bif_eq_if]
  by_cases s0 : x.s < 0
  · by_cases n0 : x.n < 0
    · simp only [n0, ↓reduceIte, s0, Int.coe_natAbs_eq_neg n0.le, abs_of_neg s0, zpow_neg, inv_inv,
      ← neg_mul, neg_neg]
    · simp only [n0, ↓reduceIte, s0, Int.coe_natAbs_eq_self (not_lt.mp n0), abs_of_nonpos s0.le,
      zpow_neg, inv_inv]
  · by_cases n0 : x.n < 0
    · simp only [n0, ↓reduceIte, s0, Int.coe_natAbs_eq_neg n0.le, abs_of_nonneg (not_lt.mp s0), ←
      neg_mul, neg_neg]
    · simp only [n0, ↓reduceIte, s0, Int.coe_natAbs_eq_self (not_lt.mp n0),
      abs_of_nonneg (not_lt.mp s0)]

/-- `val` and `valq` are related -/
lemma coe_valq (x : Decimal) : x.valq = x.val := by
  simp [val_eq, valq_eq]

/-- `Decimal.val` commutes with negation for `ℚ` -/
@[simp] lemma val_neg (x : Decimal) : (-x).val = -x.val := by
  simp only [neg_eq, val_eq, Int.cast_neg, neg_mul]

/-- `Decimal.val 0 = 0` -/
@[simp] lemma val_zero : (0 : Decimal).val = 0 := by
  simp only [zero_def, val_eq, Int.cast_zero, zpow_zero, mul_one]

-- Test `Decimal` conversion
example : (Decimal.mk 123 (-2) : ℝ) = 1.23 := by norm_num [Decimal.val_eq]
example : ((123e-2 : Decimal) : ℝ) = 1.23 := by norm_num [Decimal.val_eq, OfScientific.ofScientific]
example : ((1.23 : Decimal) : ℝ) = 1.23 := by norm_num [Decimal.val_eq, OfScientific.ofScientific]
example : ((121e17 : Decimal) : ℝ) = 121e17 := by
  norm_num [Decimal.val_eq, OfScientific.ofScientific]

/-- Print `Decimal` exactly in Decimal notation -/
instance : Repr Decimal where
  reprPrec x _ :=
    if x.n = 0 then "0" else
    let m :=
      let s := toString x.n.natAbs
      let s := toString s.head ++ "." ++ s.drop 1
      let s := bif x.n < 0 then "-" ++ s else s
      s.dropRightWhile fun c ↦ c == '0' || c == '.'
    let s := x.s + Nat.log 10 x.n.natAbs
    if s = 0 then m else
    m ++ "e" ++ toString s

/-!
### Exactly rounded precision reduction
-/

/-- Round to at most `p` significant digits -/
def prec (x : Decimal) (p : ℕ) (up : Bool) : Decimal :=
  let d := Nat.log 10 x.n.toNat
  bif d ≤ p then x else
  let t := d - p
  ⟨x.n.rdiv (10 ^ t) up, x.s + t⟩

/-- Round to absolute precision `10 ^ p` -/
def aprec (x : Decimal) (p : ℤ) (up : Bool) : Decimal :=
  bif p ≤ x.s then x else
  let t := (p - x.s).toNat
  ⟨x.n.rdiv (10 ^ t) up, x.s + t⟩

/-- `prec` rounds down if desired -/
lemma prec_le (x : Decimal) (p : ℕ) : (x.prec p false).val ≤ x.val := by
  simp only [prec, bif_eq_if, decide_eq_true_eq, val_eq]
  by_cases lp : Nat.log 10 x.n.toNat ≤ p
  · simp only [lp, ↓reduceIte, le_refl]
  · simp only [lp, ↓reduceIte]
    refine le_trans (mul_le_mul_of_nonneg_right Int.rdiv_le (by positivity)) ?_
    simp only [Nat.cast_pow, Nat.cast_ofNat, div_mul_eq_mul_div, mul_div_assoc, ← zpow_natCast]
    rw [← zpow_sub₀ (by norm_num)]
    simp only [add_sub_cancel_right, le_refl]

/-- `prec` rounds up if desired -/
lemma le_prec (x : Decimal) (p : ℕ) : x.val ≤ (x.prec p true).val := by
  simp only [prec, bif_eq_if, decide_eq_true_eq, val_eq]
  by_cases lp : Nat.log 10 x.n.toNat ≤ p
  · simp only [lp, ↓reduceIte, le_refl]
  · simp only [lp, ↓reduceIte]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right Int.le_rdiv (by positivity))
    simp only [Nat.cast_pow, Nat.cast_ofNat, div_mul_eq_mul_div, mul_div_assoc, ← zpow_natCast]
    rw [← zpow_sub₀ (by norm_num)]
    simp only [add_sub_cancel_right, le_refl]

/-- `aprec` rounds down if desired -/
lemma aprec_le (x : Decimal) (p : ℤ) : (x.aprec p false).val ≤ x.val := by
  simp only [aprec, bif_eq_if, decide_eq_true_eq, val_eq]
  by_cases ps : p ≤ x.s
  · simp only [ps, ↓reduceIte, le_refl]
  · simp only [ps, ↓reduceIte]
    refine le_trans (mul_le_mul_of_nonneg_right Int.rdiv_le (by positivity)) ?_
    simp only [Nat.cast_pow, Nat.cast_ofNat, div_mul_eq_mul_div, mul_div_assoc, ← zpow_natCast]
    rw [← zpow_sub₀ (by norm_num)]
    simp only [add_sub_cancel_right, le_refl]

/-- `aprec` rounds up if desired -/
lemma le_aprec (x : Decimal) (p : ℤ) : x.val ≤ (x.aprec p true).val := by
  simp only [aprec, bif_eq_if, decide_eq_true_eq, val_eq]
  by_cases ps : p ≤ x.s
  · simp only [ps, ↓reduceIte, le_refl]
  · simp only [ps, ↓reduceIte]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right Int.le_rdiv (by positivity))
    simp only [Nat.cast_pow, Nat.cast_ofNat, div_mul_eq_mul_div, mul_div_assoc, ← zpow_natCast]
    rw [← zpow_sub₀ (by norm_num)]
    simp only [add_sub_cancel_right, le_refl]

/-!
### Exactly rounded conversion from binary exponents to decimal

We start with `n * 2^s` and want to convert it to `m * 10^t`, rounding as desired. Say we're
rounding down, and want to achieve precision `prec`:
  `m * 10^t ≤ n * 2^s   ∧ m < 10^(prec+1)`
  `m = ⌊n * 2^s / 10^t⌋ ∧ m < 10^(prec+1)`
  `m = ⌊n * 2^s / 10^t⌋ ∧ n * 2^s / 10^t < 10^(prec+1)`
  `m = ⌊n * 2^s / 10^t⌋ ∧ t = ⌈logb 10 (n * 2^s / 10^(prec+1))⌉`
We'd like to compute the above without ever blowing up, say by computing a very large `n * 2^s`
value. We can estimate `t` using approximate arithmetic, then shift it up or down a bit to get the
minimal value that works. A `t` value works if
  `f t = round (n * 2^s / 10^t)`
satisfies
  `f t < 10^(prec+1)`
Meh, doing it without blowup seems involved: it . Let's just eat the blowup for now.
-/

namespace OfBinary

-- `log_10 2` as `num / den`, roughly
def log_10_2_num :=  3010299956639812
def log_10_2_den := 10000000000000000

/-- We underestimate `t`, since we'll then increase it until we fit within prec -/
def t_underestimate (n : ℕ) (s : ℤ) (prec : ℕ) : ℤ :=
  -- `Nat.log` rounds down, and it should be `prec - 1` not `prec - 2`, so understimate.
  -- However, we don't currently prove this.
  (Nat.log 10 n : ℤ) + s * log_10_2_num / log_10_2_den - prec - 2

/-- `n * 2^s / 10^t`, rounding as desired -/
def m_of_t (n : ℕ) (s : ℤ) (t : ℤ) (up : Bool) : ℕ :=
  -- Convert to n * 2^a * 5^b
  let x := (n : ℚ) * 2 ^ (s - t) / 5 ^ t
  if up then ⌈x⌉₊ else ⌊x⌋₊

/-- `m_of_t` rounds down if desired -/
lemma m_of_t_le (n : ℕ) (s : ℤ) (t : ℤ) :
    m_of_t n s t false ≤ (n : ℝ) * 2^s / 10^t := by
  have e0 : ∀ n : ℕ, (n : ℝ) = ((n : ℚ) : ℝ) := fun _ ↦ rfl
  have e1 : (n * 2^s / 10^t : ℝ) = (n * 2^s / 10^t : ℚ) := by simp
  simp only [m_of_t, Bool.false_eq_true, ↓reduceIte, e0 ⌊(_:ℚ)⌋₊, e1, Rat.cast_le,
    (by norm_num : (10 : ℚ) = 2 * 5), mul_zpow, div_mul_eq_div_div, mul_div_assoc,
    ← zpow_sub₀ (by norm_num : (2:ℚ) ≠ 0)]
  exact Nat.floor_le (by positivity)

/-- `m_of_t` rounds up if desired -/
lemma le_m_of_t (n : ℕ) (s : ℤ) (t : ℤ) :
    (n : ℝ) * 2^s / 10^t ≤ m_of_t n s t true := by
  have e0 : ∀ n : ℕ, (n : ℝ) = ((n : ℚ) : ℝ) := fun _ ↦ rfl
  have e1 : (n * 2^s / 10^t : ℝ) = (n * 2^s / 10^t : ℚ) := by simp
  simp only [m_of_t, ↓reduceIte, e0 ⌈(_ : ℚ)⌉₊, e1, Rat.cast_le, (by norm_num : (10 : ℚ) = 2 * 5),
    mul_zpow, div_mul_eq_div_div, mul_div_assoc, ← zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
    Nat.le_ceil]

/-- `m_of_t n s t` is antitone in `t` -/
lemma antitone_m_of_t (n : ℕ) (s : ℤ) (up : Bool) : Antitone (m_of_t n s · up) := by
  intros t₁ t₂ h
  simp only [m_of_t]
  induction up
  · simp only [Bool.false_eq_true, ↓reduceIte]; bound
  · simp only [↓reduceIte]; bound

/-- A sufficiently large `t` means `m ≤ 1` -/
lemma exists_t (n : ℕ) (s : ℤ) (t : ℤ) (up : Bool) : ∃ dt : ℕ, m_of_t n s (t + dt) up ≤ 1 := by
  obtain ⟨dt, lt⟩ := pow_unbounded_of_one_lt (n * 2 ^ s / 2 ^ t / 5 ^ t : ℚ) (y := 10) (by norm_num)
  use dt
  suffices h : (n * 2^(s - (t+dt)) / 5^(t+dt) : ℚ) ≤ 1 by
    induction up
    · simp only [m_of_t, Bool.false_eq_true, ↓reduceIte, Nat.floor_le_one_of_le_one h]
    · simp only [m_of_t, ↓reduceIte, Nat.ceil_le, Nat.cast_one, h]
  simp only [sub_add_eq_sub_sub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zpow_sub₀,
    zpow_natCast, ← mul_div_assoc, zpow_add₀, div_mul_eq_div_div, div_right_comm _ ((2:ℚ)^_)]
  simp only [← div_mul_eq_div_div _ ((5:ℚ)^_), ← mul_pow, (by norm_num : 5 * 2 = (10:ℚ))]
  have ten : 0 < (10 : ℚ) ^ dt := by norm_num
  simp only [div_le_one ten, lt.le]

/-- A sufficiently large `t` means `m ≤ 10 ^ (prec + 1)` -/
lemma exists_t' (n : ℕ) (s : ℤ) (t : ℤ) (prec : ℕ) (up : Bool) :
    ∃ dt : ℕ, m_of_t n s (t + dt) up ≤ 10 ^ (prec + 1) := by
  obtain ⟨dt, h⟩ := exists_t n s t up
  exact ⟨dt, le_trans h (by bound)⟩

/-- Convert binary to `Decimal`, rounding to a desired decimal precision -/
def ofBinaryNat (n : ℕ) (s : ℤ) (prec : ℕ) (up : Bool) : Decimal :=
  bif n == 0 then 0 else
  let t := t_underestimate n s prec
  let t := t + Nat.find (exists_t' n s t prec up)
  ⟨m_of_t n s t up, t⟩

/-- `ofBinaryNat` rounds down if desired -/
lemma ofBinaryNat_le (n : ℕ) (s : ℤ) (prec : ℕ) : ofBinaryNat n s prec false ≤ (n : ℝ) * 2^s := by
  simp only [ofBinaryNat, Decimal.val_eq]
  by_cases n0 : n = 0
  · simp [n0, zero_def]
  · simp only [bif_eq_if, beq_iff_eq, n0, ↓reduceIte, Int.cast_natCast]
    rw [← le_div_iff₀ (by positivity)]
    apply m_of_t_le

/-- `ofBinaryNat` rounds up if desired -/
lemma le_ofBinaryNat (n : ℕ) (s : ℤ) (prec : ℕ) : (n : ℝ) * 2^s ≤ ofBinaryNat n s prec true := by
  simp only [ofBinaryNat, Decimal.val_eq]
  by_cases n0 : n = 0
  · simp [n0, zero_def]
  · simp only [bif_eq_if, beq_iff_eq, n0, ↓reduceIte, Int.cast_natCast]
    rw [← div_le_iff₀ (by positivity)]
    apply le_m_of_t

end OfBinary

/-- Convert binary to `Decimal`, rounding to a desired decimal precision -/
def ofBinary (n : ℤ) (s : ℤ) (prec : ℕ) (up : Bool) : Decimal :=
  let neg : Bool := n < 0
  let s := OfBinary.ofBinaryNat n.natAbs s prec (neg != up)
  bif neg then -s else s

/-- `ofBinary` rounds down if desired -/
lemma ofBinary_le (n : ℤ) (s : ℤ) (prec : ℕ) : ofBinary n s prec false ≤ (n : ℝ) * 2^s := by
  simp only [ofBinary, Bool.bne_false, bif_eq_if, decide_eq_true_eq]
  by_cases h : n < 0
  · simp only [h, ↓reduceIte, decide_true, Decimal.val_neg, neg_le]
    refine le_trans (le_of_eq ?_) (OfBinary.le_ofBinaryNat _ _ _)
    simp only [Int.coe_natAbs_eq_neg h.le, neg_mul]
  · simp only [h, ↓reduceIte, decide_false]
    refine le_trans (OfBinary.ofBinaryNat_le _ _ _) (le_of_eq ?_)
    simp only [Int.coe_natAbs_eq_self (not_lt.mp h)]

/-- `ofBinary` rounds up if desired -/
lemma le_ofBinary (n : ℤ) (s : ℤ) (prec : ℕ) : (n : ℝ) * 2^s ≤ ofBinary n s prec true := by
  simp only [ofBinary, Bool.bne_true, bif_eq_if, decide_eq_true_eq]
  by_cases h : n < 0
  · simp only [h, ↓reduceIte, decide_true, Decimal.val_neg, le_neg]
    refine le_trans (OfBinary.ofBinaryNat_le _ _ _) (le_of_eq ?_)
    simp only [Int.coe_natAbs_eq_neg h.le, neg_mul]
  · simp only [h, ↓reduceIte, decide_false]
    refine le_trans (le_of_eq ?_) (OfBinary.le_ofBinaryNat _ _ _)
    simp only [Int.coe_natAbs_eq_self (not_lt.mp h)]

/-!
### Comparison

For now we very lazily convert to `ℚ`, even though this can be very inefficient.
-/

/-- Comparison via (possibly very inefficient) conversion to `ℚ` -/
def ble (x y : Decimal) : Bool :=
  x.valq ≤ y.valq

instance : LE Decimal where le x y := x.ble y
instance : LT Decimal where lt x y := !(y.ble x)
instance : Min Decimal where min x y := bif x.ble y then x else y
instance : Max Decimal where max x y := bif x.ble y then y else x
lemma le_def (x y : Decimal) : x ≤ y ↔ x.ble y := by rfl
lemma lt_def (x y : Decimal) : x < y ↔ !(y.ble x) := by rfl

lemma le_iff (x y : Decimal) : x ≤ y ↔ x.val ≤ y.val := by
  simp [le_def, ble, ← coe_valq]

lemma lt_iff (x y : Decimal) : x < y ↔ x.val < y.val := by
  simp [lt_def, ble, ← coe_valq]

instance : Preorder Decimal where
  le_refl x := by simp [le_def, ble]
  le_trans x y z := by simp [le_def, ble]; apply le_trans
  lt_iff_le_not_ge x y := by simp [lt_def, le_def, ble]; apply le_of_lt

instance (x y : Decimal) : Decidable (x ≤ y) := by
  simp only [le_def]
  apply Bool.decEq

lemma min_def (x y : Decimal) : min x y = if x ≤ y then x else y := by simp [min, le_def]
lemma max_def (x y : Decimal) : max x y = if x ≤ y then y else x := by simp [max, le_def]

@[simp] lemma val_min (x y : Decimal) : (min x y).val = min x.val y.val := by
  simp only [min_def, LinearOrder.min_def, le_iff]
  apply apply_ite

@[simp] lemma val_max (x y : Decimal) : (max x y).val = max x.val y.val := by
  simp only [max_def, LinearOrder.max_def, le_iff]
  apply apply_ite

/-!
### Exact arithmetic
-/

/-- Exact addition of `Decimal` -/
def add (x y : Decimal) : Decimal :=
  let s := min x.s y.s
  ⟨x.n * 10^(x.s - s).natAbs + y.n * 10^(y.s - s).natAbs, s⟩

/-- Exact division by 2 for `Decimal` -/
def div2 (x : Decimal) : Decimal :=
  ⟨5 * x.n, x.s - 1⟩

instance : Add Decimal where add := Decimal.add
instance : Sub Decimal where sub x y := x + -y

lemma add_def (x y : Decimal) : x + y = x.add y := rfl
lemma sub_def (x y : Decimal) : x - y = x + (-y) := rfl

/-- `Decimal.add` is exact -/
@[simp] lemma val_add {x y : Decimal} : (x + y).val = x.val + y.val := by
  simp only [add_def, add, val_eq, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    add_mul, mul_assoc]
  refine congr_arg₂ _ ?_ ?_
  all_goals {
    rw [pow_mul_zpow (by norm_num)]
    exact congr_arg₂ _ rfl (congr_arg₂ _ rfl (by omega)) }

/-- `Decimal.sub` is exact -/
@[simp] lemma val_sub {x y : Decimal} : (x - y).val = x.val - y.val := by
  simp only [sub_def, val_add, val_neg]
  ring

/-- `Decimal.div2` is exact -/
@[simp] lemma val_div2 {x : Decimal} : x.div2.val = x.val / 2 := by
  simp only [div2, val_eq, Int.cast_mul, Int.cast_ofNat]
  rw [zpow_sub_one₀ (by norm_num)]
  field_simp
  ring

/-!
### Decimal intervals and balls
-/

/-- A nonempty interval of `Decimal` -/
structure Interval : Type where
  lo : Decimal
  hi : Decimal
  le : lo.val ≤ hi.val

/-- A nonempty ball of `Decimal` -/
structure Ball : Type where
  c : Decimal
  r : Decimal
  r0 : 0 ≤ r.val

instance : Approx Interval ℝ where approx x a := x.lo ≤ a ∧ a ≤ x.hi
instance : Approx Ball ℝ where approx x a := x.c - x.r ≤ a ∧ a ≤ x.c + x.r

instance : Zero Interval where zero := ⟨0, 0, le_refl _⟩
instance : Zero Ball where zero := ⟨0, 0, by simp only [val_zero, le_refl]⟩

def Interval.mk' (x y : Decimal) : Interval :=
  if h : x ≤ y then ⟨x, y, by simpa [le_iff] using h⟩
  else ⟨y, x, by { simp only [not_le, le_iff] at h; exact h.le } ⟩

instance : Repr Ball where
  reprPrec x p :=
    bif x.r.n == 0 then reprPrec x.c p
    else reprStr x.c ++ " ± " ++ reprStr x.r

/-- Turn an interval into a ball, exactly -/
def Interval.ball (x : Interval) : Ball :=
  let c := (x.lo + x.hi).div2
  let r0 := c - x.lo
  ⟨c, r0, by
    simp only [val_sub, val_div2, val_add, sub_nonneg, r0, c]
    linarith [x.le]⟩

/-- `.ball` commutes with `approx` -/
@[simp] lemma Interval.approx_ball (x : Interval) (x' : ℝ) : approx x.ball x' ↔ approx x x' := by
  simp only [approx, ball, val_div2, val_add, val_sub, sub_sub_cancel, and_congr_right_iff]
  intro _
  constructor
  all_goals intro _; linarith

/-- Precision reduce an `Ball`, growing it slightly if necessary -/
def Ball.prec (x : Ball) (p : ℕ) : Ball :=
  let r := x.r.prec p true
  let q := r.s - p + Nat.log 10 r.n.natAbs
  let c := x.c.aprec q false
  ⟨c, (max (x.c + x.r - c) (c - x.c + x.r)).prec p true, by
    refine le_trans ?_ (le_prec _ _)
    simp only [val_max, val_sub, val_add, le_max_iff, sub_nonneg, c]
    left
    refine le_trans (aprec_le _ _) ?_
    linarith [x.r0]⟩

/-- `Ball.prec` is conservative -/
lemma Ball.approx_prec (x : Ball) (p : ℕ) (y : ℝ) (m : approx x y) : approx (x.prec p) y := by
  simp only [prec, approx] at m ⊢
  set rp := x.r.prec p true
  set q := rp.s - ↑p + Nat.log 10 rp.n.natAbs
  set cq := x.c.aprec q false
  constructor
  · rw [sub_le_iff_le_add, ← sub_le_iff_le_add']
    refine le_trans ?_ (le_prec _ _)
    simp only [val_max, val_sub, val_add, le_max_iff, tsub_le_iff_right]
    right
    linarith
  · rw [← sub_le_iff_le_add']
    refine le_trans ?_ (le_prec _ _)
    simp only [val_max, val_sub, val_add, le_max_iff, tsub_le_iff_right, sub_add_cancel]
    left
    linarith
