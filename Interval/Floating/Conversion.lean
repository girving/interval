import Interval.Floating.Basic
import Interval.Floating.Neg
import Interval.Floating.Order
import Interval.Floating.Scale
import Interval.Floating.Standardization
import Interval.Misc.Rat

open Pointwise

/-!
## Conversion from `ℕ`, `ℤ`, `ℚ`, `Float` to `Floating`
-/

open Set
open scoped Real
open scoped UInt64.CommRing
namespace Floating

/-!
## Normalization given `n ∈ [2^62, 2^63]`
-/

/-- A normalized `n, s` pair ready for conversion to `Floating`  -/
structure Convert where
  n : ℕ
  s : ℤ
  norm : n ∈ Ico (2^62) (2^63)

noncomputable def Convert.val (x : Convert) : ℝ := x.n * 2^(x.s - 2^63)

lemma Convert.n_mod (x : Convert) : x.n % 2^64 = x.n := by
  rw [Nat.mod_eq_of_lt]
  have h := x.norm
  simp only [mem_Ico] at h
  norm_num only at h ⊢
  omega

/-- `Convert.finish` is valid` -/
lemma Convert.valid_finish (x : Convert) : Valid ⟨x.n⟩ x.s where
  zero_same := by
    intro n0; contrapose n0; clear n0
    simp only [Int64.ext_iff, Int64.n_zero, UInt64.eq_zero_iff_toNat_eq_zero, UInt64.toNat_cast,
      UInt64.size_eq_pow, e]
    have h := x.norm
    norm_num [mem_Ico] at h
    omega
  nan_same := by
    intro nm; contrapose nm; clear nm
    simp only [Int64.ext_iff, Int64.n_min, UInt64.eq_iff_toNat_eq, UInt64.toNat_cast,
      UInt64.size_eq_pow, UInt64.toNat_2_pow_63, e]
    have h := x.norm
    norm_num [mem_Ico] at h ⊢
    omega
  norm := by
    intro _ _ _
    have h := x.norm
    simp only [mem_Ico] at h
    have e : x.n % 2^64 = x.n := x.n_mod
    rw [Int64.abs_eq_self']
    · simp only [UInt64.le_iff_toNat_le, up62, UInt64.toNat_cast, UInt64.size_eq_pow, e,
        x.norm.1]
    · simp only [← not_lt, Int64.isNeg_eq_le, UInt64.toNat_cast, UInt64.size_eq_pow, e,
        decide_eq_false_iff_not, not_le, x.norm.2, not_not]
  where
  e : x.n % 2^64 = x.n := x.n_mod

/-- Build a `Floating` out of `n * 2^(s - 2^63)`, rounding if required -/
@[irreducible] def Convert.finish (x : Convert) (up : Bool) : Floating :=
  if x.s < 0 then bif up then min_norm else 0 else
  if 2^64 ≤ x.s then nan else
  { n := ⟨x.n⟩
    s := x.s
    v := x.valid_finish }

lemma valid_convert_tweak : 2 ^ 62 ∈ Ico (2 ^ 62) (2 ^ 63) := by decide

/-- Build a `Floating` out of `n * 2^(s - 2^63)`, rounding if required -/
@[irreducible] def convert_tweak (n : ℕ) (s : ℤ) (norm : n ∈ Icc (2^62) (2^63)) : Convert :=
  if e : n = 2^63 then ⟨2^62, s + 1, valid_convert_tweak⟩
  else ⟨n, s, norm.1, norm.2.lt_of_ne e⟩

/-- `Convert.finish` is correct -/
lemma Convert.approx_finish (x : Convert) (up : Bool) :
    x.val ∈ rounds (approx (x.finish up)) !up := by
  rw [finish, val]
  by_cases s0 : x.s < 0
  · simp only [s0, bif_eq_if, dite_eq_ite, ite_true]
    induction up
    · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, zero_ne_nan, not_false_eq_true,
        approx_eq_singleton, val_zero, Bool.not_false, Int.reducePow, mem_rounds_singleton,
        two_zpow_pos, mul_nonneg_iff_of_pos_right, Nat.cast_nonneg]
    · simp only [ite_true, ne_eq, min_norm_ne_nan, not_false_eq_true, approx_eq_singleton,
        val_min_norm, Bool.not_true, mem_rounds_singleton, ite_false]
      refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr x.norm.2.le) two_zpow_pos.le) ?_
      simp only [Nat.cast_pow, Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_mul_zpow, gt_iff_lt, Nat.one_lt_ofNat, zpow_le_zpow_iff_right₀]
      norm_num
      omega
  simp only [s0, dite_eq_ite, ite_false]
  by_cases s1 : 2^64 ≤ x.s
  · simp only [s1, ite_true, approx_nan, rounds_univ, mem_univ]
  have n1' : x.n < 2^64 := lt_trans x.norm.2 (by norm_num)
  have n1 : (x.n : ℤ) < 2^64 := lt_trans (Nat.cast_lt.mpr x.norm.2) (by norm_num)
  have xne : (x.n : UInt64) ≠ 2^63 := by
    simp only [ne_eq, UInt64.eq_iff_toNat_eq, UInt64.toNat_cast, UInt64.size_eq_pow,
      UInt64.toNat_2_pow_63, Nat.mod_eq_of_lt n1']
    exact x.norm.2.ne
  have n0 : 0 ≤ (⟨↑x.n⟩ : Int64) := by
    simp only [Int64.isNeg_eq_le, UInt64.toNat_cast, UInt64.size_eq_pow, Nat.mod_eq_of_lt n1',
      decide_eq_false_iff_not, not_le, ← not_lt, not_not, Int64.isNeg]
    exact x.norm.2
  simp only [approx, s1, ite_false, ext_iff, n_nan, Int64.ext_iff, Int64.n_min, s_nan, xne,
    false_and]
  simp only [not_le, not_lt] at s1 s0
  rw [Floating.val]
  simp only [Int64.coe_of_nonneg n0, UInt64.toNat_cast, Int.ofNat_emod,
    UInt64.toInt, UInt64.toInt_intCast, Int.emod_eq_of_lt s0 s1, mem_rounds_singleton,
    Bool.not_eq_true', gt_iff_lt, two_zpow_pos, mul_le_mul_right, UInt64.size_eq_pow, Nat.cast_pow,
    Nat.cast_two, Int.emod_eq_of_lt (Nat.cast_nonneg _) n1, Int.cast_natCast, le_refl, ite_self]

/-- `convert_tweak` is correct -/
lemma val_convert_tweak (n : ℕ) (s : ℤ) (norm : n ∈ Icc (2^62) (2^63)) :
    (convert_tweak n s norm).val = n * 2^(s - 2^63) := by
  rw [Convert.val, convert_tweak]
  by_cases e : n = 2^63
  · simp only [e, dite_true, Nat.cast_pow, Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_mul_zpow, gt_iff_lt, zero_lt_two, OfNat.ofNat_ne_one, zpow_right_inj₀]
    omega
  · simp only [e, dite_false]

/-- Prove a `(convert_tweak _ _ _).finish _` call is correct, in context. -/
lemma approx_convert {a : ℝ} {n : ℕ} {s : ℤ} {norm : n ∈ Icc (2^62) (2^63)} {up : Bool}
    (an : if up then a ≤ ↑n * 2^(s - 2^63) else ↑n * 2^(s - 2^63) ≤ a) :
    a ∈ rounds (approx ((convert_tweak n s norm).finish up)) !up := by
  by_cases cn : (convert_tweak n s norm).finish up = nan
  · simp only [cn, approx_nan, rounds_univ, mem_univ]
  have h := Convert.approx_finish (convert_tweak n s norm) up
  simp only [val_convert_tweak, approx, cn, ite_false, mem_rounds_singleton,
    Bool.not_eq_true'] at h ⊢
  induction up
  · exact le_trans h an
  · exact le_trans an h

/-!
## Conversion from `ℕ`
-/

lemma ofNat_norm {n : ℕ} {up : Bool}
    : let t := n.fast_log2
      let s := t - 62
      ¬t ≤ 62 → n.shiftRightRound s up ∈ Icc (2 ^ 62) (2 ^ 63) := by
  intro t s t62
  simp only [t, s, Nat.fast_log2_eq] at s t62 ⊢
  simp only [Nat.shiftRightRound_eq_rdiv, mem_Icc]
  by_cases n0 : n = 0
  · simp only [n0, Nat.log2_zero, zero_le, not_true_eq_false] at t62
  · constructor
    · apply Nat.le_rdiv_of_mul_le (pow_pos (by norm_num) _)
      rw [← pow_add, ← Nat.le_log2 n0]
      omega
    · refine Nat.rdiv_le_of_le_mul (le_trans Nat.lt_log2_self.le ?_)
      rw [←pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Conversion from `ℕ` to `Floating`, rounding up or down -/
@[irreducible] def ofNat (n : ℕ) (up : Bool) : Floating :=
  let t := n.fast_log2
  -- If `t ≤ 62`, use `of_ns` to shift left.  If `t > 62`, shift right.
  if t62 : t ≤ 62 then of_ns n (2^63) else
  let s := t - 62
  let x := convert_tweak (n.shiftRightRound s up) (s + 2^63) (ofNat_norm t62)
  x.finish up

/-- Conversion from `ℕ` literals to `Floating`, rounding down arbitrarily.
    Use `Interval.ofNat` if you want something trustworthy (it rounds both ways). -/
instance {n : ℕ} [n.AtLeastTwo] : OfNat Floating n := ⟨.ofNat n false⟩

/-- Small naturals convert exactly -/
lemma val_ofNat' {n : ℕ} (lt : n < 2^63 := by norm_num) {up : Bool}  : (ofNat n up).val = n := by
  have n62 : n.log2 ≤ 62 := by
    by_cases n0 : n = 0
    · simp only [n0, Nat.log2_zero, zero_le]
    · rw [←Nat.log2_lt n0] at lt; exact Nat.lt_succ_iff.mp lt
  have e63 : (2^63 : UInt64).toInt = 2^63 := by decide
  have nn : (n : Int64) ≠ Int64.min := by
    simp only [ne_eq, Int64.ext_iff, Int64.ofNat_eq_coe, Int64.n_min, UInt64.eq_iff_toNat_eq,
      UInt64.toNat_cast, UInt64.size_eq_pow, UInt64.toNat_2_pow_63]
    norm_num only at lt ⊢
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [ofNat]
  simp only [n62, tsub_eq_zero_of_le, CharP.cast_eq_zero, dite_true, approx, of_ns_eq_nan_iff,
    nn, if_false, val_of_ns nn, mem_rounds_singleton, e63, sub_self, Bool.not_eq_true', zpow_zero,
    mul_one, Int64.toInt_ofNat lt, Int.cast_natCast, le_refl, ite_self, Nat.fast_log2_eq]

/-- Small naturals convert exactly -/
lemma val_ofNat {n : ℕ} [n.AtLeastTwo] (lt : n < 2^63 := by norm_num) :
    (OfNat.ofNat n : Floating).val = n :=
  val_ofNat' lt

/-- Small naturals do not overflow.  Much larger values also do not overflow, but this is all
    we need at the moment. -/
lemma ofNat_ne_nan {n : ℕ} (lt : n < 2^63) (up : Bool) : ofNat n up ≠ nan := by
  simp only [Ne, ←val_inj]
  apply ne_of_gt
  simp only [val_ofNat' lt]
  exact lt_of_lt_of_le val_nan_lt_zero (Nat.cast_nonneg _)

/-- `ofNat` rounds the desired way -/
lemma approx_ofNat (n : ℕ) (up : Bool) : ↑n ∈ rounds (approx (.ofNat n up : Floating)) !up := by
  by_cases n62 : n.log2 ≤ 62
  · have lt : n < 2^63 :=
      lt_of_lt_of_le Nat.lt_log2_self (pow_le_pow_right₀ (by norm_num) (by omega))
    simp only [approx, ofNat_ne_nan lt, ↓reduceIte, val_ofNat' lt, mem_rounds_singleton,
      Bool.not_eq_true', le_refl, ite_self]
  · rw [ofNat]
    simp only [n62, dite_false, Nat.fast_log2_eq]
    apply approx_convert
    simp only [Nat.shiftRightRound_eq_rdiv]
    have t0 : (2:ℝ) ≠ 0 := by norm_num
    induction up
    · simp only [Bool.false_eq_true, ↓reduceIte, Int.reducePow, add_sub_cancel_right, zpow_natCast]
      refine le_trans (mul_le_mul_of_nonneg_right Nat.rdiv_le two_pow_pos.le) ?_
      simp only [Nat.cast_pow, Nat.cast_ofNat, div_mul_eq_mul_div, mul_div_assoc, zpow_div_pow t0]
      apply mul_le_of_le_one_right (Nat.cast_nonneg _)
      apply div_self_le_one
    · simp only [ite_true]
      refine le_trans ?_ (mul_le_mul_of_nonneg_right Nat.le_rdiv two_zpow_pos.le)
      simp only [Nat.cast_pow, Nat.cast_ofNat, div_mul_eq_mul_div, mul_div_assoc, zpow_div_pow t0]
      apply le_mul_of_one_le_right (Nat.cast_nonneg _)
      exact one_le_zpow₀ (by norm_num) (by omega)

/-- `approx_ofNat`, down version -/
lemma ofNat_le {n : ℕ} (h : ofNat n false ≠ nan) : (ofNat n false).val ≤ n := by
  simpa only [approx, h, ite_false, Bool.not_false, mem_rounds_singleton, ite_true] using
    approx_ofNat n false

/-- `approx_ofNat`, up version -/
lemma le_ofNat {n : ℕ} (h : ofNat n true ≠ nan) : n ≤ (ofNat n true).val := by
  simpa only [approx, h, ite_false, Bool.not_true, mem_rounds_singleton] using approx_ofNat n true

/-- Combined version, for use in `Interval` construction -/
lemma ofNat_le_ofNat {n : ℕ} (h : ofNat n true ≠ nan) :
    (ofNat n false).val ≤ (ofNat n true).val := by
  by_cases a : ofNat n false = nan
  · simp only [a, val_le_val, val_nan_le]
  · exact le_trans (ofNat_le a) (le_ofNat h)

/-!
## Conversion from `ℤ`
-/

/-- Conversion from `ℤ` -/
@[irreducible] def ofInt (n : ℤ) (up : Bool) : Floating :=
  bif n < 0 then -ofNat (-n).toNat !up else .ofNat n.toNat up

/-- `ofInt` rounds the desired way -/
lemma approx_ofInt (n : ℤ) (up : Bool) : ↑n ∈ rounds (approx (ofInt n up)) !up := by
  rw [ofInt]
  by_cases n0 : n < 0
  · have e : (n : ℝ) = -↑(-n).toNat := by
      have e : (n : ℝ) = -↑(-n) := by simp only [Int.cast_neg, neg_neg]
      have le : 0 ≤ -n := by omega
      rw [e, ←Int.toNat_of_nonneg le, neg_inj, Int.cast_natCast]
      rw [Int.toNat_of_nonneg le]
    simpa only [e, n0, decide_true, cond_true, approx_neg, rounds_neg, Bool.not_not, mem_neg,
      neg_neg] using approx_ofNat (-n).toNat (!up)
  · have e : (n : ℝ) = ↑n.toNat := by
      rw [←Int.toNat_of_nonneg (not_lt.mp n0), Int.cast_natCast]
      simp only [Int.toNat_of_nonneg (not_lt.mp n0)]
    simp only [e, n0, decide_false, cond_false, approx_ofNat]

/-- `approx_ofInt`, down version -/
lemma ofInt_le {n : ℤ} (h : (ofInt n false) ≠ nan) : (ofInt n false).val ≤ n := by
  simpa only [approx, h, ite_false, Bool.not_false, mem_rounds_singleton, ite_true] using
    approx_ofInt n false

/-- `approx_ofInt`, up version -/
lemma le_ofInt {n : ℤ} (h : (ofInt n true) ≠ nan) : n ≤ (ofInt n true).val := by
  simpa only [approx, h, ite_false, Bool.not_true, mem_rounds_singleton] using
    approx_ofInt n true

/-- Combined version, for use in `Interval` construction -/
lemma ofInt_le_ofInt {n : ℤ} (h : ofInt n true ≠ nan) :
    (ofInt n false).val ≤ (ofInt n true).val := by
  by_cases a : ofInt n false = nan
  · simp only [a, val_le_val, val_nan_le]
  · exact le_trans (ofInt_le a) (le_ofInt h)

/-!
## Conversion from `ℚ`
-/

/-- `ofRat_abs` gives the right input to `convert_tweak` -/
lemma ofRat_norm {x : ℚ} {up : Bool} (x0 : ¬x = 0)
  : let r := x.log2
    let n := x.num.natAbs
    let p := if r ≤ 62 then (n <<< (62 - r).toNat, x.den) else (n, x.den <<< (r - 62).toNat)
    p.1.rdiv p.2 up ∈ Icc (2 ^ 62) (2 ^ 63) := by
  intro r n p
  simp only [p, r, n, mem_Icc, Nat.shiftLeft_eq]
  generalize hr : x.log2 = r
  generalize hn : x.num.natAbs = n
  have d0 : 0 < (x.den : ℚ) := Nat.cast_pos.mpr x.den_pos
  have ae : (n : ℚ) / x.den = |x| := by rw [Rat.abs_eq_div, hn]
  have t0 : (2 : ℚ) ≠ 0 := by norm_num
  by_cases r62 : r ≤ 62
  · simp only [r62, ite_true]
    constructor
    · apply Nat.le_rdiv_of_mul_le x.den_pos
      simp only [← Nat.cast_le (α := ℚ), Nat.cast_mul, Nat.cast_pow, Nat.cast_two, ←zpow_natCast,
        ← le_div_iff₀ d0, ←div_mul_eq_mul_div, ae, ← div_le_iff₀ (G₀ := ℚ) two_zpow_pos]
      simp only [← zpow_sub₀ t0, Int.toNat_of_nonneg (sub_nonneg.mpr r62)]
      ring_nf; rw [ ←hr]
      exact Rat.log2_self_le x0
    · apply Nat.rdiv_le_of_le_mul
      simp only [←Nat.cast_le (α := ℚ), Nat.cast_mul, Nat.cast_pow, Nat.cast_two, ←zpow_natCast,
        ← div_le_iff₀ d0, ←div_mul_eq_mul_div, ae, ← le_div_iff₀ (G₀ := ℚ) two_zpow_pos]
      simp only [←zpow_sub₀ t0, Int.toNat_of_nonneg (sub_nonneg.mpr r62)]
      ring_nf; rw [←hr, add_comm]
      exact Rat.lt_log2_self.le
  · simp only [r62, ite_false]
    replace r62 := (not_le.mp r62).le
    constructor
    · apply Nat.le_rdiv_of_mul_le (mul_pos x.den_pos two_pow_pos)
      simp only [←mul_assoc, mul_comm _ (2^(_:ℤ).toNat), ←pow_add, ←Nat.cast_le (α := ℚ),
        ← le_div_iff₀ d0, ae, Nat.cast_mul, Nat.cast_pow, Nat.cast_two]
      simp only [←zpow_natCast, ←zpow_sub₀ t0, Int.toNat_of_nonneg (sub_nonneg.mpr r62),
        Nat.cast_add]
      ring_nf; rw [←hr]
      exact Rat.log2_self_le x0
    · apply Nat.rdiv_le_of_le_mul
      simp only [← mul_assoc, mul_comm _ (2^(_:ℤ).toNat), ←pow_add, ←Nat.cast_le (α := ℚ),
        ← div_le_iff₀ d0, ae, Nat.cast_mul, Nat.cast_pow, Nat.cast_two]
      simp only [←zpow_natCast, ←zpow_sub₀ t0, Int.toNat_of_nonneg (sub_nonneg.mpr r62),
        Nat.cast_add]
      ring_nf; rw [←hr, add_comm]
      exact Rat.lt_log2_self.le

/-- Conversion from `ℚ`, taking absolute values and rounding up or down -/
@[irreducible, inline] def ofRat_abs (x : ℚ) (up : Bool) : Floating :=
  if x0 : x = 0 then 0 else
  let r := x.log2
  let n := x.num.natAbs
  -- Our floating point number will be roughly
  --   `y * 2^(s - 2^63)`
  -- where
  --   `y = y * 2^(62 - r)`
  --   `s = r - 62 + 2^63`
  let p := if r ≤ 62 then (n <<< (62 - r).toNat, x.den) else (n, x.den <<< (r - 62).toNat)
  let c := convert_tweak (p.1.rdiv p.2 up) (r - 62 + 2^63) (ofRat_norm x0)
  c.finish up

/-- Conversion from `ℚ`, rounding up or down -/
@[irreducible] def ofRat (x : ℚ) (up : Bool) : Floating :=
  let neg : Bool := decide (x < 0)
  let z := ofRat_abs x (up != neg)
  bif neg then -z else z

/-- `ofRat_abs` rounds the desired way -/
lemma approx_ofRat_abs (x : ℚ) (up : Bool) : ↑|x| ∈ rounds (approx (ofRat_abs x up)) !up := by
  rw [ofRat_abs]
  simp only
  by_cases x0 : x = 0
  · simp only [x0, abs_zero, Rat.cast_zero, Rat.zero_num, Int.natAbs_zero, Nat.zero_shiftLeft,
      Rat.zero_den, dite_true, ne_eq, zero_ne_nan, not_false_eq_true, approx_eq_singleton, val_zero,
      mem_rounds_singleton, Bool.not_eq_true', le_refl, ite_self]
  simp only [Rat.cast_abs, x0, dite_false]
  apply approx_convert
  generalize x.log2 = r
  generalize hn : x.num.natAbs = n
  have ae : (n : ℝ) / x.den = |(x:ℝ)| := by rw [Rat.abs_eq_div', hn]
  have t0 : (2:ℝ) ≠ 0 := by norm_num
  simp only [Nat.shiftLeft_eq, add_sub_cancel_right]
  by_cases r62 : r ≤ 62
  · simp only [r62, ite_true]
    induction up
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine le_trans (mul_le_mul_of_nonneg_right Nat.rdiv_le two_zpow_pos.le) ?_
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ←div_mul_eq_mul_div, ae,
        mul_assoc, pow_mul_zpow t0, Int.toNat_of_nonneg (sub_nonneg.mpr r62)]
      ring_nf; simp only [zpow_zero, mul_one, le_refl]
    · simp only [ite_true]
      refine le_trans ?_ (mul_le_mul_of_nonneg_right Nat.le_rdiv two_zpow_pos.le)
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ←div_mul_eq_mul_div, ae,
        mul_assoc, pow_mul_zpow t0, Int.toNat_of_nonneg (sub_nonneg.mpr r62)]
      ring_nf; simp only [zpow_zero, mul_one, le_refl]
  · simp only [r62, ite_false]
    replace r62 := (not_le.mp r62).le
    induction up
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine le_trans (mul_le_mul_of_nonneg_right Nat.rdiv_le two_zpow_pos.le) ?_
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast,
        Int.toNat_of_nonneg (sub_nonneg.mpr r62), ← div_div, ae, div_mul_cancel₀ _ (two_zpow_pos (𝕜 := ℝ)).ne', le_refl]
    · simp only [ite_true, ge_iff_le]
      refine le_trans ?_ (mul_le_mul_of_nonneg_right Nat.le_rdiv two_zpow_pos.le)
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ←div_mul_eq_mul_div, ae, ←zpow_natCast,
        mul_assoc, pow_mul_zpow t0, Int.toNat_of_nonneg (sub_nonneg.mpr r62), ←div_div,
        div_mul_cancel₀ _ (two_zpow_pos (𝕜 := ℝ)).ne', le_refl]

/-- `ofRat` rounds the desired way -/
lemma approx_ofRat (x : ℚ) (up : Bool) : ↑x ∈ rounds (approx (ofRat x up)) !up := by
  rw [ofRat]
  by_cases x0 : x < 0
  · simp only [Bool.cond_decide, x0, decide_true, Bool.xor_true, cond_true, approx_neg,
      rounds_neg, Bool.not_not, mem_neg, ←Rat.cast_neg, ←abs_of_neg x0]
    convert approx_ofRat_abs x _
    simp only [Bool.not_not]
  · simp only [Bool.cond_decide, x0, decide_false, Bool.xor_false, ite_false]
    convert approx_ofRat_abs x _
    rw [abs_of_nonneg (by linarith)]

/-- `approx_ofRat`, down version -/
lemma ofRat_le {x : ℚ} (h : ofRat x false ≠ nan) : (ofRat x false).val ≤ x := by
  simpa only [approx, h, ite_false, Bool.not_false, mem_rounds_singleton, ite_true] using
    approx_ofRat x false

/-- `approx_ofRat`, up version -/
lemma le_ofRat {x : ℚ} (h : ofRat x true ≠ nan) : x ≤ (ofRat x true).val := by
  simpa only [approx, h, ite_false, Bool.not_true, mem_rounds_singleton] using approx_ofRat x true

/-- Combined version, for use in `Interval` construction -/
lemma ofRat_le_ofRat {x : ℚ} (h : ofRat x true ≠ nan) :
    (ofRat x false).val ≤ (ofRat x true).val := by
  by_cases a : ofRat x false = nan
  · simp only [a, val_le_val, val_nan_le]
  · exact le_trans (ofRat_le a) (le_ofRat h)

/-!
## Conversion from `Float`
-/

/-- Convert a `Float` to `Floating`.  This could be fast, but we don't need it to be. -/
@[irreducible] def ofFloat (x : Float) (up : Bool) : Floating :=
  match x.toRatParts with
  | none => nan
  | some (y, s) =>
    let t : Int64 := s
    if s ≠ (t : ℤ) then nan else
    (ofInt y up).scaleB t

/-- `ofFloat` rounding is self-consistent -/
lemma ofFloat_le_ofFloat {x : Float} (n0 : ofFloat x false ≠ nan) (n1 : ofFloat x true ≠ nan) :
    (ofFloat x false).val ≤ (ofFloat x true).val := by
  rw [ofFloat] at n0 n1
  rw [ofFloat, ofFloat]
  generalize hx : x.toRatParts = p at n0 n1
  induction' p with a b
  · simp only [le_refl]
  · simp only [ite_not] at n0 n1 ⊢
    split_ifs at n0 n1 ⊢ with e
    · simp only [ne_eq, n0, not_false_eq_true, val_scaleB, n1, gt_iff_lt, two_zpow_pos,
        mul_le_mul_right]
      exact le_trans (ofInt_le (ne_nan_of_scaleB n0)) (le_ofInt (ne_nan_of_scaleB n1))
    · simp only [le_refl]
