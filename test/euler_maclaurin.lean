/-
Copyright (c) 2026 Peter Shiller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Shiller
-/
import Interval.EulerMaclaurin.EulerMaclaurin
import Interval.EulerMaclaurin.RemainderBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
### Unit tests for the Euler-Maclaurin formula

These examples instantiate the formula in several forms: the general formula for a family of
derivatives, with integer end points and at an end point that is not an integer; the formula for a
`C^p` function, with its iterated derivatives within `[0, n]` evaluated; and the form for
`trapezoid_sum`, for a family of derivatives and for a `C^k` function on a set other than the one
used for the Gamma function. They also apply the error bounds with the constants `4 / 6 ^ p`,
`|bernoulli (2 * m)| / (2 * m)!` and `sawBound p`, and the explicit bounds for `bernoulliFun` and
`saw` at small orders. The `#print axioms` checks at the end cover ten theorems.
-/

open EulerMaclaurin MeasureTheory

open scoped Nat

/-- The derivatives of `t ↦ t ^ 2`: `t ^ 2`, `2 * t`, `2` and then `0`. -/
noncomputable def sqFamily : ℕ → ℝ → ℝ
  | 0 => fun t ↦ t ^ 2
  | 1 => fun t ↦ 2 * t
  | 2 => fun _ ↦ 2
  | _ + 3 => fun _ ↦ 0

/-- `sqFamily (k + 1)` is the derivative of `sqFamily k`. -/
theorem hasDerivAt_sqFamily (k : ℕ) (x : ℝ) :
    HasDerivAt (sqFamily k) (sqFamily (k + 1) x) x := by
  match k with
  | 0 => simpa [sqFamily] using hasDerivAt_pow 2 x
  | 1 => simpa [sqFamily] using (hasDerivAt_id x).const_mul (2 : ℝ)
  | 2 => simpa [sqFamily] using hasDerivAt_const x (2 : ℝ)
  | _ + 3 => exact hasDerivAt_const x (0 : ℝ)

/-- The iterated derivatives of `t ↦ t ^ 2` are the functions `sqFamily k`. -/
theorem iteratedDeriv_sq (k : ℕ) : iteratedDeriv k (fun t : ℝ ↦ t ^ 2) = sqFamily k := by
  induction k with
  | zero => exact iteratedDeriv_zero
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (hasDerivAt_sqFamily k x).deriv

/-- **Faulhaber's formula** `∑_{i = 1}^{n} i ^ 2 = n ^ 3 / 3 + n ^ 2 / 2 + n / 6` is the formula
of order `3` for `t ↦ t ^ 2`, whose remainder integral is zero. -/
example (n : ℕ) :
    ∑ i ∈ Finset.Ioc (0 : ℤ) n, (i : ℝ) ^ 2 = (n : ℝ) ^ 3 / 3 + (n : ℝ) ^ 2 / 2 + n / 6 := by
  have h := sum_Ioc_int_eq_integral_add_of_hasDerivWithinAt (p := 3) (F := sqFamily) (a := 0)
    (b := n) (by norm_num) (Int.natCast_nonneg n)
    (fun k _ x _ ↦ (hasDerivAt_sqFamily k x).hasDerivWithinAt)
    (by simp [sqFamily])
  have hrem : (∫ t in ((0 : ℤ) : ℝ)..((n : ℤ) : ℝ),
      periodizedBernoulli 3 t • sqFamily 3 t) = 0 := by
    simp [sqFamily]
  have hint : (∫ t in ((0 : ℤ) : ℝ)..((n : ℤ) : ℝ), sqFamily 0 t) = (n : ℝ) ^ 3 / 3 := by
    norm_num [sqFamily, integral_pow]
  have hsum : ∑ k ∈ Finset.range 3, ((bernoulli' (k + 1) : ℝ) / ((k + 1)! : ℝ)) •
        (sqFamily k ((n : ℤ) : ℝ) - sqFamily k ((0 : ℤ) : ℝ)) = (n : ℝ) ^ 2 / 2 + n / 6 := by
    norm_num [Finset.sum_range_succ, bernoulli'_one, bernoulli'_two, bernoulli'_three,
      Nat.factorial, sqFamily]
    ring
  rw [hrem, hint, hsum] at h
  simp only [sqFamily, smul_eq_mul] at h
  push_cast at h
  linarith

/-- **Faulhaber's formula** for the trapezoidal sum of `t ↦ t ^ 2`: the formula of order `3` for a
family of derivatives, in the form used for `trapezoid_sum`. The boundary terms are
`saw 2 0 * (2 * n) = n / 6` and a term which vanishes, and the remainder is zero. -/
example (n : ℕ) : trapezoid_sum (sqFamily 0) 0 n = (n : ℝ) ^ 3 / 3 + n / 6 := by
  have h := trapezoid_sum_eq_integral_add_of_hasDerivWithinAt (s := 2) (a := 0) (n := n)
    (F := sqFamily) (fun k _ x _ ↦ (hasDerivAt_sqFamily k x).hasDerivWithinAt)
    (by simp [sqFamily])
  refine h.trans ?_
  norm_num [sqFamily, integral_pow, Finset.sum_range_succ, saw_eval_zero, bernoulli_two,
    Nat.factorial]
  ring

/-- **Faulhaber's formula** from the formula for a `C^p` function. The boundary terms are the
iterated derivatives of `t ↦ t ^ 2` within `[0, n]`, which `iteratedDerivWithin_eq_iteratedDeriv`
evaluates, and the remainder vanishes because the third derivative is zero. -/
example (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ Finset.Ioc (0 : ℤ) n, (i : ℝ) ^ 2 = (n : ℝ) ^ 3 / 3 + (n : ℝ) ^ 2 / 2 + n / 6 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc : ∀ k : ℕ, ContDiff ℝ k (fun t : ℝ ↦ t ^ 2) := fun _ ↦ contDiff_id.pow 2
  have hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) n) := uniqueDiffOn_Icc (by exact_mod_cast hn)
  have hd : ∀ k : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) n,
      iteratedDerivWithin k (fun t : ℝ ↦ t ^ 2) (Set.Icc 0 n) x = sqFamily k x :=
    fun k x hx ↦ by
      rw [iteratedDerivWithin_eq_iteratedDeriv hU (hc k).contDiffAt hx, iteratedDeriv_sq]
  have hdn : ∀ k : ℕ, iteratedDerivWithin k (fun t : ℝ ↦ t ^ 2) (Set.Icc 0 n) n = sqFamily k n :=
    fun k ↦ hd k n ⟨hn0, le_rfl⟩
  have hd0 : ∀ k : ℕ, iteratedDerivWithin k (fun t : ℝ ↦ t ^ 2) (Set.Icc 0 n) 0 = sqFamily k 0 :=
    fun k ↦ hd k 0 ⟨le_rfl, hn0⟩
  have hrem : (∫ t in (0 : ℝ)..n,
      periodizedBernoulli 3 t • iteratedDerivWithin 3 (fun t : ℝ ↦ t ^ 2) (Set.Icc 0 n) t) = 0 := by
    refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans (by simp)
    rw [Set.uIcc_of_le hn0] at ht
    rw [hd 3 t ht]
    simp [sqFamily]
  have h := EulerMaclaurin.sum_Ioc_eq_integral_add (f := fun t : ℝ ↦ t ^ 2) (p := 3) three_ne_zero
    hn0 (hc 3).contDiffOn
  simp only [hdn, hd0, hrem] at h
  norm_num [Finset.sum_range_succ, integral_pow, bernoulli_one, bernoulli_two, Nat.factorial,
    sqFamily] at h
  linarith

/-- The formula at an end point that is not an integer. For `t ↦ 2 * t` on `[0, 5 / 2]` with
`p = 2`, the sum `2 * 1 + 2 * 2` over the integers in `(0, 5 / 2]` is the integral `25 / 4` plus
boundary terms. The term of order `1` vanishes, because `periodizedBernoulli 1 (5 / 2) = 0` and the
function is zero at `0`. The term of order `2` is
`periodizedBernoulli 2 (5 / 2) - periodizedBernoulli 2 0 = -1 / 12 - 1 / 6 = -1 / 4`, because the
derivative of `2 * t` is `2` and `(1 / 2!) * 2 = 1`. The remainder is zero. -/
example : ∑ i ∈ Finset.Ioc ⌊(0 : ℝ)⌋ ⌊(5 / 2 : ℝ)⌋, sqFamily 1 (i : ℝ) = 25 / 4 - 1 / 4 := by
  have hmem : (5 / 2 : ℝ) ∈ Set.Ico ((2 : ℤ) : ℝ) (((2 : ℤ) : ℝ) + 1) := by norm_num
  have hP1 : periodizedBernoulli 1 (5 / 2 : ℝ) = 0 := by
    rw [periodizedBernoulli_coe_of_mem_Ico_intCast hmem, bernoulliFun_one]
    norm_num
  have hP2 : periodizedBernoulli 2 (5 / 2 : ℝ) = -1 / 12 := by
    rw [periodizedBernoulli_coe_of_mem_Ico_intCast hmem, bernoulliFun_two]
    norm_num
  refine (sum_Ioc_eq_integral_add_of_hasDerivWithinAt (p := 2) (F := fun k ↦ sqFamily (k + 1))
    two_ne_zero (by norm_num)
    (fun k _ x _ ↦ (hasDerivAt_sqFamily (k + 1) x).hasDerivWithinAt)
    (by simp [sqFamily])).trans ?_
  have hint : (∫ t in (0 : ℝ)..5 / 2, 2 * t) = 25 / 4 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    norm_num
  norm_num [Finset.sum_range_succ, hP1, hP2, hint, sqFamily, bernoulli_two, Nat.factorial]

/-- The formula for `C^k` functions applies on a set other than the one used for the Gamma
function: here the exponential function on the whole line, with `s = 0`. -/
example (a : ℤ) (n : ℕ) :
    trapezoid_sum Real.exp a n = (∫ x in (a : ℝ)..a + n, Real.exp x) +
      ∑ m ∈ Finset.range 0, (-1 : ℝ) ^ m • saw (m + 2) 0 •
        (iteratedDerivWithin (m + 1) Real.exp Set.univ (a + n) -
          iteratedDerivWithin (m + 1) Real.exp Set.univ a) +
      (-1 : ℝ) ^ 0 • ∫ x in (a : ℝ)..a + n, saw (0 + 1) x •
        iteratedDerivWithin (0 + 1) Real.exp Set.univ x :=
  trapezoid_sum_eq_integral_add (s := 0) Real.contDiff_exp.contDiffOn uniqueDiffOn_univ
    (Set.subset_univ _)

/-- The bound for the Bernoulli polynomials at `k = 2` and `x = 1 / 2`: `|B_2(1 / 2)| = 1 / 12`
is below `4 * 2! / 6 ^ 2 = 2 / 9`. -/
example : |bernoulliFun 2 (1 / 2 : ℝ)| ≤ 4 * (2 ! : ℝ) / 6 ^ 2 :=
  abs_bernoulliFun_le_four_mul_factorial_div_six_pow 2 ⟨by norm_num, by norm_num⟩

/-- The rational bound holds in degree `1` as well: `|B_1(0)| = 1 / 2 ≤ 4 * 1! / 6`. -/
example : |bernoulliFun 1 (0 : ℝ)| ≤ 4 * (1 ! : ℝ) / 6 ^ 1 :=
  abs_bernoulliFun_le_four_mul_factorial_div_six_pow 1 ⟨le_rfl, zero_le_one⟩

/-- `sawBound` has an explicit bound in odd order: `|saw 3 x| ≤ 4 / 6 ^ 3 = 1 / 54`. -/
example (x : ℝ) : |saw 3 x| ≤ 1 / 54 :=
  (abs_saw_le 3 x).trans ((sawBound_le_four_div_six_pow 3).trans_eq (by norm_num))

/-- The error bound of the general formula with the constant `sawBound p` of `abs_saw_le`: the
bound `D = bernoulliBound p` (`abs_bernoulliFun_le`) gives `D / p ! = sawBound p`. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {p : ℕ}
    (hp : p ≠ 0) {F : ℕ → ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ k < p, ∀ x ∈ Set.Icc a b, HasDerivWithinAt (F k) (F (k + 1) x) (Set.Icc a b) x)
    (hFp : IntervalIntegrable (F p) volume a b) :
    ‖∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F 0 (i : ℝ) - (∫ t in a..b, F 0 t) -
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • F k b - periodizedBernoulli (k + 1) a • F k a)‖ ≤
      sawBound p * ∫ t in a..b, ‖F p t‖ :=
  (norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt hp hab
    (fun x hx ↦ abs_bernoulliFun_le p x hx) hF hFp).trans_eq (by rw [sawBound, div_eq_inv_mul])

/-- The error bound with the rational constant, in every order, for the exponential function,
whose derivatives are all `Real.exp`: the error is at most `4 / 6 ^ p * (exp b - exp a)`. -/
example {p : ℕ} (hp : p ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    ‖∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Real.exp i - (∫ t in a..b, Real.exp t) -
        ∑ k ∈ Finset.range p, ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • Real.exp b -
            periodizedBernoulli (k + 1) a • Real.exp a)‖ ≤
      4 / 6 ^ p * (Real.exp b - Real.exp a) := by
  simpa only [Real.norm_eq_abs, Real.abs_exp, integral_exp] using
    norm_sum_Ioc_sub_integral_sub_le_of_hasDerivWithinAt (F := fun _ ↦ Real.exp) hp hab
      (fun _ _ x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (Real.continuous_exp.intervalIntegrable a b)

/-- The classical error bound in even order for the exponential function: the error of the formula
of order `2 * m` is at most `|B_{2m}| / (2m)! * (exp b - exp a)`. -/
example {m : ℕ} (hm : m ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    ‖∑ i ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Real.exp i - (∫ t in a..b, Real.exp t) -
        ∑ k ∈ Finset.range (2 * m), ((-1 : ℝ) ^ (k + 1) / ((k + 1)! : ℝ)) •
          (periodizedBernoulli (k + 1) b • Real.exp b -
            periodizedBernoulli (k + 1) a • Real.exp a)‖ ≤
      |(bernoulli (2 * m) : ℝ)| / (2 * m)! * (Real.exp b - Real.exp a) := by
  simpa only [Real.norm_eq_abs, Real.abs_exp, integral_exp] using
    norm_sum_Ioc_sub_integral_sub_le_abs_bernoulli_of_hasDerivWithinAt (F := fun _ ↦ Real.exp)
      hm hab (fun _ _ x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (Real.continuous_exp.intervalIntegrable a b)

/-- `simp` evaluates the periodized Bernoulli polynomial at an integer. -/
example (k : ℕ) (m : ℤ) : periodizedBernoulli k (m : ℝ) = bernoulli k := by simp

/-- `simp` evaluates the periodized Bernoulli polynomial at the real number `0`. -/
example (k : ℕ) : periodizedBernoulli k (0 : ℝ) = bernoulli k := by simp

/--
info: 'trapezoid_sum_eq_integral_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms trapezoid_sum_eq_integral_add

/--
info: 'trapezoid_sum_eq_integral_add_of_hasDerivWithinAt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms trapezoid_sum_eq_integral_add_of_hasDerivWithinAt

/--
info: 'EulerMaclaurin.sum_Ioc_eq_integral_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms EulerMaclaurin.sum_Ioc_eq_integral_add

/--
info: 'EulerMaclaurin.sum_Ioc_eq_integral_add_of_hasDerivWithinAt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms EulerMaclaurin.sum_Ioc_eq_integral_add_of_hasDerivWithinAt

/--
info: 'EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le

/--
info: 'EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms norm_sum_Ioc_sub_integral_sub_le_of_abs_bernoulliFun_le_of_hasDerivWithinAt

/--
info: 'EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_hasDerivWithinAt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_of_hasDerivWithinAt

/--
info: 'EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_abs_bernoulli_of_hasDerivWithinAt'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms EulerMaclaurin.norm_sum_Ioc_sub_integral_sub_le_abs_bernoulli_of_hasDerivWithinAt

/--
info: 'abs_bernoulliFun_le_four_mul_factorial_div_six_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abs_bernoulliFun_le_four_mul_factorial_div_six_pow

/--
info: 'sawBound_le_four_div_six_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sawBound_le_four_div_six_pow
