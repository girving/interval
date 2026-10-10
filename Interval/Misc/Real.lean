module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Interval.Tactic.Approx

/-!
## `ℝ` lemmas
-/

public section

open Classical
open Pointwise

open Set
open scoped Real

variable {α 𝕜 𝕝 𝕤 : Type}
variable [Field 𝕝]
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [Semifield 𝕤] [LinearOrder 𝕤] [IsStrictOrderedRing 𝕤]


/-- Simplify to case assuming not `nan` -/
lemma mem_if_univ_iff {x : α} {u : Set α} {p : Prop} {dp : Decidable p} :
    x ∈ @ite _ p dp univ u ↔ ¬p → x ∈ u := by
  by_cases n : p
  repeat simp only [n, ite_true, ite_false, mem_univ, not_true_eq_false, IsEmpty.forall_iff,
    not_false_eq_true, forall_true_left]

/-- Simplify to case assuming not `nan` -/
lemma subset_if_univ_iff {t u : Set α} {p : Prop} {dp : Decidable p} :
    t ⊆ @ite _ p dp univ u ↔ ¬p → t ⊆ u := by
  by_cases n : p
  repeat simp only [n, ite_true, ite_false, subset_univ, not_true_eq_false, IsEmpty.forall_iff,
    not_false_eq_true, forall_true_left]

/-- Reals are either `≤ 0` or `≥ 0` -/
lemma nonpos_or_nonneg (x : 𝕜) : x ≤ 0 ∨ 0 ≤ x := by
  by_cases p : 0 ≤ x
  · right; assumption
  · left; linarith

/-- The range of nonzero multiplication is `univ` -/
@[simp] lemma range_mul_right_eq_univ {a : 𝕝} (a0 : a ≠ 0) : range (fun x ↦ x * a) = univ := by
  simp only [eq_univ_iff_forall, mem_range]
  intro x; use x / a
  simp only [div_mul_cancel₀ _ a0]

/-- Multiplying by a nonzero preserves `univ` -/
@[simp] lemma Set.univ_mul_singleton {a : 𝕝} (a0 : a ≠ 0) : univ * ({a} : Set 𝕝) = univ := by
  simp only [mul_singleton, image_univ, range_mul_right_eq_univ a0]

/-- Multiplying an `Icc` by a positive number produces the expected `Icc` -/
@[simp] lemma Set.Icc_mul_singleton {a b x : 𝕜} (x0 : 0 < x) :
    Icc a b * {x} = Icc (a * x) (b * x) := by
  simp only [mul_singleton]
  ext y; simp only [mem_image, mem_Icc]
  constructor
  · intro ⟨z, ⟨hz1, hz2⟩, hz3⟩; exact ⟨by nlinarith, by nlinarith⟩
  · intro ⟨h0,h1⟩; use y / x
    simp only [le_div_iff₀ x0, h0, div_le_iff₀ x0, h1, and_self, div_mul_cancel₀ _ x0.ne']

/-- Negative `c` version of `image_mul_right_Icc` -/
theorem image_mul_right_Icc_of_neg {a b c : 𝕜} (c0 : c < 0) :
    (fun x ↦ x * c) '' Icc a b = Icc (b * c) (a * c) := by
  ext x
  simp only [mem_image, mem_Icc]
  constructor
  · intro ⟨y,⟨ay,yb⟩,yc⟩; rw [←yc]; constructor
    · exact mul_le_mul_of_nonpos_right yb c0.le
    · exact mul_le_mul_of_nonpos_right ay c0.le
  · intro ⟨bc,ac⟩; use x/c; refine ⟨⟨?_,?_⟩,?_⟩
    · simpa only [le_div_iff_of_neg c0]
    · simpa only [div_le_iff_of_neg c0]
    · simp only [div_mul_cancel₀ _ c0.ne]

/-- A simple lemma that we use a lot -/
@[simp] lemma two_pow_pos {R : Type} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] {n : ℕ} :
    0 < (2:R) ^ n :=
  pow_pos (by norm_num) _

/-- A simple lemma that we use a lot -/
@[simp] lemma two_zpow_pos {n : ℤ} : 0 < (2 : 𝕜) ^ n :=
  zpow_pos (by norm_num) _

/-- Writing `not_lt.mpr two_zpow_pos` fails to infer inside `simp`, so we write this out -/
@[simp] lemma two_zpow_not_nonpos {n : ℤ} : ¬(2 : 𝕜) ^ n ≤ 0 :=
  not_le.mpr two_zpow_pos

/-- Writing `not_lt.mpr two_zpow_pos.le` fails to infer inside `simp`, so we write this out -/
@[simp] lemma two_zpow_not_neg {n : ℤ} : ¬(2 : 𝕜) ^ n < 0 :=
  not_lt.mpr two_zpow_pos.le

/-- The range of two power multiplication is `univ` -/
@[simp] lemma range_mul_two_zpow_eq_univ {n : ℤ} : range (fun x : 𝕜 ↦ x * 2^n) = univ :=
  range_mul_right_eq_univ two_zpow_pos.ne'

/-- Multiplying an `Icc` by a two power is nice -/
@[simp] lemma Set.Icc_mul_two_zpow {a b : 𝕜} {n : ℤ} :
    Icc a b * {2^n} = Icc (a * 2^n) (b * 2^n) := Icc_mul_singleton two_zpow_pos

/-- `Icc` commutes with `⁻¹` if we're positive -/
lemma Set.inv_Icc₀ {a b : 𝕜} (a0 : 0 < a) (b0 : 0 < b) : (Icc a b)⁻¹ = Icc b⁻¹ a⁻¹ := by
  ext x
  simp only [mem_inv, mem_Icc, and_comm]
  by_cases x0 : x ≤ 0
  · have i0 : x⁻¹ ≤ 0 := inv_nonpos.mpr x0
    simp only [(by linarith : ¬a ≤ x⁻¹), false_and, false_iff, not_and, not_le,
      lt_of_le_of_lt x0 (inv_pos.mpr b0), implies_true]
  · simp only [not_le] at x0
    simp only [le_inv_comm₀ x0 a0, inv_le_comm₀ b0 x0]

/-- `pow` and `zpow` multiply via addition -/
lemma pow_mul_zpow {a : 𝕝} (a0 : a ≠ 0) (b : ℕ) (c : ℤ) : a^b * a^c = a^(b + c) := by
  simp only [zpow_add₀ a0, zpow_natCast]

/-- `zpow` and `pow` divide via subtraction -/
lemma zpow_mul_pow {a : 𝕝} (a0 : a ≠ 0) (b : ℤ) (c : ℕ) : a^b * a^c = a^(b + c) := by
  simp only [zpow_add₀ a0, zpow_natCast]

/-- `pow` and `zpow` multiply via addition -/
lemma zpow_div_pow {a : 𝕝} (a0 : a ≠ 0) (b : ℤ) (c : ℕ) : a^b / a^c = a^(b - c) := by
  simp only [zpow_sub₀ a0, zpow_natCast]

/-- `-` and `⁻¹` commute on `Set ℝ` -/
@[simp] lemma Set.inv_neg {s : Set 𝕝} : (-s)⁻¹ = -s⁻¹ := by
  ext x; simp only [_root_.inv_neg, mem_neg, mem_inv]

/-- `x - y ≤ x + z ↔ -y ≤ z` -/
@[simp] lemma sub_le_add_iff_left (x y z : 𝕜) : x - y ≤ x + z ↔ -y ≤ z := by
  simp only [sub_eq_add_neg, add_le_add_iff_left]

/-- `x + y ≤ x - z ↔ y ≤ -z` -/
@[simp] lemma add_le_sub_iff_left (x y z : 𝕜) : x + y ≤ x - z ↔ y ≤ -z := by
  simp only [sub_eq_add_neg, add_le_add_iff_left]

set_option maxHeartbeats 1000000 in
/-- Rewrite `Icc * Icc ⊆ Icc` in terms of inequalities -/
lemma Icc_mul_Icc_subset_Icc {a b c d x y : ℝ} (ab : a ≤ b) (cd : c ≤ d) :
    Icc a b * Icc c d ⊆ Icc x y ↔
      x ≤ a * c ∧ x ≤ a * d ∧ x ≤ b * c ∧ x ≤ b * d ∧
      a * c ≤ y ∧ a * d ≤ y ∧ b * c ≤ y ∧ b * d ≤ y := by
  have am : a ∈ Icc a b := left_mem_Icc.mpr ab
  have bm : b ∈ Icc a b := right_mem_Icc.mpr ab
  have cm : c ∈ Icc c d := left_mem_Icc.mpr cd
  have dm : d ∈ Icc c d := right_mem_Icc.mpr cd
  simp only [←image2_mul, image2_subset_iff]
  constructor
  · intro h
    simp only [mem_Icc (a := x)] at h
    exact ⟨(h _ am _ cm).1, (h _ am _ dm).1, (h _ bm _ cm).1, (h _ bm _ dm).1,
           (h _ am _ cm).2, (h _ am _ dm).2, (h _ bm _ cm).2, (h _ bm _ dm).2⟩
  · simp only [mem_Icc]
    rintro ⟨xac,xad,xbc,xbd,acy,ady,bcy,bdy⟩ u ⟨au,ub⟩ v ⟨cv,vd⟩
    all_goals cases nonpos_or_nonneg c
    all_goals cases nonpos_or_nonneg d
    all_goals cases nonpos_or_nonneg u
    all_goals cases nonpos_or_nonneg v
    all_goals exact ⟨by nlinarith, by nlinarith⟩

omit [IsStrictOrderedRing 𝕜] in
/-- Rewrite `Icc^2 ⊆ Icc` in terms of inequalities -/
lemma sqr_Icc_subset_Icc {a b x y : 𝕜} :
    (fun x ↦ x^2) '' Icc a b ⊆ Icc x y ↔ ∀ u, a ≤ u → u ≤ b → x ≤ u^2 ∧ u^2 ≤ y := by
  simp only [subset_def, mem_image, mem_Icc, forall_exists_index, and_imp]
  constructor
  · intro h u au ub; exact h _ u au ub rfl
  · intro h u v av vb vu; rw [←vu]; exact h v av vb
