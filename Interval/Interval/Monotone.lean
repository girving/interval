import Interval.Interval.Basic

/-!
## Approximating monotonic functions with intervals
-/

open Set
open scoped Real
namespace Interval

/-- If `f` is monotonic, we can approximate it as the union of endpoints -/
lemma mem_approx_of_monotone' {f : ℝ → ℝ} {a u v : ℝ} (fs : MonotoneOn f (Icc u v))
    (auv : a ∈ Icc u v) (x y : Interval) (ux : f u ∈ approx x) (vy : f v ∈ approx y) :
    f a ∈ approx (x ∪ y) := by
  by_cases xn : x = nan; · simp [xn]
  by_cases yn : y = nan; · simp [yn]
  simp only [approx, lo_eq_nan, xn, ↓reduceIte, mem_Icc, yn, lo_union, Floating.min_eq_nan, or_self,
    Floating.val_min, hi_union, ne_eq, hi_eq_nan, not_false_eq_true, Floating.val_max, min_le_iff,
    le_max_iff] at ux vy ⊢
  have uv : u ≤ v := by simp only [mem_Icc] at auv; linarith
  have h0 := fs (left_mem_Icc.mpr uv) auv auv.1
  have h1 := fs auv (right_mem_Icc.mpr uv) auv.2
  exact ⟨.inl (by linarith), .inr (by linarith)⟩

/-- If `f` is monotonic, we can approximate it as the union of endpoints -/
lemma mem_approx_of_antitone' {f : ℝ → ℝ} {a u v : ℝ} (fs : AntitoneOn f (Icc u v))
    (auv : a ∈ Icc u v) (x y : Interval) (ux : f u ∈ approx x) (vy : f v ∈ approx y) :
    f a ∈ approx (x ∪ y) := by
  by_cases xn : x = nan; · simp [xn]
  by_cases yn : y = nan; · simp [yn]
  simp only [approx, lo_eq_nan, xn, ↓reduceIte, mem_Icc, yn, lo_union, Floating.min_eq_nan, or_self,
    Floating.val_min, hi_union, ne_eq, hi_eq_nan, not_false_eq_true, Floating.val_max, min_le_iff,
    le_max_iff] at ux vy ⊢
  have uv : u ≤ v := by simp only [mem_Icc] at auv; linarith
  have h0 := fs (left_mem_Icc.mpr uv) auv auv.1
  have h1 := fs auv (right_mem_Icc.mpr uv) auv.2
  exact ⟨.inr (by linarith), .inl (by linarith)⟩

/-- If `f` is monotonic, we can approximate it as the union of endpoints -/
lemma mem_approx_of_monotone {f : ℝ → ℝ} {s : Set ℝ} (fs : MonotoneOn f s)
    (g : Floating → Interval) (fg : ∀ (a : ℝ) (x : Floating), a ∈ approx x → f a ∈ approx (g x))
    {a : ℝ} {x : Interval} (ax : a ∈ approx x) (xn : x ≠ nan)
    (as : a ∈ s) (ls : x.lo.val ∈ s) (hs : x.hi.val ∈ s) :
    f a ∈ approx (g x.lo ∪ g x.hi) := by
  simp only [approx, lo_eq_nan, xn, ↓reduceIte, mem_Icc] at ax
  simp only [approx, lo_union, Floating.min_eq_nan, lo_eq_nan, Floating.val_min, hi_union,
    mem_ite_univ_left, not_or, mem_Icc, min_le_iff, and_imp]
  intro n0 n1
  rw [Floating.val_max (hi_ne_nan n0) (hi_ne_nan n1), le_max_iff]
  constructor
  · left
    have m := fg x.lo.val x.lo (by approx)
    simp only [approx, lo_eq_nan, n0, ↓reduceIte, mem_Icc] at m
    exact le_trans m.1 (fs ls as ax.1)
  · right
    have m := fg x.hi.val x.hi (by approx)
    simp only [approx, lo_eq_nan, n1, ↓reduceIte, mem_Icc] at m
    exact le_trans (fs as hs ax.2) m.2

/-- If `f` is antitone, we can approximate it as the union of endpoints -/
lemma mem_approx_of_antitone {f : ℝ → ℝ} {s : Set ℝ} (fs : AntitoneOn f s)
    (g : Floating → Interval) (fg : ∀ (a : ℝ) (x : Floating), a ∈ approx x → f a ∈ approx (g x))
    {a : ℝ} {x : Interval} (ax : a ∈ approx x) (xn : x ≠ nan)
    (as : a ∈ s) (ls : x.lo.val ∈ s) (hs : x.hi.val ∈ s) :
    f a ∈ approx (g x.lo ∪ g x.hi) := by
  rw [← neg_neg (f a), ← neg_neg (_ ∪ _), approx_neg, union_neg, Set.neg_mem_neg]
  refine mem_approx_of_monotone fs.neg (g := fun x ↦ -g x) ?_ ax xn as ls hs
  intro _ _ ax; exact mem_approx_neg (fg _ _ ax)
