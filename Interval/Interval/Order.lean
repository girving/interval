import Interval.Interval.Basic

/-!
## Interval orderings

We define `≤, <` on `Interval` such that if they are true, we know the corresponding operator holds
on any approximated reals. This unfortunately means that we don't get a `Preorder`, since
reflexivity fails.
-/

open Set
open scoped Real
namespace Interval

-- Interval comparison
def blt (x y : Interval) : Bool := x != nan && x.hi.blt y.lo
def ble (x y : Interval) : Bool := x != nan && x.hi.ble y.lo

-- Ordering instances
instance : LT Interval where lt x y := x.blt y
instance : LE Interval where le x y := x.ble y
instance : DecidableRel (α := Interval) (· < ·) | a, b => by dsimp [LT.lt]; infer_instance
instance : DecidableRel (α := Interval) (· ≤ ·) | a, b => by dsimp [LE.le]; infer_instance

/-- Interval <, expanded -/
lemma lt_def (x y : Interval) : x < y ↔ x ≠ nan ∧ x.hi < y.lo := by
  trans (x.blt y = true)
  · rfl
  · simp [blt, Floating.blt_eq_lt]

/-- Interval ≤, expanded -/
lemma le_def (x y : Interval) : x ≤ y ↔ x ≠ nan ∧ x.hi ≤ y.lo := by
  trans (x.ble y = true)
  · rfl
  · simp [ble, Floating.ble_eq_le]

/-!
### Transitivity and antisymmetry

As advised in https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Idiomatic.20notation.20for.20interval.20comparison/near/472576792.
-/

/-- `< → ≤` -/
lemma le_of_lt' {x y : Interval} (xy : x < y) : x ≤ y := by
  simp only [le_def, lt_def, Floating.val_le_val, Floating.val_lt_val] at xy ⊢
  exact ⟨xy.1, xy.2.le⟩

/-- `≤` is transitive -/
lemma le_trans' {x y z : Interval} (xy : x ≤ y) (yz : y ≤ z) : x ≤ z := by
  simp only [le_def, Floating.val_le_val] at xy yz ⊢
  exact ⟨xy.1, by linarith [y.le]⟩

/-- `<` and `≤` compose -/
lemma lt_of_le_of_lt' {x y z : Interval} (xy : x ≤ y) (yz : y < z) : x < z := by
  simp only [le_def, lt_def, Floating.val_le_val, Floating.val_lt_val] at xy yz ⊢
  exact ⟨xy.1, by linarith [y.le]⟩

/-- `<` and `<` compose -/
lemma lt_of_lt_of_le' {x y z : Interval} (xy : x < y) (yz : y ≤ z) : x < z := by
  simp only [le_def, lt_def, Floating.val_le_val, Floating.val_lt_val] at xy yz ⊢
  exact ⟨xy.1, by linarith [y.le]⟩

/-- `<` and `<` compose -/
lemma lt_trans' {x y z : Interval} (xy : x < y) (yz : y < z) : x < z := by
  simp only [lt_def, Floating.val_lt_val] at xy yz ⊢
  exact ⟨xy.1, by linarith [y.le]⟩

/-- `<` is asymmetric -/
lemma lt_asymm' {x y : Interval} (xy : x < y) : ¬y < x := by
  simp only [lt_def, Floating.val_lt_val] at xy ⊢
  by_cases yn : y = nan
  · simp [yn]
  · simp [yn]; linarith [x.le, y.le]

/-- `≤` is transitive -/
instance : IsTrans Interval (· ≤ ·) where
  trans _ _ _ xy yz := Interval.le_trans' xy yz

/-- `<` is transitive -/
instance : IsTrans Interval (· < ·) where
  trans _ _ _ xy yz := Interval.lt_trans' xy yz

/-- `<` is asymmetric -/
instance : IsAsymm Interval (· < ·) where
  asymm _ _ xy := Interval.lt_asymm' xy

/-!
### Interval comparison approximates real comparison
-/

/-- If we know `x < y` for intervals, we know it for approximated reals -/
lemma approx_lt (x y : Interval) (a b : ℝ) (ax : a ∈ approx x) (ay : b ∈ approx y) (xy : x < y) :
    a < b := by
  simp only [lt_def, Floating.val_lt_val, ne_eq] at xy
  rcases xy with ⟨xn, lt⟩
  have yn : y.lo ≠ nan := Floating.ne_nan_of_le (x.hi_ne_nan xn) (by linarith)
  simp only [approx, Interval.lo_eq_nan, xn, ↓reduceIte, Set.mem_Icc, yn] at ax ay
  linarith

/-- If we know `x ≤ y` for intervals, we know it for approximated reals -/
lemma approx_le (x y : Interval) (a b : ℝ) (ax : a ∈ approx x) (ay : b ∈ approx y) (xy : x ≤ y) :
    a ≤ b := by
  simp only [le_def, Floating.val_le_val, ne_eq] at xy
  rcases xy with ⟨xn, le⟩
  have yn : y.lo ≠ nan := Floating.ne_nan_of_le (x.hi_ne_nan xn) (by linarith)
  simp only [approx, Interval.lo_eq_nan, xn, ↓reduceIte, Set.mem_Icc, yn] at ax ay
  linarith
