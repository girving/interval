import Interval.Floating.Floor
import Interval.Interval.Basic

/-!
## `natFloor` for `Interval`
-/

open Set
open scoped Real
namespace Interval

/-- The greatest natural definitely `≤ x` (or 0 if that fails) -/
def natFloor (x : Interval) : ℕ :=
  x.lo.natFloor

@[simp] lemma natFloor_nan : (nan : Interval).natFloor = 0 := by decide +kernel

lemma natFloor_le {a : ℝ} {x : Interval} (ax : a ∈ approx x) : x.natFloor ≤ ⌊a⌋₊ := by
  rw [natFloor]
  by_cases xn : x = nan
  · simp [xn]
  simp only [approx, lo_eq_nan, xn, ↓reduceIte, mem_Icc] at ax
  exact le_trans (Floating.natFloor_le Floating.val_mem_approx) (Nat.floor_le_floor ax.1)
