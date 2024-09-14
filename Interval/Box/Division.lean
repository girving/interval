import Interval.Box.Basic
import Interval.Interval.Division

/-!
## `Box` inverse and division
-/

open Pointwise
open Set
open scoped Real
namespace Box

/-- `Box / Interval` via reciproval multiplication -/
@[irreducible] def div_scalar (z : Box) (x : Interval) : Box :=
  x⁻¹.mul_box z

/-- `Box` inversion via scalar division -/
instance : Inv Box where
  inv z := (star z).div_scalar z.normSq

lemma inv_def (z : Box) : z⁻¹ = (star z).div_scalar z.normSq := rfl

/-- `Box / Interval` is conservative -/
@[approx] lemma approx_div_scalar {z : Box} {x : Interval} :
    approx z / Complex.ofReal '' approx x ⊆ approx (z.div_scalar x) := by
  rw [Box.div_scalar, div_eq_inv_mul]
  refine subset_trans (mul_subset_mul ?_ subset_rfl) (Interval.approx_mul_box _ _)
  intro a
  simp only [Complex.ofReal_eq_coe, mem_inv, mem_image, forall_exists_index, and_imp]
  intro b m e
  use b⁻¹
  constructor
  · exact mem_approx_inv m
  · rw [Complex.ofReal_inv, e, inv_inv]

/-- `Box` inversion is conservative -/
noncomputable instance : ApproxInv Box ℂ where
  approx_inv z := by
    rw [Box.inv_def]
    intro w m
    simp only [mem_inv] at m
    rw [←inv_inv w]
    generalize w⁻¹ = z at m
    rw [Complex.inv_def, Box.div_scalar, mul_comm]
    apply Interval.approx_mul_box
    apply mul_mem_mul
    · apply mem_image_of_mem
      approx
    · exact mem_approx_star m
