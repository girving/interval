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
  x⁻¹ • z

/-- `Box` inversion via scalar division -/
instance : Inv Box where
  inv z := (star z).div_scalar z.normSq

lemma inv_def (z : Box) : z⁻¹ = (star z).div_scalar z.normSq := rfl

/-- `Box / Interval` is conservative -/
@[approx] lemma approx_div_scalar {w : ℂ} {a : ℝ} {z : Box} {x : Interval} (wz : w ∈ approx z)
    (ax : a ∈ approx x) : w / a ∈ approx (z.div_scalar x) := by
  rw [Box.div_scalar, div_eq_inv_mul, ← Complex.ofReal_inv, ← smul_eq_mul, Complex.coe_smul]
  approx

/-- `Box` inversion is conservative -/
noncomputable instance : ApproxInv Box ℂ where
  approx_inv z := by
    rw [Box.inv_def]
    intro w m
    simp only [mem_inv] at m
    rw [←inv_inv w]
    generalize w⁻¹ = z at m
    rw [Complex.inv_def, Box.div_scalar, mul_comm, ← smul_eq_mul, Complex.coe_smul]
    exact mem_approx_smul (by approx) (mem_approx_star m)
