import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Abs
import Mathlib.Tactic.Bound

/-!
# L'Hopital's rule over any normed field
-/

open Filter
open Set
open scoped Topology

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

@[bound] lemma norm_sub_norm_le_norm_add {E : Type*} [SeminormedAddGroup E] (x y : E) :
    ‖x‖ - ‖y‖ ≤ ‖x + y‖ := by simpa using norm_sub_norm_le x (-y)

attribute [bound] norm_add_le

/-- L'Hôpital's rule using derivatives at a point, general field version -/
theorem lhopital_field {f g : 𝕜 → 𝕜} {a f' g' : 𝕜} (df : HasDerivAt f f' a) (dg : HasDerivAt g g' a)
    (g'0 : g' ≠ 0) (f0 : f a = 0) (g0 : g a = 0) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) (𝓝 (f' / g')) := by
  simp only [Metric.tendsto_nhds, NormedAddGroup.dist_eq, eventually_nhdsWithin_iff,
    mem_compl_iff, mem_singleton_iff]
  intro e ep
  simp only [hasDerivAt_iff_isLittleO, f0, sub_zero, smul_eq_mul, Asymptotics.isLittleO_iff,
    g0] at df dg
  have g'p : 0 < ‖g'‖ := norm_pos_iff.mpr g'0
  generalize hb : 2 * (1 + ‖f' / g'‖) / ‖g'‖ = b
  generalize hc : min (e / 2 / b) (2⁻¹ * ‖g'‖) = c
  have b0 : 0 < b := by
    rw [← hb]
    refine div_pos (mul_pos (by norm_num) ?_) g'p
    exact add_pos_of_pos_of_nonneg (by bound) (by bound)
  have c0 : 0 < c := by bound
  have cb : c * b < e := by
    simp only [← hc]
    calc min (e / 2 / b) (2⁻¹ * ‖g'‖) * b
      _ ≤ (e / 2 / b) * b := by bound
      _ = e / 2 := by field_simp [b0.ne']; ring
      _ < e := by bound
  have cg : c ≤ 2⁻¹ * ‖g'‖ := by bound
  clear hc
  filter_upwards [df c0, dg c0]
  intro x fx gx xa
  generalize hy : x - a = y at fx gx
  have y0 : y ≠ 0 := by simpa only [← hy, sub_ne_zero]
  have yp : 0 < ‖y‖ := norm_pos_iff.mpr y0
  have lo : ‖g x‖ ≥ 2⁻¹ * ‖g'‖ * ‖y‖ := by
    calc ‖g x‖
      _ = ‖y * g' + (g x - y * g')‖ := by ring_nf
      _ ≥ ‖y * g'‖ - ‖g x - y * g'‖ := by bound
      _ ≥ ‖y * g'‖ - c * ‖y‖ := by bound
      _ = (‖g'‖ - c) * ‖y‖ := by simp only [sub_mul, norm_mul, mul_comm]
      _ ≥ (‖g'‖ - 2⁻¹ * ‖g'‖) * ‖y‖ := by bound
      _ = 2⁻¹ * ‖g'‖ * ‖y‖ := by ring
  have dg0 : g x ≠ 0 := by
    contrapose lo
    simp only [ne_eq, not_not] at lo
    simp only [lo, norm_zero, ge_iff_le, not_le]
    bound
  calc ‖f x / g x - f' / g'‖
    _ = ‖(f x - y * f') / g x + (y * f' / g x - f' / g')‖ := by ring_nf
    _ ≤ ‖(f x - y * f') / g x‖ + ‖y * f' / g x - f' / g'‖ := by bound
    _ = ‖(f x - y * f')‖ / ‖g x‖ + ‖y * f' / g x - f' / g'‖ := by simp only [norm_div]
    _ ≤ c * ‖y‖ / ‖g x‖ + ‖y * f' / g x - f' / g'‖ := by bound
    _ = (c * ‖y‖ + ‖y * f' - f' / g' * g x‖) / ‖g x‖ := by
        simp only [← norm_div, sub_div, mul_div_cancel_right₀ _ dg0, add_div]
    _ = (c * ‖y‖ + ‖y * f' - f' / g' * (g x - y * g' + y * g')‖) / ‖g x‖ := by rw [sub_add_cancel]
    _ = (c * ‖y‖ + ‖y * f' - f' / g' * (g x - y * g') - y * f' / g' * g'‖) / ‖g x‖ := by ring_nf
    _ = (c * ‖y‖ + ‖f' / g'‖ * ‖g x - y * g'‖) / ‖g x‖ := by
        simp only [div_mul_cancel₀ _ g'0, sub_sub_cancel_left, norm_neg, norm_mul, norm_div]
    _ ≤ (c * ‖y‖ + ‖f' / g'‖ * (c * ‖y‖)) / ‖g x‖ := by bound
    _ = c * ‖y‖ * (1 + ‖f' / g'‖) / ‖g x‖ := by ring
    _ ≤ c * ‖y‖ * (1 + ‖f' / g'‖) / (2⁻¹ * ‖g'‖ * ‖y‖) := by bound
    _ = c * b * ‖y‖ / ‖y‖ := by rw [← hb]; ring_nf
    _ = c * b := by rw [mul_div_cancel_right₀ _ yp.ne']
    _ < e := by bound
