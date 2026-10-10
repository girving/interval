module

public import Interval.EulerMaclaurin.PartialDerivCommute
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
### Iterated ifferentiation under the integral sign
-/

public section

open Set
open Function (uncurry)
open Metric (closedBall)
open scoped Real
open scoped Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → ℝ → E} {a b t : ℝ}

/-- `hasDerivAt_integral_of_dominated_loc_of_deriv_le` for smooth functions -/
lemma deriv_interval_integral_of_contDiff (fc : ContDiff ℝ ⊤ (uncurry f)) (ab : a ≤ b) :
    deriv (fun t ↦ ∫ x in a..b, f t x) t = ∫ x in a..b, deriv (fun t ↦ f t x) t := by
  apply HasDerivAt.deriv
  set f' := fun t x ↦ deriv (fun t ↦ f t x) t
  have e' : ∀ t x, deriv (fun t ↦ f t x) t = f' t x := fun _ _ ↦ rfl
  simp only [intervalIntegral.integral_of_le ab, e']
  have de : ∀ t x, f' t x = fderiv ℝ (uncurry f) (t,x) (1,0) := by
    intro t x
    have e : (fun t ↦ f t x) = uncurry f ∘ (fun t ↦ (t,x)) := rfl
    simp only [f']
    rw [← fderiv_apply_one_eq_deriv, e, fderiv_comp]
    · rw [(hasFDerivAt_prodMk_left t x).fderiv]
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inl_apply]
    · exact (fc.differentiable (by decide)).differentiableAt
    · simp only [differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.prodMk]
  have dc : Continuous (uncurry f') := by
    simp only [f'] at de ⊢
    simp only [de, ← ContinuousLinearMap.apply_apply ((1 : ℝ), (0 : ℝ))]
    exact (ContinuousLinearMap.continuous _).comp (fc.continuous_fderiv (by decide))
  have pc : IsCompact (closedBall t 1 ×ˢ Icc a b) := (isCompact_closedBall _ _).prod isCompact_Icc
  have pn : (closedBall t 1 ×ˢ Icc a b).Nonempty := by use (t,a); simp [ab]
  obtain ⟨m,_,mm⟩ := pc.exists_isMaxOn pn dc.norm.continuousOn
  set c := ‖uncurry f' m‖
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (bound := fun _ ↦ c)
    (Metric.ball_mem_nhds t zero_lt_one) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards []
    intro t
    exact fc.continuous.along_snd.aestronglyMeasurable
  · exact fc.continuous.along_snd.integrableOn_Ioc
  · exact dc.along_snd.aestronglyMeasurable
  · simp only [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards []
    intro t tm x xm
    simp only [isMaxOn_iff, mem_prod, Metric.mem_closedBall, mem_Icc, and_imp, Prod.forall] at mm
    exact mm _ _ xm.le tm.1.le tm.2
  · apply MeasureTheory.integrable_const
  · filter_upwards []
    intro x t _
    have e : (fun t ↦ f t x) = uncurry f ∘ (fun t ↦ (t,x)) := rfl
    simp only [hasDerivAt_deriv_iff, f', e]
    apply DifferentiableAt.comp
    · exact fc.contDiffAt.differentiableAt (by decide)
    · exact differentiableAt_id.prodMk (differentiableAt_const _)

/-- Iterated differentiation under the integral sign -/
lemma iteratedDeriv_interval_integral_of_contDiff (fc : ContDiff ℝ ⊤ (uncurry f)) (ab : a ≤ b)
    (n : ℕ) : iteratedDeriv n (fun t ↦ ∫ x in a..b, f t x) t =
      ∫ x in a..b, iteratedDeriv n (fun t ↦ f t x) t := by
  induction n generalizing f with
  | zero =>
    simp
  | succ n h =>
    simp only [iteratedDeriv_succ']
    rw [← h]
    · refine congr_arg₂ _ ?_ rfl
      ext t
      exact deriv_interval_integral_of_contDiff fc ab
    · refine ContDiff.deriv ?_ contDiff_fst
      exact fc.comp₂ contDiff_snd (contDiff_snd.comp contDiff_fst)
