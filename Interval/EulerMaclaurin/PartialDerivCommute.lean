module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Partial derivatives commute
-/

public section

open Function (uncurry)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma fderiv_fderiv_comm {f : E × F → G} {z : E × F} {dx : E} {dy : F} (sf : ContDiff ℝ 2 f) :
    fderiv ℝ (fun x ↦ fderiv ℝ (fun y ↦ f (x,y)) z.2 dy) z.1 dx =
    fderiv ℝ (fun y ↦ fderiv ℝ (fun x ↦ f (x,y)) z.1 dx) z.2 dy := by
  set f' := fderiv ℝ f
  set f'' := fderiv ℝ f' z
  have h1 : ∀ z, HasFDerivAt f (f' z) z :=
    fun z ↦ (sf.hasStrictFDerivAt (by norm_num)).hasFDerivAt
  have h2 : HasFDerivAt f' f'' z :=
    ((sf.fderiv_right (m := 1) (by norm_num)).hasStrictFDerivAt (by norm_num)).hasFDerivAt
  have h := second_derivative_symmetric_of_eventually (.of_forall h1) h2 (0,dy) (dx,0)
  have px : ∀ x y, fderiv ℝ (fun x ↦ f (x, y)) x dx = f' (x,y) (dx,0) := by
    intro x y
    have h : HasFDerivAt (fun x : E ↦ f (x,y)) ((f' (x,y)).comp (.inl ℝ E F)) x :=
      (h1 _).comp _ (hasFDerivAt_prodMk_left _ _)
    simp [h.fderiv]
  have py : ∀ x y, fderiv ℝ (fun y ↦ f (x, y)) y dy = f' (x,y) (0,dy) := by
    intro x y
    have h : HasFDerivAt (fun y : F ↦ f (x,y)) ((f' (x,y)).comp (.inr ℝ E F)) y :=
      (h1 _).comp _ (hasFDerivAt_prodMk_right _ _)
    simp [h.fderiv]
  have pxy : fderiv ℝ (fun x ↦ f' (x,z.2) (0,dy)) z.1 dx = f'' (dx,0) (0,dy) := by
    have h : HasFDerivAt (fun x : E ↦ f' (x,z.2) (0,dy))
        ((f' z).comp (0 : E →L[ℝ] E × F) + (f''.comp (.inl ℝ E F)).flip (0,dy)) z.1 :=
      (h2.comp _ (hasFDerivAt_prodMk_left _ _)).clm_apply (hasFDerivAt_const _ _)
    simp [h.fderiv]
  have pyx : fderiv ℝ (fun y ↦ f' (z.1,y) (dx,0)) z.2 dy = f'' (0,dy) (dx,0) := by
    have h : HasFDerivAt (fun y : F ↦ f' (z.1,y) (dx,0))
        ((f' z).comp (0 : F →L[ℝ] E × F) + (f''.comp (.inr ℝ E F)).flip (dx,0)) z.2 :=
      (h2.comp _ (hasFDerivAt_prodMk_right _ _)).clm_apply (hasFDerivAt_const _ _)
    simp [h.fderiv]
  simp only [py, px, pxy, pyx, h]

lemma deriv_deriv_comm {f : ℝ × ℝ → E} {z : ℝ × ℝ} (sf : ContDiff ℝ 2 f) :
    deriv (fun x ↦ deriv (fun y ↦ f (x,y)) z.2) z.1 =
    deriv (fun y ↦ deriv (fun x ↦ f (x,y)) z.1) z.2 := by
  simpa using fderiv_fderiv_comm sf (dx := 1) (dy := 1) (z := z)

lemma _root_.ContDiff.iteratedDeriv_right {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {m : WithTop ℕ∞} {n : ℕ∞} {i : ℕ}
    (hf : ContDiff 𝕜 n f) (hmn : m + i ≤ n) : ContDiff 𝕜 m (iteratedDeriv i f) := by
  have e : iteratedDeriv i f = fun x ↦ iteratedDeriv i f x := rfl
  simp only [e, iteratedDeriv_eq_iteratedFDeriv, ← ContinuousMultilinearMap.apply_apply]
  exact contDiff_const.clm_apply (hf.iteratedFDeriv_right hmn)

lemma _root_.ContDiff.deriv {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → 𝕜 → F} {g : E → 𝕜} {m : WithTop ℕ∞} (fc : ContDiff 𝕜 ⊤ (uncurry f))
    (gc : ContDiff 𝕜 ⊤ g) : ContDiff 𝕜 m fun z ↦ deriv (fun y ↦ f z y) (g z) := by
  simp_rw [← fderiv_apply_one_eq_deriv]
  simp_rw [← ContinuousLinearMap.apply_apply (v := (1 : 𝕜))]
  exact contDiff_const.clm_apply (ContDiff.fderiv fc (gc.of_le le_top) le_top)

lemma _root_.ContDiff.iteratedDeriv {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → 𝕜 → F} {g : E → 𝕜}
    {m : WithTop ℕ∞} {n : ℕ} (fc : ContDiff 𝕜 ⊤ (uncurry f)) (gc : ContDiff 𝕜 ⊤ g) :
    ContDiff 𝕜 m fun z ↦ iteratedDeriv n (fun y ↦ f z y) (g z) := by
  revert fc f
  induction n with
  | zero =>
    intro f fc
    simp only [iteratedDeriv_zero]
    exact (fc.of_le le_top).comp (contDiff_id.prodMk (gc.of_le le_top))
  | succ n ic =>
    intro f fc
    simp only [iteratedDeriv_succ']
    apply ic
    refine ContDiff.deriv ?_ contDiff_snd
    exact (fc.of_le le_top).comp₂ (contDiff_fst.comp contDiff_fst) contDiff_snd

lemma deriv_iteratedDeriv_comm {f : ℝ × ℝ → E} {z : ℝ × ℝ} (fc : ContDiff ℝ ⊤ f) (n : ℕ) :
    deriv (fun x ↦ iteratedDeriv n (fun y ↦ f (x,y)) z.2) z.1 =
    iteratedDeriv n (fun y ↦ deriv (fun x ↦ f (x,y)) z.1) z.2 := by
  induction n generalizing f z with
  | zero =>
    simp
  | succ n h =>
    simp only [iteratedDeriv_succ]
    rw [deriv_deriv_comm (f := fun z : ℝ × ℝ ↦ iteratedDeriv n (fun y ↦ f (z.1,y)) z.2)]
    · refine congr_arg₂ _ ?_ rfl
      ext w
      simp only
      exact h fc (z := (z.1,w))
    · refine ContDiff.iteratedDeriv ?_ contDiff_snd
      exact fc.comp₂ (contDiff_fst.comp contDiff_fst) contDiff_snd
