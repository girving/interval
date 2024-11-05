import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
### Power series coefficient facts
-/

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {x : 𝕜} {r : ENNReal}

lemma iteratedDeriv_add {n : ℕ} {x : 𝕜} {f g : 𝕜 → E} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    iteratedDeriv n (fun x ↦ f x + g x) x = iteratedDeriv n f x + iteratedDeriv n g x := by
  simp only [← iteratedDerivWithin_univ]
  rw [← iteratedDerivWithin_add]
  · rfl
  · trivial
  · exact uniqueDiffOn_univ
  · exact contDiffOn_univ.mpr hf
  · exact contDiffOn_univ.mpr hg

lemma _root_.ContDiff.deriv' (fc : ContDiff 𝕜 ⊤ f) : ContDiff 𝕜 ⊤ (deriv f) :=
  fc.iterate_deriv 1

lemma iteratedDeriv_mul (fc : ContDiff 𝕜 ⊤ f) {n : ℕ} {y : 𝕜} :
    iteratedDeriv n (fun x ↦ x • f x) y =
      y • iteratedDeriv n f y + n • iteratedDeriv (n - 1) f y := by
  induction' n with n h generalizing f
  · simp only [iteratedDeriv_zero, zero_le, tsub_eq_zero_of_le, zero_smul, add_zero]
  · have ds : deriv (fun x ↦ x • f x) = (fun x ↦ f x + x • deriv f x) := by
      ext y
      rw [deriv_smul]
      · simp only [deriv_id'', one_smul, add_comm]
      · exact differentiableAt_id'
      · exact fc.contDiffAt.differentiableAt le_top
    nth_rw 1 [iteratedDeriv_succ', ds, iteratedDeriv_add, h]
    · simp only [← iteratedDeriv_succ', add_tsub_cancel_right, ← add_assoc, add_comm _ (y • _)]
      simp only [add_assoc, add_right_inj]
      match n with
      | 0 => simp only [iteratedDeriv_zero, zero_add, zero_smul, add_zero, one_smul]
      | n+1 => simp only [add_tsub_cancel_right, add_nsmul, one_smul]; abel
    · exact fc.deriv'
    · exact fc.of_le le_top
    · exact ContDiff.smul contDiff_id (fc.deriv'.of_le le_top)
