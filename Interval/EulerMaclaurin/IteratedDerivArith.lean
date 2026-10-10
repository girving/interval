module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
### Power series coefficient facts
-/

public section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : 𝕜 → E}

lemma iteratedDeriv_id_smul {n : ℕ} (fc : ContDiff 𝕜 n f) {y : 𝕜} :
    iteratedDeriv n (fun x ↦ x • f x) y =
      y • iteratedDeriv n f y + n • iteratedDeriv (n - 1) f y := by
  induction n generalizing f with
  | zero =>
    simp only [iteratedDeriv_zero, zero_le, tsub_eq_zero_of_le, zero_smul, add_zero]
  | succ n h =>
    have ds : deriv (fun x ↦ x • f x) = (fun x ↦ f x + x • deriv f x) := by
      ext y
      rw [deriv_fun_smul]
      · simp only [deriv_id'', one_smul, add_comm]
      · exact differentiableAt_fun_id
      · exact fc.contDiffAt.differentiableAt (by norm_cast)
    nth_rw 1 [iteratedDeriv_succ', ds]
    change iteratedDeriv n (f + _) y = _
    rw [iteratedDeriv_add, h]
    · simp only [← iteratedDeriv_succ', add_tsub_cancel_right, ← add_assoc, add_comm _ (y • _)]
      simp only [add_assoc, add_right_inj]
      match n with
      | 0 => simp only [iteratedDeriv_zero, zero_add, zero_smul, add_zero, one_smul]
      | n+1 => simp only [add_tsub_cancel_right, add_nsmul, one_smul]; abel
    · exact fc.deriv'
    · exact ContDiff.contDiffAt (fc.of_le (mod_cast (Nat.le_succ _)))
    · exact ContDiff.contDiffAt (ContDiff.smul contDiff_id (fc.deriv'.of_le le_rfl))
