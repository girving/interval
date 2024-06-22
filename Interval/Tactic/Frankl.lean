import Interval.Tactic.Interval

/-!
# The inequality from Alweiss et al.

Exploring Claim 3 of https://arxiv.org/abs/2211.11731.
-/

open Real (log sqrt)
open Set
noncomputable section

def φ : ℝ := (sqrt 5 - 1) / 2

def H (x : ℝ) : ℝ := -x * log x - (1 - x) * log (1 - x)

lemma phi_pos : 0 < φ := by
  simp only [φ]
  interval

lemma alweiss_somewhere : 0.9 * H 0.9 ≤ φ * H (0.9 ^ 2) := by
  simp only [φ, H]
  interval

/-- It would be nice if `interval` did this -/
proof_wanted alweiss : ∀ x ∈ Icc φ 1, x * H x ≤ φ * H (x ^ 2)
