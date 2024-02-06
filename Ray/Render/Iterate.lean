import Ray.Approx.Box
import Ray.Dynamics.Mandelbrot

/-!
## Mandelbrot iteration

We iterate until either a cutoff is reached or we exceed a given radius, recording why we stopped.
-/

open Complex (abs)
open Real (log)
open Set

private local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

/-- Why we exited out of an iteration -/
inductive Exit : Type
  | count
  | large
  | nan

/-- An iteration result -/
structure Iter where
  /-- The final value after iteration -/
  z : Box
  /-- Number of steps taken -/
  n : ℕ
  /-- Why we stopped iterating -/
  exit : Exit

/-- Helper for `iterate` -/
def iterate' (c z : Box) (rs : Floating) (k n : ℕ) : Iter := match n with
  | 0 => ⟨z, k, .count⟩
  | n + 1 =>
    -- Conveniently, `z.re.sqr` and `z.im.sqr` are needed by both iteration and squared magnitude
    let zr2 := z.re.sqr
    let zi2 := z.im.sqr
    let z2 := zr2.lo.add zi2.lo false
    if z2 = nan then ⟨z, k, .nan⟩ else  -- We hit nan, so stop computing
    if rs ≤ z2 then ⟨z, k, .large⟩ else  -- Early exit if we know that `r ≤ |z|`
    let zri := z.re * z.im
    let w := ⟨zr2 - zi2, zri.scaleB 1⟩ + c
    iterate' c w rs (k+1) n

/-- Iterate until we reach a given count or definitely exceed a given radius.
    Returns the final iterate, and the number of steps taken. -/
def iterate (c z : Box) (r : Floating) (n : ℕ) : Iter :=
  let rs := r.mul r true
  if rs = nan then ⟨z, 0, .nan⟩ else
  iterate' c z (r.mul r true) 0 n

/-- All correctness properties of `iterate'` in a single lemma -/
lemma iterate'_correct {c z : Box} {rs : Floating} {c' z' : ℂ} {rs' : ℝ}
    (cm : c' ∈ approx c) (zm : z' ∈ approx z) (rsn : rs ≠ nan) (rsm : rs' ≤ rs.val) (k n : ℕ) :
    let i := iterate' c z rs k n
    let w' := (f' 2 c')^[i.n - k] z'
    k ≤ i.n ∧ w' ∈ approx i.z ∧ (i.exit = .large → rs' ≤ abs w' ^ 2) := by
  induction' n with n h generalizing k z z'
  · simpa only [iterate', le_refl, ge_iff_le, tsub_eq_zero_of_le, Function.iterate_zero, id_eq,
      IsEmpty.forall_iff, and_true, true_and]
  · simp only [iterate', Floating.val_le_val]
    generalize hzr2 : z.re.sqr = zr2
    generalize hzi2 : z.im.sqr = zi2
    generalize hz2 : zr2.lo.add zi2.lo false = z2
    generalize hw : (⟨zr2 - zi2, (z.re * z.im).scaleB 1⟩ : Box) + c = w
    have we : w = z.sqr + c := by rw [←hw, Box.sqr, hzr2, hzi2]
    have wa : f' 2 c' z' ∈ approx w := by rw [we, f']; mono
    generalize hw' : f' 2 c' z' = w' at wa
    by_cases z2n : z2 = nan
    · simpa only [z2n, ite_true, le_refl, ge_iff_le, tsub_eq_zero_of_le, Function.iterate_zero,
        id_eq, IsEmpty.forall_iff, and_true, true_and]
    by_cases rz : rs.val ≤ z2.val
    · simp only [z2n, rz, ite_true, le_refl, ge_iff_le, tsub_eq_zero_of_le, Function.iterate_zero,
        id_eq, zm, forall_true_left, true_and, Complex.abs_def,
        Real.sq_sqrt (Complex.normSq_nonneg _), if_false]
      refine le_trans (le_trans rsm rz) ?_
      simp only [Complex.normSq_apply, ←sq, ←hz2, ←hzr2, ←hzi2] at z2n ⊢
      rcases Floating.ne_nan_of_add z2n with ⟨nr, ni⟩
      simp only [ne_eq, Interval.lo_eq_nan] at nr ni
      refine le_trans (Floating.val_add_le z2n) (add_le_add ?_ ?_)
      · apply Interval.lo_le nr; mono
      · apply Interval.lo_le ni; mono
    · simp only [rz, ite_false, z2n]
      generalize hi : iterate' c w rs (k + 1) n = i
      specialize h wa (k+1)
      simp only [hi] at h
      refine ⟨by omega, ?_⟩
      have ie : i.n - k = (i.n - (k + 1)) + 1 := by omega
      rw [ie, Function.iterate_succ_apply, hw']
      exact h.2

/-- `iterate` produces a correct iterate -/
@[mono] lemma mem_approx_iterate {c z : Box} {r : Floating} {c' z' : ℂ}
    (cm : c' ∈ approx c) (zm : z' ∈ approx z) (n : ℕ) :
    let i := iterate c z r n; (f' 2 c')^[i.n] z' ∈ approx i.z := by
  rw [iterate]; simp only
  generalize r.mul r true = rs
  by_cases rsn : rs = nan
  · simpa only [rsn, ite_true, Function.iterate_zero, id_eq]
  · simp only [rsn, ite_false]
    exact (iterate'_correct cm zm rsn (le_refl _) 0 n).2.1

/-- If `iterate` claims the result is large, it is` -/
lemma iterate_large {c z : Box} {r : Floating} {c' z' : ℂ}
    (cm : c' ∈ approx c) (zm : z' ∈ approx z) (n : ℕ) :
    let i := iterate c z r n; i.exit = .large → r.val ≤ abs ((f' 2 c')^[i.n] z') := by
  rw [iterate]; simp only
  generalize hrs : r.mul r true = rs
  by_cases rsn : rs = nan
  · simp only [rsn, ite_true, Function.iterate_zero, id_eq, IsEmpty.forall_iff]
  · simp only [rsn, ite_false]
    intro e
    by_cases r0 : r.val < 0
    · exact le_trans r0.le (Complex.abs.nonneg _)
    · have le := (iterate'_correct cm zm rsn (le_refl _) 0 n).2.2 e
      simp only [←hrs, not_lt, Nat.sub_zero] at le rsn r0 ⊢
      rw [←Real.sqrt_sq r0, ←Real.sqrt_sq (Complex.abs.nonneg _)]
      refine Real.sqrt_le_sqrt (le_trans ?_ le)
      simp only [pow_two]
      exact Floating.le_mul rsn
