import Mathlib.Data.Complex.Basic
import Interval.Interval.Basic
import Interval.Interval.Conversion
import Interval.Interval.Mul
import Interval.Interval.Scale
import Interval.Unbundled

open Classical
open Pointwise

/-!
## Complex interval arithmic (on top of 64-bit fixed point intervals)
-/

open Set
open scoped Real ComplexConjugate

/-- Rectangular boxes of complex numbers -/
@[unbox] structure Box where
  re : Interval
  im : Interval
  deriving DecidableEq, BEq

namespace Box

variable {z w : Box} {z' w' : ℂ}
variable {x y : Interval} {x' y' : ℝ}

/-- `Box` has nice equality -/
instance : LawfulBEq Box where
  eq_of_beq {x y} e := by
    induction' x with xlo xhi; induction' y with ylo yhi
    have g : ((xlo == ylo && xhi == yhi) = true) := e
    simp only [Bool.and_eq_true, beq_iff_eq] at g
    simp only [g.1, g.2]
  rfl {x} := by
    have e : (x == x) = (x.re == x.re && x.im == x.im) := rfl
    simp only [e, beq_self_eq_true, Bool.and_self]

/-- Reduce `Box s` equality to `Interval` equality -/
lemma ext_iff (z w : Box) : z = w ↔ z.re = w.re ∧ z.im = w.im := by
  induction z; induction w; simp only [mk.injEq]

instance : Repr Box where
  reprPrec z _ := "(" ++ repr z.re ++ " + " ++ repr z.im ++ "i⟩"

/-- Simplification of `∈ image2` for `Box` -/
@[simp] lemma mem_image2_iff {z : ℂ} {s t : Set ℝ} :
    z ∈ image2 (fun r i ↦ (⟨r,i⟩ : ℂ)) s t ↔ z.re ∈ s ∧ z.im ∈ t := by
  simp only [image2, Complex.ext_iff, exists_eq_right_right, mem_setOf_eq]

/-- `Box` approximates `ℂ` -/
instance instApprox : Approx Box ℂ where
  approx z z' := approx z.re z'.re ∧ approx z.im z'.im

/-- `Box` zero -/
instance : Zero Box where
  zero := ⟨0,0⟩

/-- `Box` one -/
instance : One Box where
  one := ⟨1,0⟩

/-- `Box` negation -/
instance : Neg Box where
  neg x := ⟨-x.re, -x.im⟩

/-- `Box` addition -/
instance : Add Box where
  add x y := ⟨x.re + y.re, x.im + y.im⟩

/-- `Box` subtraction -/
instance : Sub Box where
  sub x y := ⟨x.re - y.re, x.im - y.im⟩

/-- Complex conjugation -/
instance : Star Box where
  star x := ⟨x.re, -x.im⟩

/-- `Box` multiplication -/
instance : Mul Box where
  mul z w := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

/-- `Interval * Box` -/
instance : SMul Interval Box where
  smul x z := ⟨x * z.re, x * z.im⟩

/-- `Box` squaring (tighter than `z * z`) -/
def sqr (z : Box) : Box :=
  let w := z.re * z.im
  ⟨z.re.sqr - z.im.sqr, w.scaleB 1⟩

/-- Power of two scaling -/
@[irreducible] def scaleB (z : Box) (t : Int64) : Box :=
  ⟨z.re.scaleB t, z.im.scaleB t⟩

-- Definition lemmas
lemma neg_def {z : Box} : -z = ⟨-z.re, -z.im⟩ := rfl
lemma add_def {z w : Box} : z + w = ⟨z.re + w.re, z.im + w.im⟩ := rfl
lemma sub_def {z w : Box} : z - w = ⟨z.re - w.re, z.im - w.im⟩ := rfl
lemma mul_def {z w : Box} : z * w = ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩ := rfl
lemma smul_def {x : Interval} {z : Box} : x • z = ⟨x * z.re, x * z.im⟩ := rfl
@[simp] lemma re_conj {z : Box} : (star z).re = z.re := rfl
@[simp] lemma im_conj {z : Box} : (star z).im = -z.im := rfl

-- Bounds properties of `Box` arithmetic
@[simp] lemma re_zero : (0 : Box).re = 0 := rfl
@[simp] lemma im_zero : (0 : Box).im = 0 := rfl
@[simp] lemma re_one : (1 : Box).re = 1 := rfl
@[simp] lemma im_one : (1 : Box).im = 0 := rfl
@[simp] lemma approx_zero_iff : approx (0 : Box) z' ↔ z' = 0 := by
  simp only [instApprox, re_zero, Interval.approx_zero, im_zero, Complex.ext_iff, Complex.zero_re,
    Complex.zero_im]
@[simp] lemma re_neg {z : Box} : (-z).re = -z.re := rfl
@[simp] lemma im_neg {z : Box} : (-z).im = -z.im := rfl
@[simp] lemma re_smul {x : Interval} {z : Box} : (x • z).re = x * z.re := by simp [smul_def]
@[simp] lemma im_smul {x : Interval} {z : Box} : (x • z).im = x * z.im := by simp [smul_def]

/-- Prove `re ∈` via full `∈` -/
@[approx] lemma approx_re {z : ℂ} {w : Box} (zw : approx w z) : approx w.re z.re := zw.1

/-- Prove `im ∈` via full `∈` -/
@[approx] lemma approx_im {z : ℂ} {w : Box} (zw : approx w z) : approx w.im z.im := zw.2

/-- Split `∈ approx` into components -/
lemma approx_iff_ext {z : ℂ} {w : Box} : approx w z ↔ approx w.re z.re ∧ approx w.im z.im := by
  rfl

instance : ApproxZero Box ℂ where approx_zero := by simp [approx_iff_ext]
instance : ApproxZeroIff Box ℂ where approx_zero_imp x a := by simpa only [approx_zero_iff] using a
instance : ApproxOne Box ℂ where approx_one := by simp [approx_iff_ext]

/-- `star` is conservative -/
instance : ApproxStar Box ℂ where
  approx_star m := by
    simp only [instApprox, RCLike.star_def, re_conj, Complex.conj_re, m.1, im_conj, Complex.conj_im,
      Interval.approx_neg, neg_neg, m.2, and_self]

@[approx] lemma approx_conj (m : approx z z') : approx (star z) (conj z') := approx_star m

/-- `Box.neg` respects `approx` -/
instance : ApproxNeg Box ℂ where
  approx_neg m := by simpa [instApprox, mem_neg, mem_image2] using m

/-- `Box.add` respects `approx` -/
instance : ApproxAdd Box ℂ where
  approx_add _ _ := by
    simp only [instApprox, add_def, Complex.add_re, Complex.add_im]
    approx

/-- `Box.sub` respects `approx` -/
instance : ApproxSub Box ℂ where
  approx_sub _ _ := by
    simp only [instApprox, sub_def, Complex.sub_re, Complex.sub_im]
    approx

/-- `Box` approximates `ℂ` as an additive group -/
noncomputable instance : ApproxAddGroup Box ℂ where

/-- `Box` multiplication approximates `ℂ` -/
instance : ApproxMul Box ℂ where
  approx_mul z w := by
    simp only [Box.instApprox, Complex.mul_re, Complex.mul_im, Box.mul_def]
    approx

/-- `Interval • Box` approximates `ℂ` -/
@[approx] lemma approx_smul (ax : approx x x') (az : approx z z') : approx (x • z) (x' • z') := by
  simp only [instApprox, smul_def, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im, add_zero]
  approx

/-- `Box` approximates `ℂ` as a ring -/
noncomputable instance : ApproxRing Box ℂ where

/-- `Box` squaring approximates `ℂ` -/
@[approx] lemma approx_sqr (az : approx z z') : approx z.sqr (z' ^ 2) := by
  simp only [instApprox, sqr, Complex.mul_re, Complex.mul_im, pow_two z', ← pow_two z'.re,
    ← pow_two z'.im, mul_comm z'.im, ← two_mul]
  approx

/-- `Box` scaling approximates `ℂ` -/
@[approx] lemma approx_scaleB (az : approx z z') (t : Int64) :
    approx (z.scaleB t) (z' * 2 ^ (t : ℤ)) := by
  have two : (2 : ℂ) = (2 : ℝ) := by  norm_num
  simp only [scaleB, instApprox, two, Complex.mul_re, ← Complex.ofReal_zpow, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.ofReal_re, Complex.mul_im, zero_add]
  approx

/-- `Box` doubling approximates `ℂ` -/
@[approx] lemma approx_scaleB_one (az : approx z z') : approx (z.scaleB 1) (2 * z') := by
  simpa only [Int64.coe_one, zpow_one, mul_comm _ (2 : ℂ)] using approx_scaleB az 1

/-!
### Multiplication and division by `I`
-/

@[irreducible] def mul_I (z : Box) : Box := ⟨-z.im, z.re⟩
@[irreducible] def div_I (z : Box) : Box := ⟨z.im, -z.re⟩

@[approx] lemma approx_mul_I (m : approx z z') : approx z.mul_I (z' * Complex.I) := by
  rw [mul_I, approx_iff_ext]; simp; approx

@[approx] lemma approx_div_I (m : approx z z') : approx z.div_I (z' / Complex.I) := by
  rw [div_I, approx_iff_ext]; simp; approx

@[approx] lemma approx_div_I' (m : approx z z') : approx z.div_I (-z' * Complex.I) := by
  rw [div_I, approx_iff_ext]; simp; approx

@[simp] lemma div_I_mul_I {z : Box} : z.div_I.mul_I = z := by rw [div_I, mul_I]; simp
@[simp] lemma mul_I_div_I {z : Box} : z.mul_I.div_I = z := by rw [div_I, mul_I]; simp

/-!
### Square magnitude
-/

/-- `Box` square magnitude -/
@[irreducible] def normSq (z : Box) : Interval :=
  z.re.sqr + z.im.sqr

/-- `normSq` is conservative -/
@[approx] lemma approx_normSq (m : approx z z') : approx z.normSq (‖z'‖ ^ 2) := by
  rw [normSq]
  simp only [Complex.sq_norm, Complex.normSq, ←pow_two, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  approx

/-- `normSq` is conservative -/
@[approx] lemma approx_normSq' (m : approx z z') : approx z.normSq z'.normSq := by
  simp only [Complex.normSq_eq_norm_sq]
  approx

/-- Lower bounds on `normSq` produce lower bounds on contained radii -/
lemma sqrt_normSq_le_abs (m : approx z z') : Real.sqrt z.normSq.lo.val ≤ ‖z'‖ := by
  by_cases n : z.normSq = nan
  · rw [Real.sqrt_eq_zero_of_nonpos]
    all_goals simp [n]
  simp only [Real.sqrt_le_iff, norm_nonneg, true_and]
  apply Interval.lo_le n
  approx

/-- Upper bounds on `normSq` produce upper bounds on contained radii -/
lemma abs_le_sqrt_normSq (m : approx z z') (n : z.normSq ≠ nan) :
    ‖z'‖ ≤ Real.sqrt z.normSq.hi.val := by
  apply Real.le_sqrt_of_sq_le
  apply Interval.le_hi n
  approx

/-!
### Conversion
-/

@[coe, irreducible] def _root_.Complex.ofRat (z : ℚ × ℚ) : ℂ := ⟨z.1, z.2⟩

lemma _root_.Complex.ofRat_def (z : ℚ × ℚ) : Complex.ofRat z = ⟨z.1, z.2⟩ := by
  rw [Complex.ofRat]

noncomputable instance : Coe (ℚ × ℚ) ℂ where
  coe z := Complex.ofRat z

@[irreducible] def ofRat (z : ℚ × ℚ) : Box :=
  ⟨z.1, z.2⟩

@[approx] lemma approx_ofRat (z : ℚ × ℚ) : approx (ofRat z) (z : ℂ) := by
  simp only [instApprox, ofRat, Complex.ofRat]
  approx

/-!
### Unbundled instances
-/

instance : NegZeroClass' Box where
  neg_zero' := by decide +kernel

instance : AddZeroClass' Box where
  zero_add' x := by simp only [add_def, re_zero, zero_add', im_zero]
  add_zero' x := by simp only [add_def, re_zero, add_zero', im_zero]

instance : SubZeroClass Interval where
  zero_sub' x := by simp only [zero_sub']
  sub_zero' x := by simp only [sub_zero']
