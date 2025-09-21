import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Algebra.Star.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Interval.Tactic.Approx

/-!
## Approximate arithmetic typeclasses
-/

open Set

variable {R A B : Type}

/-- `A` approximates `R`, in that we know which `R`s an `A` corresponds to. -/
class Approx (A : Type) (R : Type) where
  approx (x : A) (y : R) : Prop

export Approx (approx)

/-- `0 : A` is conservative, and `0` only approximates `0` -/
class ApproxZero (A R : Type) [Zero R] [Zero A] [Approx A R] where
  approx_zero : approx (0 : A) (0 : R)
  approx_zero_imp : ∀ (x : R), approx (0 : A) x → x = 0

/-- `1 : A` is conservative -/
class ApproxOne (A R : Type) [One R] [One A] [Approx A R] where
  approx_one : approx (1 : A) (1 : R)

/-- `-A` is conservative -/
class ApproxNeg (A R : Type) [Neg R] [Neg A] [Approx A R] where
  approx_neg {x : A} {y : R} (m : approx x y) : approx (-x) (-y)

/-- `A + A` is conservative -/
class ApproxAdd (A R : Type) [Add R] [Add A] [Approx A R] where
  approx_add {x y : A} {z w : R} (xz : approx x z) (yw : approx y w) : approx (x + y) (z + w)

/-- `A - A` is conservative -/
class ApproxSub (A R : Type) [Sub R] [Sub A] [Approx A R] where
  approx_sub {x y : A} {z w : R} (xz : approx x z) (yw : approx y w) : approx (x - y) (z - w)

/-- `A * A` is conservative -/
class ApproxMul (A R : Type) [Mul R] [Mul A] [Approx A R] where
  approx_mul {x y : A} {z w : R} (xz : approx x z) (yw : approx y w) : approx (x * y) (z * w)

/-- `A⁻¹` is conservative -/
class ApproxInv (A R : Type) [Inv R] [Inv A] [Approx A R] where
  approx_inv {x : A} {y : R} (m : approx x y) : approx x⁻¹ y⁻¹

/-- `star A` is conservative -/
class ApproxStar (A R : Type) [Star R] [Star A] [Approx A R] where
  approx_star {x : A} {y : R} (m : approx x y) : approx (star x) (star y)

/-- `A / A` is conservative -/
class ApproxDiv (A R : Type) [Div R] [Div A] [Approx A R] where
  approx_div {x y : A} {z w : R} (xz : approx x z) (yw : approx y w) : approx (x / y) (z / w)

/-- `A • B` is conservative -/
class ApproxSMul (A B A' B' : Type) [SMul A B] [SMul A' B'] [Approx A A'] [Approx B B'] where
  approx_smul {s' : A'} {x' : B'} {s : A} {x : B} (sm : approx s s') (xm : approx x x') :
      approx (s • x) (s' • x')

/-- `A` approximates the additive group `R` -/
class ApproxAddGroup (A R : Type) [AddGroup R] extends
  Zero A, Neg A, Add A, Sub A, Approx A R,
  ApproxZero A R, ApproxNeg A R, ApproxAdd A R, ApproxSub A R where

/-- `A` approximates the ring `R` -/
class ApproxRing (A R : Type) [Ring R] extends
  ApproxAddGroup A R, One A, Mul A, ApproxOne A R, ApproxMul A R where

/-- `A` approximates the field `R` -/
class ApproxField (A R : Type) [Field R] extends ApproxRing A R, Div A, ApproxDiv A R where

export ApproxZero (approx_zero)
export ApproxOne (approx_one)
export ApproxNeg (approx_neg)
export ApproxAdd (approx_add)
export ApproxSub (approx_sub)
export ApproxMul (approx_mul)
export ApproxInv (approx_inv)
export ApproxStar (approx_star)
export ApproxDiv (approx_div)
export ApproxSMul (approx_smul)

attribute [simp] approx_zero approx_one

lemma approx_zero_iff [Approx A R] [Zero A] [Zero R] [ApproxZero A R] (x : R) :
    approx (0 : A) x ↔ x = 0 := by
  constructor
  · apply ApproxZero.approx_zero_imp
  · intro x0; rw [x0]; exact approx_zero

/-!
## Everything approximates itself
-/

instance : Approx R R where approx x y := x = y
instance [Zero R] : ApproxZero R R where
  approx_zero := by simp only [approx]
  approx_zero_imp x a := by simp only [approx] at a; simp only [a]
instance [One R] : ApproxOne R R where approx_one := by simp only [approx]
instance [Neg R] : ApproxNeg R R where approx_neg := by simp only [approx]; aesop
instance [Add R] : ApproxAdd R R where approx_add := by simp only [approx]; aesop
instance [Sub R] : ApproxSub R R where approx_sub := by simp only [approx]; aesop
instance [Mul R] : ApproxMul R R where approx_mul := by simp only [approx]; aesop
instance [Inv R] : ApproxInv R R where approx_inv := by simp only [approx]; aesop
instance [Div R] : ApproxDiv R R where approx_div := by simp only [approx]; aesop
instance [SMul A B] : ApproxSMul A B A B where approx_smul := by simp only [approx]; aesop

/-!
## Typeclass for `nan`
-/

/-- The set of approximated elements. Default to using `approx` as a membership function. -/
def approxSet [Approx A R] (x : A) : Set R :=
  {y | approx x y}

/-!
## Typeclass for `nan`
-/

class Nan (A : Type) where
  nan : A

class ApproxNan (A R : Type) [Approx A R] [Nan A] : Prop where
  approx_nan (x : R) : approx (Nan.nan : A) x

export Nan (nan)
export ApproxNan (approx_nan)
attribute [simp] approx_nan

/-!
### Rounding utilities

For when we approximately round up or down.
-/

variable {I J : Type} [LinearOrder I]
variable {up : Bool}
variable {s t : Set I}

def Rounds [Approx A R] [LE R] (x : A) (y : R) (up : Bool) : Prop :=
  ∃ a, approx x a ∧ if up then y ≤ a else a ≤ y

@[simp] lemma rounds_same {x y : I} : Rounds x y up ↔ if up then y ≤ x else x ≤ y := by
  simp only [Rounds, approx, exists_eq_left']

@[simp, approx] lemma rounds_nan [Approx A I] [Nan A] [ApproxNan A I] {y : I} :
    Rounds (nan : A) y up := by
  use y
  simp only [approx_nan, le_refl, ite_self, and_self]

@[approx] lemma rounds_neg [Approx A I] [Neg A] [AddGroup I] [ApproxNeg A I] [AddLeftMono I]
    [AddRightMono I] {x : A} {y : I} (a : Rounds x (-y) !up) : Rounds (-x) y up := by
  obtain ⟨z, xz, r⟩ := a
  refine ⟨-z, approx_neg xz, ?_⟩
  simpa [neg_le (a := z), le_neg (a := y)] using r

@[approx] lemma Rounds.neg [Approx A I] [Neg A] [AddGroup I] [ApproxNeg A I] [AddLeftMono I]
    [AddRightMono I] {x : A} {y : I} (a : Rounds x y !up) : Rounds (-x) (-y) up := by
  apply rounds_neg
  simpa only [neg_neg]

/-!
## `approx` machinery
-/

-- Make `approx` handle `s ⊆ s`
attribute [approx] subset_refl

attribute [approx] approx_neg approx_add approx_sub approx_mul approx_div approx_smul approx_inv
  approx_star approx_zero approx_one approx_nan

/-- Test `approx` -/
example [Field R] [ApproxField A R] {a b c : R} {x y z : A}
    (am : approx x a) (bm : approx y b) (cm : approx z c) :
    approx (x + y * -z) (a + b * -c) := by approx

/-!
## Convexity of `approx`
-/

/-- `A` has a convex `approx` -/
class ApproxConnected (A R : Type) [Approx A R] [Preorder R] where
  connected (x : A) : OrdConnected (approxSet x : Set R)

/-- `Icc ⊆ approx` if the endpoints are included -/
lemma approx_of_mem_Icc [Approx A R] [Preorder R] [ApproxConnected A R] {a b c : R}
    {x : A} (xa : approx x a) (xc : approx x c) (abc : b ∈ Icc a c) : approx x b :=
  (ApproxConnected.connected _).out xa xc abc
