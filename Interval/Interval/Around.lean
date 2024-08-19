import Interval.Interval.Basic

open Classical
open Pointwise

/-!
## An `Interval` that contains a particular value

This is useful when we need to thread correctness properties through a computation.
-/

open Set
open scoped Real

/-- An `Interval` containing a value. -/
@[unbox] structure Around (c : ℝ) where
  /-- The interval -/
  i : Interval
  /-- We contain `c` -/
  mem : c ∈ approx i

namespace Around

variable {c : ℝ}

-- Teach `approx` about `Around`
attribute [approx] Around.mem

/-- `Around` intersections are always valid -/
instance : Inter (Around c) where
  inter x y := {
    i := x.i.inter y.i ⟨c, x.mem, y.mem⟩
    mem := by approx }
