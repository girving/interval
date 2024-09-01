import Interval.Floating.Basic
import Interval.Floating.Conversion

/-!
## Floating point `log2`
-/

open Set
open scoped Real
namespace Floating

/-- `n` s.t. `2^n ≤ |x| < 2^(n+1)`, or `nan` -/
@[irreducible] def log2 (x : Floating) : Fixed 0 :=
  bif x == 0 || x == nan || x.s == .max then nan else
  -- The result is `x.n.abs.log2 + x.s - 2^63` if that doesn't overflow.
  let a : Fixed 0 := ⟨⟨x.n.abs.log2⟩ - 1⟩
  let b : Fixed 0 := ⟨⟨x.s - 2^63 + 1⟩⟩
  a + b
