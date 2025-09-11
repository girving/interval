import Aesop
import Interval.Tactic.Init

/-!
# The `approx` tactic

Given an `Approx A R` relationship, the `approx` tactic proves that expressions over `A` are
conservative approximations of expressions over `R`, using `aesop` recursion.
-/

-- Attribute for `apply` rules for the `approx` tactic
macro "approx" : attr =>
  `(attr|aesop safe apply (rule_sets := [$(Lean.mkIdent `Approx):ident]))

/-- Aesop configuration for `approx` -/
def approxConfig : Aesop.Options := {
  enableSimp := false
}

/-- `approx` tactic for proving simple `approx x a` goals.

`approx x a` says that `x` is a conservative approximation of `a` as defined by the `Approx`
typeclass. For example, `approx_add` says that `approx (x + y) (a + b)` if `approx x a` and
`approx y b`. `approx_add` is registered as an `@[approx]` lemma so that the `approx` tactic
can apply it. -/
syntax "approx" : tactic

-- Rewrite `approx` into `aesop`
macro_rules
  | `(tactic| approx) => `(tactic| aesop (rule_sets := [Approx]) (config := approxConfig))
