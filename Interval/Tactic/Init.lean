import Aesop.Frontend.Command
import Lean.Util.Trace

/-!
# Interval tactics setup
-/

/-!
### Aesop rule set for `approx`

This module defines the `Approx` Aesop rule set which is used by the
`approx` tactic. Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

declare_aesop_rule_sets [Approx]

/-!
### Trace classes for the `interval` tactic
-/

initialize Lean.registerTraceClass `interval
initialize Lean.registerTraceClass `interval.debug

/-!
### Simp lemma sets
-/

/-- Simp lemmas for cleaning up `bif` statements -/
register_simp_attr to_if

/-- Simp lemmas for reducing from `Int64` and `UInt64` to `BitVec` -/
register_simp_attr to_bitvec

/-- Simp lemmas for reducing from `Int64` and `UInt64` to `ℕ` and `ℤ` as prep for `omega` -/
register_simp_attr to_omega
