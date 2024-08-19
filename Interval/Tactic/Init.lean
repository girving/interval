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
