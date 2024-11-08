import Lean.Elab.Tactic.ElabTerm

/-!
# A faster version of `decide`

Courtesy of Kyle Miller, see:
  https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/.60decide.60.20that.20can.20see.20through.20.60irreducible.60/near/467640232
-/

open Lean Elab Tactic Meta

/-- `decide`, but use the kernel more for speed and seeing through `irreducible` -/
elab "fast_decide" : tactic => closeMainGoalUsing `fast_decide fun type _ ↦ do
  -- zeta reduce to eliminatate dependencies on local definitions
  let type ← zetaReduce (← instantiateMVars type)
  if type.hasFVar || type.hasMVar then
    throwError "expected type must not contain free or meta variables{indentExpr type}"
  if let false ← ofExceptKernelException <|
      Kernel.isDefEq (← getEnv) {} (← mkDecide type) (.const ``true []) then
    throwError "decidable instance does not reduce to true"
  mkDecideProof type

/-- `fast_decide`, but skip checking during elaboration for even more speed -/
elab "faster_decide" : tactic => closeMainGoalUsing `it_is_decided (fun ty _ ↦ mkDecideProof ty)
