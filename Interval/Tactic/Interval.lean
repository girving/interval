import Interval.Division
import Interval.Interval.Conversion
import Interval.Interval.Mul
import Interval.Series
import Interval.Tactic.Init
import Mathlib.Tactic.Monotonicity.Basic
import Qq

/-!
# The `interval` tactic

`interval` attempts to prove real inequalities between constant expressions by lifting the
expressions from `ℝ` to `Interval`.

**Warning:** We use `native_decide`, so you must trust the compiler.
-/

open Lean (Expr MetaM MVarId)
open Lean.Meta
open Lean.Elab.Tactic
open Qq

namespace IntervalTactic

inductive Ineq where
  | lt : Ineq
  | le : Ineq
  | gt : Ineq
  | ge : Ineq

structure Goal where
  op : Ineq
  x : Q(Interval)
  y : Q(Interval)

def Ineq.str : Ineq → String
  | .lt => "<"
  | .le => "≤"
  | .gt => ">"
  | .ge => "≥"

partial def lift (e : Q(ℝ)) : MetaM Q(Interval) := do
  match e with
    | ~q(0) => return q(0)
    | ~q(1) => return q(1)
    | ~q(@OfNat.ofNat ℝ $n $i) => return q(Interval.ofNat $n)
    | ~q(@OfNat.ofNat ℝ $n $i / @OfNat.ofNat ℝ $d $j) => return q(Interval.ofRat ($n / $d))
    | ~q(1 / @OfNat.ofNat ℝ $d $j) => return q(Interval.ofRat (1 / $d))
    | ~q(@OfScientific.ofScientific ℝ _ $x $u $t) => do
      return q(@OfScientific.ofScientific Interval _ $x $u $t)
    | ~q(-$x) => return q(-$(← lift x))
    | ~q($x + $y) => return q($(← lift x) + $(← lift y))
    | ~q($x - $y) => return q($(← lift x) - $(← lift y))
    | ~q($x * $y) => return q($(← lift x) * $(← lift y))
    | ~q($x / $y) => return q($(← lift x) / $(← lift y))
    | ~q(@HPow.hPow ℝ ℝ ℝ _ $x $y) => return q($(← lift x).pow $(← lift y))
    | ~q(@HPow.hPow ℝ ℕ ℝ _ $x (@OfNat.ofNat ℕ $y _)) =>
      return q($(← lift x).pow (Interval.ofNat $y))
    | ~q(Real.exp $x) => return q($(← lift x).exp)
    | ~q(Real.log $x) => return q($(← lift x).log)
    | ~q(Real.sqrt $x) => return q($(← lift x).sqrt)
    | ~q(|$x|) => return q($(← lift x).abs)
    | _ => throwError f!"`interval` works only for certain constant real inequalities, not {e}"

def liftGoal (p : Q(Prop)) : MetaM Goal := do
  match p with
    | ~q(@LE.le ℝ $i $x $y) => return ⟨.le, ← lift x, ← lift y⟩
    | ~q(@LT.lt ℝ $i $x $y) => return ⟨.lt, ← lift x, ← lift y⟩
    | ~q(@GE.ge ℝ $i $x $y) => return ⟨.ge, ← lift x, ← lift y⟩
    | ~q(@GT.gt ℝ $i $x $y) => return ⟨.gt, ← lift x, ← lift y⟩
    | _ => throwError "`interval` works only for constant real inequalities"

def ilt (x y : Interval) : Prop := x != nan && x.hi.blt y.lo
def ile (x y : Interval) : Prop := x != nan && x.hi.ble y.lo

instance {x y : Interval} : Decidable (ilt x y) := by unfold ilt; infer_instance
instance {x y : Interval} : Decidable (ile x y) := by unfold ile; infer_instance

lemma liftLt (x y : Interval) : ∀ (a b : ℝ), a ∈ approx x → b ∈ approx y → ilt x y → a < b := by
  intro a b ax ay xy
  simp only [ilt, Floating.blt_eq_lt, Floating.val_lt_val, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at xy
  rcases xy with ⟨xn, lt⟩
  have yn : y.lo ≠ nan := Floating.ne_nan_of_le (x.hi_ne_nan xn) (by linarith)
  simp only [approx, Interval.lo_eq_nan, xn, ↓reduceIte, Set.mem_Icc, yn] at ax ay
  linarith

lemma liftLe (x y : Interval) : ∀ (a b : ℝ), a ∈ approx x → b ∈ approx y → ile x y → a ≤ b := by
  intro a b ax ay xy
  simp only [ile, Floating.ble_eq_le, Floating.val_le_val, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at xy
  rcases xy with ⟨xn, le⟩
  have yn : y.lo ≠ nan := Floating.ne_nan_of_le (x.hi_ne_nan xn) (by linarith)
  simp only [approx, Interval.lo_eq_nan, xn, ↓reduceIte, Set.mem_Icc, yn] at ax ay
  linarith

/-- Turn a real inequality goal into an `Interval` goal -/
def Goal.app (g : Goal) : Lean.Expr :=
  let ⟨op, x, y⟩ := g
  match op with
    | .lt => q(liftLt $x $y)
    | .le => q(liftLe $x $y)
    | .gt => q(liftLt $y $x)
    | .ge => q(liftLe $y $x)

/-- Evaluate whether an inequality is known between explicit `Interval`s -/
def Ineq.eval (op : Ineq) (x y : Interval) : Bool :=
  match op with
    | .lt => ilt x y
    | .le => ile x y
    | .gt => ilt y x
    | .ge => ile y x

/-- Close a goal using a tactic -/
def close (g : MVarId) (tac : Lean.Syntax) : TacticM Unit := do
  let gs ← Lean.Elab.Tactic.run g do evalTactic tac
  trace[interval.debug] "close: {tac} ↦ {gs}"
  match gs with
    | [] => return ()
    | _ => throwError "close {tac}: unexpected goals {gs}"

/-- Delegate `toMessageData` to `str` for `Ineq` -/
instance : Lean.ToMessageData Ineq where
  toMessageData i := i.str

/-- Necessary to avoid kernel errors for some reason -/
@[irreducible] def _root_.Interval.toMessageData (x : Interval) : Lean.MessageData :=
  .ofFormat (repr x)

/-- Delegate `toMessageData` to `repr` for `Interval` -/
instance : Lean.ToMessageData Interval where
  toMessageData x := x.toMessageData

/-- Unsafe native evaluation of interval expressions -/
unsafe def eval (x : Q(Interval)) : MetaM Interval :=
  Lean.Meta.evalExpr Interval q(Interval) x

/-- Prove a real inequality by lifting from `ℝ` to `Interval`.
    **Warning:** We use `native_decide`, so you must trust the compiler. -/
elab "interval" : tactic => do
  let g ← liftGoal (← getMainTarget)
  let f := g.app
  trace[interval.debug] "interval expr: {f}"
  -- Ideally, we'd be able to evaluate the interval first using `native_decide`, then
  -- re-evaluate them and show a nice error only if `native_decide` fails. But I don't
  -- know how to detect `native_decide` failure, so I'll do the check up-front.
  let ix ← unsafe eval g.x
  let iy ← unsafe eval g.y
  match g.op.eval ix iy with
    | false => throwError "interval: `{ix} {g.op} {iy}` is false"
    | true => do
      trace[interval] "interval: {ix} {g.op} {iy}"
      let gs ← (← getMainGoal).apply f
      match gs with
        | [a0, a1, op] => do
          -- Perform interval calculation
          close op (← `(tactic| native_decide))
          -- Prove conservativeness
          let approx ← `(tactic| approx)
          close a0 approx
          close a1 approx
        | _ => throwError "expected 3 goals, got {gs}"

end IntervalTactic

/-!
#### Tests for the `interval` tactic
-/
section IntervalTacticTests
open IntervalTactic (ile ilt)
open Real (log exp)

example : (2 : ℝ) < 3 := by interval
example : exp 1 < 2.7182818284591 := by interval
example : log 200 * 20000 ≤ 106000 := by interval
example : |exp (1 + log 7) - 19.02797279921331| < 1e-14 := by interval
example : (5 : ℝ) ^ (0.18732 : ℝ) < 1.351858 := by interval

end IntervalTacticTests
