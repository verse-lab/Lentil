import Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

private def checkNamedHyps (actualHyps expectedHyps : List (String × Expr)) : MetaM Unit :=
  go 0 actualHyps expectedHyps
where go : Nat → List (String × Expr) → List (String × Expr) → MetaM Unit
  | _, [], [] => pure ()
  | idx, (actualName, actualPred) :: actualHyps,
      (expectedName, expectedPred) :: expectedHyps => do
    unless actualName == expectedName do
      throwError "tcheck_goal: temporal hypothesis {idx} is named '{actualName}', expected '{expectedName}'"
    unless ← isDefEq actualPred expectedPred do
      throwError "tcheck_goal: temporal hypothesis '{actualName}' has predicate{indentExpr actualPred}\nbut expected{indentExpr expectedPred}"
    go (idx + 1) actualHyps expectedHyps
  | _, _, _ => throwError "tcheck_goal: internal hypothesis-count mismatch"

/--
`tcheck_goal_form` checks that the current proof-mode goal is in the
canonical literal `Entails [...] goal` form used by the proof-mode tactics.

It does not change the goal. This is useful in tests after a tactic that
reflects over the hypothesis list: if the goal still contains unreduced list
computations, then the check fails.
-/
elab "tcheck_goal_form" : tactic => do
  unless (← recognizeEntailsHypsFromGoal).isSome do
    throwError "tcheck_goal_form: goal is not in canonical Entails form"

/--
`tcheck_goal expected` checks that the current proof-mode goal has the
literal named hypothesis list and target predicate in `expected`.

Unlike `show Entails [...] goal`, this tactic does not forget proof-mode
hypothesis names. For example,
```lean
tcheck_goal Entails [⟨"hp", p⟩, ⟨"hq", q⟩] r
```
checks that the context contains exactly `hp : p` followed by `hq : q`, and
that the goal is `r`. Predicates are compared by definitional equality.
-/
elab "tcheck_goal " expected:term : tactic => withMainContext do
  let (actualσ, _, _, actualHyps, actualGoal) ←
    parseCanonicalEntails (← getMainTarget)
      m!"tcheck_goal: goal is not in canonical Entails form"
  let expected ← Term.withoutErrToSorry <| Term.elabTermAndSynthesize expected none
  let (expectedσ, _, _, expectedHyps, expectedGoal) ←
    parseCanonicalEntails expected
      m!"tcheck_goal: expected an Entails expression with a literal hypothesis list"
  unless ← isDefEq actualσ expectedσ do
    throwError "tcheck_goal: expected state type{indentExpr expectedσ}\nbut the goal has state type{indentExpr actualσ}"
  unless actualHyps.length == expectedHyps.length do
    throwError "tcheck_goal: expected {expectedHyps.length} temporal hypotheses, but the goal has {actualHyps.length}"
  checkNamedHyps actualHyps expectedHyps
  unless ← isDefEq actualGoal expectedGoal do
    throwError "tcheck_goal: goal predicate is{indentExpr actualGoal}\nbut expected{indentExpr expectedGoal}"

end TLA.ProofMode
