import Lentil.ProofMode.Tactics.Rename
import Lentil.ProofMode.Tactics.Revert

namespace TLA.ProofMode

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

theorem Entails_rcases_and {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
    (chosen name1 name2 : String) {a b : pred σ}
    (hpred : hyps.find? (fun h => h.name == chosen) = some ⟨chosen, tla_and a b⟩) :
    letI hyps' := hyps.eraseP fun h => h.name == chosen
    Entails (hyps' ++ [⟨name1, a⟩, ⟨name2, b⟩]) goal → Entails hyps goal := by
  unfold Entails
  simp only [List.map_append, repeatedAnd_append, ← impl_intro_add_r]
  intro h
  conv at h => enter [2] ; dsimp only [repeatedAnd, LentilLib.List.foldrD, List.map]
  apply Entails_revert (toRevert := chosen)
  rw [hpred] ; dsimp only [Option.elim] ; exact h

-- Not sure if this is generally useful, so just make it as a `private theorem` for now
private theorem exists_put_witness_back {α : Type v} {p : α → pred σ} {Γ g : pred σ} :
  (∀ x, ((Γ) |-tla- ((p x) → g))) = ((Γ) |-tla- ((∃ x, (p x)) → g)) := by tla_unfold_simp ; grind

-- NOTE: This proof is slightly repetitive with the one above
theorem Entails_rcases_exists {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
    (chosen : String) (newName : String)
    {α : Type v} {p : α → pred σ}
    (hpred : hyps.find? (fun h => h.name == chosen) = some ⟨chosen, tla_exists p⟩) :
    letI hyps' := hyps.eraseP fun h => h.name == chosen
    (∀ x : α, Entails (hyps' ++ [⟨newName, p x⟩]) goal) → Entails hyps goal := by
  unfold Entails
  simp only [List.map_append, repeatedAnd_append, ← impl_intro_add_r]
  intro h
  conv at h => enter [x, 2] ; dsimp only [repeatedAnd, LentilLib.List.foldrD, List.map]
  rw [exists_put_witness_back] at h
  apply Entails_revert (toRevert := chosen)
  rw [hpred] ; dsimp only [Option.elim] ; exact h

private def rcasesTacDSimps : Array Name :=
  #[``List.find?, ``List.eraseP, ``List.cons_append, ``List.nil_append,
  ``String.reduceBEq, ``String.reduceBNe,
  ``or, ``and, ``not, ``cond_true, ``cond_false]

/-- Generate a name for the hyp slot consumed by this pattern: idents land their
    own name; `_` and tuples get fresh hygienic names that may be re-targeted on
    the recursive call. -/
private def nameStrForPat (pat : TSyntax `rcasesPat) : TacticM String := do
  match pat with
  | `(rcasesPat| $name:ident) => return toString name.getId
  | _ =>
    let freshName ← mkFreshUserName `h
    -- Use something that cannot be a valid identifier to avoid accidental collision
    return "-" ++ toString freshName

/-- Unwrap a `rcasesPatLo` to its underlying single `rcasesPat`, rejecting `|`
    alternations and `: ty` ascriptions. -/
private def unwrapPatLo (p : TSyntax ``Lean.Parser.Tactic.rcasesPatLo) : TacticM (TSyntax `rcasesPat) := do
  match p with
  | `(rcasesPatLo| $_:rcasesPatMed : $_:term) =>
    throwError "tla_rcases: type ascription ': ty' is not supported"
  | `(rcasesPatLo| $med:rcasesPatMed) =>
    match med with
    | `(rcasesPatMed| $ps:rcasesPat|*) =>
      let elems := ps.getElems
      if elems.size == 1 then return elems[0]!
      else throwError "tla_rcases: alternation '|' is not supported"
    | _ => throwError "tla_rcases: unexpected rcasesPatMed shape"
  | _ => throwError "tla_rcases: unexpected rcasesPatLo shape"

/-- Are we facing a tuple pattern that needs another recursion? -/
private def isTuple (pat : TSyntax `rcasesPat) : Bool :=
  match pat with
  | `(rcasesPat| ⟨ $_,* ⟩) => true
  | _ => false

-- FIXME: There is some back and forth conversion of `List` and `Array`, and ideally
-- the list of patterns should only be processed once. They should be refactored
-- for a more efficient implementation in the future.
/-- Split tuple sub-patterns into (head, tail) with right-associative wrapping
    for n > 2: `[p₁, p₂, …, pₙ]` becomes `(p₁, ⟨p₂, …, pₙ⟩)`. -/
private def splitBinaryRightAssoc (pats : Array (TSyntax ``Lean.Parser.Tactic.rcasesPatLo))
    : TacticM (TSyntax `rcasesPat × TSyntax `rcasesPat) := do
  match pats.toList with
  | [] => throwError "tla_rcases: empty tuple ⟨⟩ is not supported"
  | [_] => throwError "tla_rcases: unary tuple ⟨..⟩ is not supported; drop the brackets"
  | [p1, p2] => return (← unwrapPatLo p1, ← unwrapPatLo p2)
  | p1 :: rest =>
    let restArr := rest.toArray
    let tup ← `(rcasesPat| ⟨ $[$restArr],* ⟩)
    return (← unwrapPatLo p1, tup)

partial def tlaRcasesCore (currentHypStr : String) (pat : TSyntax `rcasesPat) : TacticM Unit := do
  match pat with
  | `(rcasesPat| $name:ident) =>
    let nameStr := toString name.getId
    -- Essentially renaming
    if nameStr != currentHypStr then
      let hypIdent := mkIdent (.mkSimple currentHypStr)
      evalTactic <| ← `(tactic| tla_rename $hypIdent:ident => $name:ident)
  | `(rcasesPat| _) =>
    -- FIXME: This is not very good, since the generated names are not readable.
    -- A better design should be to only support `-` at the tail positions.
    pure ()
  | `(rcasesPat| ⟨ $pats,* ⟩) =>
    let (pat1, pat2) ← splitBinaryRightAssoc pats.getElems
    let some (_, hyps) ← recognizeEntailsHypsFromGoal | throwError "tla_rcases: failed to read the hypotheses from the goal"
    let some (_, pred) := hyps.find? (fun ⟨n, _⟩ => n == currentHypStr) | throwError "tla_rcases: hypothesis '{currentHypStr}' not found in the goal's Entails list"
    match_expr pred with
    | TLA.tla_and _ _ _ =>
      let n1Str ← nameStrForPat pat1
      let n2Str ← nameStrForPat pat2
      -- Inline `hpred := by rfl` so Lean can pin down the implicit `a, b` at
      -- the time `refine` is elaborated (they don't otherwise appear in the
      -- visible conclusion).
      evalTactic <| ← `(tactic|
        refine $(mkIdent ``Entails_rcases_and)
          ($(quote currentHypStr)) ($(quote n1Str)) ($(quote n2Str)) (by rfl) ?_)
      postDSimpAfterApplyingReflectionTheorem rcasesTacDSimps
      if isTuple pat1 then tlaRcasesCore n1Str pat1
      if isTuple pat2 then tlaRcasesCore n2Str pat2
    | TLA.tla_exists _ _ _ =>
      let nInnerStr ← nameStrForPat pat2
      evalTactic <| ← `(tactic|
        refine $(mkIdent ``Entails_rcases_exists)
          ($(quote currentHypStr)) ($(quote nInnerStr)) (by rfl) ?_)
      evalTactic <| ← `(tactic| rintro $pat1)
      postDSimpAfterApplyingReflectionTheorem rcasesTacDSimps
      if isTuple pat2 then tlaRcasesCore nInnerStr pat2
    | _ =>
      throwError "tla_rcases: cannot destructure pred {pred} with pattern {pat}"
  | _ =>
    throwError "tla_rcases: unsupported pattern (use ident, '_', or ⟨..⟩ tuples)"

/--
`tla_rcases h with pat` destructures a temporal hypothesis in the proof-mode
context.

If `h : p ∧ q`, then
```lean
tla_rcases h with ⟨hp, hq⟩
```
removes `h` and adds `hp : p` and `hq : q`. If `h : ∃ x, P x`, then
```lean
tla_rcases h with ⟨x, hx⟩
```
introduces a Lean witness `x` and a temporal hypothesis `hx : P x`.
-/
syntax (name := tlaRcasesTac) "tla_rcases" ident " with " rcasesPat : tactic

elab_rules : tactic
  | `(tactic| tla_rcases $hyp:ident with $pat) => withMainContext do
    tlaRcasesCore (toString hyp.getId) pat

end TLA.ProofMode
