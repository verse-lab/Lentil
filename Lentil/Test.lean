import Lentil.Basic

-- challenge: to what extent can you automate the following proofs?

macro "unseal" : tactic =>
  `(tactic|
      (simp [pred_implies, leads_to, satisfies, tla_implies, always, eventually, drop_drop] at *))

lemma leads_to_trans {α} {Γ p q r : predicate α} :
  Γ ⊢ p ↝ q → Γ ⊢ q ↝ r → Γ ⊢ p ↝ r :=
  by
    intro h1 h2
    unseal
    intro σ h k hh
    specialize h1 σ h k hh
    sorry
