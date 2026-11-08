module

public import Lentil.Rules.BigOp

/-! Typeclasses describing how a single temporal hypothesis behaves under a
modality, used by the proof-mode modality tactics.

As in the Iris proof mode, a tactic walks over the proof-mode context and
queries one instance per hypothesis; the typeclass search then descends through
the structure of that hypothesis. To support a custom connective, add an
instance.

A leading modality hidden behind a `[tl_modality_unfold]` head is recognized by
the tactics themselves, so such a definition needs no instance as long as it
occurs at the top of a hypothesis. Underneath another connective (e.g.
`∀ x, wrapped (p x)`), it needs its own instance, like the built-in wrappers
below.

NOTE: On the choice of typeclasses. Originally, the tactics recognized a leading
modality syntactically and thus rejected hypotheses such as `∀ x, □ p x`, where
the modality sits underneath another connective. A first fix also looked
underneath `∀` at the meta level and certified each rewritten hypothesis with an
equation, e.g. `(∀ x, □ p x) = □ (∀ x, p x)`. Typeclasses improve on both:
- Instances prove entailments (`p |-tl- □ q`) rather than equations, so they
  also cover hypotheses that only imply `□` of their peeled form: `∃ x, □ p x`
  and `□ p ∨ □ q` peel to `∃ x, p x` and `p ∨ q`, but are not equal to
  `□ (∃ x, p x)` and `□ (p ∨ q)`.
- Instance resolution is the structural recursion that the meta code would
  otherwise implement by hand (nested `∀`s, `⋀ x ∈ l, □ p x`, `◯ □ p`, ...),
  but it is open: a new connective, or a definition hiding a modality, needs
  one instance rather than a commuting lemma plus a new case in the meta code.
- Per hypothesis, the tactics make a single instance query instead of
  assembling a rewriting proof, and a failed query yields an actionable error:
  it names the hypothesis and the class that lacks an instance.

One caveat: instance resolution returns eta-reduced terms carrying the binder
names of the instances, so the tactics restore the user's binder names
afterwards (`alignBinders`). -/

namespace Lentil.ProofMode

open Lentil

@[expose] public section

section

variable {σ : Type u}

/-- `p |-tl- □ q`: `tmonotone` turns a hypothesis `p` into `q` under a goal `□ r`. -/
class IntoAlways (p : pred σ) (q : outParam (pred σ)) : Prop where
  into_always : (p) |-tl- (□ q)

/-- `p |-tl- ◯ q`: `tmonotone` turns a hypothesis `p` into `q` under a goal `◯ r`. -/
class IntoLater (p : pred σ) (q : outParam (pred σ)) : Prop where
  into_later : (p) |-tl- (◯ q)

/-- `p |-tl- □ p`: a hypothesis `p` remains valid at every later time point, so
`ttoggle_goal_under_always` and `tadvance` can keep it unchanged. -/
class AlwaysStable (p : pred σ) : Prop where
  always_stable : (p) |-tl- (□ p)

section IntoAlways

instance intoAlways_always (p : pred σ) : IntoAlways [tlfml| □ p] p := ⟨pred_implies_refl _⟩

instance intoAlways_leads_to (p q : pred σ) : IntoAlways [tlfml| p ↝ q] [tlfml| p → ◇ q] :=
  ⟨pred_implies_refl _⟩

instance intoAlways_always_implies (p q : pred σ) : IntoAlways [tlfml| p ⇒ q] [tlfml| p → q] :=
  ⟨pred_implies_refl _⟩

instance intoAlways_weak_fairness (a : action σ) :
    IntoAlways [tlfml| 𝒲ℱ a] [tlfml| (□ (Enabled a)) → ◇ ⟨a⟩] := ⟨pred_implies_refl _⟩

instance intoAlways_strong_fairness (a : action σ) :
    IntoAlways [tlfml| 𝒮ℱ a] [tlfml| (□ ◇ (Enabled a)) → ◇ ⟨a⟩] := ⟨pred_implies_refl _⟩

-- CHECK Might rewrite some of the proofs below using rules

instance intoAlways_forall {α : Sort v} (p q : α → pred σ) [h : ∀ x, IntoAlways (p x) (q x)] :
    IntoAlways (tl_forall p) (tl_forall q) :=
  ⟨fun e i hp k x => (h x).into_always e i (hp x) k⟩

instance intoAlways_exists {α : Sort v} (p q : α → pred σ) [h : ∀ x, IntoAlways (p x) (q x)] :
    IntoAlways (tl_exists p) (tl_exists q) :=
  ⟨fun e i hp k => let ⟨x, hx⟩ := hp ; ⟨x, (h x).into_always e i hx k⟩⟩

instance intoAlways_and (p₁ p₂ q₁ q₂ : pred σ) [h₁ : IntoAlways p₁ q₁] [h₂ : IntoAlways p₂ q₂] :
    IntoAlways [tlfml| p₁ ∧ p₂] [tlfml| q₁ ∧ q₂] :=
  ⟨fun e i hp k => ⟨h₁.into_always e i hp.1 k, h₂.into_always e i hp.2 k⟩⟩

instance intoAlways_or (p₁ p₂ q₁ q₂ : pred σ) [h₁ : IntoAlways p₁ q₁] [h₂ : IntoAlways p₂ q₂] :
    IntoAlways [tlfml| p₁ ∨ p₂] [tlfml| q₁ ∨ q₂] :=
  ⟨fun e i hp k => hp.elim (fun h => .inl (h₁.into_always e i h k)) (fun h => .inr (h₂.into_always e i h k))⟩

instance intoAlways_later (p q : pred σ) [h : IntoAlways p q] : IntoAlways [tlfml| ◯ p] [tlfml| ◯ q] :=
  ⟨fun e i hp k => by
    have h' := h.into_always e (i + 1) hp k
    show q e (i + k + 1)
    rwa [show i + k + 1 = i + 1 + k by omega]⟩

instance intoAlways_bigwedge {β : Type v} (p q : β → pred σ) (l : List β)
    [h : ∀ x, IntoAlways (p x) (q x)] : IntoAlways (tl_bigwedge p l) (tl_bigwedge q l) := ⟨by
  rw [bigwedge_forall_list p l, bigwedge_forall_list q l]
  exact fun e i hp k x hx => (h x).into_always e i (hp x hx) k⟩

instance intoAlways_bigvee {β : Type v} (p q : β → pred σ) (l : List β)
    [h : ∀ x, IntoAlways (p x) (q x)] : IntoAlways (tl_bigvee p l) (tl_bigvee q l) := ⟨by
  rw [bigvee_exists_list p l, bigvee_exists_list q l]
  exact fun e i hp k => let ⟨x, hx, hpx⟩ := hp ; ⟨x, hx, (h x).into_always e i hpx k⟩⟩

instance intoAlways_pure (P : Prop) : @IntoAlways σ [tlfml| ⌞ P ⌟] [tlfml| ⌞ P ⌟] :=
  ⟨fun _ _ h _ => h⟩

instance intoAlways_true : @IntoAlways σ tl_true tl_true := intoAlways_pure _

instance intoAlways_false : @IntoAlways σ tl_false tl_false := intoAlways_pure _

end IntoAlways

section IntoLater

instance intoLater_later (p : pred σ) : IntoLater [tlfml| ◯ p] p := ⟨pred_implies_refl _⟩

instance intoLater_forall {α : Sort v} (p q : α → pred σ) [h : ∀ x, IntoLater (p x) (q x)] :
    IntoLater (tl_forall p) (tl_forall q) :=
  ⟨fun e i hp x => (h x).into_later e i (hp x)⟩

instance intoLater_exists {α : Sort v} (p q : α → pred σ) [h : ∀ x, IntoLater (p x) (q x)] :
    IntoLater (tl_exists p) (tl_exists q) :=
  ⟨fun e i hp => let ⟨x, hx⟩ := hp ; ⟨x, (h x).into_later e i hx⟩⟩

instance intoLater_and (p₁ p₂ q₁ q₂ : pred σ) [h₁ : IntoLater p₁ q₁] [h₂ : IntoLater p₂ q₂] :
    IntoLater [tlfml| p₁ ∧ p₂] [tlfml| q₁ ∧ q₂] :=
  ⟨fun e i hp => ⟨h₁.into_later e i hp.1, h₂.into_later e i hp.2⟩⟩

instance intoLater_or (p₁ p₂ q₁ q₂ : pred σ) [h₁ : IntoLater p₁ q₁] [h₂ : IntoLater p₂ q₂] :
    IntoLater [tlfml| p₁ ∨ p₂] [tlfml| q₁ ∨ q₂] :=
  ⟨fun e i hp => hp.elim (fun h => .inl (h₁.into_later e i h)) (fun h => .inr (h₂.into_later e i h))⟩

instance intoLater_always (p q : pred σ) [h : IntoLater p q] : IntoLater [tlfml| □ p] [tlfml| □ q] :=
  ⟨fun e i hp k => by
    have h' := h.into_later e (i + k) (hp k)
    show q e (i + 1 + k)
    rwa [show i + 1 + k = i + k + 1 by omega]⟩

instance intoLater_eventually (p q : pred σ) [h : IntoLater p q] :
    IntoLater [tlfml| ◇ p] [tlfml| ◇ q] :=
  ⟨fun e i hp => let ⟨k, hk⟩ := hp ; ⟨k, by
    have h' := h.into_later e (i + k) hk
    show q e (i + 1 + k)
    rwa [show i + 1 + k = i + k + 1 by omega]⟩⟩

instance intoLater_bigwedge {β : Type v} (p q : β → pred σ) (l : List β)
    [h : ∀ x, IntoLater (p x) (q x)] : IntoLater (tl_bigwedge p l) (tl_bigwedge q l) := ⟨by
  rw [bigwedge_forall_list p l, bigwedge_forall_list q l]
  exact fun e i hp x hx => (h x).into_later e i (hp x hx)⟩

instance intoLater_bigvee {β : Type v} (p q : β → pred σ) (l : List β)
    [h : ∀ x, IntoLater (p x) (q x)] : IntoLater (tl_bigvee p l) (tl_bigvee q l) := ⟨by
  rw [bigvee_exists_list p l, bigvee_exists_list q l]
  exact fun e i hp => let ⟨x, hx, hpx⟩ := hp ; ⟨x, hx, (h x).into_later e i hpx⟩⟩

instance intoLater_pure (P : Prop) : @IntoLater σ [tlfml| ⌞ P ⌟] [tlfml| ⌞ P ⌟] :=
  ⟨fun _ _ h => h⟩

instance intoLater_true : @IntoLater σ tl_true tl_true := intoLater_pure _

instance intoLater_false : @IntoLater σ tl_false tl_false := intoLater_pure _

end IntoLater

section AlwaysStable

instance alwaysStable_always (p : pred σ) : AlwaysStable [tlfml| □ p] :=
  ⟨fun e i hp k j => by rw [Nat.add_assoc] ; exact hp (k + j)⟩

instance alwaysStable_leads_to (p q : pred σ) : AlwaysStable [tlfml| p ↝ q] := alwaysStable_always _

instance alwaysStable_always_implies (p q : pred σ) : AlwaysStable [tlfml| p ⇒ q] :=
  alwaysStable_always _

instance alwaysStable_weak_fairness (a : action σ) : AlwaysStable [tlfml| 𝒲ℱ a] := alwaysStable_always _

instance alwaysStable_strong_fairness (a : action σ) : AlwaysStable [tlfml| 𝒮ℱ a] :=
  alwaysStable_always _

instance alwaysStable_eventually_always (p : pred σ) : AlwaysStable [tlfml| ◇ □ p] :=
  ⟨fun e i hp k => let ⟨j, hj⟩ := hp ; ⟨j, fun m => by
    have h' := hj (k + m)
    rwa [show i + k + j + m = i + j + (k + m) by omega]⟩⟩

instance alwaysStable_forall {α : Sort v} (p : α → pred σ) [h : ∀ x, AlwaysStable (p x)] :
    AlwaysStable (tl_forall p) :=
  ⟨fun e i hp k x => (h x).always_stable e i (hp x) k⟩

instance alwaysStable_exists {α : Sort v} (p : α → pred σ) [h : ∀ x, AlwaysStable (p x)] :
    AlwaysStable (tl_exists p) :=
  ⟨fun e i hp k => let ⟨x, hx⟩ := hp ; ⟨x, (h x).always_stable e i hx k⟩⟩

instance alwaysStable_and (p q : pred σ) [hp : AlwaysStable p] [hq : AlwaysStable q] :
    AlwaysStable [tlfml| p ∧ q] :=
  ⟨fun e i h k => ⟨hp.always_stable e i h.1 k, hq.always_stable e i h.2 k⟩⟩

instance alwaysStable_or (p q : pred σ) [hp : AlwaysStable p] [hq : AlwaysStable q] :
    AlwaysStable [tlfml| p ∨ q] :=
  ⟨fun e i h k => h.elim (fun h => .inl (hp.always_stable e i h k)) (fun h => .inr (hq.always_stable e i h k))⟩

instance alwaysStable_later (p : pred σ) [h : AlwaysStable p] : AlwaysStable [tlfml| ◯ p] :=
  ⟨fun e i hp k => by
    have h' := h.always_stable e (i + 1) hp k
    show p e (i + k + 1)
    rwa [show i + k + 1 = i + 1 + k by omega]⟩

instance alwaysStable_bigwedge {β : Type v} (p : β → pred σ) (l : List β)
    [h : ∀ x, AlwaysStable (p x)] : AlwaysStable (tl_bigwedge p l) := ⟨by
  rw [bigwedge_forall_list p l]
  exact fun e i hp k x hx => (h x).always_stable e i (hp x hx) k⟩

instance alwaysStable_bigvee {β : Type v} (p : β → pred σ) (l : List β)
    [h : ∀ x, AlwaysStable (p x)] : AlwaysStable (tl_bigvee p l) := ⟨by
  rw [bigvee_exists_list p l]
  exact fun e i hp k => let ⟨x, hx, hpx⟩ := hp ; ⟨x, hx, (h x).always_stable e i hpx k⟩⟩

instance alwaysStable_pure (P : Prop) : @AlwaysStable σ [tlfml| ⌞ P ⌟] := ⟨fun _ _ h _ => h⟩

instance alwaysStable_true : @AlwaysStable σ tl_true := alwaysStable_pure _

instance alwaysStable_false : @AlwaysStable σ tl_false := alwaysStable_pure _

end AlwaysStable

end

end

end Lentil.ProofMode
