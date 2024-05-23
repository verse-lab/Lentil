import Aesop
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.PushNeg
import Duper

-- basic semantics & connectives

def exec (α : Type) := ℕ → α
def predicate (α : Type) := exec α → Prop

def state_pred {α : Type} (f : α → Prop) : predicate α :=
  λ σ ↦ f (σ 0)

notation:50 "⌜" P "⌝" => (state_pred P)

def action (α : Type) := α → α → Prop
def action_pred {α : Type} (a : action α) : predicate α :=
  λ σ ↦ a (σ 0) (σ 1)

notation:90 "⟨" P:91 "⟩" => (action_pred P)

def drop {α : Type} (k : ℕ) (σ : exec α) : exec α := λ n ↦ σ (n + k)

notation:max σ "[" i ":]" => (drop i σ)

-- @[simp]
lemma drop_drop {α : Type} (k₀ k₁ : ℕ) (σ : exec α) : σ[k₀:][k₁:] = σ[k₀ + k₁:] :=
  by
    funext n
    simp [drop]
    apply congrArg
    linarith

def tla_and {α : Type} (p q : predicate α) : predicate α := λ σ ↦ p σ ∧ q σ
def tla_or {α : Type} (p q : predicate α) : predicate α := λ σ ↦ p σ ∨ q σ
def tla_implies {α : Type} (p q : predicate α) : predicate α := λ σ ↦ p σ → q σ
def tla_not {α : Type} (p : predicate α) : predicate α := λ σ ↦ ¬ p σ
def tla_forall {α β : Type} (p : α → predicate β) : predicate β := λ σ ↦ ∀ x, p x σ
def tla_exist {α β : Type} (p : α → predicate β) : predicate β := λ σ ↦ ∃ x, p x σ

infixr:55 "∧" => tla_and
infixr:55 "∨" => tla_or
infixr:30 "→" => tla_implies
prefix:66 "¬" => tla_not
notation:50 "∀" x:51 "," p:51 => (tla_forall (λ x ↦ p))
notation:50 "∃" x:51 "," p:51 => (tla_exist (λ x ↦ p))

def always {α : Type} (p : predicate α) : predicate α := λ σ ↦ ∀ k, p σ[k:]
def eventually {α : Type} (p : predicate α) : predicate α := λ σ ↦ ∃ k, p σ[k:]
def later {α : Type} (p : predicate α) : predicate α := λ σ ↦ p σ[1:]

prefix:66 "□" => always
prefix:66 "◇" => eventually
prefix:66 "◯" => later

-- FIXME: make this an infix?
def satisfies {α : Type} (p : predicate α) (σ : exec α) : Prop := p σ

notation:55 σ:56 "⊨" p:56 => (satisfies p σ)

def valid {α : Type} (p : predicate α) : Prop := ∀ σ, σ ⊨ p
def pred_implies {α : Type} (p q : predicate α) : Prop := ∀ σ, σ ⊨ p → σ ⊨ q

prefix:51 "⊢" => valid
infix:51 "⊢" => pred_implies

def enabled {α : Type} (a : action α) (s : α) : Prop := ∃ s', a s s'
def tla_enabled {α : Type} (a : action α) : predicate α := state_pred (enabled a)

def weak_fairness {α : Type} (a : action α) : predicate α := □ (□ (tla_enabled a) → ◇⟨a⟩)
def strong_fairness {α : Type} (a : action α) : predicate α := □ (□◇ (tla_enabled a) → ◇⟨a⟩)

prefix:51 "𝒲ℱ" => weak_fairness
prefix:51 "𝒮ℱ" => strong_fairness

def leads_to {α : Type} (p q : predicate α) : predicate α := □ (p → ◇ q)

infix:60 "↝" => leads_to

-- TODO until related?
