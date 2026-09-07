import Mathlib
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.Incompleteness.Examples
import Foundation.FirstOrder.Incompleteness.Tarski

/-! # STAGE 2 — BUCKET 2c: infinitely many TRUE sentences.
    `topPow_inj` already reports [propext]; only the conjunction
    case of `topPow_true` outstanding. Spike only. -/

open Function LO LO.FirstOrder LO.FirstOrder.Arithmetic

def topPow : ℕ → ArithmeticSentence
  | 0 => ⊤
  | n + 1 => (⊤ : ArithmeticSentence) ⋏ topPow n

#check @LO.Semantics.And.models_and
#check @LO.Semantics.Top.models_verum

/- Route A — Charlie's, assuming `models_and` is an iff. -/

example (σ τ : ArithmeticSentence)
    (h1 : ℕ↓[ℒₒᵣ] ⊧ σ) (h2 : ℕ↓[ℒₒᵣ] ⊧ τ) :
    ℕ↓[ℒₒᵣ] ⊧ (σ ⋏ τ) :=
  LO.Semantics.And.models_and.mpr ⟨h1, h2⟩

/- Route B — the same, if it is a plain implication. -/

example (σ τ : ArithmeticSentence)
    (h1 : ℕ↓[ℒₒᵣ] ⊧ σ) (h2 : ℕ↓[ℒₒᵣ] ⊧ τ) :
    ℕ↓[ℒₒᵣ] ⊧ (σ ⋏ τ) :=
  LO.Semantics.And.models_and _ ⟨h1, h2⟩

/- Route C — via models_iff, no named conjunction lemma at all. -/

example (σ τ : ArithmeticSentence)
    (h1 : ℕ↓[ℒₒᵣ] ⊧ σ) (h2 : ℕ↓[ℒₒᵣ] ⊧ τ) :
    ℕ↓[ℒₒᵣ] ⊧ (σ ⋏ τ) := by
  rw [models_iff] at h1 h2 ⊢
  exact ⟨h1, h2⟩

/- ── the theorems ────────────────────────────────────────────── -/

theorem topPow_true (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧ topPow n := by
  induction n with
  | zero => exact LO.Semantics.Top.models_verum _
  | succ n ih =>
    exact LO.Semantics.And.models_and.mpr
      ⟨LO.Semantics.Top.models_verum _, ih⟩

theorem topPow_inj : Function.Injective topPow := by
  intro a b h
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => rfl
    | succ m => exact absurd h (by simp [topPow])
  | succ n ih =>
    cases b with
    | zero => exact absurd h (by simp [topPow])
    | succ m =>
      simp only [topPow] at h
      exact congrArg Nat.succ (ih (by injection h))

#print axioms topPow_true
#print axioms topPow_inj
