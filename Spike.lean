import Mathlib
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.Incompleteness.Examples
import Foundation.FirstOrder.Incompleteness.Tarski

/-! # STAGE 2 — BUCKET 1b: the true-sentence witness for `Tr` nontriviality.
    Everything else in bucket 1 certified last build. Spike only. -/

open Function LO LO.FirstOrder LO.FirstOrder.Arithmetic

def Tr (p : ℕ × Bool) : Prop :=
  ∃ σ : ArithmeticSentence, Encodable.decode p.1 = some σ ∧ ℕ↓[ℒₒᵣ] ⊧ σ

/- ── candidate true sentences: which one elaborates and is true? ── -/

/-- Candidate A: implication from falsum to falsum. -/
example : ℕ↓[ℒₒᵣ] ⊧ ((⊥ : ArithmeticSentence) ➝ (⊥ : ArithmeticSentence)) := by
  simp

/-- Candidate B: negation of falsum. -/
example : ℕ↓[ℒₒᵣ] ⊧ (∼(⊥ : ArithmeticSentence)) := by
  simp

/-- Candidate C: an equation in the binder notation. -/
example : ℕ↓[ℒₒᵣ] ⊧ (“0 = 0” : ArithmeticSentence) := by
  simp

/- ── the branch, using candidate A ───────────────────────────── -/

theorem Tr_no_snt_A :
    ¬ ∃ σ : ArithmeticSentence, ∀ p : ℕ × Bool,
        (𝗜𝚺₁ ⊢ σ) ↔ Tr p := by
  rintro ⟨σ, h⟩
  have hzero : ¬ Tr (0, false) := by
    rintro ⟨τ, hτ, -⟩
    exact absurd hτ (by decide)
  have hone : Tr
      (Encodable.encode ((⊥ : ArithmeticSentence) ➝ (⊥ : ArithmeticSentence)),
       false) := by
    refine ⟨_, Encodable.encodek _, ?_⟩
    simp
  exact hzero ((h (0, false)).mp ((h _).mpr hone))

#print axioms Tr_no_snt_A
