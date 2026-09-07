import Mathlib
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.Incompleteness.Examples
import Foundation.FirstOrder.Incompleteness.Tarski

/-! # STAGE 2 — BUCKET 1c: ask the library, don't guess.
    Find (i) a true arithmetic sentence, (ii) the lemma that proves it true.
    Spike only. -/

open Function LO LO.FirstOrder LO.FirstOrder.Arithmetic

/- ── what IS a sentence, and what operations does it have? ────── -/

#check (⊥ : ArithmeticSentence)
#check (∼(⊥ : ArithmeticSentence))
#check fun (σ τ : ArithmeticSentence) => σ ⋏ τ
#check fun (σ τ : ArithmeticSentence) => σ ⋎ τ

/- ── the satisfaction relation, unfolded ─────────────────────── -/

#check @LO.FirstOrder.Arithmetic.undefinability_of_truth

example : ¬ (ℕ↓[ℒₒᵣ] ⊧ (⊥ : ArithmeticSentence)) := by
  exact?

example : ℕ↓[ℒₒᵣ] ⊧ (∼(⊥ : ArithmeticSentence)) := by
  exact?

/- ── if the above works, the nontriviality is immediate ───────── -/

def Tr (p : ℕ × Bool) : Prop :=
  ∃ σ : ArithmeticSentence, Encodable.decode p.1 = some σ ∧ ℕ↓[ℒₒᵣ] ⊧ σ

example : ¬ Tr (0, false) := by
  rintro ⟨τ, hτ, -⟩
  exact absurd hτ (by decide)
