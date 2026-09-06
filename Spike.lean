import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.Incompleteness.Tarski
import Foundation.FirstOrder.Incompleteness.Examples

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

-- 1. THE JOINT: does the sentence-quote agree with the numeral-quote?
example (σ : ArithmeticSentence) (θ : ArithmeticSemisentence 1) :
    θ/[⌜σ⌝] = θ/[⌜(⌜σ⌝ : ℕ)⌝] := rfl

-- 2. DENOTATION AT A FIBRE: is this well-formed as a Prop?
#check fun (θ : ArithmeticSemisentence 1) (n : ℕ) => (ℕ↓[ℒₒᵣ] ⊧ θ/[⌜n⌝])

-- 3. THE TRUTH SET, as a predicate on fibre indices
#check fun (n : ℕ) => ∃ σ : ArithmeticSentence, (⌜σ⌝ : ℕ) = n ∧ ℕ↓[ℒₒᵣ] ⊧ σ

-- 4. IS THE CODING INJECTIVE? (needed to pull the witness back)
example : Function.Injective (fun σ : ArithmeticSentence => (⌜σ⌝ : ℕ)) := by
  exact?

-- 5. NONTRIVIALITY: a true sentence and a false one
#check (⊤ : ArithmeticSentence)
example : ℕ↓[ℒₒᵣ] ⊧ (⊤ : ArithmeticSentence) := by simp
example : ¬ (ℕ↓[ℒₒᵣ] ⊧ (⊥ : ArithmeticSentence)) := by simp
