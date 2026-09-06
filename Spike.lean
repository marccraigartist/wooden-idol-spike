import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.Löb
import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.Incompleteness.Tarski
import Foundation.FirstOrder.Incompleteness.Examples

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

-- A. THE PROOF RELATION: what is the type of "IΣ₁ proves σ"?
#check fun (σ : ArithmeticSentence) => (𝗜𝚺₁ ⊢ σ)
#check (inferInstance : Entailment.Consistent 𝗜𝚺₁)
#check @Entailment.Consistent
#check (𝗜𝚺₁).consistent.val
#check (⊥ : ArithmeticSentence)

-- B. TRUTH AT THE STANDARD MODEL: the exact notation
#check @undefinability_of_truth
#print undefinability_of_truth

-- C. OPEN FORMULAS AND SUBSTITUTION: naming a subset of the wall
#check @ArithmeticSemisentence
#check fun (θ : ArithmeticSemisentence 1) (σ : ArithmeticSentence) => θ/[⌜σ⌝]
#check fun (n : ℕ) => (⌜n⌝ : Semiterm ℒₒᵣ Empty 0)

-- D. CODING: is every sentence's code a natural number, injectively?
#check fun (σ : ArithmeticSentence) => (⌜σ⌝ : ℕ)
