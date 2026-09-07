import Mathlib
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.Incompleteness.Examples
import Foundation.FirstOrder.Incompleteness.Tarski

/-! # STAGE 2 — BUCKET 2: infinitely many true sentences.
    Needed for the TABLE branch of the three-way kill: tables have
    finite support, so `Tr` must be infinite for the branch to bite.
    Spike only. -/

open Function LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Iterated conjunction of ⊤ with itself: ⊤, ⊤ ⋏ ⊤, ⊤ ⋏ ⊤ ⋏ ⊤, ... -/
def topPow : ℕ → ArithmeticSentence
  | 0 => ⊤
  | n + 1 => (⊤ : ArithmeticSentence) ⋏ topPow n

#check @topPow

/-- Each is true in the standard model. -/
theorem topPow_true (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧ topPow n := by
  induction n with
  | zero => exact models_iff.mpr trivial
  | succ n ih =>
    show ℕ↓[ℒₒᵣ] ⊧ ((⊤ : ArithmeticSentence) ⋏ topPow n)
    exact?

/-- And they are pairwise distinct. -/
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
      exact congrArg Nat.succ (ih (by injection h with _ h2; exact h2))

#print axioms topPow_true
#print axioms topPow_inj
