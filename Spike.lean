import Foundation.FirstOrder.Incompleteness.Tarski
import Foundation.FirstOrder.Arithmetic.Basic

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! # STAGE 2 PROBE — bucket 2b: silent addresses, minimal.
    Spike only. Nothing load-bearing. -/

/- ── BLOCK A: the joint, confirmed twice already ─────────────── -/

example (σ : ArithmeticSentence) :
    (⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)
      = (⌜(Encodable.encode σ : ℕ)⌝ : Semiterm ℒₒᵣ Empty 0) := by
  rfl

/- ── BLOCK B: the two bodies ─────────────────────────────────── -/

abbrev Pt : Type := ℕ × Bool

noncomputable def den2 (θ : ArithmeticSemisentence 1) (p : Pt) : Prop :=
  ℕ↓[ℒₒᵣ] ⊧ θ/[(⌜p.1⌝ : Semiterm ℒₒᵣ Empty 0)]

noncomputable def den1 (θ : ArithmeticSemisentence 1) (p : Pt) : Prop :=
  ∃ σ : ArithmeticSentence,
    Encodable.decode p.1 = some σ ∧
    ℕ↓[ℒₒᵣ] ⊧ θ/[(⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)]

/- ── BLOCK C: THE DECIDING QUESTION. No proofs. ──────────────── -/
/-  Does the wall have addresses that read as nothing?
    true  = that address reads as a sentence
    false = silent address, den2 speaks where den1 is mute       -/

#eval (Encodable.decode 0 : Option ArithmeticSentence).isSome
#eval (Encodable.decode 1 : Option ArithmeticSentence).isSome
#eval (Encodable.decode 2 : Option ArithmeticSentence).isSome
#eval (Encodable.decode 3 : Option ArithmeticSentence).isSome
#eval (Encodable.decode 7 : Option ArithmeticSentence).isSome
#eval (Encodable.decode 42 : Option ArithmeticSentence).isSome
#eval (Encodable.decode 100 : Option ArithmeticSentence).isSome

#eval ((List.range 200).filter
  (fun n => ((Encodable.decode n : Option ArithmeticSentence)).isSome)).length

/- ── BLOCK D: the destination, restated ──────────────────────── -/

theorem no_namer_den1 :
    ¬ ∃ θ : ArithmeticSemisentence 1,
        ∀ σ : ArithmeticSentence,
          (ℕ↓[ℒₒᵣ] ⊧ σ) ↔ den1 θ (Encodable.encode σ, false) := by
  rintro ⟨θ, hθ⟩
  apply undefinability_of_truth
  refine ⟨θ, fun σ => ?_⟩
  have h := hθ σ
  simp [den1, Encodable.encodek] at h
  exact h

#print axioms no_namer_den1
