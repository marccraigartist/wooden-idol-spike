import Foundation.FirstOrder.Incompleteness.Tarski
import Foundation.FirstOrder.Arithmetic.Basic

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! # STAGE 2 PROBE — bucket 2: does the wall have silent addresses?
    Spike only. Nothing here is load-bearing. -/

/- ── BLOCK A: confirm the joint from bucket 1 ────────────────── -/

#check @LO.FirstOrder.Arithmetic.undefinability_of_truth
#check (inferInstance : Encodable ArithmeticSentence)

/-- The joint that passed by `rfl` last build. Restated alone,
    with nothing around it, so the pass is unambiguous. -/
example (σ : ArithmeticSentence) :
    (⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)
      = (⌜(Encodable.encode σ : ℕ)⌝ : Semiterm ℒₒᵣ Empty 0) := by
  rfl

/- ── BLOCK B: the two bodies ─────────────────────────────────── -/

abbrev Pt : Type := ℕ × Bool

/-- den₂ — DONE. Every address is handed to θ as a statement. -/
noncomputable def den2 (θ : ArithmeticSemisentence 1) (p : Pt) : Prop :=
  ℕ↓[ℒₒᵣ] ⊧ θ/[(⌜p.1⌝ : Semiterm ℒₒᵣ Empty 0)]

/-- den₁ — DOING. The reading is performed, and can fail. -/
noncomputable def den1 (θ : ArithmeticSemisentence 1) (p : Pt) : Prop :=
  ∃ σ : ArithmeticSentence,
    Encodable.decode p.1 = some σ ∧
    ℕ↓[ℒₒᵣ] ⊧ θ/[(⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)]

/- ── BLOCK C: the one direction that should hold ─────────────── -/

/-- Where the reading succeeds, the doing agrees with the done. -/
theorem den1_imp_den2 (θ : ArithmeticSemisentence 1) (p : Pt) :
    den1 θ p → den2 θ p := by
  rintro ⟨σ, hσ, h⟩
  have he : Encodable.encode σ = p.1 := by
    have := Encodable.encode_decode (α := ArithmeticSentence) p.1
    rw [hσ] at this
    simpa using this.symm
  unfold den2
  rw [← he]
  exact h

/- ── BLOCK D: THE DECIDING QUESTION ──────────────────────────── -/
/-  Is `decode` total on ℕ?  If some address reads as nothing,
    den₂ speaks where den₁ is silent and the two bodies are two.  -/

/-- Attempt 1: is decoding surjective onto `some`? If this fails,
    silent addresses exist. -/
example : ∀ n : ℕ, ∃ σ : ArithmeticSentence,
    Encodable.decode n = some σ := by
  intro n
  exact ⟨_, rfl⟩

/-- Attempt 2: the negation — a silent address exists. -/
example : ∃ n : ℕ, (Encodable.decode n : Option ArithmeticSentence) = none := by
  exact ⟨0, rfl⟩

/-- Attempt 3: address 0, printed either way. -/
#reduce (Encodable.decode 0 : Option ArithmeticSentence)
#eval (Encodable.decode 0 : Option ArithmeticSentence).isSome
#eval (Encodable.decode 1 : Option ArithmeticSentence).isSome
#eval (Encodable.decode 2 : Option ArithmeticSentence).isSome
#eval (Encodable.decode 7 : Option ArithmeticSentence).isSome

/- ── BLOCK E: the destination, restated ──────────────────────── -/

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

#print axioms den1_imp_den2
#print axioms no_namer_den1
