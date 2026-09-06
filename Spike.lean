import Foundation.FirstOrder.Incompleteness.Tarski
import Foundation.FirstOrder.Arithmetic.Basic

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! # STAGE 2 PROBE — the two-body naming test
    Spike only. Nothing here is load-bearing. -/

/- ── BLOCK A: what the two quotes actually are ───────────────── -/

#check @LO.FirstOrder.Arithmetic.undefinability_of_truth
#check (inferInstance : Encodable ArithmeticSentence)
#check @Encodable.encodek
#check fun (σ : ArithmeticSentence) => (Encodable.encode σ : ℕ)
#check fun (σ : ArithmeticSentence) => (⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)

/- ── BLOCK B: the fibre space ────────────────────────────────── -/

abbrev Pt : Type := ℕ × Bool

/-- den₂ — DONE. The fibre index is taken as already being a
    statement: hand it to θ as a numeral, no act performed. -/
noncomputable def den2 (θ : ArithmeticSemisentence 1) (p : Pt) : Prop :=
  ℕ↓[ℒₒᵣ] ⊧ θ/[(⌜p.1⌝ : Semiterm ℒₒᵣ Empty 0)]

/-- den₁ — DOING. The decoder is performed inside the denotation.
    Fibre n names the sentence n decodes to, if any. -/
noncomputable def den1 (θ : ArithmeticSemisentence 1) (p : Pt) : Prop :=
  ∃ σ : ArithmeticSentence,
    Encodable.decode p.1 = some σ ∧
    ℕ↓[ℒₒᵣ] ⊧ θ/[(⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)]

#check @den1
#check @den2

/- ── BLOCK C: the joint the probe broke last time ────────────── -/

example (σ : ArithmeticSentence) :
    (⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)
      = (⌜(Encodable.encode σ : ℕ)⌝ : Semiterm ℒₒᵣ Empty 0) := by
  rfl

/- ── BLOCK D: THE TWO-BODY THEOREM ───────────────────────────── -/

theorem two_body (θ : ArithmeticSemisentence 1) (p : Pt) :
    den1 θ p ↔ den2 θ p := by
  constructor
  · rintro ⟨σ, hσ, h⟩
    have : Encodable.encode σ = p.1 := by
      have := Encodable.encodek σ
      omega_nat <;> simp_all
    simp_all [den2]
  · intro h
    refine ⟨?_, ?_, ?_⟩ <;> simp_all [den1, den2]

/- ── BLOCK E: does Tarski still land on den₁? ────────────────── -/

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

#print axioms two_body
#print axioms no_namer_den1
