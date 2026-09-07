import Mathlib
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.Incompleteness.Examples
import Foundation.FirstOrder.Incompleteness.Tarski

/-! # STAGE 2 — BUCKET 1. Only `Tr_notall` outstanding. Spike only. -/

open Function LO LO.FirstOrder LO.FirstOrder.Arithmetic

inductive WallL2 : Type
  | tbl : ℕ → WallL2
  | snt : ArithmeticSentence → WallL2
  | frm : ArithmeticSemisentence 1 → WallL2

def bitAtP (e p : ℕ) : Bool := e / 2^p % 2 == 1

noncomputable def wallDen2 : WallL2 → (ℕ × Bool) → Prop
  | .tbl ℓ, p => bitAtP ℓ (Nat.pair p.1 (Bool.toNat p.2)) = true
  | .snt σ, _ => 𝗜𝚺₁ ⊢ σ
  | .frm θ, p => ∃ σ : ArithmeticSentence,
      Encodable.decode p.1 = some σ ∧
      ℕ↓[ℒₒᵣ] ⊧ θ/[(⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)]

def Tr (p : ℕ × Bool) : Prop :=
  ∃ σ : ArithmeticSentence, Encodable.decode p.1 = some σ ∧ ℕ↓[ℒₒᵣ] ⊧ σ

theorem Tr_invariant (p : ℕ × Bool) (h : Tr p) : Tr (p.1, not p.2) := h

theorem Tr_backward (p : ℕ × Bool) (h : Tr p) :
    ∃ q, Tr q ∧ (q.1, not q.2) = p := by
  refine ⟨(p.1, not p.2), h, ?_⟩
  have : not (not p.2) = p.2 := by cases p.2 <;> rfl
  exact Prod.ext rfl this

theorem Tr_nonempty : ∃ p : ℕ × Bool, Tr p := by
  refine ⟨(Encodable.encode (⊤ : ArithmeticSentence), false),
    (⊤ : ArithmeticSentence), Encodable.encodek _, ?_⟩
  exact models_iff.mpr trivial

/- ── the three pieces `Tr_notall` needs, probed separately ───── -/

example : Encodable.decode (Encodable.encode (⊥ : ArithmeticSentence))
    = some (⊥ : ArithmeticSentence) := by
  exact?

example (τ : ArithmeticSentence)
    (h : some τ = some (⊥ : ArithmeticSentence)) : τ = ⊥ := by
  exact?

example : ¬ (ℕ↓[ℒₒᵣ] ⊧ (⊥ : ArithmeticSentence)) := by
  exact?

theorem Tr_no_frm :
    ¬ ∃ θ : ArithmeticSemisentence 1,
        ∀ p : ℕ × Bool, wallDen2 (.frm θ) p ↔ Tr p := by
  rintro ⟨θ, h⟩
  apply undefinability_of_truth
  refine ⟨θ, fun σ => ?_⟩
  have hp := h (Encodable.encode σ, false)
  simp only [wallDen2, Tr, Encodable.encodek, Option.some.injEq] at hp
  constructor
  · intro hs
    obtain ⟨τ, hτ, ht⟩ := hp.mpr ⟨σ, rfl, hs⟩
    rwa [← hτ] at ht
  · intro ht
    obtain ⟨τ, hτ, hs⟩ := hp.mp ⟨σ, rfl, ht⟩
    rwa [← hτ] at hs

#print axioms Tr_invariant
#print axioms Tr_backward
#print axioms Tr_nonempty
#print axioms Tr_no_frm
