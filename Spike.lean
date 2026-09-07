import Mathlib
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.Incompleteness.Examples
import Foundation.FirstOrder.Incompleteness.Tarski

/-! # STAGE 2 — BUCKET 1, probe.
    The three-case language, the new denotation, the truth-set invariant,
    and the two branches of namelessness that are NOT the old table argument.
    Spike only. Idol.lean and Idol2.lean untouched. -/

open Function LO LO.FirstOrder LO.FirstOrder.Arithmetic

/- ── the three-case language ─────────────────────────────────── -/

/-- Table codes, closed arithmetic sentences, and — new — one-variable
    formulas, which denote AT the fibre index by reading it. -/
inductive WallL2 : Type
  | tbl : ℕ → WallL2
  | snt : ArithmeticSentence → WallL2
  | frm : ArithmeticSemisentence 1 → WallL2

/-- Placeholder for the real `bitAt`; only its finite-support behaviour
    matters and that branch is not probed here. -/
def bitAtP (e p : ℕ) : Bool := e / 2^p % 2 == 1

/-- The new denotation. Note the third case: the decoding is PERFORMED,
    and at a silent address it simply fails. -/
noncomputable def wallDen2 : WallL2 → (ℕ × Bool) → Prop
  | .tbl ℓ, p => bitAtP ℓ (Nat.pair p.1 (Bool.toNat p.2)) = true
  | .snt σ, _ => 𝗜𝚺₁ ⊢ σ
  | .frm θ, p => ∃ σ : ArithmeticSentence,
      Encodable.decode p.1 = some σ ∧
      ℕ↓[ℒₒᵣ] ⊧ θ/[(⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)]

/-- THE NEW INVARIANT — the fibres whose address reads as a TRUE sentence.
    Silent fibres are outside it. -/
def Tr (p : ℕ × Bool) : Prop :=
  ∃ σ : ArithmeticSentence, Encodable.decode p.1 = some σ ∧ ℕ↓[ℒₒᵣ] ⊧ σ

/-- Invariant under the Flicker: `T` moves only the second coordinate. -/
theorem Tr_invariant (p : ℕ × Bool) (h : Tr p) : Tr (p.1, not p.2) := h

/- ── the branch that matters: open formulas die on Tarski ────── -/

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

/- ── the branch that is nearly free: closed sentences ─────────── -/

theorem Tr_no_snt :
    ¬ ∃ σ : ArithmeticSentence,
        ∀ p : ℕ × Bool, wallDen2 (.snt σ) p ↔ Tr p := by
  rintro ⟨σ, h⟩
  have hzero : ¬ Tr (0, false) := by
    rintro ⟨τ, hτ, -⟩
    exact absurd hτ (by decide)
  have htrue : ∃ p : ℕ × Bool, Tr p := by
    refine ⟨(Encodable.encode (⊤ : ArithmeticSentence), false), ⊤, ?_, ?_⟩
    · exact Encodable.encodek _
    · simp
  obtain ⟨q, hq⟩ := htrue
  exact hzero ((h (0, false)).mp ((h q).mpr hq))

#print axioms Tr_invariant
#print axioms Tr_no_frm
#print axioms Tr_no_snt
