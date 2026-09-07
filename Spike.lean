import Mathlib
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.Incompleteness.Examples
import Foundation.FirstOrder.Incompleteness.Tarski

/-! # STAGE 2 — BUCKET 1d. Five certified; `Tr_notall` isolated.
    Spike only. -/

open Function LO LO.FirstOrder LO.FirstOrder.Arithmetic

/- ── isolate the failing step, four ways ─────────────────────── -/

/-- Route 1: let `exact?` search from the original goal. -/
example (h : ℕ↓[ℒₒᵣ] ⊧ (⊥ : ArithmeticSentence)) : False := by
  exact?

/-- Route 2: via `models_iff`, the lemma that worked for ⊤. -/
example (h : ℕ↓[ℒₒᵣ] ⊧ (⊥ : ArithmeticSentence)) : False := by
  rw [models_iff] at h
  exact?

/- Route 3: inspect what the model lemmas expose.
   NOTE: plain block comment — a `/-- -/` doc comment cannot
   precede a `#check`, which is what killed the last build. -/

#check @models_iff
#check @notModels_iff
#check @LO.Semantics.Bot.models_falsum

example : (ℕ↓[ℒₒᵣ] ⊧ (⊥ : ArithmeticSentence)) ↔ False := by
  exact?

/-- Route 4: the explicit lemma found in Foundation f212e81. -/
example (h : ℕ↓[ℒₒᵣ] ⊧ (⊥ : ArithmeticSentence)) : False := by
  exact (LO.Semantics.Bot.models_falsum _) h
