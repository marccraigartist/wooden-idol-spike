99import Idol
import Foundation.FirstOrder.Incompleteness.Tarski

/-!
# WOODEN IDOL — STAGE 2: THE INTEGRATED LANGUAGE

Sidecar to the frozen `Idol.lean` (v4.3, certified 6 Sep 2026). Nothing
above is edited. This file builds ONE new system whose language has three
cases — tables, closed arithmetic sentences, and one-variable arithmetic
formulas that denote AT the fibre index by reading it — and proves all
twelve constraints for it.

THE WELD IS CLOSED HERE. One-variable arithmetic formulas now denote
genuine subsets of the READABLE fibres, through their decoded sentence
codes, and B3/B11 are witnessed on the TARSKI TRUTH-SET, whose
namelessness is `undefinability_of_truth` rather than the language's
poverty. Silent addresses — the majority: 161 of the first 200 — denote
nothing under every open formula.

REMAINING DECLARED DEBT (unchanged): B1 is certified in its
NO-FINITE-TABLE form. The prose's "no algorithm" awaits Phase F.

B10 keeps its TABLE witness by explicit decision, not necessity.

Every supporting fact below was certified in Spike before transplant.
-/

open Function LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace Stage2

/-! ## Infinitely many distinct true sentences -/

def topPow : ℕ → ArithmeticSentence
  | 0 => ⊤
  | n + 1 => (⊤ : ArithmeticSentence) ⋏ topPow n

theorem topPow_true (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧ topPow n := by
  induction n with
  | zero => exact LO.Semantics.Top.models_verum _
  | succ n ih =>
    exact LO.Semantics.And.models_and.mpr
      ⟨LO.Semantics.Top.models_verum _, ih⟩

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
      exact congrArg Nat.succ (ih (by injection h))

/-! ## The three-case language -/

inductive WallL : Type
  | tbl : ℕ → WallL
  | snt : ArithmeticSentence → WallL
  | frm : ArithmeticSemisentence 1 → WallL

noncomputable def wallPrf : WallL → Prop
  | .tbl _ => False
  | .snt σ => 𝗜𝚺₁ ⊢ σ
  | .frm _ => False

/-- The third case performs the reading, and it can fail. -/
noncomputable def wallDen : WallL → (ℕ × Bool) → Prop
  | .tbl ℓ, p => bitAt ℓ (Nat.pair p.1 (Bool.toNat p.2)) = true
  | .snt σ, _ => 𝗜𝚺₁ ⊢ σ
  | .frm θ, p => ∃ σ : ArithmeticSentence,
      Encodable.decode p.1 = some σ ∧
      ℕ↓[ℒₒᵣ] ⊧ θ/[(⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)]

noncomputable def Wall : System where
  X := ℕ × Bool
  T := Tf
  Φ := Bool
  φ := true
  L := WallL
  falsum := .snt ⊥
  con := .snt (𝗜𝚺₁).consistent.val
  den := wallDen
  Prf := wallPrf
  R := CoOrbit Tf
  C := fun p _ => p
  interp := fun e x y => bitAt e (Nat.pair (fbEnc x) (fbEnc y))
  finuniversal := flick_finvuniversal

/-! ## The truth-set -/

def Tr (p : ℕ × Bool) : Prop :=
  ∃ σ : ArithmeticSentence, Encodable.decode p.1 = some σ ∧ ℕ↓[ℒₒᵣ] ⊧ σ

theorem Tr_invariant : Invariant Tf Tr := fun _p h => h

theorem Tr_backward (p : ℕ × Bool) (h : Tr p) : ∃ q, Tr q ∧ Tf q = p := by
  refine ⟨(p.1, not p.2), h, ?_⟩
  show (p.1, not (not p.2)) = p
  have : not (not p.2) = p.2 := by cases p.2 <;> rfl
  exact Prod.ext rfl this

theorem Tr_nonempty : ∃ p : ℕ × Bool, Tr p := by
  refine ⟨(Encodable.encode (⊤ : ArithmeticSentence), false),
    (⊤ : ArithmeticSentence), Encodable.encodek _, ?_⟩
  exact models_iff.mpr trivial

theorem Tr_notall : ∃ p : ℕ × Bool, ¬ Tr p := by
  refine ⟨(Encodable.encode (⊥ : ArithmeticSentence), false), ?_⟩
  rintro ⟨τ, hτ, ht⟩
  have hd : Encodable.decode
      (Encodable.encode (⊥ : ArithmeticSentence))
      = some (⊥ : ArithmeticSentence) := Encodable.encodek _
  have he : τ = (⊥ : ArithmeticSentence) :=
    Option.some.inj (hτ.symm.trans hd)
  rw [he] at ht
  exact (LO.Semantics.Bot.models_falsum _) ht

theorem Tr_at_topPow (n : ℕ) : Tr (Encodable.encode (topPow n), false) :=
  ⟨topPow n, Encodable.encodek _, topPow_true n⟩

theorem Tr_addr_inj : Function.Injective
    (fun n : ℕ => Nat.pair (Encodable.encode (topPow n)) (Bool.toNat false)) := by
  intro a b hab
  have h1 := pair_inj hab
  exact topPow_inj (Encodable.encode_injective h1.1)

/-! ## THE THREE-WAY KILL

On the weld, one lazy case sufficed. Here every naming method must be
closed separately: tables die on finite support, closed sentences on
constant denotation, open formulas on Tarski.
-/

/-- Branch 1 — tables have finite support; the truth-set is infinite. -/
theorem Tr_no_tbl :
    ¬ ∃ ℓ : ℕ, ∀ p : ℕ × Bool, wallDen (.tbl ℓ) p ↔ Tr p := by
  rintro ⟨ℓ, h⟩
  have hbound : ∀ p : ℕ × Bool, Tr p →
      Nat.pair p.1 (Bool.toNat p.2) < ℓ := by
    intro p hp
    have h1 : bitAt ℓ (Nat.pair p.1 (Bool.toNat p.2)) = true := (h p).mpr hp
    have h2 := bitAt_le h1
    have h3 := two_pow_gt (Nat.pair p.1 (Bool.toNat p.2))
    omega
  have hsmall : ℓ + 1 ≤ ℓ := by
    have hemb : Function.Embedding (Fin (ℓ + 1)) (Fin ℓ) :=
      ⟨fun k => Fin.mk
          (Nat.pair (Encodable.encode (topPow k.1)) (Bool.toNat false))
          (hbound _ (Tr_at_topPow k.1)), by
        intro a b hab
        exact Fin.val_injective
          (Tr_addr_inj (congrArg (fun t : Fin ℓ => t.1) hab))⟩
    have hle : Fintype.card (Fin (ℓ + 1)) ≤ Fintype.card (Fin ℓ) :=
      Fintype.card_le_of_embedding (α := Fin (ℓ + 1)) (β := Fin ℓ) hemb
    simp only [Fintype.card_fin] at hle
    exact hle
  omega

/-- Branch 2 — closed sentences denote everywhere or nowhere. -/
theorem Tr_no_snt :
    ¬ ∃ σ : ArithmeticSentence,
        ∀ p : ℕ × Bool, wallDen (.snt σ) p ↔ Tr p := by
  rintro ⟨σ, h⟩
  obtain ⟨q, hq⟩ := Tr_nonempty
  obtain ⟨r, hr⟩ := Tr_notall
  exact hr ((h r).mp ((h q).mpr hq))

/-- Branch 3 — THE TARSKI BRANCH. -/
theorem Tr_no_frm :
    ¬ ∃ θ : ArithmeticSemisentence 1,
        ∀ p : ℕ × Bool, wallDen (.frm θ) p ↔ Tr p := by
  rintro ⟨θ, h⟩
  apply undefinability_of_truth
  refine ⟨θ, fun σ => ?_⟩
  have hp := h (Encodable.encode σ, false)
  simp only [wallDen, Tr, Encodable.encodek, Option.some.injEq] at hp
  constructor
  · intro hs
    obtain ⟨τ, hτ, ht⟩ := hp.mpr ⟨σ, rfl, hs⟩
    rwa [← hτ] at ht
  · intro ht
    obtain ⟨τ, hτ, hs⟩ := hp.mp ⟨σ, rfl, ht⟩
    rwa [← hτ] at hs

/-- All three together. -/
theorem wallNameless :
    ¬ ∃ ℓ : WallL, ∀ p : ℕ × Bool, wallDen ℓ p ↔ Tr p := by
  rintro ⟨ℓ, h⟩
  cases ℓ with
  | tbl t => exact Tr_no_tbl ⟨t, h⟩
  | snt s => exact Tr_no_snt ⟨s, h⟩
  | frm f => exact Tr_no_frm ⟨f, h⟩

/-! ## B3 and B11, re-witnessed -/

theorem wall3 : Wall.B3 :=
  ⟨Tr, Tr_invariant, Tr_backward, wallNameless⟩

theorem wall11 : Wall.B11 := by
  refine ⟨Tr, Tr_invariant, ?_, ?_, wallNameless⟩
  · intro hI
    obtain ⟨p, hp⟩ := Tr_nonempty
    exact (Iff.of_eq (congrFun hI p)).mp hp
  · intro hI
    obtain ⟨p, hp⟩ := Tr_notall
    exact hp ((Iff.of_eq (congrFun hI p)).mpr trivial)

/-! ## The Silence, unchanged -/

theorem wall5 : Wall.B5 := by
  constructor
  · exact Entailment.Consistent.not_bot (𝓢 := 𝗜𝚺₁)
  · exact consistent_unprovable 𝗜𝚺₁

/-! ## The rest, transported -/

theorem wall1 : Wall.B1 := fl1
theorem wall4 : Wall.B4 := fun _x _y => Iff.rfl
theorem wall6 : Wall.B6 := ⟨false, fun h => Bool.noConfusion h⟩
theorem wall7 : Wall.B7 := ⟨Tf, flnot⟩
theorem wall9 : Wall.B9 := flnot
theorem wall12 : Wall.B12 := fl12

theorem wall8 : Wall.B8 := by
  refine ⟨fun p => p.2 = true, ⟨(0, true), rfl⟩,
    ⟨(0, false), fun h => Bool.noConfusion h⟩, ?_, ?_⟩
  · intro x y hx
    exact hx
  · intro x y hx
    exact Or.inl hx

theorem wall2 : Wall.B2 := by
  refine ⟨(0, false), flnot (0, false), ?_⟩
  intro ℓ hℓ n
  refine ⟨2 * (n + 1), by omega, ?_⟩
  show Wall.den ℓ (Tf^[2 * (n + 1)] (0, false))
  rw [flick_even 0 false (n + 1)]
  exact hℓ

theorem wall10 : Wall.B10 := by
  refine ⟨flTinj, ?_⟩
  refine ⟨.tbl (2 ^ Nat.pair 0 1), (0, true), ?_, ?_⟩
  · show bitAt (2 ^ Nat.pair 0 1) (Nat.pair 0 1) = true
    rw [bitAt_two_pow]
    exact decide_eq_true rfl
  · intro h
    have h0 : bitAt (2 ^ Nat.pair 0 1) (Nat.pair 0 0) = true := h (0, false)
    rw [bitAt_two_pow] at h0
    have heq : Nat.pair 0 0 = Nat.pair 0 1 := decide_eq_true_iff.mp h0
    exact absurd (pair_inj heq).2 (by decide)

/-! ## ═══ THE WOODEN IDOL, STAGE 2 ═══

One system. Three language cases. All twelve constraints. Arithmetic
speaks about individual fibres, and cannot say which of them are true.
-/

theorem wooden_idol_stage2 : ∃ S : System, All12 S :=
  ⟨Wall, ⟨wall1, wall2, wall3, wall4, wall5, wall6, wall7, wall8,
          wall9, wall10, wall11, wall12⟩⟩

end Stage2

#print axioms Stage2.topPow_true
#print axioms Stage2.topPow_inj
#print axioms Stage2.Tr_no_tbl
#print axioms Stage2.Tr_no_snt
#print axioms Stage2.Tr_no_frm
#print axioms Stage2.wallNameless
#print axioms Stage2.wall3
#print axioms Stage2.wall11
#print axioms Stage2.wooden_idol_stage2
