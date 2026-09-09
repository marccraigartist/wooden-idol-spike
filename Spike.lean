import Mathlib
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.Incompleteness.Examples
import Foundation.FirstOrder.Incompleteness.Tarski
import Idol

/-! # STAGE 2 — BUCKETS 1 AND 2, consolidated and green.
    Everything `Idol2.lean` needs, certified in one place.
    Spike only. -/

open Function LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## Bucket 2 — infinitely many distinct TRUE sentences.
    Needed for the TABLE branch: tables have finite support, so the
    truth-set must be infinite for the pigeonhole to bite. -/

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

/-! ## Bucket 1 — the three-case language and the truth-set. -/

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

/-- The truth-set is infinite: every `topPow n` sits at its own address. -/
theorem Tr_infinite : Function.Injective
    (fun n : ℕ => (Encodable.encode (topPow n), false)) ∧
    ∀ n : ℕ, Tr (Encodable.encode (topPow n), false) := by
  constructor
  · intro a b hab
    have h1 : Encodable.encode (topPow a) = Encodable.encode (topPow b) :=
      congrArg Prod.fst hab
    exact topPow_inj (Encodable.encode_injective h1)
  · intro n
    exact ⟨topPow n, Encodable.encodek _, topPow_true n⟩

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

theorem Tr_no_snt :
    ¬ ∃ σ : ArithmeticSentence,
        ∀ p : ℕ × Bool, wallDen2 (.snt σ) p ↔ Tr p := by
  rintro ⟨σ, h⟩
  obtain ⟨q, hq⟩ := Tr_nonempty
  obtain ⟨r, hr⟩ := Tr_notall
  exact hr ((h r).mp ((h q).mpr hq))

#print axioms topPow_true
#print axioms topPow_inj
#print axioms Tr_invariant
#print axioms Tr_backward
#print axioms Tr_nonempty
#print axioms Tr_notall
#print axioms Tr_infinite
#print axioms Tr_no_frm
#print axioms Tr_no_snt
/-! ## SOURCE AUDIT — B9 and B12 are equivalent -/

theorem B12_implies_B9 (S : System) (h12 : S.B12) : S.B9 := by
  intro x hx
  obtain ⟨n, y, _hn, hy, hTy⟩ := h12 x
  have hfix : S.T^[n] x = x := Function.iterate_fixed hx n
  have hyx : y = x := hy.symm.trans hfix
  exact hTy (hyx.symm ▸ hx)

theorem B9_iff_B12 (S : System) : S.B9 ↔ S.B12 := by
  constructor
  · intro h9 x
    exact ⟨1, S.T x, Nat.one_pos, rfl, h9 (S.T x)⟩
  · exact B12_implies_B9 S

#print axioms B12_implies_B9
#print axioms B9_iff_B12
