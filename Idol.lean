import Mathlib

/-!
# WOODEN IDOL v3.14 — Leake Street, CAMP 4: κ, THE DOOR

v3.13 unchanged (Camps 1–3, the Eleven, the diagonal, the no-finite-table).
NEW: Camp 4 — the first theorem in this file about the ARTIST rather than
the wall. Nothing finite can keep leaving. `traj` is the first mention of
an INPUT anywhere in the project: a door cut into the closed wall.
Still exactly one public `sorry` (B5, the Silence).
-/

open Function

/-! ## Part 0 — the signature (dry since v2.1) -/

structure System where
  X : Type
  T : X → X
  Φ : Type
  φ : Φ
  L : Type
  falsum : L
  con : L
  den : L → X → Prop
  Prf : L → Prop
  R : X → X → Prop
  C : X → X → X
  interp : ℕ → X → X → Bool
  -- f-i-n-u-n-i-v-e-r-s-a-l
  finuniversal : ∀ Q : X → X → Prop, (∀ x y, Decidable (Q x y)) →
    ∀ K : Finset X, ∃ e, ∀ x ∈ K, ∀ y ∈ K, interp e x y = true ↔ Q x y

-- CANARY: sings while the field is named truly. `--` comments only.
#check @System.finuniversal

def Invariant {X : Type} (T : X → X) (I : X → Prop) : Prop := ∀ x, I x → I (T x)
def Reachable {X : Type} (T : X → X) (x y : X) : Prop := ∃ n, T^[n] x = y
def CoOrbit {X : Type} (T : X → X) (x y : X) : Prop := ∃ n m, T^[n] x = T^[m] y
def Consistent (S : System) : Prop := ¬ S.Prf S.falsum

namespace System
def B1 (S : System) : Prop := ¬ ∃ e : ℕ, ∀ x y, S.interp e x y = true ↔ Reachable S.T x y
def B2 (S : System) : Prop :=
  ∃ x : S.X, S.T x ≠ x ∧
    ∀ ℓ : S.L, S.den ℓ x → ∀ n, ∃ m, n < m ∧ S.den ℓ (S.T^[m] x)
def B3 (S : System) : Prop :=
  ∃ I : S.X → Prop, Invariant S.T I ∧
    (∀ x, I x → ∃ y, I y ∧ S.T y = x) ∧ ¬ ∃ ℓ : S.L, ∀ x, S.den ℓ x ↔ I x
def B4 (S : System) : Prop := ∀ x y, S.R x y ↔ CoOrbit S.T x y
def B5 (S : System) : Prop := Consistent S ∧ ¬ S.Prf S.con
def B6 (S : System) : Prop := ∃ φ' : S.Φ, φ' ≠ S.φ
def B7 (S : System) : Prop := ∃ F : S.X → S.X, ∀ x, F x ≠ x
def B8 (S : System) : Prop :=
  ∃ K : S.X → Prop, (∃ a, K a) ∧ (∃ b, ¬ K b) ∧
    (∀ x y, K x → K (S.C x y)) ∧ (∀ x y, K (S.C x y) → K x ∨ K y)
def B9 (S : System) : Prop := ∀ x, S.T x ≠ x
def B10 (S : System) : Prop :=
  Injective S.T ∧ ∃ ℓ : S.L, ∃ x, S.den ℓ x ∧ ¬ ∀ y, S.den ℓ y
def B11 (S : System) : Prop :=
  ∃ I : S.X → Prop, Invariant S.T I ∧
    I ≠ (fun _ => False) ∧ I ≠ (fun _ => True) ∧ ¬ ∃ ℓ : S.L, ∀ x, S.den ℓ x ↔ I x
def B12 (S : System) : Prop := ∀ x, ∃ n y, 0 < n ∧ S.T^[n] x = y ∧ S.T y ≠ y
end System

structure All12 (S : System) : Prop where
  b1 : S.B1
  b2 : S.B2
  b3 : S.B3
  b4 : S.B4
  b5 : S.B5
  b6 : S.B6
  b7 : S.B7
  b8 : S.B8
  b9 : S.B9
  b10 : S.B10
  b11 : S.B11
  b12 : S.B12

/-! ## Part 2 — certified impossibilities (dry, untouched) -/

theorem extensional_selfref_fixed {X : Type} [Nonempty X] (F : X → X)
    (h : ∀ x, F (F x) = F x) : ∃ x, F x = x := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  exact ⟨F x₀, h x₀⟩

theorem B7_extensional_impossible {X : Type} [Nonempty X] (F : X → X)
    (hff : ∀ x, F x ≠ x) (hsr : ∀ x, F (F x) = F x) : False := by
  obtain ⟨y, hy⟩ := extensional_selfref_fixed F hsr
  exact hff y hy

theorem B3naive_B9_inconsistent {X : Type} (T : X → X)
    (h3 : ∃ I : X → Prop, (∃ x, I x) ∧ ∀ x, I x → T x = x)
    (h9 : ∀ x, T x ≠ x) : False := by
  obtain ⟨I, ⟨x, hx⟩, hstab⟩ := h3
  exact h9 x (hstab x hx)

theorem B9_implies_B12 (S : System) (h9 : S.B9) : S.B12 := by
  intro x
  exact ⟨1, S.T x, by decide, by simp, h9 (S.T x)⟩

theorem naive_B1_always_false (S : System) :
    ∃ f : S.X → S.X → Bool, ∀ x y, f x y = true ↔ Reachable S.T x y := by
  classical
  exact ⟨fun x y => decide (Reachable S.T x y), fun x y => decide_eq_true_iff⟩

/-! ## Part 3 — no finite idol (dry, untouched) -/

theorem iterate_periodic {X : Type} {T : X → X} {x : X} {i j : ℕ}
    (hij : i < j) (hcol : T^[i] x = T^[j] x) :
    ∀ k, i ≤ k → T^[k + (j - i)] x = T^[k] x := by
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = i + m := ⟨k - i, by omega⟩
  calc T^[i + m + (j - i)] x
      = T^[m + j] x := by rw [show i + m + (j - i) = m + j from by omega]
    _ = T^[m] (T^[j] x) := Function.iterate_add_apply T m j x
    _ = T^[m] (T^[i] x) := by rw [hcol]
    _ = T^[m + i] x := (Function.iterate_add_apply T m i x).symm
    _ = T^[i + m] x := by rw [Nat.add_comm m i]

theorem iterate_drop {X : Type} {T : X → X} {x : X} {i j n : ℕ}
    (hij : i < j) (hcol : T^[i] x = T^[j] x) (hn : j ≤ n) :
    T^[n] x = T^[n - (j - i)] x := by
  have hge : i ≤ n - (j - i) := by omega
  have hper := iterate_periodic hij hcol (n - (j - i)) hge
  rw [show (n - (j - i)) + (j - i) = n from by omega] at hper
  exact hper

theorem iterate_collides {X : Type} [Fintype X] (T : X → X) (x : X) :
    ∃ i j : ℕ, i < j ∧ j ≤ Fintype.card X ∧ T^[i] x = T^[j] x := by
  by_contra h
  have hinj : Function.Injective (fun n : Fin (Fintype.card X + 1) => T^[(n : ℕ)] x) := by
    intro n₁ n₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h ⟨(n₁ : ℕ), (n₂ : ℕ), hlt, Nat.lt_succ_iff.mp n₂.isLt, heq⟩
    · exact h ⟨(n₂ : ℕ), (n₁ : ℕ), hlt, Nat.lt_succ_iff.mp n₁.isLt, heq.symm⟩
  have hle : Fintype.card (Fin (Fintype.card X + 1)) ≤ Fintype.card X :=
    Fintype.card_le_of_embedding (α := Fin (Fintype.card X + 1)) (β := X)
      ⟨fun n => T^[(n : ℕ)] x, hinj⟩
  simp only [Fintype.card_fin] at hle
  omega

def boundedReach {X : Type} [DecidableEq X] (T : X → X) (x y : X) : ℕ → Bool
  | 0 => x == y
  | n + 1 => (T^[n + 1] x == y) || boundedReach T x y n

theorem boundedReach_true {X : Type} [DecidableEq X] (T : X → X) (x y : X) :
    ∀ N, boundedReach T x y N = true → ∃ n, n ≤ N ∧ T^[n] x = y := by
  intro N
  induction N with
  | zero =>
    intro h
    simp only [boundedReach] at h
    exact ⟨0, by omega, beq_iff_eq.mp h⟩
  | succ N ih =>
    intro h
    simp only [boundedReach, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨N + 1, by omega, h⟩
    · obtain ⟨n, hn, hne⟩ := ih h
      exact ⟨n, by omega, hne⟩

theorem boundedReach_hit {X : Type} [DecidableEq X] (T : X → X) (x y : X) :
    ∀ N m, m ≤ N → T^[m] x = y → boundedReach T x y N = true := by
  intro N
  induction N with
  | zero =>
    intro m hm hxy
    have : m = 0 := by omega
    subst this
    simp only [boundedReach]
    exact beq_iff_eq.mpr hxy
  | succ N ih =>
    intro m hm hxy
    simp only [boundedReach]
    rcases Nat.lt_or_ge m (N + 1) with hlt | hge
    · rw [ih m (by omega) hxy]
      exact Bool.or_true _
    · have : m = N + 1 := by omega
      subst this
      rw [beq_iff_eq.mpr hxy]
      exact Bool.true_or _

theorem reach_bounded {X : Type} [Fintype X] (T : X → X) (x y : X)
    (h : Reachable T x y) : ∃ n, n < Fintype.card X ∧ T^[n] x = y := by
  classical
  obtain ⟨n0, hn0⟩ := h
  have hex : ∃ n, T^[n] x = y := ⟨n0, hn0⟩
  obtain ⟨n, hn, hnmin⟩ : ∃ n, T^[n] x = y ∧ ∀ m, m < n → T^[m] x ≠ y :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm hme => Nat.find_min hex hm hme⟩
  obtain ⟨i, j, hij, hjle, hcol⟩ := iterate_collides T x
  by_cases hnj : j ≤ n
  · have hdrop := iterate_drop hij hcol hnj
    exact absurd (hdrop.symm.trans hn) (hnmin (n - (j - i)) (by omega))
  · exact ⟨n, by omega, hn⟩

theorem boundedReach_iff {X : Type} [Fintype X] [DecidableEq X] (T : X → X) (x y : X) :
    boundedReach T x y (Fintype.card X) = true ↔ Reachable T x y := by
  constructor
  · intro h
    obtain ⟨n, _, hne⟩ := boundedReach_true T x y (Fintype.card X) h
    exact ⟨n, hne⟩
  · rintro ⟨n, hn⟩
    obtain ⟨m, hm, hme⟩ := reach_bounded T x y ⟨n, hn⟩
    exact boundedReach_hit T x y (Fintype.card X) m (by omega) hme

theorem finite_B1_fails (S : System) [Fintype S.X] [DecidableEq S.X] : ¬ S.B1 := by
  have hdec : ∀ x y : S.X, Decidable (Reachable S.T x y) := fun x y =>
    decidable_of_iff (boundedReach S.T x y (Fintype.card S.X) = true)
      (boundedReach_iff S.T x y)
  intro h1
  obtain ⟨e, he⟩ := S.finuniversal (Reachable S.T) hdec Finset.univ
  refine h1 ⟨e, fun x y => he x (Finset.mem_univ x) y (Finset.mem_univ y)⟩

theorem no_finite_idol (S : System) [Fintype S.X] [DecidableEq S.X]
    (h : All12 S) : False :=
  finite_B1_fails S h.b1

/-! ## The Diagonal (dry, untouched) -/

theorem diagonal_noUniversal {X : Type} (interp : ℕ → X → X → Bool)
    (f : ℕ → X) (hf : Injective f)
    (huniv : ∀ Q : X → X → Prop, (∀ x y, Decidable (Q x y)) →
      ∃ e, ∀ x y, interp e x y = true ↔ Q x y) : False := by
  obtain ⟨e, he⟩ := huniv
    (fun x y => ∀ e', x = f e' → ¬ interp e' x y = true)
    (fun x y => Classical.propDecidable _)
  obtain ⟨mp, mpr⟩ := he (f e) (f e)
  cases hp : interp e (f e) (f e) with
  | false =>
    have hall : ∀ e', f e = f e' → ¬ interp e' (f e) (f e) = true := by
      intro e' he'
      have hee : e = e' := hf he'
      subst hee
      rw [hp]
      decide
    exact absurd (mpr hall) (by rw [hp]; decide)
  | true =>
    exact (mp hp e rfl) hp

theorem old_universal_refutes (S : System)
    (hf : ∃ f : ℕ → S.X, Injective f)
    (huniv : ∀ Q : S.X → S.X → Prop, (∀ x y, Decidable (Q x y)) →
      ∃ e, ∀ x y, S.interp e x y = true ↔ Q x y) : False := by
  obtain ⟨f, hfinj⟩ := hf
  exact diagonal_noUniversal S.interp f hfinj huniv

/-! ## The Pulse and the Eight (dry, untouched) -/

def idxB : Bool → Bool → ℕ
  | false, false => 0
  | false, true => 1
  | true, false => 2
  | true, true => 3

def codeB (Q : Bool → Bool → Prop) (hdec : ∀ x y, Decidable (Q x y)) : ℕ :=
  (hdec false false).decide.toNat + 2 * (hdec false true).decide.toNat +
    4 * (hdec true false).decide.toNat + 8 * (hdec true true).decide.toNat

def interpB (e : ℕ) : Bool → Bool → Bool := fun x y => (e / 2 ^ idxB x y) % 2 == 1

theorem codeB_ok (Q : Bool → Bool → Prop) (hdec : ∀ x y, Decidable (Q x y)) :
    ∀ x y, interpB (codeB Q hdec) x y = (hdec x y).decide := by
  intro x y
  cases x <;> cases y <;> simp only [interpB, codeB, idxB] <;>
    cases h00 : (hdec false false).decide <;> cases h01 : (hdec false true).decide <;>
    cases h10 : (hdec true false).decide <;> cases h11 : (hdec true true).decide <;> decide

theorem finuniversalB : ∀ (Q : Bool → Bool → Prop), (∀ x y, Decidable (Q x y)) →
    ∀ K : Finset Bool, ∃ e, ∀ x ∈ K, ∀ y ∈ K, interpB e x y = true ↔ Q x y := by
  intro Q hdec K
  refine ⟨codeB Q hdec, fun x _ y _ => ?_⟩
  show interpB (codeB Q hdec) x y = true ↔ Q x y
  rw [codeB_ok Q hdec x y]
  exact decide_eq_true_iff

theorem not_iterate_two (x : Bool) : not^[2] x = x := by
  cases x <;> rfl

theorem not_iterate_even (x : Bool) (k : ℕ) : not^[2 * k] x = x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by omega, Function.iterate_add_apply,
      not_iterate_two, ih]

theorem not_injective : Injective (not : Bool → Bool) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

theorem not_ne_self : ∀ x : Bool, not x ≠ x := by
  intro x
  cases x with
  | false => intro h; exact Bool.noConfusion h
  | true => intro h; exact Bool.noConfusion h

theorem not_not_ne_self : ∀ x : Bool, not (not x) ≠ not x := by
  intro x
  cases x with
  | false => intro h; exact Bool.noConfusion h
  | true => intro h; exact Bool.noConfusion h

def Cycle2 : System where
  X := Bool
  T := not
  Φ := Bool
  φ := true
  L := Bool
  falsum := false
  con := true
  den := fun b x => x = b
  Prf := fun _ => False
  R := CoOrbit not
  C := fun x _ => x
  interp := interpB
  finuniversal := finuniversalB

theorem hb2 : Cycle2.B2 := by
  refine ⟨false, ?_, ?_⟩
  · show (not (false : Bool)) ≠ (false : Bool)
    exact not_ne_self false
  · intro ℓ hℓ n
    have hℓ' : ℓ = false := hℓ.symm
    subst hℓ'
    refine ⟨2 * (n + 1), by omega, ?_⟩
    show not^[2 * (n + 1)] false = false
    exact not_iterate_even false (n + 1)

theorem hb4 : Cycle2.B4 := fun _x _y => Iff.rfl

theorem hb6 : Cycle2.B6 := by
  refine ⟨false, ?_⟩
  show (false : Bool) ≠ (true : Bool)
  decide

theorem hb7 : Cycle2.B7 := ⟨not, fun x => not_ne_self x⟩

theorem hb8 : Cycle2.B8 := by
  refine ⟨fun x => x = true, ⟨true, rfl⟩, ⟨false, ?_⟩, ?_, ?_⟩
  · show ¬ (false = true)
    decide
  · intro x y hx
    show x = true
    exact hx
  · intro x y hx
    show x = true ∨ y = true
    exact Or.inl hx

theorem hb9 : Cycle2.B9 := not_ne_self

theorem hb10 : Cycle2.B10 := by
  refine ⟨not_injective, true, true, rfl, ?_⟩
  intro h
  exact absurd (show (false:Bool) = true from h false) (by decide)

theorem hb12 : Cycle2.B12 := by
  intro x
  exact ⟨1, not x, by decide, rfl, not_not_ne_self x⟩

theorem partial_idol : ∃ S : System, S.B2 ∧ S.B4 ∧ S.B6 ∧ S.B9 ∧ S.B10 ∧ S.B12 :=
  ⟨Cycle2, hb2, hb4, hb6, hb9, hb10, hb12⟩

theorem idol8 : ∃ S : System,
    S.B2 ∧ S.B4 ∧ S.B6 ∧ S.B7 ∧ S.B8 ∧ S.B9 ∧ S.B10 ∧ S.B12 :=
  ⟨Cycle2, hb2, hb4, hb6, hb7, hb8, hb9, hb10, hb12⟩

/-! ## ═══ CAMP 1 — the Codebook (certified at v3.9, byte-identical) ═══ -/

theorem two_pow_pos (p : ℕ) : 0 < 2^p := by
  induction p with
  | zero => exact Nat.zero_lt_one
  | succ p ih => rw [Nat.pow_succ]; omega

theorem two_pow_le_two_pow {q p : ℕ} (h : q ≤ p) : 2^q ≤ 2^p := by
  have key : ∀ d t : ℕ, 2 ^ t ≤ 2 ^ (t + d) := by
    intro d
    induction d with
    | zero =>
      intro t
      exact Nat.le_of_eq (congrArg (fun z => (2:ℕ)^z) (Nat.add_zero t))
    | succ d ih =>
      intro t
      have h1 : 2 ^ (t + d) + 2 ^ (t + d) = 2 ^ (t + d + 1) := by
        rw [Nat.pow_succ, Nat.mul_two]
      calc 2 ^ t ≤ 2 ^ (t + d) := ih t
        _ ≤ 2 ^ (t + d) + 2 ^ (t + d) := Nat.le_add_right _ _
        _ ≤ 2 ^ (t + d + 1) := h1.le
  have he : p = q + (p - q) := by omega
  rw [he]
  exact key (p - q) q

theorem two_pow_double {q p : ℕ} (h : q < p) : 2^q + 2^q ≤ 2^p := by
  have h1 := two_pow_le_two_pow (by omega : q + 1 ≤ p)
  have e : 2^(q+1) = 2^q * 2 := by rw [Nat.pow_succ]
  have e2 : 2^q * 2 = 2^q + 2^q := by omega
  omega

theorem two_pow_lt_two_pow {q p : ℕ} (h : q < p) : 2^q < 2^p := by
  have h1 := two_pow_double h
  have hp := two_pow_pos q
  omega

theorem two_pow_lt_two_pow' {a b : ℕ} (h : a < b) : 2^a < 2^b := two_pow_lt_two_pow h

theorem two_pow_succ_add (a : ℕ) : 2^(a+1) = 2^a + 2^a := by
  rw [Nat.pow_succ, Nat.mul_two]

theorem two_pow_gt (n : ℕ) : 2 ^ n > n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    have h1 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := two_pow_succ_add n
    omega

def bitAt (e p : ℕ) : Bool := e / 2^p % 2 == 1

theorem bitAt_zero (p : ℕ) : bitAt 0 p = false := by
  show ((0:ℕ) / 2^p % 2 == 1) = false
  rw [Nat.zero_div, Nat.zero_mod]
  rfl

theorem bitAt_two_pow (q p : ℕ) : bitAt (2^q) p = decide (p = q) := by
  rcases Nat.lt_trichotomy p q with hlt | heq | hgt
  · have h1 : (2:ℕ)^q / 2^p = 2^(q - p) := by
      refine Nat.div_eq_of_eq_mul_left (two_pow_pos p) ?_
      rw [← Nat.pow_add, Nat.add_comm, show p + (q - p) = q from by omega]
    have h2 : (2:ℕ)^(q - p) % 2 = 0 := by
      have h3 : q - p = (q - p - 1) + 1 := by omega
      rw [h3, Nat.pow_succ, Nat.mul_mod_left]
    have h4 : decide (p = q) = false := decide_eq_false_iff_not.mpr (by omega)
    show ((2:ℕ)^q / 2^p % 2 == 1) = decide (p = q)
    rw [h1, h2, h4]
    rfl
  · rw [heq]
    have h1 : (2:ℕ)^q / 2^q = 1 := Nat.div_self (two_pow_pos q)
    have h2 : (1:ℕ) % 2 = 1 := Nat.mod_eq_of_lt (by omega)
    show ((2:ℕ)^q / 2^q % 2 == 1) = decide (q = q)
    rw [h1, h2, decide_eq_true rfl]
    rfl
  · have h1 : (2:ℕ)^q / 2^p = 0 := Nat.div_eq_of_lt (two_pow_lt_two_pow' hgt)
    have h4 : decide (p = q) = false := decide_eq_false_iff_not.mpr (by omega)
    show ((2:ℕ)^q / 2^p % 2 == 1) = decide (p = q)
    rw [h1, Nat.zero_mod, h4]
    rfl

theorem bitAt_le {ℓ a : ℕ} (h : bitAt ℓ a = true) : 2 ^ a ≤ ℓ := by
  by_contra hge
  have hlt : ℓ < 2 ^ a := by omega
  simp only [bitAt, beq_iff_eq] at h
  rw [Nat.div_eq_of_lt hlt, Nat.zero_mod] at h
  exact absurd h (by decide)

theorem bitAt_add_two_pow_of_lt (u k p : ℕ) (h : p < k) :
    bitAt (2^k + u) p = bitAt u p := by
  have hp := two_pow_pos p
  have hk : p + (k - p) = k := by omega
  have hpq : 2^p * 2^(k - p) = 2^k := by rw [← Nat.pow_add, hk]
  have hev : 2^(k - p) % 2 = 0 := by
    have h1 : k - p = (k - p - 1) + 1 := by omega
    rw [h1, Nat.pow_succ, Nat.mul_mod_left]
  have hdiv : (2^k + u) / 2^p = 2^(k - p) + u / 2^p := by
    have h1 : 2^k + u = u + 2^p * 2^(k - p) := by rw [Nat.add_comm, ← hpq]
    rw [h1, Nat.add_mul_div_left u (2^(k - p)) hp, Nat.add_comm]
  have hfin : (2^(k - p) + u / 2^p) % 2 = u / 2^p % 2 := by
    rcases Nat.mod_two_eq_zero_or_one (u / 2^p) with h0 | h0
    · rw [Nat.add_mod, hev, h0, Nat.zero_add, Nat.zero_mod]
    · rw [Nat.add_mod, hev, h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  show ((2^k + u) / 2^p % 2 == 1) = (u / 2^p % 2 == 1)
  rw [hdiv, hfin]

theorem bitAt_add_eq (s p : ℕ) : bitAt (s + 2^p) p = !(bitAt s p) := by
  have hp := two_pow_pos p
  have hdiv : (s + 2^p) / 2^p = s / 2^p + 1 := by
    have h1 : s + 2^p = s + 2^p * 1 := by rw [Nat.mul_one]
    rw [h1, Nat.add_mul_div_left s 1 hp]
  rcases Nat.mod_two_eq_zero_or_one (s / 2^p) with h0 | h0
  · show ((s + 2^p) / 2^p % 2 == 1) = !(s / 2^p % 2 == 1)
    rw [hdiv, h0]
    have h1 : (s / 2^p + 1) % 2 = 1 := by omega
    rw [h1]
    decide
  · show ((s + 2^p) / 2^p % 2 == 1) = !(s / 2^p % 2 == 1)
    rw [hdiv, h0]
    have h1 : (s / 2^p + 1) % 2 = 0 := by omega
    rw [h1]
    decide

/-- ★ THE FOUNDATION ★ digit decomposition. -/
theorem mod_two_pow_succ (u a : ℕ) :
    u % 2^(a+1) = u % 2^a + 2^a * ((u / 2^a) % 2) := by
  have hd : 2^a * (u / 2^a) + u % 2^a = u := Nat.div_add_mod u (2^a)
  have hq2 : u / 2^a = 2 * (u / 2^a / 2) + u / 2^a % 2 :=
    (Nat.div_add_mod (u / 2^a) 2).symm
  have hb : (u / 2^a) % 2 ≤ 1 := by
    rcases Nat.mod_two_eq_zero_or_one (u / 2^a) with h | h
    · omega
    · omega
  have h2p : (2:ℕ)^(a+1) = 2^a * 2 := by rw [Nat.pow_succ, Nat.mul_comm]
  have hu : u = 2^(a+1) * (u / 2^a / 2) + (2^a * (u / 2^a % 2) + u % 2^a) := by
    conv_lhs => rw [← hd, hq2]
    rw [h2p]
    ring
  have hSlt : 2^a * (u / 2^a % 2) + u % 2^a < 2^(a+1) := by
    rw [h2p]
    have h1 : 2^a * (u / 2^a % 2) ≤ 2^a * 1 :=
      Nat.mul_le_mul (Nat.le_refl _) hb
    rw [Nat.mul_one] at h1
    have h2 := Nat.mod_lt u (two_pow_pos a)
    omega
  have hmod : (2^(a+1) * (u / 2^a / 2) + (2^a * (u / 2^a % 2) + u % 2^a)) % 2^(a+1)
      = 2^a * (u / 2^a % 2) + u % 2^a := by
    rw [Nat.add_comm (2^(a+1) * (u / 2^a / 2)) (2^a * (u / 2^a % 2) + u % 2^a),
      Nat.mul_comm (2^(a+1)) (u / 2^a / 2), Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hSlt, Nat.add_comm]
  rw [Nat.add_comm (u % 2^a) (2^a * (u / 2^a % 2)), ← hmod]
  conv_lhs => rw [hu]

/-- THE KEY — anti-carry. -/
theorem bitAt_add_two_pow_of_gt' (u a p : ℕ) (hlt : a < p) (h0 : bitAt u a = false) :
    bitAt (u + 2^a) p = bitAt u p := by
  have hp := two_pow_pos p
  have h0' : (u / 2^a) % 2 = 0 := by
    simp only [bitAt] at h0
    rcases Nat.mod_two_eq_zero_or_one (u / 2^a) with hz | ho
    · exact hz
    · rw [ho] at h0
      exact absurd h0 (by decide)
  have hp2 : 2^p = 2^(a+1) * 2^(p - a - 1) := by
    rw [← Nat.pow_add, show a + 1 + (p - a - 1) = p from by omega]
  have hlink : u % 2^p % 2^(a+1) = u % 2^(a+1) :=
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
  have humod : u % 2^(a+1) = u % 2^a := by
    rw [mod_two_pow_succ, h0', Nat.mul_zero, Nat.add_zero]
  have hstep : u % 2^p % 2^(a+1) + 2^a < 2^(a+1) := by
    rw [hlink, humod]
    have hm := Nat.mod_lt u (two_pow_pos a)
    rw [two_pow_succ_add]
    omega
  have hdivlt : (u % 2^p) / 2^(a+1) < 2^(p - a - 1) := by
    refine Nat.div_lt_of_lt_mul ?_
    exact Nat.lt_of_lt_of_eq (Nat.mod_lt u hp) hp2
  have hsmall : u % 2^p + 2^a < 2^p := by
    have hR : 2^(a+1) * ((u % 2^p) / 2^(a+1)) + u % 2^p % 2^(a+1) = u % 2^p :=
      Nat.div_add_mod _ _
    calc u % 2^p + 2^a
        = (2^(a+1) * ((u % 2^p) / 2^(a+1)) + u % 2^p % 2^(a+1)) + 2^a := by
          omega
      _ = 2^(a+1) * ((u % 2^p) / 2^(a+1)) + (u % 2^p % 2^(a+1) + 2^a) :=
          Nat.add_assoc _ _ _
      _ < 2^(a+1) * ((u % 2^p) / 2^(a+1)) + 2^(a+1) := Nat.add_lt_add_left hstep _
      _ ≤ 2^(a+1) * ((u % 2^p) / 2^(a+1) + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
      _ ≤ 2^(a+1) * 2^(p - a - 1) :=
          Nat.mul_le_mul (Nat.le_refl (2^(a+1))) (by omega)
      _ = 2^p := hp2.symm
  have hdiv : (u + 2^a) / 2^p = u / 2^p := by
    have hu : 2^p * (u / 2^p) + u % 2^p = u := Nat.div_add_mod u (2^p)
    have he : u + 2^a = 2^p * (u / 2^p) + (u % 2^p + 2^a) := by
      conv_lhs => rw [← hu]
      rw [Nat.add_assoc]
    rw [he, Nat.add_comm (2^p * (u / 2^p)) (u % 2^p + 2^a),
      Nat.add_mul_div_left (u % 2^p + 2^a) (u / 2^p) hp,
      Nat.div_eq_of_lt hsmall, Nat.zero_add]
  show ((u + 2^a) / 2^p % 2 == 1) = (u / 2^p % 2 == 1)
  rw [hdiv]

theorem pair_inj {a b c d : ℕ} (h : Nat.pair a b = Nat.pair c d) :
    a = c ∧ b = d := by
  have h1 := congrArg Nat.unpair h
  simp only [Nat.unpair_pair] at h1
  exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩

def tabN (Q : ℕ → ℕ → Prop) (hdec : ∀ x y, Decidable (Q x y)) :
    List (ℕ × ℕ) → ℕ
  | [] => 0
  | (x, y) :: ps => (if Q x y then 2 ^ Nat.pair x y else 0) + tabN Q hdec ps

theorem bitAt_tabN (Q : ℕ → ℕ → Prop) (hdec : ∀ x y, Decidable (Q x y)) :
    ∀ ps : List (ℕ × ℕ), ps.Nodup →
      ∀ p, bitAt (tabN Q hdec ps) p =
        decide (∃ q ∈ ps, Nat.pair q.1 q.2 = p ∧ Q q.1 q.2) := by
  intro ps
  induction ps with
  | nil =>
    intro _ p
    have hE : ¬ ∃ q ∈ ([] : List (ℕ × ℕ)), Nat.pair q.1 q.2 = p ∧ Q q.1 q.2 := by
      rintro ⟨q, hq, -, -⟩
      exact absurd hq (by simp)
    rw [show tabN Q hdec [] = 0 from rfl, bitAt_zero,
      decide_eq_false_iff_not.mpr hE]
  | cons a ps ih =>
    obtain ⟨x, y⟩ := a
    intro hnd p
    obtain ⟨hhead, hnd'⟩ := List.nodup_cons.mp hnd
    have h0 : bitAt (tabN Q hdec ps) (Nat.pair x y) = false := by
      rw [ih hnd' (Nat.pair x y)]
      exact decide_eq_false_iff_not.mpr (by
        rintro ⟨⟨q1, q2⟩, hq, hpq, -⟩
        have hpq' : Nat.pair q1 q2 = Nat.pair x y := hpq
        rcases pair_inj hpq' with ⟨e1, e2⟩
        subst e1
        subst e2
        exact hhead hq)
    by_cases hQ : Q x y
    · have htabT : tabN Q hdec ((x, y) :: ps)
          = 2 ^ Nat.pair x y + tabN Q hdec ps := by
        simp only [tabN, hQ, reduceIte]
      rw [htabT]
      rcases Nat.lt_trichotomy p (Nat.pair x y) with hlt | heq | hgt
      · rw [bitAt_add_two_pow_of_lt _ _ _ hlt, ih hnd' p, decide_eq_decide.mpr ?_]
        constructor
        · rintro ⟨q, hq, hpq, hQq⟩
          exact ⟨q, List.mem_cons_of_mem _ hq, hpq, hQq⟩
        · rintro ⟨q, hmem, hpq, hQq⟩
          rcases List.mem_cons.mp hmem with hq0 | hmem
          · subst hq0
            have hpe : Nat.pair x y = p := hpq
            exact absurd hpe (by omega)
          · exact ⟨q, hmem, hpq, hQq⟩
      · subst heq
        rw [Nat.add_comm (2 ^ Nat.pair x y) (tabN Q hdec ps), bitAt_add_eq, h0,
          Bool.not_false]
        exact (decide_eq_true
          ⟨(x, y), List.mem_cons.mpr (Or.inl rfl), rfl, hQ⟩).symm
      · rw [Nat.add_comm (2 ^ Nat.pair x y) (tabN Q hdec ps),
          bitAt_add_two_pow_of_gt' _ _ _ hgt h0, ih hnd' p, decide_eq_decide.mpr ?_]
        constructor
        · rintro ⟨q, hq, hpq, hQq⟩
          exact ⟨q, List.mem_cons_of_mem _ hq, hpq, hQq⟩
        · rintro ⟨q, hmem, hpq, hQq⟩
          rcases List.mem_cons.mp hmem with hq0 | hmem
          · subst hq0
            have hpe : Nat.pair x y = p := hpq
            exact absurd hpe (by omega)
          · exact ⟨q, hmem, hpq, hQq⟩
    · have htabF : tabN Q hdec ((x, y) :: ps) = tabN Q hdec ps := by
        simp only [tabN, hQ, reduceIte, Nat.zero_add]
      rw [htabF, ih hnd' p, decide_eq_decide.mpr ?_]
      constructor
      · rintro ⟨q, hq, hpq, hQq⟩
        exact ⟨q, List.mem_cons_of_mem _ hq, hpq, hQq⟩
      · rintro ⟨q, hmem, hpq, hQq⟩
        rcases List.mem_cons.mp hmem with hq0 | hmem
        · subst hq0
          exact absurd hQq hQ
        · exact ⟨q, hmem, hpq, hQq⟩

theorem finuniversalNat (Q : ℕ → ℕ → Prop) (hdec : ∀ x y, Decidable (Q x y))
    (K : Finset ℕ) :
    ∃ e, ∀ x ∈ K, ∀ y ∈ K, bitAt e (Nat.pair x y) = true ↔ Q x y := by
  have hnd : ((K ×ˢ K).toList).Nodup := Finset.nodup_toList (K ×ˢ K)
  refine ⟨tabN Q hdec (K ×ˢ K).toList, fun x hx y hy => ?_⟩
  rw [bitAt_tabN Q hdec (K ×ˢ K).toList hnd (Nat.pair x y), decide_eq_true_iff]
  constructor
  · rintro ⟨⟨x', y'⟩, hq, hpq, hQq⟩
    rcases pair_inj hpq with ⟨e1, e2⟩
    rw [← e1, ← e2]
    exact hQq
  · exact fun hQ =>
      ⟨(x, y), Finset.mem_toList.mpr (Finset.mem_product.mpr ⟨hx, hy⟩),
        rfl, hQ⟩

def Codebook : System where
  X := ℕ
  T := fun x => x + 1
  Φ := Unit
  φ := ()
  L := ℕ
  falsum := 0
  con := 1
  den := fun _ _ => False
  Prf := fun _ => False
  R := CoOrbit (fun x => x + 1)
  C := fun x _ => x
  interp := fun e x y => bitAt e (Nat.pair x y)
  finuniversal := finuniversalNat

theorem Codebook_ok (Q : ℕ → ℕ → Prop) (hdec : ∀ x y, Decidable (Q x y))
    (K : Finset ℕ) :
    ∃ e, ∀ x ∈ K, ∀ y ∈ K, Codebook.interp e x y = true ↔ Q x y :=
  finuniversalNat Q hdec K

/-! ## ═══ CAMP 3 — the Flicker (certified at v3.12, byte-identical) ═══ -/

def Tf (p : ℕ × Bool) : ℕ × Bool := (p.1, not p.2)

theorem flick_two (n : ℕ) (b : Bool) : Tf^[2] (n, b) = (n, b) := by
  show Tf (Tf (n, b)) = (n, b)
  exact congrArg (Prod.mk n) (not_iterate_two b)

theorem flick_even (n : ℕ) (b : Bool) (k : ℕ) : Tf^[2 * k] (n, b) = (n, b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by omega, Function.iterate_add_apply,
      flick_two, ih]

theorem flnot : ∀ p : ℕ × Bool, Tf p ≠ p := by
  intro p
  show (p.1, not p.2) ≠ p
  intro h
  have hs : not p.2 = p.2 := congrArg Prod.snd h
  rcases p with ⟨n, b⟩
  cases b with
  | false => exact Bool.noConfusion hs
  | true => exact Bool.noConfusion hs

theorem flTinj : Injective Tf := by
  rintro ⟨n, ba⟩ ⟨m, bb⟩ h
  have h1 : n = m := congrArg Prod.fst h
  have h2 : not ba = not bb := congrArg Prod.snd h
  have h3 : ba = bb := not_injective h2
  subst h1
  exact congrArg (Prod.mk n) h3

def fbEnc (p : ℕ × Bool) : ℕ := Nat.pair p.1 (Bool.toNat p.2)
def fbDec (m : ℕ) : ℕ × Bool := ((Nat.unpair m).1, (Nat.unpair m).2 == 1)

theorem fbDec_fbEnc (p : ℕ × Bool) : fbDec (fbEnc p) = p := by
  rcases p with ⟨n, b⟩
  have hu := Nat.unpair_pair (a := n) (b := Bool.toNat b)
  cases b with
  | false =>
    show ((Nat.unpair (Nat.pair n (Bool.toNat false))).1,
        (Nat.unpair (Nat.pair n (Bool.toNat false))).2 == 1) = (n, false)
    rw [hu]
    refine congrArg (Prod.mk n) ?_
    show ((0:ℕ) == 1) = false
    rfl
  | true =>
    show ((Nat.unpair (Nat.pair n (Bool.toNat true))).1,
        (Nat.unpair (Nat.pair n (Bool.toNat true))).2 == 1) = (n, true)
    rw [hu]
    refine congrArg (Prod.mk n) ?_
    show ((1:ℕ) == 1) = true
    rfl

theorem flick_finvuniversal :
    ∀ (Q : (ℕ × Bool) → (ℕ × Bool) → Prop), (∀ x y, Decidable (Q x y)) →
      ∀ K : Finset (ℕ × Bool), ∃ e, ∀ x ∈ K, ∀ y ∈ K,
        bitAt e (Nat.pair (fbEnc x) (fbEnc y)) = true ↔ Q x y := by
  intro Q hdec K
  obtain ⟨e, he⟩ := finuniversalNat (fun a b => Q (fbDec a) (fbDec b))
    (fun a b => hdec (fbDec a) (fbDec b)) (K.image fbEnc)
  refine ⟨e, fun x hx y hy => ?_⟩
  have h1 := he (fbEnc x) (Finset.mem_image_of_mem fbEnc hx)
    (fbEnc y) (Finset.mem_image_of_mem fbEnc hy)
  rw [fbDec_fbEnc, fbDec_fbEnc] at h1
  exact h1

def Flicker : System where
  X := ℕ × Bool
  T := Tf
  Φ := Bool
  φ := true
  L := ℕ
  falsum := 0
  con := 1
  den := fun ℓ p => bitAt ℓ (Nat.pair p.1 (Bool.toNat p.2))
  Prf := fun _ => False
  R := CoOrbit Tf
  C := fun p _ => p
  interp := fun e x y => bitAt e (Nat.pair (fbEnc x) (fbEnc y))
  finuniversal := flick_finvuniversal

theorem flickNameless :
    ¬ ∃ ℓ : ℕ, ∀ p : ℕ × Bool,
      Flicker.den ℓ p ↔ (fun q : ℕ × Bool => q.1 % 2 = 0) p := by
  rintro ⟨ℓ, h⟩
  have hbound : ∀ p : ℕ × Bool, Flicker.den ℓ p → fbEnc p < ℓ := by
    intro p hp
    have h1 : bitAt ℓ (fbEnc p) = true := by
      show bitAt ℓ (Nat.pair p.1 (Bool.toNat p.2)) = true
      exact hp
    have h2 := bitAt_le h1
    have h3 := two_pow_gt (fbEnc p)
    omega
  have heven : ∀ k : ℕ, (2:ℕ) * k % 2 = 0 := fun k => by omega
  have hn : ∀ k : ℕ, Flicker.den ℓ (2 * k, false) :=
    fun k => (h (2 * k, false)).mpr (heven k)
  have hginj : Function.Injective
      (fun k : ℕ => Nat.pair (2 * k) (Bool.toNat false)) := by
    intro k j hj
    have hpc := pair_inj hj
    have h2k : 2 * k = 2 * j := hpc.1
    omega
  have hsmall : ℓ + 1 ≤ ℓ := by
    have hemb : Function.Embedding (Fin (ℓ + 1)) (Fin ℓ) :=
      ⟨fun k => Fin.mk (Nat.pair (2 * k.1) (Bool.toNat false))
          (hbound _ (hn k.1)), by
        intro a b hab
        exact Fin.val_injective
          (hginj (congrArg (fun t : Fin ℓ => t.1) hab))⟩
    have hle : Fintype.card (Fin (ℓ + 1)) ≤ Fintype.card (Fin ℓ) :=
      Fintype.card_le_of_embedding (α := Fin (ℓ + 1)) (β := Fin ℓ) hemb
    simp only [Fintype.card_fin] at hle
    exact hle
  omega

theorem flick3 : Flicker.B3 := by
  refine ⟨fun p => p.1 % 2 = 0, ?_, ?_, flickNameless⟩
  · intro p hp
    exact hp
  · intro p hp
    exact ⟨(p.1, not p.2), hp, congrArg (Prod.mk p.1) (not_iterate_two p.2)⟩

theorem flick11 : Flicker.B11 := by
  refine ⟨fun p => p.1 % 2 = 0, ?_, ?_, ?_, flickNameless⟩
  · intro p hp
    exact hp
  · intro hI
    exact (Iff.of_eq (congrFun hI (0, false))).mp (Nat.zero_mod 2)
  · intro hI
    have hpt : ¬ ((1:ℕ) % 2 = 0) := by decide
    exact (not_congr (Iff.of_eq (congrFun hI (1, false)))).mp hpt trivial

theorem fl2 : Flicker.B2 := by
  refine ⟨(0, false), flnot (0, false), ?_⟩
  intro ℓ hℓ n
  refine ⟨2 * (n + 1), by omega, ?_⟩
  show Flicker.den ℓ (Tf^[2 * (n + 1)] (0, false))
  rw [flick_even 0 false (n + 1)]
  exact hℓ

theorem fl4 : Flicker.B4 := fun _x _y => Iff.rfl

theorem fl6 : Flicker.B6 := by
  refine ⟨false, ?_⟩
  show (false : Bool) ≠ (true : Bool)
  decide

theorem fl7 : Flicker.B7 := ⟨Tf, flnot⟩

theorem fl8 : Flicker.B8 := by
  refine ⟨fun p => p.2 = true, ⟨(0, true), rfl⟩, ⟨(0, false), ?_⟩, ?_, ?_⟩
  · show ¬ (false = true)
    decide
  · intro x y hx
    show x.2 = true
    exact hx
  · intro x y hx
    show x.2 = true ∨ y.2 = true
    exact Or.inl hx

theorem fl9 : Flicker.B9 := flnot

theorem fl10 : Flicker.B10 := by
  refine ⟨flTinj, ?_⟩
  show ∃ ℓ : ℕ, ∃ x, Flicker.den ℓ x ∧ ¬ ∀ y, Flicker.den ℓ y
  refine ⟨2 ^ Nat.pair 0 1, (0, true), ?_, ?_⟩
  · show bitAt (2 ^ Nat.pair 0 1)
        (Nat.pair (0, true).1 (Bool.toNat (0, true).2)) = true
    show bitAt (2 ^ Nat.pair 0 1) (Nat.pair 0 1) = true
    rw [bitAt_two_pow]
    exact decide_eq_true rfl
  · intro h
    have h0 : bitAt (2 ^ Nat.pair 0 1) (Nat.pair 0 0) = true := by
      have h1 := h (0, false)
      show bitAt (2 ^ Nat.pair 0 1)
        (Nat.pair (0, false).1 (Bool.toNat (0, false).2)) = true
      exact h1
    rw [bitAt_two_pow] at h0
    have heq : Nat.pair 0 0 = Nat.pair 0 1 := decide_eq_true_iff.mp h0
    exact absurd (pair_inj heq).2 (by decide)

theorem fl12 : Flicker.B12 := by
  intro p
  refine ⟨1, Tf p, by decide, rfl, ?_⟩
  show Tf (Tf p) ≠ Tf p
  exact fun h => not_not_ne_self p.2 (congrArg Prod.snd h)

theorem idol10 : ∃ S : System,
    S.B2 ∧ S.B4 ∧ S.B6 ∧ S.B7 ∧ S.B8 ∧ S.B9 ∧ S.B10 ∧ S.B12 ∧ S.B3 ∧ S.B11 :=
  ⟨Flicker, fl2, fl4, fl6, fl7, fl8, fl9, fl10, fl12, flick3, flick11⟩

/-! ## ═══ CAMP 2 — THE NO-FINITE-TABLE ═══

B1 on the Flicker: no table in the stock decides reachability.
Every table has finite support (bitAt_le: a set bit's power fits in ℓ);
reachability's true instances cross every fiber. Named honestly:
this certifies the no-finite-table form of B1. The Church–Turing
stock upgrade — the prose's "no algorithm" — is the file's declared
major debt, fenced for its own session.
-/

theorem fl1 : Flicker.B1 := by
  intro he
  obtain ⟨e, h⟩ := he
  -- DIRECTION NOTE: h's iff runs `interp = true ↔ Reachable`; we know
  -- Reachable and conclude the bit — .mpr. Read it the right way round.
  have htrue : ∀ k : ℕ,
      bitAt e (Nat.pair (Nat.pair (2 * k) 0) (Nat.pair (2 * k) 1)) = true := by
    intro k
    have hr : Reachable Flicker.T (2 * k, false) (2 * k, true) :=
      ⟨1, by show Tf (2 * k, false) = (2 * k, true); rfl⟩
    have h1 : Flicker.interp e (2 * k, false) (2 * k, true) = true :=
      (h (2 * k, false) (2 * k, true)).mpr hr
    show bitAt e (Nat.pair (fbEnc (2 * k, false)) (fbEnc (2 * k, true))) = true
    exact h1
  have hlt : ∀ k : ℕ,
      Nat.pair (Nat.pair (2 * k) 0) (Nat.pair (2 * k) 1) < e := by
    intro k
    have h2 := bitAt_le (htrue k)
    have h3 := two_pow_gt (Nat.pair (Nat.pair (2 * k) 0) (Nat.pair (2 * k) 1))
    omega
  have hemb : Function.Embedding (Fin (e + 1)) (Fin e) :=
    ⟨fun k => Fin.mk (Nat.pair (Nat.pair (2 * k.1) 0) (Nat.pair (2 * k.1) 1))
      (hlt _), by
      intro a b hab
      have h1 : Nat.pair (Nat.pair (2 * a.1) 0) (Nat.pair (2 * a.1) 1)
          = Nat.pair (Nat.pair (2 * b.1) 0) (Nat.pair (2 * b.1) 1) :=
        congrArg (fun t : Fin e => t.1) hab
      rcases pair_inj h1 with ⟨h2, _⟩
      rcases pair_inj h2 with ⟨h3, _⟩
      exact Fin.val_injective (show a.1 = b.1 from by omega)⟩
  have hle : Fintype.card (Fin (e + 1)) ≤ Fintype.card (Fin e) :=
    Fintype.card_le_of_embedding (α := Fin (e + 1)) (β := Fin e) hemb
  simp only [Fintype.card_fin] at hle
  omega

/-- ELEVEN OF TWELVE — everything except the Silence. -/
theorem idol11 : ∃ S : System,
    S.B1 ∧ S.B2 ∧ S.B4 ∧ S.B6 ∧ S.B7 ∧ S.B8 ∧ S.B9 ∧ S.B10 ∧ S.B12 ∧ S.B3 ∧ S.B11 :=
  ⟨Flicker, fl1, fl2, fl4, fl6, fl7, fl8, fl9, fl10, fl12, flick3, flick11⟩

/-! ## ═══ CAMP 4 — κ: DEPARTURE REQUIRES INFINITY ═══

The first theorem in this file about the ARTIST rather than the wall.
A sequence in a finite type can only *leave* finitely many of its values
behind. Applied twice: to the wall's trajectory (memory must be infinite)
and to the input stream κ itself (arrivals that never return must be
infinitely many). This is also the file's first mention of an INPUT —
`traj` is the open signature in miniature, a door cut into the wall.
-/

/-- Index `n` is a *departure* of `s`: the value `s n` is never seen again. -/
def IsDeparture {α : Type*} (s : ℕ → α) (n : ℕ) : Prop :=
  ∀ m, n < m → s m ≠ s n

/-- `s` keeps departing: departures occur beyond every bound. -/
def KeepsDeparting {α : Type*} (s : ℕ → α) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ IsDeparture s n

/-- Distinct departure indices carry distinct values. -/
theorem departure_injOn {α : Type*} (s : ℕ → α) :
    Set.InjOn s {n | IsDeparture s n} := by
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact ha b h hab.symm
  · exact hb a h hab

/-- In a finite type there are only finitely many departures. -/
theorem finite_departures {α : Type*} [Finite α] (s : ℕ → α) :
    {n | IsDeparture s n}.Finite :=
  Set.Finite.of_finite_image (Set.toFinite _) (departure_injOn s)

/-- ★ THE THEOREM — nothing finite can keep leaving. -/
theorem departure_requires_infinity {α : Type*} [Finite α] (s : ℕ → α) :
    ¬ KeepsDeparting s := by
  intro h
  obtain ⟨N, hN⟩ := (finite_departures s).bddAbove
  obtain ⟨n, hn, hd⟩ := h (N + 1)
  have : n ≤ N := hN hd
  omega

theorem infinite_of_keepsDeparting {α : Type*} (s : ℕ → α)
    (h : KeepsDeparting s) : Infinite α := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  exact departure_requires_infinity s h

/-! ### The open wall — state driven by an input stream κ -/

/-- The wall's trajectory under inputs `u`: the next state depends on who arrives. -/
def traj {X U : Type*} (step : U → X → X) (u : ℕ → U) (x₀ : X) : ℕ → X
  | 0 => x₀
  | n + 1 => step (u n) (traj step u x₀ n)

/-- A wall that keeps leaving states behind has infinite memory — whatever κ does. -/
theorem wall_departure_requires_infinite_state {X U : Type*}
    (step : U → X → X) (u : ℕ → U) (x₀ : X)
    (h : KeepsDeparting (traj step u x₀)) : Infinite X :=
  infinite_of_keepsDeparting _ h

/-- Arrivals that never return are infinitely many: κ cannot be finite. -/
theorem artist_departure_requires_infinite_kappa {U : Type*} (u : ℕ → U)
    (h : KeepsDeparting u) : Infinite U :=
  infinite_of_keepsDeparting u h

/-- The hook into the Idol: a wall that keeps departing cannot be finite. -/
theorem idol_departure_requires_infinity (S : System) (x : S.X)
    (h : KeepsDeparting (fun n => S.T^[n] x)) : Infinite S.X :=
  infinite_of_keepsDeparting _ h

/-! ## Tier 3 — the open wall -/

theorem wooden_idol : ∃ S : System, All12 S := by
  sorry

#print axioms no_finite_idol
#print axioms partial_idol
#print axioms idol8
#print axioms finuniversalNat
#print axioms Codebook_ok
#print axioms idol10
#print axioms idol11
#print axioms departure_requires_infinity
#print axioms wall_departure_requires_infinite_state
#print axioms artist_departure_requires_infinite_kappa
#print axioms idol_departure_requires_infinity
#print axioms wooden_idol
