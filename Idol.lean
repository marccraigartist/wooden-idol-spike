/-! ## ═══ CAMP 6 — κ: ARRIVAL, AND WHAT THE WALL CAN SEE ═══ -/

/-- Index `n` is an *arrival*: the value `s n` was never seen before. -/
def IsArrival {α : Type*} (s : ℕ → α) (n : ℕ) : Prop :=
  ∀ m, m < n → s m ≠ s n

/-- `s` keeps arriving: first occurrences beyond every bound. -/
def KeepsArriving {α : Type*} (s : ℕ → α) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ IsArrival s n

/-- Distinct arrival indices carry distinct values. -/
theorem arrival_injOn {α : Type*} (s : ℕ → α) :
    Set.InjOn s {n | IsArrival s n} := by
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hb a h hab.symm
  · exact ha b h hab

theorem finite_arrivals {α : Type*} [Finite α] (s : ℕ → α) :
    {n | IsArrival s n}.Finite :=
  Set.Finite.of_finite_image (Set.toFinite _) (arrival_injOn s)

/-- The dual: nothing finite can keep producing novelty. -/
theorem arrival_requires_infinity {α : Type*} [Finite α] (s : ℕ → α) :
    ¬ KeepsArriving s := by
  intro h
  obtain ⟨N, hN⟩ := (finite_arrivals s).bddAbove
  obtain ⟨n, hn, ha⟩ := h (N + 1)
  have : n ≤ N := hN ha
  omega

/-- ★ THE ASYMMETRY — arrival is decided by the finite past. -/
instance arrival_decidable {α : Type*} [DecidableEq α] (s : ℕ → α) (n : ℕ) :
    Decidable (IsArrival s n) :=
  decidable_of_iff (∀ m ∈ Finset.range n, s m ≠ s n) (by
    constructor
    · intro h m hm
      exact h m (Finset.mem_range.mpr hm)
    · intro h m hm
      exact h m (Finset.mem_range.mp hm))

#print axioms arrival_requires_infinity
