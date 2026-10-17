module

public import TimeTraps.Probability.ReflectedLifetimeDecayObjective
public import TimeTraps.Spectral.PlacementUniqueness

@[expose] public section

/-! Sharp prescribed-strength placement for the objective defined from
actual killing-lifetime survival. The full equality case and attained
maximum follow from the proved lifetime/operator identification. -/

namespace TimeTraps.Probability

open Set TimeTraps.Spectral

variable {n : ℕ}

noncomputable def reflectedPlacementDecayValues (C : PlacementProblem n) (z : ℝ) : Set ℝ :=
  {r | ∃ x : Fin n → ℝ, ∃ hx : C.Admissible x,
    r = reflectedLifetimeDecayRate (C.physical x hx) z}

theorem reflectedPlacement_decay_upper_bound (C : PlacementProblem n)
    (x : Fin n → ℝ) (hx : C.Admissible x) {z : ℝ} (hz : z ∈ Icc 0 C.length) :
    reflectedLifetimeDecayRate (C.physical x hx) z ≤ C.diffusivity * C.root ^ 2 := by
  rw [reflectedLifetimeDecayRate_eq (C.physical x hx) hz]
  exact C.arbitrary_upper_bound x hx

theorem reflectedPlacement_decay_eq_iff (C : PlacementProblem n)
    (x : Fin n → ℝ) (hx : C.Admissible x) {z : ℝ} (hz : z ∈ Icc 0 C.length) :
    reflectedLifetimeDecayRate (C.physical x hx) z = C.diffusivity * C.root ^ 2 ↔ x = C.optimalSite := by
  rw [reflectedLifetimeDecayRate_eq (C.physical x hx) hz]
  exact C.value_eq_iff_sites x hx

theorem reflectedPlacementDecayValues_eq (C : PlacementProblem n)
    {z : ℝ} (hz : z ∈ Icc 0 C.length) : reflectedPlacementDecayValues C z = C.principalValues := by
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, reflectedLifetimeDecayRate_eq (C.physical x hx) hz⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (reflectedLifetimeDecayRate_eq (C.physical x hx) hz).symm⟩

theorem reflectedPlacement_decay_maximum (C : PlacementProblem n)
    {z : ℝ} (hz : z ∈ Icc 0 C.length) :
    IsGreatest (reflectedPlacementDecayValues C z) (C.diffusivity * C.root ^ 2) := by
  rw [reflectedPlacementDecayValues_eq C hz]
  exact C.placement_maximum

theorem reflectedPlacement_decay_strict_loss (C : PlacementProblem n)
    (x : Fin n → ℝ) (hx : C.Admissible x) {z : ℝ} (hz : z ∈ Icc 0 C.length)
    (hne : x ≠ C.optimalSite) :
    reflectedLifetimeDecayRate (C.physical x hx) z < C.diffusivity * C.root ^ 2 := by
  rw [reflectedLifetimeDecayRate_eq (C.physical x hx) hz]
  exact C.strict_loss_of_other_sites x hx hne

end TimeTraps.Probability
