module

public import TimeTraps.Probability.ReflectedRobinLifetimeDecayObjective
public import TimeTraps.Spectral.RobinPlacementUniqueness

@[expose] public section

/-! Sharp prescribed-strength placement for the objective defined from
actual killing-lifetime survival. The full equality case and attained
maximum follow from the proved lifetime/operator identification. -/

namespace TimeTraps.Probability

open Set TimeTraps.Spectral

variable {n : ℕ}

noncomputable def reflectedRobinPlacementDecayValues (C : RobinPlacementProblem n) (z : ℝ) : Set ℝ :=
  {r | ∃ x : Fin n → ℝ, ∃ hx : C.Admissible x,
    r = reflectedRobinLifetimeDecayRate (C.physical x hx) z}

theorem reflectedRobinPlacement_decay_upper_bound (C : RobinPlacementProblem n)
    (x : Fin n → ℝ) (hx : C.Admissible x) {z : ℝ} (hz : z ∈ Icc 0 C.length) :
    reflectedRobinLifetimeDecayRate (C.physical x hx) z ≤ C.diffusivity * C.root ^ 2 := by
  rw [reflectedRobinLifetimeDecayRate_eq (C.physical x hx) hz]
  exact C.arbitrary_upper_bound x hx

theorem reflectedRobinPlacement_decay_eq_iff (C : RobinPlacementProblem n)
    (x : Fin n → ℝ) (hx : C.Admissible x) {z : ℝ} (hz : z ∈ Icc 0 C.length) :
    reflectedRobinLifetimeDecayRate (C.physical x hx) z = C.diffusivity * C.root ^ 2 ↔ x = C.candidateSite := by
  rw [reflectedRobinLifetimeDecayRate_eq (C.physical x hx) hz]
  exact C.value_eq_iff_sites x hx

theorem reflectedRobinPlacementDecayValues_eq (C : RobinPlacementProblem n)
    {z : ℝ} (hz : z ∈ Icc 0 C.length) : reflectedRobinPlacementDecayValues C z = C.principalValues := by
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, reflectedRobinLifetimeDecayRate_eq (C.physical x hx) hz⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (reflectedRobinLifetimeDecayRate_eq (C.physical x hx) hz).symm⟩

theorem reflectedRobinPlacement_decay_maximum (C : RobinPlacementProblem n)
    {z : ℝ} (hz : z ∈ Icc 0 C.length) :
    IsGreatest (reflectedRobinPlacementDecayValues C z) (C.diffusivity * C.root ^ 2) := by
  rw [reflectedRobinPlacementDecayValues_eq C hz]
  exact C.placement_maximum

theorem reflectedRobinPlacement_decay_strict_loss (C : RobinPlacementProblem n)
    (x : Fin n → ℝ) (hx : C.Admissible x) {z : ℝ} (hz : z ∈ Icc 0 C.length)
    (hne : x ≠ C.candidateSite) :
    reflectedRobinLifetimeDecayRate (C.physical x hx) z < C.diffusivity * C.root ^ 2 := by
  rw [reflectedRobinLifetimeDecayRate_eq (C.physical x hx) hz]
  exact C.strict_loss_of_other_sites x hx hne

theorem reflectedRobinPlacement_decay_optimizer_iff (C : RobinPlacementProblem n)
    (x : Fin n → ℝ) (hx : C.Admissible x) {z : ℝ} (hz : z ∈ Icc 0 C.length) :
    (∀ y : Fin n → ℝ, ∀ hy : C.Admissible y,
      reflectedRobinLifetimeDecayRate (C.physical y hy) z ≤
        reflectedRobinLifetimeDecayRate (C.physical x hx) z) ↔ x = C.candidateSite := by
  have he (y : Fin n → ℝ) (hy : C.Admissible y) :=
    reflectedRobinLifetimeDecayRate_eq (C.physical y hy) hz
  simp only [he]
  exact C.optimizer_iff x hx

end TimeTraps.Probability
