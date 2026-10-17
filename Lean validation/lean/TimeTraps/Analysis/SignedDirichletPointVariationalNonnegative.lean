module

public import TimeTraps.Analysis.SignedDirichletPointVariationalMinimizerPhysical
public import TimeTraps.Analysis.DirichletPositiveGroundAbsolute

@[expose] public section

/-! Absolute value preserves the actual signed point form, the selected
zero traces and the L2 mass. Hence a nonnegative physical principal
eigenstate exists without any sign assumption on the contact strengths
or the principal value. Strict positivity and simplicity are separate. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedDirichletPointProblem.absState_form (P : SignedDirichletPointProblem ι l r)
    (u : IntervalDirichletSpace P.boundary) :
    P.form (P.boundary.absState u) (P.boundary.absState u) = P.form u u := by
  change intervalDirichletPointForm P.boundary P.diffusivity P.strength P.site P.site_mem _ _ =
    intervalDirichletPointForm P.boundary P.diffusivity P.strength P.site P.site_mem _ _
  rw [intervalDirichletPointForm_apply, intervalDirichletPointForm_apply]
  rw [intervalPointForm_congr P.diffusivity P.strength P.site P.boundary.interval_pos.le P.site_mem
    (P.boundary.absState_representative u) (P.boundary.absState_representative u)]
  exact (u.val.representative_spec P.boundary.interval_pos).1.abs_point_form
    P.diffusivity P.strength P.site

theorem SignedDirichletPointProblem.squareMass_abs (P : SignedDirichletPointProblem ι l r)
    (u : ℝ → ℝ) : P.squareMass (fun x => |u x|) = P.squareMass u :=
  interval_abs_square_mass u l r

theorem SignedDirichletPointProblem.quadraticForm_abs (P : SignedDirichletPointProblem ι l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    P.quadraticForm (fun x => |u x|) = P.quadraticForm u :=
  hu.abs_point_form P.diffusivity P.strength P.site

theorem SignedDirichletPointProblem.nonnegative_rayleigh_minimizer
    (P : SignedDirichletPointProblem ι l r) :
    ∃ u : ℝ → ℝ, IntervalEnergy u l r ∧
      (∀ x ∈ P.boundary.zero_sites, u x = 0) ∧ (∀ x, 0 ≤ u x) ∧
      0 < P.squareMass u ∧ P.quadraticForm u / P.squareMass u = P.principalValue := by
  obtain ⟨u, hu, huz, hm, he⟩ := P.rayleigh_minimum.1
  refine ⟨fun x => |u x|, hu.abs, ?_, fun x => abs_nonneg (u x), ?_, ?_⟩
  · intro x hx
    change |u x| = 0
    rw [huz x hx, abs_zero]
  · rwa [P.squareMass_abs]
  · rw [P.quadraticForm_abs hu, P.squareMass_abs]
    exact he.symm

theorem SignedDirichletPointProblem.nonnegative_principal_eigenstate
    (P : SignedDirichletPointProblem ι l r) :
    ∃ u : ℝ → ℝ, ∃ hu : IntervalEnergy u l r,
      ∃ huz : ∀ x ∈ P.boundary.zero_sites, u x = 0,
      (∀ x, 0 ≤ u x) ∧ 0 < P.squareMass u ∧
      (∀ v : ℝ → ℝ, IntervalEnergy v l r →
        (∀ x ∈ P.boundary.zero_sites, v x = 0) →
        intervalPointForm P.diffusivity P.strength P.site l r u v =
          P.principalValue * ∫ x in l..r, u x * v x) ∧
      (P.boundary.stateL (P.boundary.ofEnergy hu huz),
        P.principalValue • P.boundary.stateL (P.boundary.ofEnergy hu huz)) ∈ P.operator.graph := by
  obtain ⟨u, hu, huz, hnonneg, hm, hmin⟩ := P.nonnegative_rayleigh_minimizer
  exact ⟨u, hu, huz, hnonneg, hm, P.minimizer_weak hu huz hm hmin,
    P.minimizer_operator_graph hu huz hm hmin⟩

end TimeTraps.Analysis
