module

public import TimeTraps.Analysis.RegularSturmVariationalMinimizerPhysical
public import TimeTraps.Analysis.IntervalEnergyAbsolute

@[expose] public section

/-! Absolute value preserves the actual signed point form, the selected
zero traces and the L2 mass. Hence a nonnegative physical principal
eigenstate exists without any sign assumption on the contact strengths
or the principal value. Strict positivity and simplicity are separate. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem RegularSturmProblem.squareMass_abs (P : RegularSturmProblem ι l r)
    (u : ℝ → ℝ) : P.squareMass (fun x => |u x|) = P.squareMass u := by
  simp only [RegularSturmProblem.squareMass, sq_abs]

theorem RegularSturmProblem.quadraticForm_abs (P : RegularSturmProblem ι l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    P.quadraticForm (fun x => |u x|) = P.quadraticForm u := by
  have hgrad : (∫ x in l..r, P.conductance x * deriv (fun y => |u y|) x ^ 2) =
      ∫ x in l..r, P.conductance x * deriv u x ^ 2 := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [hu.abs_derivative_square_ae] with x hx
    rw [hx]
  simp only [RegularSturmProblem.quadraticForm, regularSturmPhysicalForm,
    mul_assoc, ← pow_two, sq_abs, hgrad]

theorem RegularSturmProblem.nonnegative_rayleigh_minimizer
    (P : RegularSturmProblem ι l r) :
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

theorem RegularSturmProblem.nonnegative_principal_eigenstate
    (P : RegularSturmProblem ι l r) :
    ∃ u : ℝ → ℝ, ∃ hu : IntervalEnergy u l r,
      ∃ huz : ∀ x ∈ P.boundary.zero_sites, u x = 0,
      (∀ x, 0 ≤ u x) ∧ 0 < P.squareMass u ∧
      (∀ v : ℝ → ℝ, IntervalEnergy v l r →
        (∀ x ∈ P.boundary.zero_sites, v x = 0) →
        regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u v =
          P.principalValue * ∫ x in l..r, P.speed x * u x * v x) ∧
      (P.stateL (P.boundary.ofEnergy hu huz),
        P.principalValue • P.stateL (P.boundary.ofEnergy hu huz)) ∈ P.operator.graph := by
  obtain ⟨u, hu, huz, hnonneg, hm, hmin⟩ := P.nonnegative_rayleigh_minimizer
  exact ⟨u, hu, huz, hnonneg, hm, P.minimizer_weak hu huz hm hmin,
    P.minimizer_operator_graph hu huz hm hmin⟩

end TimeTraps.Analysis
