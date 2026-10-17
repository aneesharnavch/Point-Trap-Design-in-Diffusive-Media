module

public import TimeTraps.Analysis.RegularSturmVariationalMinimizerHilbert

@[expose] public section

/-! Every physical selected-zero Rayleigh minimizer satisfies the original
equation against every selected-zero H1 test and lies in the actual L2
operator graph. A positive-mass principal weak eigenstate conversely
attains the independently defined Rayleigh minimum. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem RegularSturmProblem.minimizer_weak
    (P : RegularSturmProblem ι l r) {u : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0)
    (hm : 0 < P.squareMass u)
    (hmin : P.quadraticForm u / P.squareMass u = P.principalValue) :
    ∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u v =
        P.principalValue * ∫ x in l..r, P.speed x * u x * v x := by
  have he : P.form (P.boundary.ofEnergy hu huz) (P.boundary.ofEnergy hu huz) =
      P.principalValue * ‖P.stateL (P.boundary.ofEnergy hu huz)‖ ^ 2 := by
    rw [P.quadraticForm_ofEnergy, P.squareMass_ofEnergy]
    exact (div_eq_iff hm.ne').mp hmin
  have h := (P.hilbert_eigen_iff_physical (P.boundary.ofEnergy hu huz) P.principalValue).mp
    (P.minimizer_hilbert _ he)
  intro v hv hvz
  have hv' := h v hv hvz
  rw [regularSturmPhysicalForm_congr P.conductance P.potential P.strength P.site P.boundary.interval_pos.le P.site_mem
    (P.boundary.ofEnergy_representative hu huz) (fun _ _ => rfl)] at hv'
  have hi : (∫ x in l..r, P.speed x * (P.boundary.ofEnergy hu huz).val.representative
      P.boundary.interval_pos x * v x) = ∫ x in l..r, P.speed x * u x * v x := by
    apply intervalIntegral.integral_congr_Ioo_of_le P.boundary.interval_pos.le
    intro x hx
    change P.speed x * (P.boundary.ofEnergy hu huz).val.representative P.boundary.interval_pos x * v x = P.speed x * u x * v x
    rw [P.boundary.ofEnergy_representative hu huz (Ioo_subset_Icc_self hx)]
  rwa [hi] at hv'

theorem RegularSturmProblem.minimizer_iff_weak
    (P : RegularSturmProblem ι l r) {u : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0)
    (hm : 0 < P.squareMass u) :
    P.quadraticForm u / P.squareMass u = P.principalValue ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        (∀ x ∈ P.boundary.zero_sites, v x = 0) →
        regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u v =
          P.principalValue * ∫ x in l..r, P.speed x * u x * v x := by
  refine ⟨P.minimizer_weak hu huz hm, ?_⟩
  intro h
  apply (div_eq_iff hm.ne').mpr
  simpa only [RegularSturmProblem.quadraticForm,
    RegularSturmProblem.squareMass, pow_two, mul_assoc] using h u hu huz

theorem RegularSturmProblem.minimizer_operator_graph
    (P : RegularSturmProblem ι l r) {u : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0)
    (hm : 0 < P.squareMass u)
    (hmin : P.quadraticForm u / P.squareMass u = P.principalValue) :
    (P.stateL (P.boundary.ofEnergy hu huz),
      P.principalValue • P.stateL (P.boundary.ofEnergy hu huz)) ∈ P.operator.graph := by
  apply (P.operator_eigen_iff_hilbert _ P.principalValue).mpr
  apply P.minimizer_hilbert
  rw [P.quadraticForm_ofEnergy, P.squareMass_ofEnergy]
  exact (div_eq_iff hm.ne').mp hmin

end TimeTraps.Analysis
