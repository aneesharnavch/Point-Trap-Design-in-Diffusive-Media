module

public import TimeTraps.Analysis.SignedPeriodicPointVariationalMinimizerHilbert

@[expose] public section

/-! Every physical endpoint-matched periodic Rayleigh minimizer satisfies the original
equation against every endpoint-matched periodic H1 test and lies in the actual L2
operator graph. A positive-mass principal weak eigenstate conversely
attains the independently defined Rayleigh minimum. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedPeriodicPointProblem.minimizer_weak
    (P : SignedPeriodicPointProblem ι l r) {u : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (huz : u l = u r)
    (hm : 0 < P.squareMass u)
    (hmin : P.quadraticForm u / P.squareMass u = P.principalValue) :
    ∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (v l = v r) →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        P.principalValue * ∫ x in l..r, u x * v x := by
  have he : P.form (P.boundary.ofEnergy hu huz.symm) (P.boundary.ofEnergy hu huz.symm) =
      P.principalValue * ‖P.boundary.stateL (P.boundary.ofEnergy hu huz.symm)‖ ^ 2 := by
    rw [P.quadraticForm_ofEnergy hu huz, P.squareMass_ofEnergy hu huz]
    exact (div_eq_iff hm.ne').mp hmin
  have h := (P.hilbert_eigen_iff_physical (P.boundary.ofEnergy hu huz.symm) P.principalValue).mp
    (P.minimizer_hilbert _ he)
  intro v hv hvz
  have hv' := h v hv hvz
  rw [intervalPointForm_congr P.diffusivity P.strength P.site P.boundary.interval_pos.le P.site_mem
    (P.boundary.ofEnergy_representative hu huz.symm) (fun _ _ => rfl)] at hv'
  have hi : (∫ x in l..r, (P.boundary.ofEnergy hu huz.symm).val.representative
      P.boundary.interval_pos x * v x) = ∫ x in l..r, u x * v x := by
    apply intervalIntegral.integral_congr_Ioo_of_le P.boundary.interval_pos.le
    intro x hx
    change (P.boundary.ofEnergy hu huz.symm).val.representative P.boundary.interval_pos x * v x = u x * v x
    rw [P.boundary.ofEnergy_representative hu huz.symm (Ioo_subset_Icc_self hx)]
  rwa [hi] at hv'

theorem SignedPeriodicPointProblem.minimizer_iff_weak
    (P : SignedPeriodicPointProblem ι l r) {u : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (huz : u l = u r)
    (hm : 0 < P.squareMass u) :
    P.quadraticForm u / P.squareMass u = P.principalValue ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        (v l = v r) →
        intervalPointForm P.diffusivity P.strength P.site l r u v =
          P.principalValue * ∫ x in l..r, u x * v x := by
  refine ⟨P.minimizer_weak hu huz hm, ?_⟩
  intro h
  apply (div_eq_iff hm.ne').mpr
  simpa only [SignedPeriodicPointProblem.quadraticForm,
    SignedPeriodicPointProblem.squareMass, pow_two] using h u hu huz

theorem SignedPeriodicPointProblem.minimizer_operator_graph
    (P : SignedPeriodicPointProblem ι l r) {u : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (huz : u l = u r)
    (hm : 0 < P.squareMass u)
    (hmin : P.quadraticForm u / P.squareMass u = P.principalValue) :
    (P.boundary.stateL (P.boundary.ofEnergy hu huz.symm),
      P.principalValue • P.boundary.stateL (P.boundary.ofEnergy hu huz.symm)) ∈ P.operator.graph := by
  apply (P.operator_eigen_iff_hilbert _ P.principalValue).mpr
  apply P.minimizer_hilbert
  rw [P.quadraticForm_ofEnergy hu huz, P.squareMass_ofEnergy hu huz]
  exact (div_eq_iff hm.ne').mp hmin

end TimeTraps.Analysis
