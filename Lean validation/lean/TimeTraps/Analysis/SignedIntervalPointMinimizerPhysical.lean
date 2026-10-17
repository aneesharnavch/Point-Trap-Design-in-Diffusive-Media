module

public import TimeTraps.Analysis.SignedIntervalPointMinimizerHilbert

@[expose] public section

/-! Every physical Rayleigh minimizer satisfies the original equation
against every actual H1 test, and belongs to the actual L2 operator graph.
Conversely, a positive-mass weak eigenstate at the principal value attains
the independently defined Rayleigh minimum. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.minimizer_weak
    (P : SignedIntervalPointProblem ι l r) {u : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hm : 0 < P.squareMass u)
    (hmin : P.quadraticForm u / P.squareMass u = P.principalValue) :
    ∀ v : ℝ → ℝ, IntervalEnergy v l r →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        P.principalValue * ∫ x in l..r, u x * v x := by
  have he : P.form (ofEnergy hu P.interval_pos) (ofEnergy hu P.interval_pos) =
      P.principalValue * ‖(ofEnergy hu P.interval_pos).state‖ ^ 2 := by
    rw [P.quadraticForm_ofEnergy, P.squareMass_ofEnergy]
    exact (div_eq_iff hm.ne').mp hmin
  have h := (P.hilbert_eigen_iff_physical (ofEnergy hu P.interval_pos) P.principalValue).mp
    (P.minimizer_hilbert _ he)
  intro v hv
  have hv' := h v hv
  rw [intervalPointForm_congr P.diffusivity P.strength P.site P.interval_pos.le P.site_mem
    (representative_ofEnergy hu P.interval_pos) (fun _ _ => rfl)] at hv'
  have hi : (∫ x in l..r, (ofEnergy hu P.interval_pos).representative P.interval_pos x * v x) =
      ∫ x in l..r, u x * v x := by
    apply intervalIntegral.integral_congr_Ioo_of_le P.interval_pos.le
    intro x hx
    change (ofEnergy hu P.interval_pos).representative P.interval_pos x * v x = u x * v x
    rw [representative_ofEnergy hu P.interval_pos (Ioo_subset_Icc_self hx)]
  rwa [hi] at hv'

theorem SignedIntervalPointProblem.minimizer_iff_weak
    (P : SignedIntervalPointProblem ι l r) {u : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hm : 0 < P.squareMass u) :
    P.quadraticForm u / P.squareMass u = P.principalValue ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        intervalPointForm P.diffusivity P.strength P.site l r u v =
          P.principalValue * ∫ x in l..r, u x * v x := by
  refine ⟨P.minimizer_weak hu hm, ?_⟩
  intro h
  apply (div_eq_iff hm.ne').mpr
  simpa only [SignedIntervalPointProblem.quadraticForm,
    SignedIntervalPointProblem.squareMass, pow_two] using h u hu

theorem SignedIntervalPointProblem.minimizer_operator_graph
    (P : SignedIntervalPointProblem ι l r) {u : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hm : 0 < P.squareMass u)
    (hmin : P.quadraticForm u / P.squareMass u = P.principalValue) :
    ((ofEnergy hu P.interval_pos).state,
      P.principalValue • (ofEnergy hu P.interval_pos).state) ∈ P.operator.graph := by
  apply (P.operator_eigen_iff_hilbert _ P.principalValue).mpr
  apply P.minimizer_hilbert
  rw [P.quadraticForm_ofEnergy, P.squareMass_ofEnergy]
  exact (div_eq_iff hm.ne').mp hmin

end TimeTraps.Analysis
