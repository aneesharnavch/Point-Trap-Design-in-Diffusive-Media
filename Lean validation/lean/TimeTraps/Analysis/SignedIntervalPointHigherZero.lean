module

public import TimeTraps.Analysis.SignedIntervalPointHigherZeroIntegral
public import TimeTraps.Analysis.SignedIntervalPointHigherZeroOrthogonality
public import TimeTraps.Analysis.SignedIntervalPointPositiveGround

@[expose] public section

/-! Every physical weak eigenstate whose real eigenvalue differs from
the principal value has an open-interval zero. The positive ground state
is already constructed from the independent Rayleigh problem. Neither
simplicity nor a spectral basis is assumed. Nontriviality is unnecessary
for this conclusion, so the theorem also includes the zero state. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.weak_eigen_exists_interior_zero
    (P : SignedIntervalPointProblem ι l r) {u : ℝ → ℝ} {ev : ℝ}
    (hu : IntervalEnergy u l r)
    (he : ∀ v : ℝ → ℝ, IntervalEnergy v l r →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        ev * ∫ x in l..r, u x * v x)
    (hne : ev ≠ P.principalValue) : ∃ x ∈ Ioo l r, u x = 0 := by
  obtain ⟨w, hw, hwpos, _, hew, _⟩ := P.positive_principal_eigenstate
  have huc : ContinuousOn u (Icc l r) := by
    simpa only [uIcc_of_le P.interval_pos.le] using hu.continuousOn
  have hwc : ContinuousOn w (Icc l r) := by
    simpa only [uIcc_of_le P.interval_pos.le] using hw.continuousOn
  exact exists_interior_zero_of_weighted_integral_eq_zero P.interval_pos huc hwc
    (fun x hx => hwpos x (Ioo_subset_Icc_self hx))
    (P.weak_eigen_orthogonal hu hw he hew hne)

theorem SignedIntervalPointProblem.operator_eigen_exists_interior_zero
    (P : SignedIntervalPointProblem ι l r) (u : IntervalSobolevSpace l r) {ev : ℝ}
    (he : (u.state, ev • u.state) ∈ P.operator.graph)
    (hne : ev ≠ P.principalValue) :
    ∃ x ∈ Ioo l r, u.representative P.interval_pos x = 0 :=
  P.weak_eigen_exists_interior_zero (u.representative_spec P.interval_pos).1
    ((P.operator_eigen_iff_physical u ev).mp he) hne

end TimeTraps.Analysis
