module

public import TimeTraps.Analysis.SignedPeriodicPointHigherZeroOrthogonality
public import TimeTraps.Analysis.SignedPeriodicPointPositiveGroundAttainment
public import TimeTraps.Analysis.SignedIntervalPointHigherZeroIntegral

@[expose] public section

/-! Every nonprincipal signed periodic weak eigenstate has a zero
in the open interval. The proof uses the independently attained positive
ground state and orthogonality, not an assumed oscillation theorem or
exact nodal count. The actual L2 graph supplies its H1 representative. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedPeriodicPointProblem.weak_eigen_exists_interior_zero
    (P : SignedPeriodicPointProblem ι l r) {u : ℝ → ℝ} {ev : ℝ}
    (hu : IntervalEnergy u l r) (huz : u l = u r)
    (he : ∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (v l = v r) →
      intervalPointForm P.diffusivity P.strength P.site l r u v =
        ev * ∫ x in l..r, u x * v x)
    (hne : ev ≠ P.principalValue) : ∃ x ∈ Ioo l r, u x = 0 := by
  obtain ⟨w, hw, hwz, hwpos, _hm, hew, _hg⟩ := P.positive_principal_eigenstate
  have huc : ContinuousOn u (Icc l r) := by
    simpa only [uIcc_of_le P.boundary.interval_pos.le] using hu.continuousOn
  have hwc : ContinuousOn w (Icc l r) := by
    simpa only [uIcc_of_le P.boundary.interval_pos.le] using hw.continuousOn
  exact exists_interior_zero_of_weighted_integral_eq_zero P.boundary.interval_pos huc hwc (fun x hx => hwpos x (Ioo_subset_Icc_self hx))
    (P.weak_eigen_orthogonal hu hw huz hwz he hew hne)

theorem SignedPeriodicPointProblem.operator_eigen_exists_interior_zero
    (P : SignedPeriodicPointProblem ι l r) (u : IntervalSobolevL2 l r) {ev : ℝ}
    (hg : (u, ev • u) ∈ P.operator.graph) (hne : ev ≠ P.principalValue) :
    ∃ U : ℝ → ℝ, IntervalEnergy U l r ∧
      (U l = U r) ∧
      u =ᵐ[volume.restrict (Ioo l r)] U ∧ ∃ x ∈ Ioo l r, U x = 0 := by
  obtain ⟨v, hv, _he⟩ := (P.operator_graph_iff_hilbert _ _).mp hg
  have hgv : (P.boundary.stateL v, ev • P.boundary.stateL v) ∈ P.operator.graph := by
    rwa [hv]
  have hz := P.weak_eigen_exists_interior_zero
    (v.val.representative_spec P.boundary.interval_pos).1
    (P.boundary.representative_periodic v).symm
    ((P.operator_eigen_iff_physical v ev).mp hgv) hne
  refine ⟨v.val.representative P.boundary.interval_pos,
    (v.val.representative_spec P.boundary.interval_pos).1,
    (P.boundary.representative_periodic v).symm, ?_, hz⟩
  rw [← hv]
  exact (v.val.representative_spec P.boundary.interval_pos).2.1

end TimeTraps.Analysis
