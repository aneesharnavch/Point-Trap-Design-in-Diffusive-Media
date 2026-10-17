module

public import TimeTraps.Probability.ReflectedFiniteKinkEigenExpectation
public import TimeTraps.Spectral.ReflectedEigenstateKinkOperator

@[expose] public section

/-! The actual killed expectation evolves every original physical weak
eigenstate by its exponential eigenvalue factor. Spatial regularity,
reaction and reflection conditions are derived from the full weak
equation. No global regularity outside the physical interval is needed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ} {P : SpectralProblem n} {ev : ℝ} {u : ℝ → ℝ}

theorem reflectedWeakEigenstate_weighted_memLp (hu : WeakEigenEquation P ev u)
    (x : ℝ) (T : ℝ≥0) :
    MemLp (reflectedAtomicWeightedValue u P.length P.diffusivity x P.site P.strength T)
      2 brownianDyadicMeasure := by
  have hc := finiteKinkPotential_continuous hu.kinkBase_contDiff.continuous
    Finset.univ P.site hu.kinkCoefficient
  apply (reflectedAtomicWeightedValue_memLp hc P.length P.length_pos P.diffusivity P.diffusivity_pos
    x P.site P.strength (fun i => (P.strength_pos i).le) T).ae_eq
  exact Eventually.of_forall (fun ω => congrArg
    (fun z : ℝ => reflectedAtomicSurvival P.length P.diffusivity x P.site P.strength T ω * z)
    (hu.kinkPotential_eq (foldedTrajectory_mem P.length P.length_pos P.diffusivity x brownianDyadicPath T ω)))

theorem reflectedWeakEigenstate_expectation (hu : WeakEigenEquation P ev u)
    (x : ℝ) (T : ℝ≥0) :
    reflectedAtomicValueExpectation u P.length P.diffusivity x P.site P.strength T =
      Real.exp (-ev * T.val) * u (reflectedFold P.length x) := by
  have hsource (z : ℝ) (hz : z ∈ Icc 0 P.length) :
      P.diffusivity * deriv (deriv hu.kinkBase) z = -ev * hu.kinkPotential z := by
    rw [hu.kinkBase_curvature_potential hz]
    field_simp [ne_of_gt P.diffusivity_pos]
  have he := reflectedFiniteKinkC2_eigen_expectation hu.kinkBase_contDiff
    P.length P.length_pos P.diffusivity P.diffusivity_pos P.site hu.kinkCoefficient P.strength
    P.site_interior (fun i => (P.strength_pos i).le) x ev T
    hu.kinkSlope_endpoints.1 hu.kinkSlope_endpoints.2 hu.kinkPotential_reaction hsource
  have hv : reflectedAtomicValueExpectation hu.kinkPotential P.length P.diffusivity x P.site P.strength T =
      reflectedAtomicValueExpectation u P.length P.diffusivity x P.site P.strength T := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => congrArg
      (fun z : ℝ => reflectedAtomicSurvival P.length P.diffusivity x P.site P.strength T ω * z)
      (hu.kinkPotential_eq (foldedTrajectory_mem P.length P.length_pos P.diffusivity x brownianDyadicPath T ω)))
  calc
    _ = reflectedAtomicValueExpectation hu.kinkPotential P.length P.diffusivity x P.site P.strength T := hv.symm
    _ = Real.exp (-ev * T.val) * hu.kinkPotential (reflectedFold P.length x) := he
    _ = _ := congrArg (fun z : ℝ => Real.exp (-ev * T.val) * z)
      (hu.kinkPotential_eq (reflectedFold_mem P.length P.length_pos x))

theorem reflectedWeakEigenstate_expectation_at_start (hu : WeakEigenEquation P ev u)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) (T : ℝ≥0) :
    reflectedAtomicValueExpectation u P.length P.diffusivity x P.site P.strength T =
      Real.exp (-ev * T.val) * u x := by
  simpa only [reflectedFold_eq_self P.length P.length_pos x hx] using
    reflectedWeakEigenstate_expectation hu x T

theorem reflectedIntervalEigenstate_expectation (P : SpectralProblem n)
    (i : CompactSpectralIndex P.intervalPointProblem.inverse) (x : ℝ) (T : ℝ≥0) :
    reflectedAtomicValueExpectation ((P.intervalPointProblem.eigenstate i).representative P.length_pos)
      P.length P.diffusivity x P.site P.strength T =
      Real.exp (-i.1⁻¹ * T.val) *
        (P.intervalPointProblem.eigenstate i).representative P.length_pos (reflectedFold P.length x) :=
  reflectedWeakEigenstate_expectation (P.interval_eigenbasis_weak i) x T

end TimeTraps.Probability
