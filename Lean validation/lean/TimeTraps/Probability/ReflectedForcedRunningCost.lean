module

public import TimeTraps.Probability.ReflectedForcedRunningCostInfinite

@[expose] public section

/-! The actual infinite-horizon expected signed running cost is exactly
the existing physical solution operator applied to the continuous source.
The expectation itself satisfies the full-H1 weak equation. Integrability
and disappearance of the terminal value were proved independently. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ} {P : SpectralProblem n} {g u : ℝ → ℝ}

def reflectedForcedRunningCostExpectation (P : SpectralProblem n) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ ω, (∫ r in Ioi (0 : ℝ),
    reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength r.toNNReal ω)
    ∂brownianDyadicMeasure

theorem reflectedForcedRunningCost_expected_time_infinite (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    (∫ r in Ioi (0 : ℝ),
      reflectedAtomicValueExpectation g P.length P.diffusivity x P.site P.strength r.toNNReal) = u x := by
  have ht : Tendsto (fun T : ℝ≥0 => T.val) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  exact tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0
    (reflectedForcedRunningCost_expectation_integrable hg hx) ht)
    (reflectedForcedRunningCost_expected_time_tendsto hu hg hx)

theorem reflectedForcedRunningCost_expected_infinite (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    reflectedForcedRunningCostExpectation P g x = u x := by
  exact (integral_integral_swap (reflectedForcedRunningCost_joint_integrable hg hx)).symm.trans
    (reflectedForcedRunningCost_expected_time_infinite hu hg hx)

theorem reflectedForcedRunningCost_solution_eqOn (P : SpectralProblem n)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 P.length)) :
    EqOn (reflectedForcedRunningCostExpectation P g) (P.forcedSolutionState g hg) (Icc 0 P.length) := by
  intro x hx
  exact reflectedForcedRunningCost_expected_infinite (P.forcedSolution_weak g hg) hg hx

theorem reflectedForcedRunningCost_weak_equation (P : SpectralProblem n)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 P.length)) :
    WeakForcedEquation P g (reflectedForcedRunningCostExpectation P g) := by
  have hu := P.forcedSolution_weak g hg
  have he := reflectedForcedRunningCost_solution_eqOn P g hg
  refine ⟨hu.energy.congr (by simpa only [uIcc_of_le P.length_pos.le] using he.symm), ?_⟩
  intro v hv
  exact (intervalPointForm_congr P.diffusivity P.strength P.site P.length_pos.le
    (fun i => Ioo_subset_Icc_self (P.site_interior i)) he (fun _ _ => rfl)).trans (hu.weak_form v hv)

theorem reflectedForcedRunningCost_solution_finite (P : SpectralProblem n)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length)
    (T : ℝ≥0) :
    (∫ ω, (∫ r in (0 : ℝ)..T.val,
      reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength r.toNNReal ω)
      ∂brownianDyadicMeasure) =
      P.forcedSolutionState g hg x - reflectedAtomicValueExpectation (P.forcedSolutionState g hg)
        P.length P.diffusivity x P.site P.strength T := by
  simpa only [reflectedFold_eq_self P.length P.length_pos x hx] using
    reflectedForcedRunningCost_expected_finite (P.forcedSolution_weak g hg) hg x T

end TimeTraps.Probability

end
