module

public import TimeTraps.Probability.ReflectedForcedRunningCostStoppingSlice

@[expose] public section

/-! Absolute integrability of the actual signed cost before killing,
on the complete time/path/threshold product, follows from the exact
fixed-time absolute-value identity and the proved survival decay.
The resulting expectation is the original full-H1 forced solution. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ} {P : SpectralProblem n} {g u : ℝ → ℝ}

local instance : IsProbabilityMeasure (exponentialKillingMeasure brownianDyadicMeasure) :=
  exponentialKilling_probability brownianDyadicMeasure

def reflectedForcedRunningCostStoppedExpectation (P : SpectralProblem n) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ p, (∫ r in Ioi (0 : ℝ), reflectedForcedRunningCostStoppedValue P g x r p)
    ∂exponentialKillingMeasure brownianDyadicMeasure

theorem reflectedForcedRunningCostStoppedValue_joint_integrable
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    Integrable (Function.uncurry (reflectedForcedRunningCostStoppedValue P g x))
      ((volume.restrict (Ioi (0 : ℝ))).prod (exponentialKillingMeasure brownianDyadicMeasure)) := by
  apply (integrable_prod_iff (reflectedForcedRunningCostStoppedValue_jointly_aestronglyMeasurable hg x)).mpr
  constructor
  · exact Eventually.of_forall (reflectedForcedRunningCostStoppedValue_integrable hg x)
  · apply (reflectedForcedRunningCost_joint_integrable hg hx).integral_norm_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (reflectedForcedRunningCostStoppedValue_integral_norm hg x r hr.le).symm

theorem reflectedForcedRunningCostStoppedValue_path_integrable_ae
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      IntegrableOn (fun r : ℝ => reflectedForcedRunningCostStoppedValue P g x r p) (Ioi (0 : ℝ)) :=
  (reflectedForcedRunningCostStoppedValue_joint_integrable hg hx).prod_left_ae

theorem reflectedForcedRunningCostStoppedValue_integral_integrable
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    Integrable (fun p => ∫ r in Ioi (0 : ℝ), reflectedForcedRunningCostStoppedValue P g x r p)
      (exponentialKillingMeasure brownianDyadicMeasure) :=
  (reflectedForcedRunningCostStoppedValue_joint_integrable hg hx).integral_prod_right

theorem reflectedForcedRunningCostStoppedExpectation_eq
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    reflectedForcedRunningCostStoppedExpectation P g x = reflectedForcedRunningCostExpectation P g x := by
  calc
    _ = ∫ r in Ioi (0 : ℝ), ∫ p, reflectedForcedRunningCostStoppedValue P g x r p
        ∂exponentialKillingMeasure brownianDyadicMeasure :=
      (integral_integral_swap (reflectedForcedRunningCostStoppedValue_joint_integrable hg hx)).symm
    _ = ∫ r in Ioi (0 : ℝ),
        reflectedAtomicValueExpectation g P.length P.diffusivity x P.site P.strength r.toNNReal := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact reflectedForcedRunningCostStoppedValue_expectation hg x r hr.le
    _ = _ := integral_integral_swap (reflectedForcedRunningCost_joint_integrable hg hx)

theorem reflectedForcedRunningCostStoppedExpectation_solution_eqOn (P : SpectralProblem n)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 P.length)) :
    EqOn (reflectedForcedRunningCostStoppedExpectation P g)
      (P.forcedSolutionState g hg) (Icc 0 P.length) := by
  intro x hx
  exact (reflectedForcedRunningCostStoppedExpectation_eq hg hx).trans
    (reflectedForcedRunningCost_solution_eqOn P g hg hx)

theorem reflectedForcedRunningCostStoppedExpectation_weak_equation (P : SpectralProblem n)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 P.length)) :
    WeakForcedEquation P g (reflectedForcedRunningCostStoppedExpectation P g) := by
  have hu := P.forcedSolution_weak g hg
  have he := reflectedForcedRunningCostStoppedExpectation_solution_eqOn P g hg
  refine ⟨hu.energy.congr (by simpa only [uIcc_of_le P.length_pos.le] using he.symm), ?_⟩
  intro v hv
  exact (intervalPointForm_congr P.diffusivity P.strength P.site P.length_pos.le
    (fun i => Ioo_subset_Icc_self (P.site_interior i)) he (fun _ _ => rfl)).trans (hu.weak_form v hv)

end TimeTraps.Probability

end
