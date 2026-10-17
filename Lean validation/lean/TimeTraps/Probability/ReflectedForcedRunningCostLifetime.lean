module

public import TimeTraps.Probability.ReflectedForcedRunningCostStoppingIntegral
public import TimeTraps.Probability.ExtendedLifetimeFiniteMean

@[expose] public section

/-! For every original positive-contact spectral problem, the literal
first-attainment lifetime is almost surely finite and integrable. Its
mean is the existing full-H1 solution with unit source. Finiteness is
derived from the proved survival integral, not stipulated. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ}

theorem reflectedForcedRunningCost_unit_expectation (P : SpectralProblem n)
    (x : ℝ) (T : ℝ≥0) :
    reflectedAtomicValueExpectation (fun _ => 1) P.length P.diffusivity x P.site P.strength T =
      reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength T := by
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => mul_one _)

theorem reflectedForcedRunningCost_unit_survival_integral (P : SpectralProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    IntegrableOn (fun r : ℝ =>
      reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength r.toNNReal) (Ioi (0 : ℝ)) ∧
    (∫ r in Ioi (0 : ℝ), reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength r.toNNReal) =
      P.forcedSolutionState (fun _ => 1) continuousOn_const x := by
  constructor
  · apply (reflectedForcedRunningCost_expectation_integrable
      (P := P) (g := fun _ => 1) continuousOn_const hx).congr
    exact Eventually.of_forall (fun r => reflectedForcedRunningCost_unit_expectation P x r.toNNReal)
  · have he := reflectedForcedRunningCost_expected_time_infinite
      (P.forcedSolution_weak (fun _ => 1) continuousOn_const) continuousOn_const hx
    simpa only [reflectedForcedRunningCost_unit_expectation] using he

theorem reflectedForcedRunningCost_attainment_extended_mean (P : SpectralProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    (∫⁻ p, reflectedAtomicAttainmentLifetimeValue P.length P.diffusivity x P.site P.strength p
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      ENNReal.ofReal (P.forcedSolutionState (fun _ => 1) continuousOn_const x) := by
  rw [reflectedAtomicAttainmentLifetimeValue_mean_survival P.length P.length_pos P.diffusivity
    P.diffusivity_pos x P.site P.strength (fun i => (P.strength_pos i).le)]
  have hi := reflectedForcedRunningCost_unit_survival_integral P hx
  rw [← ofReal_integral_eq_lintegral_ofReal hi.1 (Eventually.of_forall
    (fun r => (reflectedAtomicMeanSurvival_bounds P.length P.diffusivity_pos x P.site P.strength
      (fun i => (P.strength_pos i).le) r.toNNReal).1)), hi.2]

theorem reflectedForcedRunningCost_attainment_lifetime (P : SpectralProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    (∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reflectedAtomicAttainmentLifetimeValue P.length P.diffusivity x P.site P.strength p < ∞) ∧
    Integrable (fun p =>
      (reflectedAtomicAttainmentLifetimeValue P.length P.diffusivity x P.site P.strength p).toReal)
      (exponentialKillingMeasure brownianDyadicMeasure) ∧
    (∫ p, (reflectedAtomicAttainmentLifetimeValue P.length P.diffusivity x P.site P.strength p).toReal
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      P.forcedSolutionState (fun _ => 1) continuousOn_const x := by
  have hn : 0 ≤ P.forcedSolutionState (fun _ => 1) continuousOn_const x := by
    rw [← (reflectedForcedRunningCost_unit_survival_integral P hx).2]
    exact integral_nonneg (fun r =>
      (reflectedAtomicMeanSurvival_bounds P.length P.diffusivity_pos x P.site P.strength
        (fun i => (P.strength_pos i).le) r.toNNReal).1)
  exact extendedLifetime_finite_mean (exponentialKillingMeasure brownianDyadicMeasure)
    (reflectedAtomicAttainmentLifetimeValue P.length P.diffusivity x P.site P.strength)
    (reflectedAtomicAttainmentLifetimeValue_aemeasurable P.length P.length_pos P.diffusivity
      P.diffusivity_pos x P.site P.strength (fun i => (P.strength_pos i).le)) hn
    (reflectedForcedRunningCost_attainment_extended_mean P hx)

theorem reflectedForcedRunningCost_attainment_ne_top (P : SpectralProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reflectedAtomicAttainmentLifetime P.length P.diffusivity x P.site P.strength p ≠ ⊤ := by
  filter_upwards [(reflectedForcedRunningCost_attainment_lifetime P hx).1] with p hp
  intro ht
  change nonnegativeLifetimeValue
    (reflectedAtomicAttainmentLifetime P.length P.diffusivity x P.site P.strength p) < ∞ at hp
  rw [ht, nonnegativeLifetimeValue_top] at hp
  exact (lt_irrefl _) hp

end TimeTraps.Probability
