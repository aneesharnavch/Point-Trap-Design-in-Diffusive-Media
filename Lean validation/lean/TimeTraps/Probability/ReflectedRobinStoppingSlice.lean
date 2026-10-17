module

public import TimeTraps.Probability.ReflectedRobinStoppingData

@[expose] public section

/-! Integrating the independent exponential threshold gives the actual
local-time survival weight, for both signed observations and their
absolute values. These are identities for the literal first-attainment
lifetime at each fixed time. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {P : ReflectedRobinReactionData ι} {g : ℝ → ℝ}

theorem reflectedRobinCostStoppedValue_threshold_ae (P : ReflectedRobinReactionData ι)
    (g : ℝ → ℝ) (x r : ℝ) (hr : 0 ≤ r) :
    reflectedRobinCostStoppedValue P g x r =ᵐ[exponentialKillingMeasure brownianDyadicMeasure]
      (fun p => if reflectedAtomicClock P.length P.diffusivity x P.site P.strength r p.1 < p.2
        then reflectedRobinCostObservation P g x r p.1 else 0) := by
  filter_upwards [reflectedAtomicAttainmentLifetime_survival_iff_ae P.length P.length_pos
    P.diffusivity P.diffusivity_pos x P.site P.strength P.strength_nonneg r hr] with p hp
  rw [reflectedRobinCostStoppedValue_eq P g x r hr p]
  simp only [hp]
  rfl

theorem reflectedRobinCostStoppedValue_expectation
    (hg : ContinuousOn g (Icc 0 P.length)) (x r : ℝ) (hr : 0 ≤ r) :
    (∫ p, reflectedRobinCostStoppedValue P g x r p
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      reflectedAtomicValueExpectation g P.length P.diffusivity x P.site P.strength r.toNNReal := by
  let _ := unitExponential_probability
  have hi : Integrable (fun p : (ℕ → ℝ) × ℝ =>
      if reflectedAtomicClock P.length P.diffusivity x P.site P.strength r p.1 < p.2
      then reflectedRobinCostObservation P g x r p.1 else 0)
      (brownianDyadicMeasure.prod (expMeasure 1)) :=
    (reflectedRobinCostStoppedValue_integrable hg x r).congr
      (reflectedRobinCostStoppedValue_threshold_ae P g x r hr)
  calc
    _ = ∫ p : (ℕ → ℝ) × ℝ,
        (if reflectedAtomicClock P.length P.diffusivity x P.site P.strength r p.1 < p.2
        then reflectedRobinCostObservation P g x r p.1 else 0)
        ∂brownianDyadicMeasure.prod (expMeasure 1) :=
      integral_congr_ae (reflectedRobinCostStoppedValue_threshold_ae P g x r hr)
    _ = ∫ ω, (∫ e,
        (if reflectedAtomicClock P.length P.diffusivity x P.site P.strength r ω < e
        then reflectedRobinCostObservation P g x r ω else 0) ∂expMeasure 1)
        ∂brownianDyadicMeasure := integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro ω
      change (∫ e, (Ioi (reflectedAtomicClock P.length P.diffusivity x P.site P.strength r ω)).indicator
        (fun _ => reflectedRobinCostObservation P g x r ω) e ∂expMeasure 1) = _
      rw [integral_indicator_const _ measurableSet_Ioi, measureReal_def,
        unitExponential_tail _ (reflectedAtomicClock_nonneg P.length P.diffusivity_pos x
          P.site P.strength P.strength_nonneg r ω),
        ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
      rfl

theorem reflectedRobinCostStoppedValue_integral_norm
    (hg : ContinuousOn g (Icc 0 P.length)) (x r : ℝ) (hr : 0 ≤ r) :
    (∫ p, ‖reflectedRobinCostStoppedValue P g x r p‖
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      ∫ ω, ‖reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength r.toNNReal ω‖
        ∂brownianDyadicMeasure := by
  calc
    _ = ∫ p, reflectedRobinCostStoppedValue P (fun z => ‖g z‖) x r p
        ∂exponentialKillingMeasure brownianDyadicMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun _ => norm_indicator_eq_indicator_norm _ _)
    _ = reflectedAtomicValueExpectation (fun z => ‖g z‖)
        P.length P.diffusivity x P.site P.strength r.toNNReal :=
      reflectedRobinCostStoppedValue_expectation hg.norm x r hr
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro ω
      change reflectedAtomicSurvival P.length P.diffusivity x P.site P.strength r.toNNReal ω *
          ‖g (foldedTrajectory P.length P.diffusivity x brownianDyadicPath r.toNNReal ω)‖ =
        ‖reflectedAtomicSurvival P.length P.diffusivity x P.site P.strength r.toNNReal ω *
          g (foldedTrajectory P.length P.diffusivity x brownianDyadicPath r.toNNReal ω)‖
      rw [norm_mul]
      exact congrArg (fun a : ℝ => a *
        ‖g (foldedTrajectory P.length P.diffusivity x brownianDyadicPath r.toNNReal ω)‖)
        (Real.norm_of_nonneg (reflectedAtomicSurvival_bounds P.length P.diffusivity_pos x P.site P.strength
          P.strength_nonneg r.toNNReal ω).1.le).symm

end TimeTraps.Probability
