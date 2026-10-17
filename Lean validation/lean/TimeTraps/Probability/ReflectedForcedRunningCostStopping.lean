module

public import TimeTraps.Probability.ReflectedForcedRunningCostStoppingIntegral

@[expose] public section

/-! Finite and infinite expected running costs stopped at the paper's
literal first-attainment lifetime. The final integral is over precisely
the physical times before that lifetime, including the infinite-lifetime
case. The source may have either sign. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ} {P : SpectralProblem n} {g u : ℝ → ℝ}

local instance : IsProbabilityMeasure (exponentialKillingMeasure brownianDyadicMeasure) :=
  exponentialKilling_probability brownianDyadicMeasure

theorem reflectedForcedRunningCostStoppedValue_path_integral (P : SpectralProblem n)
    (g : ℝ → ℝ) (x : ℝ) (p : (ℕ → ℝ) × ℝ) :
    (∫ r in Ioi (0 : ℝ), reflectedForcedRunningCostStoppedValue P g x r p) =
      ∫ r in {r : ℝ | 0 < r ∧ (r : WithTop ℝ) <
        reflectedAtomicAttainmentLifetime P.length P.diffusivity x P.site P.strength p},
        g (foldedTrajectory P.length P.diffusivity x brownianDyadicPath r.toNNReal p.1) := by
  have hm (t : WithTop ℝ) : MeasurableSet {r : ℝ | (r : WithTop ℝ) < t} := by
    induction t using WithTop.recTopCoe with
    | top => simpa only [WithTop.coe_lt_top, ofPred_true] using MeasurableSet.univ
    | coe t =>
      have he : {r : ℝ | (r : WithTop ℝ) < (t : WithTop ℝ)} = Iio t :=
        Set.ext (fun _ => WithTop.coe_lt_coe)
      rw [he]
      exact measurableSet_Iio
  calc
    _ = ∫ r in Ioi (0 : ℝ),
        {s : ℝ | (s : WithTop ℝ) < reflectedAtomicAttainmentLifetime
          P.length P.diffusivity x P.site P.strength p}.indicator
          (fun s => g (foldedTrajectory P.length P.diffusivity x brownianDyadicPath s.toNNReal p.1)) r := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      convert! reflectedForcedRunningCostStoppedValue_eq P g x r hr.le p using 1
      simp only [indicator_apply, mem_ofPred_eq]
    _ = _ := by
      rw [integral_indicator (hm _), Measure.restrict_restrict (hm _)]
      have he : {r : ℝ | (r : WithTop ℝ) < reflectedAtomicAttainmentLifetime
          P.length P.diffusivity x P.site P.strength p} ∩ Ioi 0 =
          {r : ℝ | 0 < r ∧ (r : WithTop ℝ) < reflectedAtomicAttainmentLifetime
            P.length P.diffusivity x P.site P.strength p} :=
        Set.ext (fun _ => and_comm)
      rw [he]

theorem reflectedForcedRunningCostStoppedValue_time_joint_integrable
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) (T : ℝ≥0) :
    Integrable (Function.uncurry (reflectedForcedRunningCostStoppedValue P g x))
      ((volume.restrict (Ioc (0 : ℝ) T.val)).prod (exponentialKillingMeasure brownianDyadicMeasure)) :=
  (reflectedForcedRunningCostStoppedValue_joint_integrable hg hx).mono_measure
    (Measure.prod_mono (Measure.restrict_mono_set volume (fun _ hr => hr.1)) le_rfl)

theorem reflectedForcedRunningCostStoppedValue_expected_finite (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) (T : ℝ≥0) :
    (∫ p, (∫ r in (0 : ℝ)..T.val, reflectedForcedRunningCostStoppedValue P g x r p)
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      u x - reflectedAtomicValueExpectation u P.length P.diffusivity x P.site P.strength T := by
  calc
    _ = ∫ p, (∫ r in Ioc (0 : ℝ) T.val, reflectedForcedRunningCostStoppedValue P g x r p)
        ∂exponentialKillingMeasure brownianDyadicMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun _ => intervalIntegral.integral_of_le T.coe_nonneg)
    _ = ∫ r in Ioc (0 : ℝ) T.val, ∫ p, reflectedForcedRunningCostStoppedValue P g x r p
        ∂exponentialKillingMeasure brownianDyadicMeasure :=
      (integral_integral_swap (reflectedForcedRunningCostStoppedValue_time_joint_integrable hg hx T)).symm
    _ = ∫ r in Ioc (0 : ℝ) T.val,
        reflectedAtomicValueExpectation g P.length P.diffusivity x P.site P.strength r.toNNReal := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact reflectedForcedRunningCostStoppedValue_expectation hg x r hr.1.le
    _ = ∫ r in (0 : ℝ)..T.val,
        reflectedAtomicValueExpectation g P.length P.diffusivity x P.site P.strength r.toNNReal :=
      (intervalIntegral.integral_of_le T.coe_nonneg).symm
    _ = _ := by
      simpa only [reflectedFold_eq_self P.length P.length_pos x hx] using
        reflectedForcedRunningCost_expected_time_finite hu hg x T

theorem reflectedForcedRunningCostStoppedValue_path_cost_integrable
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    Integrable (fun p => ∫ r in {r : ℝ | 0 < r ∧ (r : WithTop ℝ) <
      reflectedAtomicAttainmentLifetime P.length P.diffusivity x P.site P.strength p},
        g (foldedTrajectory P.length P.diffusivity x brownianDyadicPath r.toNNReal p.1))
      (exponentialKillingMeasure brownianDyadicMeasure) := by
  apply (reflectedForcedRunningCostStoppedValue_integral_integrable hg hx).congr
  exact Eventually.of_forall (reflectedForcedRunningCostStoppedValue_path_integral P g x)

theorem reflectedForcedRunningCostStoppedValue_expected_infinite (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    (∫ p, (∫ r in {r : ℝ | 0 < r ∧ (r : WithTop ℝ) <
      reflectedAtomicAttainmentLifetime P.length P.diffusivity x P.site P.strength p},
        g (foldedTrajectory P.length P.diffusivity x brownianDyadicPath r.toNNReal p.1))
      ∂exponentialKillingMeasure brownianDyadicMeasure) = u x := by
  have he := integral_congr_ae (μ := exponentialKillingMeasure brownianDyadicMeasure) (Eventually.of_forall
    (reflectedForcedRunningCostStoppedValue_path_integral P g x))
  exact he.symm.trans ((reflectedForcedRunningCostStoppedExpectation_eq hg hx).trans
    (reflectedForcedRunningCost_expected_infinite hu hg hx))

end TimeTraps.Probability
