module

public import TimeTraps.Probability.ReflectedRobinStoppingIntegral

@[expose] public section

/-! Literal cost on the full pre-attainment interval, including infinite
lifetimes. Its ordinary expectation equals the actual weighted cost;
absolute integrability was derived from whole-time survival. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {P : ReflectedRobinReactionData ι} {g : ℝ → ℝ}

theorem reflectedRobinCostStoppedValue_path_integral (P : ReflectedRobinReactionData ι)
    (g : ℝ → ℝ) (x : ℝ) (p : (ℕ → ℝ) × ℝ) :
    (∫ r in Ioi (0 : ℝ), reflectedRobinCostStoppedValue P g x r p) =
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
      convert! reflectedRobinCostStoppedValue_eq P g x r hr.le p using 1
      simp only [indicator_apply, mem_ofPred_eq]
    _ = _ := by
      rw [integral_indicator (hm _), Measure.restrict_restrict (hm _)]
      have he : {r : ℝ | (r : WithTop ℝ) < reflectedAtomicAttainmentLifetime
          P.length P.diffusivity x P.site P.strength p} ∩ Ioi 0 =
          {r : ℝ | 0 < r ∧ (r : WithTop ℝ) < reflectedAtomicAttainmentLifetime
            P.length P.diffusivity x P.site P.strength p} :=
        Set.ext (fun _ => and_comm)
      rw [he]

theorem reflectedRobinCostStoppedValue_path_cost_integrable
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ)
    (hs : IntegrableOn (fun r : ℝ => reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength r.toNNReal) (Ioi (0 : ℝ))) :
    Integrable (fun p => ∫ r in {r : ℝ | 0 < r ∧ (r : WithTop ℝ) <
      reflectedAtomicAttainmentLifetime P.length P.diffusivity x P.site P.strength p},
      g (foldedTrajectory P.length P.diffusivity x brownianDyadicPath r.toNNReal p.1))
      (exponentialKillingMeasure brownianDyadicMeasure) := by
  apply (reflectedRobinCostStoppedValue_integral_integrable hg x hs).congr
  exact Eventually.of_forall (reflectedRobinCostStoppedValue_path_integral P g x)

theorem reflectedRobinCostStoppedValue_expected_infinite
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ)
    (hs : IntegrableOn (fun r : ℝ => reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength r.toNNReal) (Ioi (0 : ℝ))) :
    (∫ p, (∫ r in {r : ℝ | 0 < r ∧ (r : WithTop ℝ) <
      reflectedAtomicAttainmentLifetime P.length P.diffusivity x P.site P.strength p},
      g (foldedTrajectory P.length P.diffusivity x brownianDyadicPath r.toNNReal p.1))
      ∂exponentialKillingMeasure brownianDyadicMeasure) = reflectedRobinCostExpectation P g x := by
  exact (integral_congr_ae (Eventually.of_forall
    (reflectedRobinCostStoppedValue_path_integral P g x))).symm.trans
      (reflectedRobinCostStoppedExpectation_eq hg x hs)

end TimeTraps.Probability
