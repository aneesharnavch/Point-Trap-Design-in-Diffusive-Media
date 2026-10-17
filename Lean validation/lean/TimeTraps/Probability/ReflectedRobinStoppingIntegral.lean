module

public import TimeTraps.Probability.ReflectedRobinStoppingSlice

@[expose] public section

/-! Absolute integrability of the actual signed cost before killing,
on the complete time/path/threshold product, follows from the exact
fixed-time absolute-value identity and actual whole-time survival
integrability. No finite-lifetime assumption is imposed. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {P : ReflectedRobinReactionData ι} {g : ℝ → ℝ}

local instance : IsProbabilityMeasure (exponentialKillingMeasure brownianDyadicMeasure) :=
  exponentialKilling_probability brownianDyadicMeasure

def reflectedRobinCostStoppedExpectation (P : ReflectedRobinReactionData ι) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ p, (∫ r in Ioi (0 : ℝ), reflectedRobinCostStoppedValue P g x r p)
    ∂exponentialKillingMeasure brownianDyadicMeasure

theorem reflectedRobinCostStoppedValue_joint_integrable
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ)
    (hs : IntegrableOn (fun r : ℝ => reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength r.toNNReal) (Ioi (0 : ℝ))) :
    Integrable (Function.uncurry (reflectedRobinCostStoppedValue P g x))
      ((volume.restrict (Ioi (0 : ℝ))).prod (exponentialKillingMeasure brownianDyadicMeasure)) := by
  apply (integrable_prod_iff (reflectedRobinCostStoppedValue_jointly_aestronglyMeasurable hg x)).mpr
  constructor
  · exact Eventually.of_forall (reflectedRobinCostStoppedValue_integrable hg x)
  · apply (reflectedRobinRunningCost_joint_integrable_of_survival P.length P.length_pos P.diffusivity
      P.diffusivity_pos P.site P.strength P.strength_nonneg hg x hs).integral_norm_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (reflectedRobinCostStoppedValue_integral_norm hg x r hr.le).symm

theorem reflectedRobinCostStoppedValue_path_integrable_ae
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ)
    (hs : IntegrableOn (fun r : ℝ => reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength r.toNNReal) (Ioi (0 : ℝ))) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      IntegrableOn (fun r : ℝ => reflectedRobinCostStoppedValue P g x r p) (Ioi (0 : ℝ)) :=
  (reflectedRobinCostStoppedValue_joint_integrable hg x hs).prod_left_ae

theorem reflectedRobinCostStoppedValue_integral_integrable
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ)
    (hs : IntegrableOn (fun r : ℝ => reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength r.toNNReal) (Ioi (0 : ℝ))) :
    Integrable (fun p => ∫ r in Ioi (0 : ℝ), reflectedRobinCostStoppedValue P g x r p)
      (exponentialKillingMeasure brownianDyadicMeasure) :=
  (reflectedRobinCostStoppedValue_joint_integrable hg x hs).integral_prod_right

theorem reflectedRobinCostStoppedExpectation_eq
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ)
    (hs : IntegrableOn (fun r : ℝ => reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength r.toNNReal) (Ioi (0 : ℝ))) :
    reflectedRobinCostStoppedExpectation P g x = reflectedRobinCostExpectation P g x := by
  calc
    _ = ∫ r in Ioi (0 : ℝ), ∫ p, reflectedRobinCostStoppedValue P g x r p
        ∂exponentialKillingMeasure brownianDyadicMeasure :=
      (integral_integral_swap (reflectedRobinCostStoppedValue_joint_integrable hg x hs)).symm
    _ = ∫ r in Ioi (0 : ℝ),
        reflectedAtomicValueExpectation g P.length P.diffusivity x P.site P.strength r.toNNReal := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact reflectedRobinCostStoppedValue_expectation hg x r hr.le
    _ = _ := integral_integral_swap (reflectedRobinRunningCost_joint_integrable_of_survival P.length P.length_pos P.diffusivity
      P.diffusivity_pos P.site P.strength P.strength_nonneg hg x hs)

end TimeTraps.Probability

end
