module

public import TimeTraps.Probability.ReflectedFellerOperator
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Strong continuity of the actual reflected-Gaussian operators, in the
uniform norm on the whole closed interval. A single integrable constant
dominates the continuous-function-valued standard-Gaussian samples. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem reflectedFellerOperator_continuous (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    Continuous (fun v : ℝ≥0 => reflectedFellerOperator L hL v f) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  change Tendsto (fun w : ℝ≥0 => ∫ z, reflectedFellerSample L hL w z f ∂gaussianReal 0 1)
    (𝓝 v) (𝓝 (∫ z, reflectedFellerSample L hL v z f ∂gaussianReal 0 1))
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => ‖f‖)
  · exact Eventually.of_forall (fun w => (reflectedFellerSample_integrable L hL w f).aestronglyMeasurable)
  · exact Eventually.of_forall (fun w => Eventually.of_forall
      (fun z => reflectedFellerSample_norm L hL w z f))
  · exact integrable_const _
  · exact Eventually.of_forall (fun z => ((reflectedFellerSample_continuous L hL f).comp
      (continuous_id.prodMk continuous_const)).tendsto v)

theorem reflectedFellerOperator_tendsto_zero (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    Tendsto (fun v : ℝ≥0 => reflectedFellerOperator L hL v f) (𝓝 0) (𝓝 f) := by
  simpa only [reflectedFellerOperator_zero] using (reflectedFellerOperator_continuous L hL f).tendsto 0

theorem reflectedFellerOperator_uniform_limit (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    Tendsto (fun v : ℝ≥0 => ‖reflectedFellerOperator L hL v f - f‖) (𝓝 0) (𝓝 0) := by
  simpa only [sub_self, norm_zero] using ((reflectedFellerOperator_tendsto_zero L hL f).sub_const f).norm

end TimeTraps.Probability
