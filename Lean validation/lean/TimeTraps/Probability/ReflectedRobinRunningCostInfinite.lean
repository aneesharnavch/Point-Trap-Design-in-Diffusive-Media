module

public import TimeTraps.Probability.ReflectedRobinWeakTail

@[expose] public section

/-! Whole-time absolute integrability follows from the actual integrable
survival and compact test bounds. These helpers apply to signed tests;
the weak equation supplies survival finiteness separately. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {g : ℝ → ℝ}

theorem reflectedRobinRunningCost_joint_integrable_of_survival
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hg : ContinuousOn g (Icc 0 L)) (x : ℝ)
    (hs : IntegrableOn (fun r : ℝ => reflectedAtomicMeanSurvival L D x a κ r.toNNReal) (Ioi (0 : ℝ))) :
    Integrable (fun p : ℝ × (ℕ → ℝ) => reflectedAtomicWeightedValue g L D x a κ p.1.toNNReal p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod brownianDyadicMeasure) := by
  have hm := ((reflectedRobinRunningCost_jointlyMeasurable L hL D hD a κ hκ hg x).comp
    (measurable_fst.real_toNNReal.prodMk measurable_snd)).aestronglyMeasurable
      (μ := (volume.restrict (Ioi (0 : ℝ))).prod brownianDyadicMeasure)
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Eventually.of_forall (fun r =>
      (reflectedRobinRunningCost_memLp L hL D hD a κ hκ hg x r.toNNReal).integrable (by norm_num))
  · apply (hs.const_mul ‖reflectedRobinKinkSource L g hg‖).mono' hm.norm.integral_prod_right'
    filter_upwards [] with r
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact reflectedRobinRunningCost_integral_norm_le L hL D hD a κ hκ hg x r.toNNReal

theorem reflectedRobinRunningCost_expectation_tendsto_of_survival
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hg : ContinuousOn g (Icc 0 L)) (x : ℝ)
    (hs : Tendsto (reflectedAtomicMeanSurvival L D x a κ) atTop (𝓝 0)) :
    Tendsto (reflectedAtomicValueExpectation g L D x a κ) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun T => ?_))
    (by simpa only [mul_zero] using hs.const_mul ‖reflectedRobinKinkSource L g hg‖)
  exact (norm_integral_le_integral_norm _).trans
    (reflectedRobinRunningCost_integral_norm_le L hL D hD a κ hκ hg x T)

end TimeTraps.Probability
