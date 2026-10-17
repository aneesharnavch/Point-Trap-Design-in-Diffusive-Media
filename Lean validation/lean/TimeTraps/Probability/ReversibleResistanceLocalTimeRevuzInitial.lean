module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzState

@[expose] public section

/-! Actual fixed-site and band expectations may be integrated against
every continuous initial weight. The common clock cap gives the uniform
bound needed to pass the full band-radius limit under that integral. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistanceLocalTime_initial_integrable (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) (T : ℝ≥0) (w : C(Icc A.source.left A.source.right, ℝ)) :
    Integrable (fun x => w x * ∫ ω, reversibleResistanceLocalTime A x.val a.val T ω ∂brownianDyadicMeasure)
      (reversibleResistanceLengthMeasure A) := by
  obtain ⟨S, hS⟩ := reversibleResistanceInversePath_bounded_all_starts A T
  apply (integrable_const (‖w‖ * resistanceRevuzMeanBound A S)).mono'
    ((w.continuous.measurable.mul (reversibleResistanceLocalTime_mean_measurable A a T)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  change ‖w x * (∫ ω, reversibleResistanceLocalTime A x.val a.val T ω ∂brownianDyadicMeasure)‖ ≤ _
  rw [norm_mul, Real.norm_of_nonneg (integral_nonneg
    (fun ω => reversibleResistanceLocalTime_nonneg A x.val a.val T ω))]
  exact mul_le_mul (w.norm_coe_le_norm x) (reversibleResistanceLocalTime_mean_bound A x.val a.val T S (hS x.val))
    (integral_nonneg (fun ω => reversibleResistanceLocalTime_nonneg A x.val a.val T ω)) (norm_nonneg w)

theorem reversibleResistancePhysicalOccupationBand_initial_tendsto (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) (T : ℝ≥0) (w : C(Icc A.source.left A.source.right, ℝ)) :
    Tendsto (fun h : ℝ => ∫ x, w x *
      (∫ ω, reversibleResistancePhysicalOccupationBand A x.val a.val h T ω ∂brownianDyadicMeasure)
        ∂reversibleResistanceLengthMeasure A) (𝓝[>] 0)
      (𝓝 (∫ x, w x * (∫ ω, reversibleResistanceLocalTime A x.val a.val T ω ∂brownianDyadicMeasure)
        ∂reversibleResistanceLengthMeasure A)) := by
  obtain ⟨S, hS⟩ := reversibleResistanceInversePath_bounded_all_starts A T
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => ‖w‖ * resistanceRevuzMeanBound A S)
  · exact Eventually.of_forall (fun h =>
      (w.continuous.measurable.mul (reversibleResistancePhysicalOccupationBand_mean_measurable A a.val h T)).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    apply Eventually.of_forall
    intro x
    rw [norm_mul, Real.norm_of_nonneg (reversibleResistancePhysicalOccupationBand_mean_nonneg A x.val a.val hh T)]
    exact mul_le_mul (w.norm_coe_le_norm x)
      (reversibleResistancePhysicalOccupationBand_mean_bound A x.val a.val hh T S (hS x.val))
      (reversibleResistancePhysicalOccupationBand_mean_nonneg A x.val a.val hh T) (norm_nonneg w)
  · exact integrable_const _
  · exact Eventually.of_forall (fun x =>
      (reversibleResistancePhysicalOccupationBand_mean_tendsto A x.val a T).const_mul (w x))

end TimeTraps.Probability
