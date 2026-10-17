module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzTime
public import TimeTraps.Probability.ContinuousPathLocalTimeData
public import TimeTraps.Probability.ReversibleResistancePairingData

@[expose] public section

/-! Measurable dependence of actual band and local-time means on the
initial state. No joint initial-state/sample version of local time is
assumed: its mean is the pointwise limit of genuine band means. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistancePhysicalOccupationBand_mean_measurable (A : IntervalMedium) (a h : ℝ) (T : ℝ≥0) :
    Measurable (fun x : Icc A.source.left A.source.right =>
      ∫ ω, reversibleResistancePhysicalOccupationBand A x.val a h T ω ∂brownianDyadicMeasure) := by
  let F : Icc A.source.left A.source.right × ℝ → ℝ := fun q =>
    reversibleResistanceTransition A (resistanceRealTimeClip T q.2).val (brownianBandIndicator a h) q.1.val
  let Q : Icc A.source.left A.source.right × ℝ →
      BrownianCompactTime T × Icc A.source.left A.source.right :=
    fun q => (resistanceRealTimeClip T q.2, q.1)
  have hQ : Measurable Q := ((resistanceRealTimeClip_measurable T).comp measurable_snd).prodMk measurable_fst
  have hF := (reversibleResistanceTransition_compact_jointlyMeasurable_borel A T
    (brownianBandIndicator_measurable a h)).comp hQ
  change Measurable F at hF
  have hm : Measurable (fun x => (∫ s in Ioc (0 : ℝ) T.val, F (x, s)) / resistancePhysicalBandMass A a h) :=
    hF.stronglyMeasurable.integral_prod_right'.measurable.div_const _
  have he : (fun x : Icc A.source.left A.source.right =>
      ∫ ω, reversibleResistancePhysicalOccupationBand A x.val a h T ω ∂brownianDyadicMeasure) =
      (fun x => (∫ s in Ioc (0 : ℝ) T.val, F (x, s)) / resistancePhysicalBandMass A a h) := by
    funext x
    rw [reversibleResistancePhysicalOccupationBand_mean_time A x.val a h T]
    congr 1
    calc
      _ = ∫ s in Ioc (0 : ℝ) T.val,
          reversibleResistanceTransition A s.toNNReal (brownianBandIndicator a h) x.val :=
        intervalIntegral.integral_of_le T.coe_nonneg
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro s hs
        dsimp only [F]
        rw [resistanceRealTimeClip_of_mem T ⟨hs.1.le, hs.2⟩]
  exact he.symm ▸ hm

theorem reversibleResistanceLocalTime_mean_measurable (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) (T : ℝ≥0) :
    Measurable (fun x : Icc A.source.left A.source.right =>
      ∫ ω, reversibleResistanceLocalTime A x.val a.val T ω ∂brownianDyadicMeasure) := by
  apply measurable_of_tendsto_metrizable
    (fun n => reversibleResistancePhysicalOccupationBand_mean_measurable A a.val (occupationBandRadius n) T)
  apply tendsto_pi_nhds.mpr
  intro x
  exact (reversibleResistancePhysicalOccupationBand_mean_tendsto A x.val a T).comp occupationBandRadius_tendsto

end TimeTraps.Probability
