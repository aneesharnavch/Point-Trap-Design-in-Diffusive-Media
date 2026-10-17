module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzTransition
public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzBandBound

@[expose] public section

/-! The band expectation is the actual transition integrated over time.
Boundedness supplies the product integrability before the Fubini exchange. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistanceBand_time_product_integrable (A : IntervalMedium) (x a h : ℝ) (T : ℝ≥0) :
    Integrable (fun p : ℝ × (ℕ → ℝ) =>
      brownianBandIndicator a h (reversibleResistancePath A x p.1.toNNReal p.2))
      ((volume.restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) := by
  have hm := (brownianBandIndicator_measurable a h).comp
    ((reversibleResistancePath_jointlyMeasurable A x).comp
      (measurable_fst.real_toNNReal.prodMk measurable_snd))
  apply (integrable_const 1).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall (fun p => brownianBandIndicator_abs_le_one a h _)

theorem reversibleResistancePhysicalOccupationBand_mean_time (A : IntervalMedium) (x a h : ℝ) (T : ℝ≥0) :
    (∫ ω, reversibleResistancePhysicalOccupationBand A x a h T ω ∂brownianDyadicMeasure) =
      (∫ s in (0 : ℝ)..T.val, reversibleResistanceTransition A s.toNNReal (brownianBandIndicator a h) x) /
        resistancePhysicalBandMass A a h := by
  change (∫ ω, brownianItoDrift (reversibleResistancePath A x) (brownianBandIndicator a h) T ω /
    resistancePhysicalBandMass A a h ∂brownianDyadicMeasure) = _
  rw [integral_div]
  congr 1
  calc
    _ = ∫ ω, (∫ s in Ioc (0 : ℝ) T.val,
        brownianBandIndicator a h (reversibleResistancePath A x s.toNNReal ω)) ∂brownianDyadicMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => intervalIntegral.integral_of_le T.coe_nonneg)
    _ = ∫ s in Ioc (0 : ℝ) T.val, (∫ ω,
        brownianBandIndicator a h (reversibleResistancePath A x s.toNNReal ω) ∂brownianDyadicMeasure) :=
      (integral_integral_swap (reversibleResistanceBand_time_product_integrable A x a h T)).symm
    _ = ∫ s in Ioc (0 : ℝ) T.val,
        reversibleResistanceTransition A s.toNNReal (brownianBandIndicator a h) x := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun s =>
        (reversibleResistanceTransition_original A s.toNNReal (brownianBandIndicator_measurable a h) x).symm)
    _ = _ := (intervalIntegral.integral_of_le T.coe_nonneg).symm

noncomputable def resistanceRealTimeClip (T : ℝ≥0) (s : ℝ) : BrownianCompactTime T :=
  ⟨min s.toNNReal T, zero_le, min_le_right _ _⟩

theorem resistanceRealTimeClip_measurable (T : ℝ≥0) : Measurable (resistanceRealTimeClip T) :=
  (measurable_id.real_toNNReal.min measurable_const).subtype_mk

theorem resistanceRealTimeClip_of_mem (T : ℝ≥0) {s : ℝ} (hs : s ∈ Icc 0 T.val) :
    (resistanceRealTimeClip T s).val = s.toNNReal := by
  change min s.toNNReal T = s.toNNReal
  apply min_eq_left
  exact (Real.toNNReal_le_iff_le_coe).mpr hs.2

end TimeTraps.Probability
