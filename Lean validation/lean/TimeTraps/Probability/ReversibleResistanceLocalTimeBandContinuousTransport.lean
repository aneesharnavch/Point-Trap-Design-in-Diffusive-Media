module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeBandContinuousTest
public import TimeTraps.Probability.ReversibleResistanceLocalTimeBandContinuousAverage

@[expose] public section

/-! Exact transport of the supported reference test to the physical
speed-weighted band integral. The conductance cancels by the proved
resistance-coordinate substitution, without differentiating it. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

theorem resistanceBandReferenceTest_integral_transport (A : IntervalMedium) (a h : ℝ)
    (hband : Ioo (a - h) (a + h) ⊆ Ioo A.source.left A.source.right) (w : ℝ → ℝ) :
    (∫ y, resistanceBandReferenceTest A a h y * w y) =
      ∫ z in Ioo (a - h) (a + h), A.source.density z * w (A.resistance z) := by
  have he : (fun y => resistanceBandReferenceTest A a h y * w y) =
      (Icc 0 A.resistanceLength).indicator (fun y =>
        brownianBandIndicator a h (A.resistanceInverse y) * A.resistanceSpeed y * w y) := by
    funext y
    by_cases hy : y ∈ Icc (0 : ℝ) A.resistanceLength
    · simp only [resistanceBandReferenceTest, indicator_of_mem hy]
    · simp only [resistanceBandReferenceTest, indicator_of_notMem hy, zero_mul]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le A.resistanceLength_pos.le,
    ← A.resistance_density_transport (brownianBandIndicator a h) w,
    intervalIntegral.integral_of_le A.source.increasing.le, integral_Ioc_eq_integral_Ioo,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      have hn : z ∉ Ioo (a - h) (a + h) := fun h => hz (hband h)
      simp only [brownianBandIndicator, indicator_of_notMem hn, zero_mul])]
  have he' : (fun z => brownianBandIndicator a h z * A.source.density z * w (A.resistance z)) =
      (Ioo (a - h) (a + h)).indicator (fun z => A.source.density z * w (A.resistance z)) := by
    funext z
    by_cases hz : z ∈ Ioo (a - h) (a + h)
    · simp only [brownianBandIndicator, indicator_of_mem hz, one_mul]
    · simp only [brownianBandIndicator, indicator_of_notMem hz, zero_mul]
  rw [he', integral_indicator measurableSet_Ioo]

theorem resistanceBandReferenceTest_window_integral (A : IntervalMedium) (a h l r : ℝ)
    (hw : ∀ z, |z - a| < h → A.resistance z ∈ Icc l r)
    (hband : Ioo (a - h) (a + h) ⊆ Ioo A.source.left A.source.right) (w : ℝ → ℝ) :
    (∫ y in Icc l r, resistanceBandReferenceTest A a h y * w y) =
      ∫ z in Ioo (a - h) (a + h), A.source.density z * w (A.resistance z) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    rw [resistanceBandReferenceTest_support A a h l r hw y hy, zero_mul])]
  exact resistanceBandReferenceTest_integral_transport A a h hband w

theorem resistancePhysicalWeightedAverage_apply (A : IntervalMedium) (S : ℝ≥0)
    {V : ℝ → C(BrownianCompactTime S, ℝ)} (hV : Continuous V) (a : ℝ) {h : ℝ} (hh : 0 < h)
    (hband : Ioo (a - h) (a + h) ⊆ Icc A.source.left A.source.right) (t : BrownianCompactTime S) :
    resistancePhysicalWeightedAverage A V a h t =
      (∫ z in Ioo (a - h) (a + h), A.source.density z * V (A.resistance z) t) /
        resistancePhysicalBandMass A a h := by
  have hi : IntervalIntegrable
      (fun z => resistancePhysicalDensity A z • V (resistancePhysicalCoordinate A z))
      volume (a - h) (a + h) :=
    (resistancePhysicalWeightedIntegrand_continuous A hV).intervalIntegrable (a - h) (a + h)
  have he := (ContinuousMap.evalCLM ℝ t).intervalIntegral_comp_comm hi
  change (∫ z in (a - h)..(a + h),
    resistancePhysicalDensity A z * V (resistancePhysicalCoordinate A z) t) =
    (∫ z in (a - h)..(a + h), resistancePhysicalDensity A z • V (resistancePhysicalCoordinate A z)) t at he
  change (resistancePhysicalBandMass A a h)⁻¹ *
    ((∫ z in (a - h)..(a + h), resistancePhysicalDensity A z • V (resistancePhysicalCoordinate A z)) t) = _
  rw [← he]
  rw [intervalIntegral.integral_of_le (by linarith : a - h ≤ a + h), integral_Ioc_eq_integral_Ioo]
  have hc : (∫ z in Ioo (a - h) (a + h), resistancePhysicalDensity A z * V (resistancePhysicalCoordinate A z) t) =
      ∫ z in Ioo (a - h) (a + h), A.source.density z * V (A.resistance z) t := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro z hz
    dsimp only
    rw [resistancePhysicalDensity_eq A (hband hz), resistancePhysicalCoordinate_eq A (hband hz)]
  rw [hc, div_eq_mul_inv, mul_comm]

end TimeTraps.Probability
