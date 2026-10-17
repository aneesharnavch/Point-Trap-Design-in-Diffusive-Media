module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentOccupation
public import TimeTraps.Probability.ReversibleResistancePhysicalBandData

@[expose] public section

/-! The bounded Borel reference test for a literal physical occupation
band. Cutting it off to the reference interval leaves the actual path
integral unchanged and makes its interior spatial support explicit. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

noncomputable def resistanceBandReferenceTest (A : IntervalMedium) (a h y : ℝ) : ℝ :=
  (Icc 0 A.resistanceLength).indicator
    (fun y => brownianBandIndicator a h (A.resistanceInverse y) * A.resistanceSpeed y) y

theorem resistanceBandReferenceTest_measurable (A : IntervalMedium) (a h : ℝ) :
    Measurable (resistanceBandReferenceTest A a h) :=
  (((brownianBandIndicator_measurable a h).comp A.resistanceInverse_continuous.measurable).mul
    A.resistanceSpeed_continuous.measurable).indicator measurableSet_Icc

theorem resistanceBandReferenceTest_bound (A : IntervalMedium) (a h : ℝ) :
    ∃ C : ℝ, ∀ y, |resistanceBandReferenceTest A a h y| ≤ C := by
  obtain ⟨C, hC, hb⟩ := reversibleResistanceSpeed_bound A
  refine ⟨C, fun y => ?_⟩
  by_cases hy : y ∈ Icc (0 : ℝ) A.resistanceLength
  · rw [resistanceBandReferenceTest, indicator_of_mem hy, abs_mul]
    exact (mul_le_mul_of_nonneg_right (brownianBandIndicator_abs_le_one a h _) (abs_nonneg _)).trans
      (by simpa only [one_mul] using hb y)
  · simp only [resistanceBandReferenceTest, indicator_of_notMem hy, abs_zero]
    exact hC

theorem resistanceBandReferenceTest_support (A : IntervalMedium) (a h l r : ℝ)
    (hw : ∀ z, |z - a| < h → A.resistance z ∈ Icc l r) :
    ∀ y ∉ Icc l r, resistanceBandReferenceTest A a h y = 0 := by
  intro y hy
  by_cases hy' : y ∈ Icc (0 : ℝ) A.resistanceLength
  · rw [resistanceBandReferenceTest, indicator_of_mem hy', brownianBandIndicator_apply]
    have hn : ¬ |A.resistanceInverse y - a| < h := by
      intro hb
      have he := hw (A.resistanceInverse y) hb
      rw [A.resistance_inverse hy'] at he
      exact hy he
    rw [if_neg hn, zero_mul]
  · exact indicator_of_notMem hy' _

theorem resistanceBandReferenceTest_time_substitution (A : IntervalMedium) (x : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ a h : ℝ, ∀ T : ℝ≥0,
      brownianItoDrift (reversibleResistancePath A x) (brownianBandIndicator a h) T ω =
        brownianItoDrift (reversibleResistanceReference A x) (resistanceBandReferenceTest A a h)
          (reversibleResistanceInversePath A x T ω) ω := by
  filter_upwards [reversibleResistancePath_integral_substitution A x] with ω hω
  intro a h T
  have he := hω (brownianBandIndicator a h) T
  change (∫ t in (0 : ℝ)..T.val,
    brownianBandIndicator a h (reversibleResistancePath A x t.toNNReal ω)) = _
  rw [he]
  apply intervalIntegral.integral_congr
  intro s _
  exact (indicator_of_mem
    (foldedTrajectory_mem A.resistanceLength A.resistanceLength_pos 1 (A.resistance x)
      brownianDyadicPath s.toNNReal ω)
    (fun y => brownianBandIndicator a h (A.resistanceInverse y) * A.resistanceSpeed y)).symm

end TimeTraps.Probability
