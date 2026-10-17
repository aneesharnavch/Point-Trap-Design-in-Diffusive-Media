module

public import TimeTraps.Probability.ReflectedInteriorOccupationConditionalKernel

@[expose] public section

/-! An explicit bound, uniform in the starting state and interior level,
for the time-integrated actual reflected Gaussian kernel. It follows from
the proved single-kink test identity and compact interval bounds. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedInteriorOccupationTest_bounds (L : ℝ) (hL : 0 < L) {a z : ℝ}
    (ha : a ∈ Icc 0 L) (hz : z ∈ Icc 0 L) :
    0 ≤ reflectedInteriorOccupationTest L a z ∧ reflectedInteriorOccupationTest L a z ≤ 2 * L := by
  have hs : z ^ 2 / L ≤ z := (div_le_iff₀ hL).mpr (by nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)])
  have hsq : 0 ≤ z ^ 2 / L := div_nonneg (sq_nonneg z) hL.le
  have hab : |z - a| ≤ L := abs_le.mpr ⟨by linarith [ha.2, hz.1], by linarith [hz.2, ha.1]⟩
  unfold reflectedInteriorOccupationTest reflectedInteriorOccupationTestBase
  constructor
  · exact add_nonneg (sub_nonneg.mpr hs) (abs_nonneg _)
  · linarith [hz.2]

theorem reflectedGaussianDensity_time_integral_uniform_bound (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) {a : ℝ} (ha : a ∈ Ioo 0 L) (T : ℝ≥0) :
    (∫ r in (0 : ℝ)..T.val, reflectedGaussianDensity L x (2 * D * r).toNNReal a) ≤
      L / D + T.val / L := by
  have hb (z : ℝ) := reflectedInteriorOccupationTest_bounds L hL (Ioo_subset_Icc_self ha) (reflectedFold_mem L hL z)
  have hm : Measurable (fun z => reflectedInteriorOccupationTest L a (reflectedFold L z)) :=
    ((reflectedInteriorOccupationTest_continuous L a).comp (reflectedFold_continuous L)).measurable
  have hi : Integrable (fun z => reflectedInteriorOccupationTest L a (reflectedFold L z))
      (reflectedGaussianLaw L x (Real.toNNReal (2 * D) * T)) := by
    apply (integrable_const (2 * L)).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hb z).1]; exact (hb z).2)
  have havg : (∫ z, reflectedInteriorOccupationTest L a (reflectedFold L z)
      ∂reflectedGaussianLaw L x (Real.toNNReal (2 * D) * T)) ≤ 2 * L := by
    simpa only [integral_const, probReal_univ, one_smul] using integral_mono hi (integrable_const (2 * L)) (fun z => (hb z).2)
  rw [← reflectedInteriorOccupationTest_gaussian_mean L hL D hD a ha x T]
  calc
    _ ≤ (2 * L + 2 * D * T.val / L) / (2 * D) :=
      div_le_div_of_nonneg_right (by linarith [(hb x).1]) (by positivity)
    _ = _ := by field_simp

theorem reflectedInteriorOccupationCoefficient_mean_uniform_bound (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) {a : ℝ} (ha : a ∈ Ioo 0 L) (T : ℝ≥0) :
    (∫ ω, reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a T ω ∂brownianDyadicMeasure) ≤
      L / D + T.val / L := by
  rw [reflectedInteriorOccupationCoefficient_gaussian_mean L hL D hD x a T]
  exact reflectedGaussianDensity_time_integral_uniform_bound L hL D hD x ha T

end TimeTraps.Probability
