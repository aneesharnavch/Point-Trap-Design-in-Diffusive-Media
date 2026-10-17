module

public import TimeTraps.Probability.ReflectedBrownianMarginal

@[expose] public section

/-! Every nonempty interior interval has positive probability under the
actual positive-time reflected Gaussian law. Positivity comes from the
ordinary Gaussian density and the identity branch of the reflection map. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem gaussianReal_Ioo_pos (x : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    {a b : ℝ} (hab : a < b) : 0 < gaussianReal x v (Ioo a b) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hvol := (gaussianReal_absolutelyContinuous' x hv) hz
  have hp : 0 < volume (Ioo a b) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  exact hp.ne' hvol

theorem reflectedGaussianLaw_Ioo_pos (L : ℝ) (hL : 0 < L) (x : ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ L)
    (hab : a < b) : 0 < reflectedGaussianLaw L x v (Ioo a b) := by
  rw [reflectedGaussianLaw, Measure.map_apply (reflectedFold_measurable L) measurableSet_Ioo]
  apply (gaussianReal_Ioo_pos x hv hab).trans_le
  apply measure_mono
  intro y hy
  change reflectedFold L y ∈ Ioo a b
  rw [reflectedFold_eq_self L hL y ⟨ha.trans hy.1.le, hy.2.le.trans hb⟩]
  exact hy

theorem foldedTrajectory_Ioo_probability_pos (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) {t : ℝ≥0} (ht : 0 < t)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ L) (hab : a < b) :
    0 < brownianDyadicMeasure
      {ω | foldedTrajectory L D x brownianDyadicPath t ω ∈ Ioo a b} := by
  have he := (foldedTrajectory_gaussian_hasLaw brownianDyadicPath_isPreBrownianReal L D hD x t).measure_eq
    (p := fun y => y ∈ Ioo a b) measurableSet_Ioo
  rw [he]
  exact reflectedGaussianLaw_Ioo_pos L hL x
    (mul_ne_zero (ne_of_gt (Real.toNNReal_pos.mpr (mul_pos (by norm_num) hD))) ht.ne') ha hb hab

end TimeTraps.Probability
