module

public import TimeTraps.Probability.ReflectedGaussianKernel
public import TimeTraps.Probability.BrownianAffineLocalTimeData
public import TimeTraps.Probability.ReflectedFoldTrajectory

@[expose] public section

/-! The actual folded affine Brownian path has the folded Gaussian law.
At strictly positive time and scale this is the two-lattice interior
density; time zero is a Dirac law. The physical `sqrt (2D)` trajectory has
variance parameter `2Dt` before folding. These are marginal statements,
with no conditional-transition or Markov assertion. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

def affineBrownianVariance (σ : ℝ) (t : ℝ≥0) : ℝ≥0 :=
  NNReal.mk (σ ^ 2) (sq_nonneg σ) * t

theorem affineBrownianVariance_pos {σ : ℝ} (hσ : 0 < σ) {t : ℝ≥0} (ht : 0 < t) :
    0 < affineBrownianVariance σ t := by
  change (0 : ℝ) < σ ^ 2 * (t : ℝ)
  exact mul_pos (sq_pos_of_pos hσ) (show (0 : ℝ) < t from ht)

theorem affineBrownianInput_hasLaw (x σ : ℝ) (t : ℝ≥0) :
    HasLaw (affineBrownianInput x σ t) (gaussianReal x (affineBrownianVariance σ t))
      brownianDyadicMeasure := by
  change HasLaw (fun ω => x + σ * brownianDyadicPath t ω)
    (gaussianReal x (affineBrownianVariance σ t)) brownianDyadicMeasure
  simpa only [affineBrownianVariance, mul_zero, zero_add] using
    gaussianReal_const_add (gaussianReal_const_mul
      (brownianDyadicPath_isPreBrownianReal.hasLaw_eval t) σ) x

theorem folded_affineBrownianInput_hasLaw (L x σ : ℝ) (t : ℝ≥0) :
    HasLaw (fun ω => reflectedFold L (affineBrownianInput x σ t ω))
      (reflectedGaussianLaw L x (affineBrownianVariance σ t)) brownianDyadicMeasure := by
  have hf : HasLaw (reflectedFold L) (reflectedGaussianLaw L x (affineBrownianVariance σ t))
      (gaussianReal x (affineBrownianVariance σ t)) :=
    ⟨(reflectedFold_measurable L).aemeasurable, rfl⟩
  exact hf.fun_comp (affineBrownianInput_hasLaw x σ t)

theorem folded_affineBrownianInput_density (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) {t : ℝ≥0} (ht : 0 < t) :
    HasLaw (fun ω => reflectedFold L (affineBrownianInput x σ t ω))
      ((volume.restrict (Ioo 0 L)).withDensity
        (reflectedGaussianKernel L x (affineBrownianVariance σ t))) brownianDyadicMeasure := by
  rw [← reflectedGaussianLaw_density L hL x (ne_of_gt (affineBrownianVariance_pos hσ ht))]
  exact folded_affineBrownianInput_hasLaw L x σ t

theorem folded_affineBrownianInput_zero_hasLaw (L x σ : ℝ) :
    HasLaw (fun ω => reflectedFold L (affineBrownianInput x σ 0 ω))
      (Measure.dirac (reflectedFold L x)) brownianDyadicMeasure := by
  simpa only [affineBrownianVariance, mul_zero, reflectedGaussianLaw_zero] using
    folded_affineBrownianInput_hasLaw L x σ 0

theorem foldedTrajectory_gaussian_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsPreBrownianReal B P)
    (L D : ℝ) (hD : 0 < D) (x : ℝ) (t : ℝ≥0) :
    HasLaw (foldedTrajectory L D x B t)
      (reflectedGaussianLaw L x (Real.toNNReal (2 * D) * t)) P := by
  have ha : HasLaw (fun ω => x + Real.sqrt (2 * D) * B t ω)
      (gaussianReal x (affineBrownianVariance (Real.sqrt (2 * D)) t)) P := by
    simpa only [affineBrownianVariance, mul_zero, zero_add] using
      gaussianReal_const_add (gaussianReal_const_mul (hB.hasLaw_eval t) (Real.sqrt (2 * D))) x
  have hf : HasLaw (reflectedFold L)
      (reflectedGaussianLaw L x (affineBrownianVariance (Real.sqrt (2 * D)) t))
      (gaussianReal x (affineBrownianVariance (Real.sqrt (2 * D)) t)) :=
    ⟨(reflectedFold_measurable L).aemeasurable, rfl⟩
  have hnonneg : 0 ≤ 2 * D := mul_nonneg (by norm_num) hD.le
  have hv : affineBrownianVariance (Real.sqrt (2 * D)) t = Real.toNNReal (2 * D) * t := by
    apply NNReal.eq
    change (Real.sqrt (2 * D)) ^ 2 * (t : ℝ) = (Real.toNNReal (2 * D) : ℝ) * (t : ℝ)
    rw [Real.sq_sqrt hnonneg, Real.coe_toNNReal _ hnonneg]
  rw [← hv]
  exact hf.fun_comp ha

theorem foldedTrajectory_gaussian_density {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsPreBrownianReal B P)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) {t : ℝ≥0} (ht : 0 < t) :
    HasLaw (foldedTrajectory L D x B t)
      ((volume.restrict (Ioo 0 L)).withDensity
        (reflectedGaussianKernel L x (Real.toNNReal (2 * D) * t))) P := by
  have hv : Real.toNNReal (2 * D) * t ≠ 0 :=
    mul_ne_zero (ne_of_gt (Real.toNNReal_pos.mpr (mul_pos (by norm_num) hD))) (ne_of_gt ht)
  rw [← reflectedGaussianLaw_density L hL x hv]
  exact foldedTrajectory_gaussian_hasLaw hB L D hD x t

end TimeTraps.Probability

end
