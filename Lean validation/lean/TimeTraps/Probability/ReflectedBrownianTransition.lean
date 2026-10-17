module

public import TimeTraps.Probability.ReflectedFoldConditional
public import TimeTraps.Probability.ReflectedBrownianMarginal
public import TimeTraps.Probability.BrownianMartingaleFiltration

@[expose] public section

/-! Actual bounded Borel transition identities for folded Brownian paths,
conditional on the original Brownian past. The transition distribution
depends only on the folded current position and the elapsed time. The
physical trajectory has the exact variance parameter 2D(t-s). Equal times
are included through the zero-variance law. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_scaled_increment_hasLaw (hB : IsPreBrownianReal B P)
    (σ : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => σ * (B t ω - B s ω))
      (gaussianReal 0 (affineBrownianVariance σ (t - s))) P := by
  have hd : nndist t.val s.val = t - s := by
    apply NNReal.eq
    rw [coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show s.val ≤ t.val from hst)),
      NNReal.coe_sub hst]
    rfl
  simpa only [mul_zero, hd, affineBrownianVariance, Pi.sub_apply] using
    gaussianReal_const_mul (hB.hasLaw_sub t s) σ

theorem foldedBrownian_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hb : ∀ y, |g y| ≤ M) :
    P[fun ω => g (reflectedFold L (x + σ * B t ω)) | brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun ω => ∫ y, g y ∂reflectedGaussianLaw L (reflectedFold L (x + σ * B s ω))
        (affineBrownianVariance σ (t - s)) := by
  have hY : Measurable[brownianNaturalFiltration B hBm s] (fun ω => x + σ * B s ω) :=
    measurable_const.add (measurable_const.mul
      (brownianNaturalFiltration_stronglyAdapted B hBm s).measurable)
  have hZ : Measurable (fun ω => σ * (B t ω - B s ω)) :=
    measurable_const.mul ((hBm t).sub (hBm s))
  have hscaled : Measurable[MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance]
      (fun ω => σ * (B t ω - B s ω)) :=
    measurable_const.mul (comap_measurable (fun ω => B t ω - B s ω))
  have hind := indep_of_indep_of_le_left (brownian_increment_indep_natural hB hBm hst)
    hscaled.comap_le
  have h := reflectedFold_condExp_gaussian ((brownianNaturalFiltration B hBm).le s) hY hZ
    (brownian_scaled_increment_hasLaw hB σ hst) hind L hL hg hb
  have he : (fun ω => g (reflectedFold L ((x + σ * B s ω) + σ * (B t ω - B s ω)))) =
      (fun ω => g (reflectedFold L (x + σ * B t ω))) := by
    funext ω
    congr 2
    ring
  rw [he] at h
  exact h

theorem foldedTrajectory_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hb : ∀ y, |g y| ≤ M) :
    P[fun ω => g (foldedTrajectory L D x B t ω) | brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun ω => ∫ y, g y ∂reflectedGaussianLaw L (foldedTrajectory L D x B s ω)
        (Real.toNNReal (2 * D) * (t - s)) := by
  have h := foldedBrownian_condExp hB hBm L hL x (Real.sqrt (2 * D)) hst hg hb
  have hD₀ : 0 ≤ 2 * D := mul_nonneg (by norm_num) hD.le
  have hv : affineBrownianVariance (Real.sqrt (2 * D)) (t - s) =
      Real.toNNReal (2 * D) * (t - s) := by
    apply NNReal.eq
    change (Real.sqrt (2 * D)) ^ 2 * ((t - s : ℝ≥0) : ℝ) =
      (Real.toNNReal (2 * D) : ℝ) * ((t - s : ℝ≥0) : ℝ)
    rw [Real.sq_sqrt hD₀, Real.coe_toNNReal _ hD₀]
  simpa only [foldedTrajectory, hv] using h

end TimeTraps.Probability
