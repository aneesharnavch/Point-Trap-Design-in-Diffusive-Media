module

public import TimeTraps.Probability.BrownianLocalTimeGaussianMeanAffine
public import TimeTraps.Probability.BrownianAffineLocalTimeBounded
public import TimeTraps.Probability.ReflectedInteriorOccupationIdentity
public import TimeTraps.Probability.ReflectedGaussianRegularity

@[expose] public section

/-! The nonnegative periodized local-time sum has the corresponding
periodized Gaussian time integral as its mean. Tonelli applies to the
actual two-lattice series. This extended identity does not presume its
finiteness or a Revuz/PCAF characterization. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedInteriorOccupationCoefficient_ofReal_sum {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : reflectedInteriorLocalTimeRegular x σ L a ω) (T : ℝ≥0) :
    ENNReal.ofReal (reflectedInteriorOccupationCoefficient x σ L a T ω) =
      ∑' k : ℤ, (ENNReal.ofReal (affineBrownianOccupationDensity x σ (a + k * (2 * L)) T ω) +
        ENNReal.ofReal (affineBrownianOccupationDensity x σ (k * (2 * L) - a) T ω)) := by
  have hleft (k : ℤ) : affineBrownianOccupationDensity x σ (a + k * (2 * L)) T ω =
      affineBrownianOccupationDensity (x - a) σ (((2 * k + 0 : ℤ) : ℝ) * L) T ω := by
    apply congrArg (fun z => σ⁻¹ * brownianLocalTimeTimeField z T ω)
    push_cast
    ring
  have hright (k : ℤ) : affineBrownianOccupationDensity x σ (k * (2 * L) - a) T ω =
      affineBrownianOccupationDensity (x + a) σ (((2 * k + 0 : ℤ) : ℝ) * L) T ω := by
    apply congrArg (fun z => σ⁻¹ * brownianLocalTimeTimeField z T ω)
    push_cast
    ring
  rw [ENNReal.tsum_add]
  simp_rw [hleft, hright]
  rw [affineBrownianLowerOccupation_ofReal_sum hσ hL hω.1 T,
    affineBrownianLowerOccupation_ofReal_sum hσ hL hω.2 T]
  have h0 : 0 ≤ affineBrownianLowerRegulator (x - a) σ L T ω / σ ^ 2 :=
    div_nonneg (affineBrownianRegulator_nonneg (x - a) hσ L 0 T ω) (sq_nonneg σ)
  have h1 : 0 ≤ affineBrownianLowerRegulator (x + a) σ L T ω / σ ^ 2 :=
    div_nonneg (affineBrownianRegulator_nonneg (x + a) hσ L 0 T ω) (sq_nonneg σ)
  rw [← ENNReal.ofReal_add h0 h1, ← add_div]
  rfl

theorem reflectedGaussianKernel_time_measurable (L x c a : ℝ) :
    Measurable (fun s : ℝ => reflectedGaussianKernel L x (c * s).toNNReal a) := by
  unfold reflectedGaussianKernel reflectedFoldDensity
  apply Measurable.tsum
  intro k
  exact (by fun_prop : Measurable (fun s : ℝ => gaussianPDF x (c * s).toNNReal (a + k * (2 * L)))).add
    (by fun_prop : Measurable (fun s : ℝ => gaussianPDF x (c * s).toNNReal (k * (2 * L) - a)))

theorem reflectedInteriorOccupationCoefficient_gaussian_lintegral
    (L : ℝ) (hL : 0 < L) (x a : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal (reflectedInteriorOccupationCoefficient x σ L a T ω) ∂brownianDyadicMeasure) =
      ∫⁻ s in Ioc (0 : ℝ) T.val, reflectedGaussianKernel L x (σ ^ 2 * s).toNNReal a := by
  have hm (y : ℝ) : Measurable (fun ω => ENNReal.ofReal (affineBrownianOccupationDensity x σ y T ω)) :=
    ((affineBrownianOccupationDensity_timeSlice_measurable x σ T).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hg (y : ℝ) : Measurable (fun s : ℝ => gaussianPDF x (σ ^ 2 * s).toNNReal y) := by fun_prop
  calc
    _ = ∫⁻ ω, ∑' k : ℤ,
        (ENNReal.ofReal (affineBrownianOccupationDensity x σ (a + k * (2 * L)) T ω) +
          ENNReal.ofReal (affineBrownianOccupationDensity x σ (k * (2 * L) - a) T ω))
          ∂brownianDyadicMeasure := by
      apply lintegral_congr_ae
      filter_upwards [reflectedInteriorLocalTimeRegular_ae x σ L a] with ω hω
      exact reflectedInteriorOccupationCoefficient_ofReal_sum hσ hL hω T
    _ = ∑' k : ℤ,
        ((∫⁻ ω, ENNReal.ofReal (affineBrownianOccupationDensity x σ (a + k * (2 * L)) T ω) ∂brownianDyadicMeasure) +
          ∫⁻ ω, ENNReal.ofReal (affineBrownianOccupationDensity x σ (k * (2 * L) - a) T ω) ∂brownianDyadicMeasure) := by
      exact (lintegral_tsum (μ := brownianDyadicMeasure)
        (fun k : ℤ => ((hm (a + k * (2 * L))).add
          (hm (k * (2 * L) - a))).aemeasurable)).trans
        (tsum_congr (fun k : ℤ => lintegral_add_left (hm (a + k * (2 * L))) _))
    _ = ∑' k : ℤ,
        ((∫⁻ s in Ioc (0 : ℝ) T.val, gaussianPDF x (σ ^ 2 * s).toNNReal (a + k * (2 * L))) +
          ∫⁻ s in Ioc (0 : ℝ) T.val, gaussianPDF x (σ ^ 2 * s).toNNReal (k * (2 * L) - a)) := by
      simp_rw [affineBrownianOccupationDensity_gaussian_lintegral x _ hσ T]
    _ = ∑' k : ℤ, ∫⁻ s in Ioc (0 : ℝ) T.val,
        (gaussianPDF x (σ ^ 2 * s).toNNReal (a + k * (2 * L)) +
          gaussianPDF x (σ ^ 2 * s).toNNReal (k * (2 * L) - a)) := by
      apply tsum_congr
      intro k
      exact (lintegral_add_left (hg (a + k * (2 * L))) _).symm
    _ = _ := (lintegral_tsum (fun k : ℤ => ((hg (a + k * (2 * L))).add
      (hg (k * (2 * L) - a))).aemeasurable)).symm

end TimeTraps.Probability
