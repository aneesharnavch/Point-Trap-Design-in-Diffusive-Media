module

public import TimeTraps.Probability.BrownianAffineLocalTimeData

@[expose] public section

/-! The scaled Tanaka correction satisfies the actual all-time absolute
value identity for x + sigma B, with a term identified with sigma times
the checked Brownian sign integral. Its ratio to occupation density is
sigma squared, hence 2D for sigma = sqrt(2D). No reflected dynamics or
additional semimartingale characterization is asserted. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

theorem affineBrownianInput_abs (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    |affineBrownianInput x σ t ω - a| = σ * |brownianDyadicPath t ω - (a - x) / σ| := by
  have he : x + σ * brownianDyadicPath t ω - a =
      σ * (brownianDyadicPath t ω - (a - x) / σ) := by
    field_simp
    ring
  rw [affineBrownianInput, he, abs_mul, abs_of_pos hσ]

theorem affineBrownianSignTerm_integral_ae (x σ a : ℝ) (t : ℝ≥0) :
    affineBrownianSignTerm x σ a t =ᵐ[brownianDyadicMeasure]
      (σ • brownianDyadicSignIntegral ((a - x) / σ) t : Lp ℝ 2 brownianDyadicMeasure) := by
  filter_upwards [brownianSignIntegralGlobalPath_integral_ae ((a - x) / σ) t,
    Lp.coeFn_smul σ (brownianDyadicSignIntegral ((a - x) / σ) t)] with ω hi hs
  rw [hs, Pi.smul_apply, smul_eq_mul]
  exact congrArg (fun z => σ * z) hi

theorem affineBrownianTanaka_decomposition_ae (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0,
      |affineBrownianInput x σ t ω - a| = |x - a| +
        affineBrownianSignTerm x σ a t ω + affineBrownianTanakaCorrection x σ a t ω := by
  filter_upwards [brownianLocalTimeGlobalPath_decomposition_ae ((a - x) / σ),
    brownianLocalTimeTimeField_globalPath_ae ((a - x) / σ), affineBrownianInput_start x σ]
    with ω hd hf hzero
  intro t
  have hi := affineBrownianInput_abs x hσ a 0 ω
  rw [hzero] at hi
  rw [affineBrownianInput_abs x hσ a t ω, hi]
  simp only [affineBrownianSignTerm, affineBrownianTanakaCorrection, hf t]
  simpa only [mul_add] using congrArg (fun z => σ * z) (hd t)

theorem affineBrownianTanakaCorrection_eq_density (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    affineBrownianTanakaCorrection x σ a t ω = σ ^ 2 * affineBrownianOccupationDensity x σ a t ω := by
  unfold affineBrownianTanakaCorrection affineBrownianOccupationDensity
  field_simp

theorem affineBrownianOccupationDensity_eq_correction (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    affineBrownianOccupationDensity x σ a t ω = affineBrownianTanakaCorrection x σ a t ω / σ ^ 2 := by
  apply (eq_div_iff (pow_ne_zero 2 hσ.ne')).mpr
  rw [mul_comm]
  exact (affineBrownianTanakaCorrection_eq_density x hσ a t ω).symm

theorem affineBrownian_diffusion_normalization (x : ℝ) {D : ℝ} (hD : 0 < D)
    (a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    affineBrownianTanakaCorrection x (Real.sqrt (2 * D)) a t ω =
      (2 * D) * affineBrownianOccupationDensity x (Real.sqrt (2 * D)) a t ω := by
  have hs : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  rw [affineBrownianTanakaCorrection_eq_density x hs a t ω, Real.sq_sqrt (by positivity)]

end TimeTraps.Probability
