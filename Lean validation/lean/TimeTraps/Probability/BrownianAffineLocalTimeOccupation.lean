module

public import TimeTraps.Probability.BrownianAffineLocalTimeData
public import TimeTraps.Analysis.AffineOccupationDensity
public import TimeTraps.Probability.BrownianLocalTimeTimeOccupation

@[expose] public section

/-! The genuine occupation formula for the actual affine Brownian input.
Every scalar Lebesgue-L1 weight is allowed, with spatial integrability and
time-integral L2 membership derived. The identity is for each fixed weight
and finite horizon on the whole real spatial line. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal Topology

theorem affineBrownianOccupationDensity_spatial_integrable_ae (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (T : ℝ≥0) {g : ℝ → ℝ} (hg : Integrable g volume) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Integrable (fun a => g a * affineBrownianOccupationDensity x σ a T ω) volume := by
  have ht := affine_comp_integrable hg x hσ.ne'
  filter_upwards [brownianLocalTimeTimeField_spatial_integrable_ae T ht] with ω hω
  exact affine_density_integrable g (fun a => brownianLocalTimeTimeField a T ω) x hσ.ne' hω

theorem affineBrownianOccupationDensity_occupation_L1_ae (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (T : ℝ≥0) {g : ℝ → ℝ} (hg : Integrable g volume) :
    (fun ω => ∫ a, g a * affineBrownianOccupationDensity x σ a T ω) =ᵐ[brownianDyadicMeasure]
      (fun ω => ∫ s in (0 : ℝ)..T.val, g (affineBrownianInput x σ s.toNNReal ω)) := by
  have ht := affine_comp_integrable hg x hσ.ne'
  filter_upwards [brownianLocalTimeTimeField_occupation_L1_ae T ht] with ω hω
  exact (affine_density_pairing g (fun a => brownianLocalTimeTimeField a T ω) x hσ).trans hω

theorem affineBrownianOccupationTime_memLp (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (T : ℝ≥0) {g : ℝ → ℝ} (hg : Integrable g volume) :
    MemLp (fun ω => ∫ s in (0 : ℝ)..T.val, g (affineBrownianInput x σ s.toNNReal ω))
      2 brownianDyadicMeasure := by
  have ht := affine_comp_integrable hg x hσ.ne'
  have hm := brownianLocalTimeTimeField_integral_memLp T ht
  have he := brownianLocalTimeTimeField_occupation_L1_ae T ht
  change MemLp (fun ω => ∫ s in (0 : ℝ)..T.val,
    g (x + σ * brownianDyadicPath s.toNNReal ω)) 2 brownianDyadicMeasure
  exact hm.ae_eq he

end TimeTraps.Probability
