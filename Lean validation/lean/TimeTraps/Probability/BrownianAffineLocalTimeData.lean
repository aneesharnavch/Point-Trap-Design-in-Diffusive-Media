module

public import TimeTraps.Probability.BrownianLocalTimeTimeRegularity
public import TimeTraps.Probability.BrownianLocalTimeGlobalSign

@[expose] public section

/-! The actual affine Brownian input x + sigma B and its rescaled
occupation-density field and Tanaka correction. These definitions concern
the process before any folding or reflection. The sign term is explicitly
sigma times the already constructed Brownian sign-integral version. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

noncomputable def affineBrownianInput (x σ : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  x + σ * brownianDyadicPath t ω

noncomputable def affineBrownianOccupationDensity (x σ a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  σ⁻¹ * brownianLocalTimeTimeField ((a - x) / σ) t ω

noncomputable def affineBrownianTanakaCorrection (x σ a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  σ * brownianLocalTimeTimeField ((a - x) / σ) t ω

noncomputable def affineBrownianSignTerm (x σ a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  σ * brownianSignIntegralGlobalPath ((a - x) / σ) t ω

theorem affineBrownianInput_start (x σ : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, affineBrownianInput x σ 0 ω = x := by
  filter_upwards [brownianDyadicPath_start_zero] with ω hω
  simp only [affineBrownianInput, hω, mul_zero, add_zero]

theorem affineBrownianOccupationDensity_nonneg (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) : 0 ≤ affineBrownianOccupationDensity x σ a t ω :=
  mul_nonneg (inv_nonneg.mpr hσ.le) (brownianLocalTimeTimeField_nonneg _ _ _)

theorem affineBrownianOccupationDensity_jointlyMeasurable (x σ : ℝ) :
    Measurable (fun p : (ℝ × ℝ≥0) × (ℕ → ℝ) =>
      affineBrownianOccupationDensity x σ p.1.1 p.1.2 p.2) := by
  let φ : (ℝ × ℝ≥0) × (ℕ → ℝ) → (ℝ × ℝ≥0) × (ℕ → ℝ) :=
    fun p => (((p.1.1 - x) / σ, p.1.2), p.2)
  have hφ : Measurable φ := by
    fun_prop
  have hm := brownianLocalTimeTimeField_jointlyMeasurable.comp hφ
  change Measurable (fun p : (ℝ × ℝ≥0) × (ℕ → ℝ) =>
    brownianLocalTimeTimeField ((p.1.1 - x) / σ) p.1.2 p.2) at hm
  change Measurable (fun p : (ℝ × ℝ≥0) × (ℕ → ℝ) =>
    σ⁻¹ * brownianLocalTimeTimeField ((p.1.1 - x) / σ) p.1.2 p.2)
  exact measurable_const.mul hm

theorem affineBrownianOccupationDensity_regular_ae (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Continuous (fun t => affineBrownianOccupationDensity x σ a t ω) ∧
      Monotone (fun t => affineBrownianOccupationDensity x σ a t ω) ∧
      affineBrownianOccupationDensity x σ a 0 ω = 0 ∧
      ∀ t : ℝ≥0, 0 ≤ affineBrownianOccupationDensity x σ a t ω := by
  filter_upwards [brownianLocalTimeTimeField_regular_ae ((a - x) / σ)] with ω hω
  refine ⟨continuous_const.mul hω.1, ?_, ?_, fun t => affineBrownianOccupationDensity_nonneg x hσ a t ω⟩
  · intro s t hst
    exact mul_le_mul_of_nonneg_left (hω.2.1 hst) (inv_nonneg.mpr hσ.le)
  · simp only [affineBrownianOccupationDensity, hω.2.2.1, mul_zero]

end TimeTraps.Probability
