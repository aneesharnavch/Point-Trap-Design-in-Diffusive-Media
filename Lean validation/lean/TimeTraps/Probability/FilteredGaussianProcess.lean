module

public import TimeTraps.Probability.FilteredIndependentIncrements
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

@[expose] public section

/-! Full Gaussian finite-dimensional laws follow from Gaussian increments
independent of the filtration past, zero start and fixed-time AE adaptedness.
Mathlib's chronological cumulative-sum construction is applied to the
mutually independent increments proved in the preceding module. Centering
and Brownian covariance then identify the actual Brownian projective laws;
almost-sure path continuity supplies the full Brownian predicate. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem filteredGaussianProcess_of_independent_increments
    (ℱ : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ)
    (hX : ∀ t, AEStronglyMeasurable[ℱ t] (X t) P)
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hgauss : ∀ s t, s ≤ t → HasGaussianLaw (fun ω => X t ω - X s ω) P)
    (hind : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) (ℱ s) P) :
    IsGaussianProcess X P := by
  have : IsProbabilityMeasure P := (hgauss 0 0 le_rfl).isProbabilityMeasure
  have hlaw (t : ℝ≥0) : HasGaussianLaw (X t) P := by
    apply (hgauss 0 t zero_le).congr
    filter_upwards [hzero] with ω hω
    rw [hω, sub_zero]
  exact (filteredProcess_hasIndepIncrements ℱ X hX hind).isGaussianProcess hlaw hzero

theorem filteredProcess_isPreBrownianReal
    (ℱ : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ)
    (hX : ∀ t, AEStronglyMeasurable[ℱ t] (X t) P)
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hgauss : ∀ s t, s ≤ t → HasGaussianLaw (fun ω => X t ω - X s ω) P)
    (hind : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) (ℱ s) P)
    (hmean : ∀ t, ∫ ω, X t ω ∂P = 0)
    (hcov : ∀ s t, s ≤ t → cov[X s, X t; P] = s.val) :
    IsPreBrownianReal X P :=
  (filteredGaussianProcess_of_independent_increments ℱ X hX hzero hgauss hind).isPreBrownianReal_of_covariance
    hmean hcov

theorem filteredProcess_isBrownianReal
    (ℱ : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ)
    (hX : ∀ t, AEStronglyMeasurable[ℱ t] (X t) P)
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hgauss : ∀ s t, s ≤ t → HasGaussianLaw (fun ω => X t ω - X s ω) P)
    (hind : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) (ℱ s) P)
    (hmean : ∀ t, ∫ ω, X t ω ∂P = 0)
    (hcov : ∀ s t, s ≤ t → cov[X s, X t; P] = s.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (X · ω)) :
    IsBrownianReal X P where
  toIsPreBrownianReal := filteredProcess_isPreBrownianReal ℱ X hX hzero hgauss hind hmean hcov
  cont := hcont

end TimeTraps.Probability
