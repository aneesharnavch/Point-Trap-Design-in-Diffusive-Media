module

public import TimeTraps.Probability.BrownianFoldSlopeIndependence
public import TimeTraps.Probability.BrownianFoldSlopeIncrementLaw
public import TimeTraps.Probability.BrownianFoldSlopeMoments
public import TimeTraps.Probability.FilteredGaussianProcess

@[expose] public section

/-! The actual continuous normalized fold-slope integral is Brownian.
Gaussian increments, independence from the original Brownian past,
almost-everywhere adaptedness, mean/covariance and continuity have all
been derived independently. The finite-dimensional Gaussian construction
therefore supplies the full Brownian law, not merely its marginals. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

theorem brownianFoldSlopeGlobalPath_covariance (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (s t : ℝ≥0) :
    cov[brownianFoldSlopeGlobalPath L hL x hσ s,
      brownianFoldSlopeGlobalPath L hL x hσ t; brownianDyadicMeasure] = (min s t).val := by
  simp only [covariance, brownianFoldSlopeGlobalPath_mean, sub_zero]
  exact brownianFoldSlopeGlobalPath_pairing L hL x hσ s t

theorem brownianFoldSlopeGlobalPath_isBrownianReal (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    IsBrownianReal (brownianFoldSlopeGlobalPath L hL x hσ) brownianDyadicMeasure := by
  apply filteredProcess_isBrownianReal brownianFiltration
    (brownianFoldSlopeGlobalPath L hL x hσ)
    (brownianFoldSlopeGlobalPath_raw_aestronglyMeasurable L hL x hσ)
    (Eventually.of_forall (brownianFoldSlopeGlobalPath_zero L hL x hσ))
    (fun s t hst => (brownianFoldSlopeGlobalPath_increment_hasLaw L hL x hσ hst).hasGaussianLaw)
    (fun s t hst => brownianFoldSlopeGlobalPath_increment_indep_past L hL x hσ hst)
    (brownianFoldSlopeGlobalPath_mean L hL x hσ)
  · intro s t hst
    rw [brownianFoldSlopeGlobalPath_covariance, min_eq_left hst]
  · exact Eventually.of_forall (brownianFoldSlopeGlobalPath_continuous L hL x hσ)

end TimeTraps.Probability
