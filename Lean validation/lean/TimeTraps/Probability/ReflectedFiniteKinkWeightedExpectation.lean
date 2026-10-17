module

public import TimeTraps.Probability.ReflectedFiniteKinkWeightedMoments

@[expose] public section

/-! Expected values in the actual survival-weighted finite-kink formula.
Every summand is integrable by the proved L² bounds, and the actual
original-Brownian stochastic integral has mean zero. No contact matching
or Neumann condition is imposed; both boundary terms remain present. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] {F : ℝ → ℝ}

theorem reflectedFiniteKinkC2WeightedLimit_integral (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedFiniteKinkC2WeightedLimit F L hL D hD a c κ hκ x T ω ∂brownianDyadicMeasure) =
      D * (∫ ω, reflectedAtomicWeightedCurvature F L D x a κ T ω ∂brownianDyadicMeasure) +
      2 * D * (∑ i, c i * ∫ ω,
        reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω ∂brownianDyadicMeasure) +
      finiteKinkSlope F Finset.univ a c 0 *
        (∫ ω, reflectedAtomicWeightedBoundary L hL D hD x a κ 0 T ω ∂brownianDyadicMeasure) -
      finiteKinkSlope F Finset.univ a c L *
        (∫ ω, reflectedAtomicWeightedBoundary L hL D hD x a κ 1 T ω ∂brownianDyadicMeasure) -
      ∫ ω, reflectedFiniteKinkC2WeightedHazard F L hL D hD a c κ hκ x T ω ∂brownianDyadicMeasure := by
  have hd := ((reflectedAtomicWeightedCurvature_memLp hF L hL D hD x a κ hκ T).integrable
    (by norm_num)).const_mul D
  have hi := ((reflectedFiniteKinkC2_weighted_occupation_sum_memLp L hL D hD a c κ hκ x T).integrable
    (by norm_num)).const_mul (2 * D)
  have h0 := ((reflectedAtomicWeightedBoundary_memLp L hL D hD x a κ hκ 0 T).integrable
    (by norm_num)).const_mul (finiteKinkSlope F Finset.univ a c 0)
  have h1 := ((reflectedAtomicWeightedBoundary_memLp L hL D hD x a κ hκ 1 T).integrable
    (by norm_num)).const_mul (finiteKinkSlope F Finset.univ a c L)
  have hA := (reflectedFiniteKinkC2WeightedHazard_memLp F L hL D hD a c κ ha hκ x T).integrable
    (by norm_num)
  have he := integral_congr_ae (μ := brownianDyadicMeasure) (Eventually.of_forall
    (reflectedFiniteKinkC2WeightedLimit_eq F L hL D hD a c κ hκ x T))
  have hs := integral_sub (((hd.add hi).add h0).sub h1) hA
  have h₁ := integral_sub ((hd.add hi).add h0) h1
  have h₂ := integral_add (hd.add hi) h0
  have h₃ := integral_add hd hi
  simp only [Pi.add_apply, Pi.sub_apply] at hs h₁ h₂ h₃
  rw [hs, h₁, h₂, h₃] at he
  have hsum : (∫ ω, ∑ i, c i * reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω
      ∂brownianDyadicMeasure) =
      ∑ i, c i * ∫ ω, reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω
        ∂brownianDyadicMeasure := by
    rw [integral_finsetSum Finset.univ (fun i _ =>
      ((reflectedAtomicWeightedOccupation_memLp L hL D hD x a κ hκ i T).integrable
        (by norm_num)).const_mul (c i))]
    simp only [integral_const_mul]
  simpa only [integral_const_mul, hsum] using he

theorem reflectedFiniteKinkC2_weighted_expected_value (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedAtomicSurvival L D x a κ T ω *
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath T ω)
        ∂brownianDyadicMeasure) =
      finiteKinkPotential F Finset.univ a c (reflectedFold L x) +
      D * (∫ ω, reflectedAtomicWeightedCurvature F L D x a κ T ω ∂brownianDyadicMeasure) +
      2 * D * (∑ i, c i * ∫ ω,
        reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω ∂brownianDyadicMeasure) +
      finiteKinkSlope F Finset.univ a c 0 *
        (∫ ω, reflectedAtomicWeightedBoundary L hL D hD x a κ 0 T ω ∂brownianDyadicMeasure) -
      finiteKinkSlope F Finset.univ a c L *
        (∫ ω, reflectedAtomicWeightedBoundary L hL D hD x a κ 1 T ω ∂brownianDyadicMeasure) -
      ∫ ω, reflectedFiniteKinkC2WeightedHazard F L hL D hD a c κ hκ x T ω ∂brownianDyadicMeasure := by
  have hv := (reflectedFiniteKinkC2_weighted_value_memLp hF L hL D hD a c κ hκ x T).integrable
    (by norm_num)
  have hI : Integrable (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
      (reflectedAtomicSurvivalMultiplier L hL D hD x a κ hκ
        (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T)) ω) brownianDyadicMeasure :=
    (Lp.memLp _).integrable (by norm_num)
  have hr := (reflectedFiniteKinkC2WeightedLimit_memLp hF L hL D hD a c κ ha hκ x T).integrable
    (by norm_num)
  have he := integral_congr_ae (reflectedFiniteKinkC2_weighted_formula hF L hL D hD a c κ ha hκ x T)
  rw [integral_sub hv (integrable_const _), integral_add hI hr, brownianIntegral_mean,
    reflectedFiniteKinkC2WeightedLimit_integral hF L hL D hD a c κ ha hκ x T] at he
  simp only [integral_const, probReal_univ, one_smul, zero_add] at he
  linarith

theorem reflectedFiniteKinkC2_weighted_expected_contact_value (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, reflectedAtomicSurvival L D x a κ T ω *
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath T ω)
        ∂brownianDyadicMeasure) =
      finiteKinkPotential F Finset.univ a c (reflectedFold L x) +
      D * (∫ ω, reflectedAtomicWeightedCurvature F L D x a κ T ω ∂brownianDyadicMeasure) +
      2 * D * (∑ i, c i * ∫ ω,
        reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω ∂brownianDyadicMeasure) +
      finiteKinkSlope F Finset.univ a c 0 *
        (∫ ω, reflectedAtomicWeightedBoundary L hL D hD x a κ 0 T ω ∂brownianDyadicMeasure) -
      finiteKinkSlope F Finset.univ a c L *
        (∫ ω, reflectedAtomicWeightedBoundary L hL D hD x a κ 1 T ω ∂brownianDyadicMeasure) -
      ∑ i, κ i * finiteKinkPotential F Finset.univ a c (a i) *
        ∫ ω, reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω ∂brownianDyadicMeasure := by
  have hA : (∫ ω, reflectedFiniteKinkC2WeightedHazard F L hL D hD a c κ hκ x T ω
      ∂brownianDyadicMeasure) =
      ∑ i, κ i * finiteKinkPotential F Finset.univ a c (a i) *
        ∫ ω, reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω ∂brownianDyadicMeasure := by
    rw [integral_congr_ae (reflectedFiniteKinkC2WeightedHazard_sum_ae F L hL D hD a c κ ha hκ x T),
      integral_finsetSum Finset.univ (fun i _ =>
        ((reflectedAtomicWeightedOccupation_memLp L hL D hD x a κ hκ i T).integrable
          (by norm_num)).const_mul (κ i * finiteKinkPotential F Finset.univ a c (a i)))]
    simp only [integral_const_mul]
  rw [reflectedFiniteKinkC2_weighted_expected_value hF L hL D hD a c κ ha hκ x T, hA]

end TimeTraps.Probability
