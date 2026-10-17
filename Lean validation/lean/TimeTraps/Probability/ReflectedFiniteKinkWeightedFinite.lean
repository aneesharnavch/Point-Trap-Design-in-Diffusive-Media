module

public import TimeTraps.Probability.ReflectedFiniteKinkC2Continuous
public import TimeTraps.Probability.ReflectedAtomicSurvivalProduct
public import TimeTraps.Probability.DyadicWeightedIncrementStieltjes

@[expose] public section

/-! Exact finite products for the actual finite-kink reflected formula
and the actual atomic survival weight. The stochastic term is the
canonical original-Brownian product-step integral. All finite-variation
terms retain their signs and the occupation normalization 2D. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {F : ℝ → ℝ}

def reflectedFiniteKinkC2WeightedRemainder (F : ℝ → ℝ)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  let H := fun t => reflectedAtomicSurvival L D x a κ t ω
  D * dyadicWeightedIncrement H (fun t => reflectedC2ItoDrift F brownianDyadicPath L D x t ω) T n +
    2 * D * (∑ i, c i * dyadicWeightedIncrement H
      (fun t => reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) t ω) T n) +
    finiteKinkSlope F Finset.univ a c 0 * dyadicWeightedIncrement H
      (fun t => affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L t ω) T n -
    finiteKinkSlope F Finset.univ a c L * dyadicWeightedIncrement H
      (fun t => affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L t ω) T n -
    dyadicStieltjesRightSum (reflectedAtomicSurvivalLossStieltjes L hL D hD x a κ hκ ω)
      (fun t => finiteKinkPotential F Finset.univ a c
        (foldedTrajectory L D x brownianDyadicPath t ω)) T n

theorem reflectedFiniteKinkC2_weighted_finite_ae (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) (n : ℕ) :
    (fun ω => reflectedAtomicSurvival L D x a κ T ω *
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath T ω) -
        finiteKinkPotential F Finset.univ a c (reflectedFold L x)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedAtomicSurvivalProductStep L D x a κ T n
          (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T)) ω +
        reflectedFiniteKinkC2WeightedRemainder F L hL D hD a c κ hκ x T n ω) := by
  let f := reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L (a i))
  filter_upwards [reflectedFiniteKinkC2_occupation_continuous_ae hF L hL D hD a c ha x T,
    reflectedAtomicSurvivalProductStep_integral_ae L D hD x a κ hκ T n f,
    reflectedFoldRegulatorPaths_ae x hσ hL, hall,
    reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ] with ω hpath hs hr hω hwpath
  let H : ℝ≥0 → ℝ := fun t => reflectedAtomicSurvival L D x a κ t ω
  let q : ℝ≥0 → ℝ := fun t => finiteKinkPotential F Finset.univ a c
    (foldedTrajectory L D x brownianDyadicPath t ω)
  let J : ℝ≥0 → ℝ := fun t => reflectedFiniteKinkC2HorizonPath hF L hL D hD a c ha x T t ω
  let b : ℝ≥0 → ℝ := fun t => reflectedC2ItoDrift F brownianDyadicPath L D x t ω
  let ell : ι → ℝ≥0 → ℝ := fun i t =>
    reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) t ω
  let lower : ℝ≥0 → ℝ := fun t => affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L t ω
  let upper : ℝ≥0 → ℝ := fun t => affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L t ω
  let K := reflectedAtomicSurvivalLossStieltjes L hL D hD x a κ hκ ω
  have hq0 : q 0 = finiteKinkPotential F Finset.univ a c (reflectedFold L x) :=
    congrArg (finiteKinkPotential F Finset.univ a c) hr.initial
  have hrel (t : ℝ≥0) (ht : t ∈ Icc 0 T) : q t - q 0 =
      J t + D * b t + (∑ i, (2 * D * c i) * ell i t) +
        finiteKinkSlope F Finset.univ a c 0 * lower t -
        finiteKinkSlope F Finset.univ a c L * upper t := by
    have he := hpath t ht.2
    rw [← hq0] at he
    simpa only [Finset.mul_sum, ← mul_assoc] using he
  have hd := dyadicWeightedIncrement_boundary_decomposition H q J (fun t => D * b t)
    lower upper (fun i => 2 * D * c i) ell (finiteKinkSlope F Finset.univ a c 0)
    (finiteKinkSlope F Finset.univ a c L) hrel n
  rw [dyadicWeightedIncrement_const_mul] at hd
  have hsum : (∑ i, (2 * D * c i) * dyadicWeightedIncrement H (ell i) T n) =
      2 * D * ∑ i, c i * dyadicWeightedIncrement H (ell i) T n := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [hsum] at hd
  have hk (t : ℝ≥0) : 1 - K t.val = H t := by
    rw [reflectedAtomicSurvivalLossStieltjes_apply_nnreal L hL D hD x a κ hκ hω t]
    exact sub_sub_cancel 1 (H t)
  have hKfun : (fun t : ℝ≥0 => 1 - K t.val) = H := funext hk
  have hp := dyadicWeightedIncrement_product_identity K q 1 T n
  change (1 - K T.val) * q T - (1 - K (0 : ℝ≥0).val) * q 0 = _ at hp
  rw [hk T, hk 0, hKfun, hd] at hp
  have hH0 : H 0 = 1 := hwpath.2.2.2.2.2
  rw [hH0, one_mul, hq0] at hp
  have hstep : brownianIntegral brownianDyadicPath_isPreBrownianReal
      (reflectedAtomicSurvivalProductStep L D x a κ T n f) ω = dyadicWeightedIncrement H J T n := hs
  rw [hstep]
  change H T * q T - finiteKinkPotential F Finset.univ a c (reflectedFold L x) =
    dyadicWeightedIncrement H J T n + _
  dsimp only [reflectedFiniteKinkC2WeightedRemainder]
  change H T * q T - finiteKinkPotential F Finset.univ a c (reflectedFold L x) =
    dyadicWeightedIncrement H J T n + (D * dyadicWeightedIncrement H b T n +
      2 * D * (∑ i, c i * dyadicWeightedIncrement H (ell i) T n) +
      finiteKinkSlope F Finset.univ a c 0 * dyadicWeightedIncrement H lower T n -
      finiteKinkSlope F Finset.univ a c L * dyadicWeightedIncrement H upper T n -
      dyadicStieltjesRightSum K q T n)
  linarith

end TimeTraps.Probability

end
