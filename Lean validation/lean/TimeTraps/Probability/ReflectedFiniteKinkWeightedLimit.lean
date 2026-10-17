module

public import TimeTraps.Probability.ReflectedFiniteKinkWeightedFinite
public import TimeTraps.Probability.ReflectedC2WeightedDrift
public import TimeTraps.Probability.ReflectedTimeWeightedStieltjes
public import TimeTraps.Probability.ReflectedAtomicWeightedOccupation

@[expose] public section

/-! All pathwise remainders in the survival-weighted finite-kink formula
converge to actual time and Stieltjes integrals. The right-product term
is converted to the actual hazard measure by exponential substitution.
The final theorem identifies the stochastic limit using its proved L²
convergence in the original Brownian integral space. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {F : ℝ → ℝ}

def reflectedFiniteKinkC2WeightedLimit (F : ℝ → ℝ)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  let hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)
  D * (∫ r in (0 : ℝ)..T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω *
    deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) +
  2 * D * (∑ i, c i * reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω) +
  finiteKinkSlope F Finset.univ a c 0 * (∫ r in Ioc (0 : ℝ) T.val,
    reflectedAtomicSurvival L D x a κ r.toNNReal ω
      ∂(affineBrownianRegulatorStieltjes x hσ hL 0 ω).measure) -
  finiteKinkSlope F Finset.univ a c L * (∫ r in Ioc (0 : ℝ) T.val,
    reflectedAtomicSurvival L D x a κ r.toNNReal ω
      ∂(affineBrownianRegulatorStieltjes x hσ hL 1 ω).measure) -
  ∫ r in Ioc (0 : ℝ) T.val,
    finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) *
      reflectedAtomicSurvival L D x a κ r.toNNReal ω
      ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω

theorem reflectedFiniteKinkC2WeightedRemainder_tendsto_ae (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (fun n => reflectedFiniteKinkC2WeightedRemainder F L hL D hD a c κ hκ x T n ω)
        atTop (𝓝 (reflectedFiniteKinkC2WeightedLimit F L hL D hD a c κ hκ x T ω)) := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L (a i))
  filter_upwards [hall, affineBrownianLatticeRegular_ae x (Real.sqrt (2 * D)) L,
    reflectedFoldRegulatorPaths_ae x hσ hL,
    reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ] with ω hc hr hx hw
  let H : ℝ≥0 → ℝ := fun t => reflectedAtomicSurvival L D x a κ t ω
  have hH : Continuous H := hw.2.2.2.1
  have hd := reflectedC2ItoDrift_weighted_tendsto hF L D x ω hx.path_continuous H hH T
  have hi := tendsto_finsetSum Finset.univ (fun (i : ι) _ =>
    (dyadicWeightedIncrement_reflectedInteriorOccupation_tendsto hσ hL (hc i) H hH T).const_mul (c i))
  have hl := dyadicWeightedIncrement_affineBrownianRegulator_tendsto hσ hL hr 0 H hH T
  have hu := dyadicWeightedIncrement_affineBrownianRegulator_tendsto hσ hL hr 1 H hH T
  let q : ℝ≥0 → ℝ := fun t => finiteKinkPotential F Finset.univ a c
    (foldedTrajectory L D x brownianDyadicPath t ω)
  have hq : Continuous q :=
    (finiteKinkPotential_continuous hF.continuous Finset.univ a c).comp hx.path_continuous
  have hk := dyadicStieltjesRightSum_tendsto
    (reflectedAtomicSurvivalLossStieltjes L hL D hD x a κ hκ ω) q hq T
  rw [reflectedAtomicSurvivalLoss_weighted_integral L hL D hD x a κ hκ hc q hq T] at hk
  exact ((((hd.const_mul D).add (hi.const_mul (2 * D))).add
    (hl.const_mul (finiteKinkSlope F Finset.univ a c 0))).sub
    (hu.const_mul (finiteKinkSlope F Finset.univ a c L))).sub hk

theorem reflectedFiniteKinkC2_weighted_formula (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) :
    (fun ω => reflectedAtomicSurvival L D x a κ T ω *
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath T ω) -
        finiteKinkPotential F Finset.univ a c (reflectedFold L x)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedAtomicSurvivalMultiplier L hL D hD x a κ hκ
          (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T)) ω +
        reflectedFiniteKinkC2WeightedLimit F L hL D hD a c κ hκ x T ω) := by
  let f := reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T
  have hf : brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
      brownianDyadicMeasure T f = f := by
    rw [reflectedFiniteKinkC2Integrand_cutoff, min_self]
  exact ae_eq_lp_limit_of_pathwise_remainder
    (fun n => brownianIntegral brownianDyadicPath_isPreBrownianReal
      (reflectedAtomicSurvivalProductStep L D x a κ T n f))
    (brownianIntegral brownianDyadicPath_isPreBrownianReal
      (reflectedAtomicSurvivalMultiplier L hL D hD x a κ hκ f))
    (fun n ω => reflectedFiniteKinkC2WeightedRemainder F L hL D hD a c κ hκ x T n ω)
    (fun ω => reflectedFiniteKinkC2WeightedLimit F L hL D hD a c κ hκ x T ω)
    (fun ω => reflectedAtomicSurvival L D x a κ T ω *
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath T ω) -
        finiteKinkPotential F Finset.univ a c (reflectedFold L x))
    (reflectedAtomicSurvivalProductStepIntegral_tendsto L hL D hD x a κ hκ T f hf)
    (reflectedFiniteKinkC2WeightedRemainder_tendsto_ae hF L hL D hD a c κ hκ x T)
    (reflectedFiniteKinkC2_weighted_finite_ae hF L hL D hD a c κ ha hκ x T)

end TimeTraps.Probability

end
