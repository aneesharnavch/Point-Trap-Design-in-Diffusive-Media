module

public import TimeTraps.Probability.ReflectedRobinWeightedFinite
public import TimeTraps.Probability.ReflectedC2WeightedDrift
public import TimeTraps.Probability.ReflectedTimeWeightedStieltjes
public import TimeTraps.Probability.ReflectedAtomicWeightedOccupation

@[expose] public section

/-! Survival-weighted finite-kink Itô with independent reaction labels.
The reaction family can include reactive endpoints. Every remainder
converges to its actual time or Stieltjes integral, and the stochastic
term converges in the original Brownian integral space. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι j : Type*} [Fintype ι] [Fintype j] {F : ℝ → ℝ}

def reflectedRobinC2WeightedLimit (F : ℝ → ℝ)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ) (b κ : j → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  let hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)
  D * (∫ r in (0 : ℝ)..T.val, reflectedAtomicSurvival L D x b κ r.toNNReal ω *
    deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) +
  2 * D * (∑ i, c i * (∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicSurvival L D x b κ r.toNNReal ω
    ∂reflectedInteriorOccupationTimeMeasure x hσ hL (a i) ω)) +
  finiteKinkSlope F Finset.univ a c 0 * (∫ r in Ioc (0 : ℝ) T.val,
    reflectedAtomicSurvival L D x b κ r.toNNReal ω
      ∂(affineBrownianRegulatorStieltjes x hσ hL 0 ω).measure) -
  finiteKinkSlope F Finset.univ a c L * (∫ r in Ioc (0 : ℝ) T.val,
    reflectedAtomicSurvival L D x b κ r.toNNReal ω
      ∂(affineBrownianRegulatorStieltjes x hσ hL 1 ω).measure) -
  ∫ r in Ioc (0 : ℝ) T.val,
    finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) *
      reflectedAtomicSurvival L D x b κ r.toNNReal ω
      ∂reflectedAtomicHazardTimeMeasure L hL D hD x b κ hκ ω

theorem reflectedRobinC2WeightedRemainder_tendsto_ae (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ) (b κ : j → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (fun n => reflectedRobinC2WeightedRemainder F L hL D hD a c b κ hκ x T n ω)
        atTop (𝓝 (reflectedRobinC2WeightedLimit F L hL D hD a c b κ hκ x T ω)) := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L (a i))
  have hkillall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : j,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (b i) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L (b i))
  filter_upwards [hall, hkillall, affineBrownianLatticeRegular_ae x (Real.sqrt (2 * D)) L,
    reflectedFoldRegulatorPaths_ae x hσ hL,
    reflectedAtomicHazard_paths_ae L hL D hD x b κ hκ] with ω hc hkill hr hx hw
  let H : ℝ≥0 → ℝ := fun t => reflectedAtomicSurvival L D x b κ t ω
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
    (reflectedAtomicSurvivalLossStieltjes L hL D hD x b κ hκ ω) q hq T
  rw [reflectedAtomicSurvivalLoss_weighted_integral L hL D hD x b κ hκ hkill q hq T] at hk
  exact ((((hd.const_mul D).add (hi.const_mul (2 * D))).add
    (hl.const_mul (finiteKinkSlope F Finset.univ a c 0))).sub
    (hu.const_mul (finiteKinkSlope F Finset.univ a c L))).sub hk

theorem reflectedRobinC2_weighted_formula (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ) (b κ : j → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0) :
    (fun ω => reflectedAtomicSurvival L D x b κ T ω *
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath T ω) -
        finiteKinkPotential F Finset.univ a c (reflectedFold L x)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedAtomicSurvivalMultiplier L hL D hD x b κ hκ
          (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T)) ω +
        reflectedRobinC2WeightedLimit F L hL D hD a c b κ hκ x T ω) := by
  let f := reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T
  have hf : brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
      brownianDyadicMeasure T f = f := by
    rw [reflectedFiniteKinkC2Integrand_cutoff, min_self]
  exact ae_eq_lp_limit_of_pathwise_remainder
    (fun n => brownianIntegral brownianDyadicPath_isPreBrownianReal
      (reflectedAtomicSurvivalProductStep L D x b κ T n f))
    (brownianIntegral brownianDyadicPath_isPreBrownianReal
      (reflectedAtomicSurvivalMultiplier L hL D hD x b κ hκ f))
    (fun n ω => reflectedRobinC2WeightedRemainder F L hL D hD a c b κ hκ x T n ω)
    (fun ω => reflectedRobinC2WeightedLimit F L hL D hD a c b κ hκ x T ω)
    (fun ω => reflectedAtomicSurvival L D x b κ T ω *
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath T ω) -
        finiteKinkPotential F Finset.univ a c (reflectedFold L x))
    (reflectedAtomicSurvivalProductStepIntegral_tendsto L hL D hD x b κ hκ T f hf)
    (reflectedRobinC2WeightedRemainder_tendsto_ae hF L hL D hD a c b κ hκ x T)
    (reflectedRobinC2_weighted_finite_ae hF L hL D hD a c b κ ha hκ x T)

end TimeTraps.Probability

end
