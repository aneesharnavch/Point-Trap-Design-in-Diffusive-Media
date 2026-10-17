module

public import TimeTraps.Probability.ReflectedFiniteKinkWeightedLimit
public import TimeTraps.Probability.ReflectedAtomicHazardStieltjesIntegral

@[expose] public section

/-! The actual atomic hazard cancels the local-time terms for precisely
the delta-interaction jump condition 2D*c_i=κ_i*V(a_i). Zero endpoint
slopes cancel reflection. The remaining finite-time identity contains
only the original Brownian product integral and the weighted curvature
drift; constant source curvature gives the mean-time identity. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {F : ℝ → ℝ}

theorem reflectedFiniteKinkC2WeightedLimit_contact_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0)
    (hzero : finiteKinkSlope F Finset.univ a c 0 = 0)
    (hright : finiteKinkSlope F Finset.univ a c L = 0)
    (hcontact : ∀ i, 2 * D * c i = κ i * finiteKinkPotential F Finset.univ a c (a i)) :
    reflectedFiniteKinkC2WeightedLimit F L hL D hD a c κ hκ x T =ᵐ[brownianDyadicMeasure]
      (fun ω => D * ∫ r in (0 : ℝ)..T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω *
        deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) := by
  filter_upwards [reflectedAtomicHazardTimeMeasure_weighted_contact_ae L hL D hD x a κ hκ ha,
    reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ] with ω hc hp
  have he := (hc (fun t => reflectedAtomicSurvival L D x a κ t ω) hp.2.2.2.1
    (finiteKinkPotential F Finset.univ a c) T).2
  have hsum : (∫ r in Ioc (0 : ℝ) T.val,
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) *
        reflectedAtomicSurvival L D x a κ r.toNNReal ω
        ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) =
      2 * D * ∑ i, c i * reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω := by
    calc
      _ = ∫ r in Ioc (0 : ℝ) T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω *
          finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)
            ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun _ => mul_comm _ _)
      _ = ∑ i, κ i * finiteKinkPotential F Finset.univ a c (a i) *
          reflectedAtomicWeightedOccupation L hL D hD x a κ i T ω := he
      _ = _ := by
        simp only [← hcontact, Finset.mul_sum, mul_assoc]
  dsimp only [reflectedFiniteKinkC2WeightedLimit]
  rw [hzero, hright, zero_mul, zero_mul, add_zero, sub_zero, hsum]
  ring

theorem reflectedFiniteKinkC2_killed_formula (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0)
    (hzero : finiteKinkSlope F Finset.univ a c 0 = 0)
    (hright : finiteKinkSlope F Finset.univ a c L = 0)
    (hcontact : ∀ i, 2 * D * c i = κ i * finiteKinkPotential F Finset.univ a c (a i)) :
    (fun ω => reflectedAtomicSurvival L D x a κ T ω *
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath T ω) -
        finiteKinkPotential F Finset.univ a c (reflectedFold L x)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedAtomicSurvivalMultiplier L hL D hD x a κ hκ
          (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T)) ω +
        D * ∫ r in (0 : ℝ)..T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω *
          deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) := by
  filter_upwards [reflectedFiniteKinkC2_weighted_formula hF L hL D hD a c κ ha hκ x T,
    reflectedFiniteKinkC2WeightedLimit_contact_ae L hL D hD a c κ ha hκ x T hzero hright hcontact]
    with ω hf hc
  rw [hc] at hf
  exact hf

theorem reflectedFiniteKinkC2_mean_time_formula (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (x : ℝ) (T : ℝ≥0)
    (hzero : finiteKinkSlope F Finset.univ a c 0 = 0)
    (hright : finiteKinkSlope F Finset.univ a c L = 0)
    (hcontact : ∀ i, 2 * D * c i = κ i * finiteKinkPotential F Finset.univ a c (a i))
    (hsource : ∀ z ∈ Icc 0 L, D * deriv (deriv F) z = -1) :
    (fun ω => reflectedAtomicSurvival L D x a κ T ω *
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath T ω) -
        finiteKinkPotential F Finset.univ a c (reflectedFold L x)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedAtomicSurvivalMultiplier L hL D hD x a κ hκ
          (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T)) ω -
        ∫ r in (0 : ℝ)..T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω) := by
  filter_upwards [reflectedFiniteKinkC2_killed_formula hF L hL D hD a c κ ha hκ x T
    hzero hright hcontact] with ω hf
  have hd : D * (∫ r in (0 : ℝ)..T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω *
      deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) =
      -(∫ r in (0 : ℝ)..T.val, reflectedAtomicSurvival L D x a κ r.toNNReal ω) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro r _
    calc
      _ = reflectedAtomicSurvival L D x a κ r.toNNReal ω *
          (D * deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) := by ring
      _ = _ := by
        rw [hsource _ (foldedTrajectory_mem L hL D x brownianDyadicPath r.toNNReal ω)]
        ring
  rw [hd] at hf
  exact hf

end TimeTraps.Probability
