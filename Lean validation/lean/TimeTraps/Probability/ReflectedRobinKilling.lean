module

public import TimeTraps.Probability.ReflectedRobinWeightedLimit
public import TimeTraps.Probability.ReflectedRobinHazardMeasure

@[expose] public section

/-! The actual combined killing cancels precisely the physical interior
jump and Robin boundary terms. The source conditions are D V'(0)=beta0
V(0), D V'(L)=-betaL V(L), and 2D c_i=kappa_i V(a_i). The stochastic
integral remains in the original Brownian integral space. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {F : ℝ → ℝ}

theorem reflectedRobinC2WeightedLimit_contact_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (β₀ βL : ℝ)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (x : ℝ) (T : ℝ≥0)
    (hzero : D * finiteKinkSlope F Finset.univ a c 0 = β₀ * finiteKinkPotential F Finset.univ a c 0)
    (hright : D * finiteKinkSlope F Finset.univ a c L = -βL * finiteKinkPotential F Finset.univ a c L)
    (hcontact : ∀ i, 2 * D * c i = κ i * finiteKinkPotential F Finset.univ a c (a i)) :
    reflectedRobinC2WeightedLimit F L hL D hD a c (reflectedRobinSite L a)
      (reflectedRobinStrength κ β₀ βL) (reflectedRobinStrength_nonneg hκ hβ₀ hβL) x T
      =ᵐ[brownianDyadicMeasure]
      (fun ω => D * ∫ r in (0 : ℝ)..T.val,
        reflectedAtomicSurvival L D x (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL)
          r.toNNReal ω * deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) := by
  filter_upwards [reflectedRobinHazardTimeMeasure_weighted_contact_ae
      L hL D hD x a κ hκ β₀ βL hβ₀ hβL (fun i => Ioo_subset_Icc_self (ha i)),
    reflectedAtomicHazard_paths_ae L hL D hD x (reflectedRobinSite L a)
      (reflectedRobinStrength κ β₀ βL) (reflectedRobinStrength_nonneg hκ hβ₀ hβL)] with ω hc hp
  have he := (hc (fun t => reflectedAtomicSurvival L D x (reflectedRobinSite L a)
    (reflectedRobinStrength κ β₀ βL) t ω) hp.2.2.2.1 (finiteKinkPotential F Finset.univ a c) T).2
  have hl : finiteKinkSlope F Finset.univ a c 0 =
      (β₀ / D) * finiteKinkPotential F Finset.univ a c 0 := by
    apply mul_left_cancel₀ hD.ne'
    rw [hzero]
    field_simp
  have hu : finiteKinkSlope F Finset.univ a c L =
      -(βL / D) * finiteKinkPotential F Finset.univ a c L := by
    apply mul_left_cancel₀ hD.ne'
    rw [hright]
    field_simp
  have hswap : (∫ r in Ioc (0 : ℝ) T.val,
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω) *
        reflectedAtomicSurvival L D x (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL)
          r.toNNReal ω
        ∂reflectedRobinHazardTimeMeasure L hL D hD x a κ hκ β₀ βL hβ₀ hβL ω) =
      ∫ r in Ioc (0 : ℝ) T.val,
        reflectedAtomicSurvival L D x (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL)
          r.toNNReal ω *
        finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)
        ∂reflectedRobinHazardTimeMeasure L hL D hD x a κ hκ β₀ βL hβ₀ hβL ω := by
    exact integral_congr_ae (Eventually.of_forall (fun _ => mul_comm _ _))
  unfold reflectedRobinHazardTimeMeasure at hswap he
  dsimp only [reflectedRobinC2WeightedLimit]
  erw [hswap, he, hl, hu]
  simp only [← hcontact, Finset.mul_sum, mul_assoc]
  unfold affineBrownianRegulatorTimeMeasure
  ring

theorem reflectedRobinC2_killed_formula (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (β₀ βL : ℝ)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (x : ℝ) (T : ℝ≥0)
    (hzero : D * finiteKinkSlope F Finset.univ a c 0 = β₀ * finiteKinkPotential F Finset.univ a c 0)
    (hright : D * finiteKinkSlope F Finset.univ a c L = -βL * finiteKinkPotential F Finset.univ a c L)
    (hcontact : ∀ i, 2 * D * c i = κ i * finiteKinkPotential F Finset.univ a c (a i)) :
    (fun ω => reflectedRobinSurvival L D x a κ β₀ βL T ω *
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath T ω) -
        finiteKinkPotential F Finset.univ a c (reflectedFold L x)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedAtomicSurvivalMultiplier L hL D hD x (reflectedRobinSite L a)
          (reflectedRobinStrength κ β₀ βL) (reflectedRobinStrength_nonneg hκ hβ₀ hβL)
          (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T)) ω +
        D * ∫ r in (0 : ℝ)..T.val, reflectedRobinSurvival L D x a κ β₀ βL r.toNNReal ω *
          deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) := by
  simp only [reflectedRobinSurvival_eq_atomic L hD]
  filter_upwards [reflectedRobinC2_weighted_formula hF L hL D hD a c (reflectedRobinSite L a)
      (reflectedRobinStrength κ β₀ βL) ha (reflectedRobinStrength_nonneg hκ hβ₀ hβL) x T,
    reflectedRobinC2WeightedLimit_contact_ae L hL D hD a c κ ha hκ β₀ βL hβ₀ hβL x T
      hzero hright hcontact] with ω hf hc
  rw [hc] at hf
  exact hf

theorem reflectedRobinC2_running_cost_formula (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c κ : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i) (β₀ βL : ℝ)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (x : ℝ) (T : ℝ≥0)
    (hzero : D * finiteKinkSlope F Finset.univ a c 0 = β₀ * finiteKinkPotential F Finset.univ a c 0)
    (hright : D * finiteKinkSlope F Finset.univ a c L = -βL * finiteKinkPotential F Finset.univ a c L)
    (hcontact : ∀ i, 2 * D * c i = κ i * finiteKinkPotential F Finset.univ a c (a i))
    (g : ℝ → ℝ) (hsource : ∀ z ∈ Icc 0 L, D * deriv (deriv F) z = -g z) :
    (fun ω => reflectedRobinSurvival L D x a κ β₀ βL T ω *
      finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath T ω) -
        finiteKinkPotential F Finset.univ a c (reflectedFold L x)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedAtomicSurvivalMultiplier L hL D hD x (reflectedRobinSite L a)
          (reflectedRobinStrength κ β₀ βL) (reflectedRobinStrength_nonneg hκ hβ₀ hβL)
          (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T)) ω -
        ∫ r in (0 : ℝ)..T.val, reflectedRobinSurvival L D x a κ β₀ βL r.toNNReal ω *
          g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) := by
  filter_upwards [reflectedRobinC2_killed_formula hF L hL D hD a c κ ha hκ β₀ βL hβ₀ hβL x T
    hzero hright hcontact] with ω hf
  have hd : D * (∫ r in (0 : ℝ)..T.val, reflectedRobinSurvival L D x a κ β₀ βL r.toNNReal ω *
      deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) =
      -(∫ r in (0 : ℝ)..T.val, reflectedRobinSurvival L D x a κ β₀ βL r.toNNReal ω *
        g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro r _
    calc
      _ = reflectedRobinSurvival L D x a κ β₀ βL r.toNNReal ω *
          (D * deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)) := by ring
      _ = _ := by
        rw [hsource _ (foldedTrajectory_mem L hL D x brownianDyadicPath r.toNNReal ω)]
        ring
  rw [hd] at hf
  simpa only [sub_eq_add_neg] using hf

end TimeTraps.Probability
