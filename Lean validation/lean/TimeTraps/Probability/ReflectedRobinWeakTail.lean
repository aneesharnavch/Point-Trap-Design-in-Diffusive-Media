module

public import TimeTraps.Probability.ReflectedRobinWeakFinite
public import TimeTraps.Probability.ReflectedAtomicSurvivalExpectationTail
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-! A nonnegative solution with a uniformly positive continuous source
supplies an actual finite mean-survival bound. Consequently survival
vanishes and is integrable over the whole time axis. No interior contact,
spectral gap, finite-lifetime or infinite-integrability premise is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {L D : ℝ} {a κ : ι → ℝ} {β₀ βL : ℝ} {g u : ℝ → ℝ}

theorem ReflectedRobinWeakEquation.actual_survival_expected_bound
    (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (hg : ContinuousOn g (Icc 0 L))
    (hupos : ∀ z ∈ Icc 0 L, 0 ≤ u z) {c : ℝ} (hc : 0 < c)
    (hcg : ∀ z ∈ Icc 0 L, c ≤ g z) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, (∫ r in (0 : ℝ)..T.val,
      reflectedAtomicSurvival L D x (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL) r.toNNReal ω)
      ∂brownianDyadicMeasure) ≤ u (reflectedFold L x) / c := by
  let b := reflectedRobinSite L a
  let ν := reflectedRobinStrength κ β₀ βL
  have hν := reflectedRobinStrength_nonneg hκ hβ₀ hβL
  have hpoint (r : ℝ) : c * reflectedAtomicMeanSurvival L D x b ν r.toNNReal ≤
      reflectedAtomicValueExpectation g L D x b ν r.toNNReal := by
    rw [reflectedAtomicMeanSurvival, ← integral_const_mul]
    apply integral_mono ((reflectedAtomicSurvival_integrable L hD x b ν hν r.toNNReal).const_mul c)
      ((reflectedRobinRunningCost_memLp L hL D hD b ν hν hg x r.toNNReal).integrable (by norm_num))
    intro ω
    change c * reflectedAtomicSurvival L D x b ν r.toNNReal ω ≤
      reflectedAtomicSurvival L D x b ν r.toNNReal ω *
        g (foldedTrajectory L D x brownianDyadicPath r.toNNReal ω)
    exact (mul_le_mul_of_nonneg_left
      (hcg _ (foldedTrajectory_mem L hL D x brownianDyadicPath r.toNNReal ω))
      (reflectedAtomicSurvival_bounds L hD x b ν hν r.toNNReal ω).1.le).trans_eq' (mul_comm _ _)
  have hmono : c * (∫ r in (0 : ℝ)..T.val, reflectedAtomicMeanSurvival L D x b ν r.toNNReal) ≤
      ∫ r in (0 : ℝ)..T.val, reflectedAtomicValueExpectation g L D x b ν r.toNNReal := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono T.coe_nonneg
      ((((reflectedAtomicMeanSurvival_continuous L hL D hD x b ν hν).comp
        continuous_real_toNNReal).const_mul c).intervalIntegrable 0 T.val)
      (((reflectedRobinRunningCost_expectation_continuous L hL D hD b ν hν hg x).comp
        continuous_real_toNNReal).intervalIntegrable 0 T.val)
    exact hpoint
  have he := hu.actual_expected_time_finite hL hD ha hκ hβ₀ hβL hg x T
  simp only [reflectedRobinSurvival_eq_atomic L hD] at he
  change (∫ r in (0 : ℝ)..T.val, reflectedAtomicValueExpectation g L D x b ν r.toNNReal) =
    u (reflectedFold L x) - reflectedAtomicValueExpectation u L D x b ν T at he
  have hres : 0 ≤ reflectedAtomicValueExpectation u L D x b ν T :=
    integral_nonneg (fun ω => mul_nonneg (reflectedAtomicSurvival_bounds L hD x b ν hν T ω).1.le
      (hupos _ (foldedTrajectory_mem L hL D x brownianDyadicPath T ω)))
  rw [reflectedAtomicSurvival_mean_time_integral L hD x b ν hν T]
  apply (le_div_iff₀ hc).mpr
  rw [he] at hmono
  nlinarith

theorem ReflectedRobinWeakEquation.actual_survival_tendsto
    (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (hg : ContinuousOn g (Icc 0 L))
    (hupos : ∀ z ∈ Icc 0 L, 0 ≤ u z) {c : ℝ} (hc : 0 < c)
    (hcg : ∀ z ∈ Icc 0 L, c ≤ g z) (x : ℝ) :
    Tendsto (reflectedAtomicMeanSurvival L D x (reflectedRobinSite L a)
      (reflectedRobinStrength κ β₀ βL)) atTop (𝓝 0) :=
  reflectedAtomicMeanSurvival_tendsto_of_expected_bound L hL D hD x
    (reflectedRobinSite L a) (reflectedRobinStrength κ β₀ βL)
    (reflectedRobinStrength_nonneg hκ hβ₀ hβL)
    (hu.actual_survival_expected_bound hL hD ha hκ hβ₀ hβL hg hupos hc hcg x)

theorem ReflectedRobinWeakEquation.actual_survival_integrable
    (hu : ReflectedRobinWeakEquation L D a κ β₀ βL g u)
    (hL : 0 < L) (hD : 0 < D) (ha : ∀ i, a i ∈ Ioo 0 L) (hκ : ∀ i, 0 ≤ κ i)
    (hβ₀ : 0 ≤ β₀) (hβL : 0 ≤ βL) (hg : ContinuousOn g (Icc 0 L))
    (hupos : ∀ z ∈ Icc 0 L, 0 ≤ u z) {c : ℝ} (hc : 0 < c)
    (hcg : ∀ z ∈ Icc 0 L, c ≤ g z) (x : ℝ) :
    IntegrableOn (fun r : ℝ => reflectedAtomicMeanSurvival L D x (reflectedRobinSite L a)
      (reflectedRobinStrength κ β₀ βL) r.toNNReal) (Ioi (0 : ℝ)) := by
  let b := reflectedRobinSite L a
  let ν := reflectedRobinStrength κ β₀ βL
  have hν := reflectedRobinStrength_nonneg hκ hβ₀ hβL
  have hcont := (reflectedAtomicMeanSurvival_continuous L hL D hD x b ν hν).comp continuous_real_toNNReal
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (u (reflectedFold L x) / c) 0
    (b := fun T : ℝ≥0 => T.val) (fun _ => hcont.integrableOn_Ioc)
    (NNReal.tendsto_coe_atTop.mpr tendsto_id)
  apply Eventually.of_forall
  intro T
  have he : (∫ r in (0 : ℝ)..T.val, ‖reflectedAtomicMeanSurvival L D x b ν r.toNNReal‖) =
      ∫ r in (0 : ℝ)..T.val, reflectedAtomicMeanSurvival L D x b ν r.toNNReal := by
    apply intervalIntegral.integral_congr
    intro r _
    exact Real.norm_of_nonneg (reflectedAtomicMeanSurvival_bounds L hD x b ν hν r.toNNReal).1
  dsimp only [Function.comp_def]
  erw [he, ← reflectedAtomicSurvival_mean_time_integral L hD x b ν hν T]
  exact hu.actual_survival_expected_bound hL hD ha hκ hβ₀ hβL hg hupos hc hcg x T

end TimeTraps.Probability
