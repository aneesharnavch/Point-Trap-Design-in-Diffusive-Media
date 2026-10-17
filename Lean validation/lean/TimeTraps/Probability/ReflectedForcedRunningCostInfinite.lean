module

public import TimeTraps.Probability.ReflectedForcedRunningCostFinite
public import TimeTraps.Probability.ReflectedGroundSurvivalBounds
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! The actual signed running cost is absolutely integrable on the full
time/sample product. This is derived from compact source bounds and the
proved positive physical spectral decay. The terminal weighted value
vanishes, with no infinite-horizon premise on the weak solution. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ} {P : SpectralProblem n} {g u : ℝ → ℝ}

theorem reflectedForcedRunningCost_joint_integrable
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    Integrable (fun p : ℝ × (ℕ → ℝ) =>
      reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength p.1.toNNReal p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod brownianDyadicMeasure) := by
  have hm := ((reflectedForcedRunningCost_jointlyMeasurable hg x).comp
    (measurable_fst.real_toNNReal.prodMk measurable_snd)).aestronglyMeasurable
      (μ := (volume.restrict (Ioi (0 : ℝ))).prod brownianDyadicMeasure)
  obtain ⟨c, C, _hc, _hC, hb⟩ := reflectedPrincipal_survival_uniform_bounds P
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Eventually.of_forall (fun r =>
      (reflectedForcedRunningCost_memLp hg x r.toNNReal).integrable (by norm_num))
  · apply ((exp_neg_integrableOn_Ioi 0 P.principalValue_pos).const_mul
      (‖forcedKinkSource P g hg‖ * C)).mono' hm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    calc
      _ ≤ ‖forcedKinkSource P g hg‖ *
          reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength r.toNNReal :=
        reflectedForcedRunningCost_integral_norm_le hg x r.toNNReal
      _ ≤ ‖forcedKinkSource P g hg‖ * (C * Real.exp (-P.principalValue * r.toNNReal.val)) :=
        mul_le_mul_of_nonneg_left (hb x hx r.toNNReal).2 (norm_nonneg _)
      _ = ‖forcedKinkSource P g hg‖ * (C * Real.exp (-P.principalValue * r)) :=
        congrArg (fun y : ℝ => ‖forcedKinkSource P g hg‖ * (C * Real.exp (-P.principalValue * y)))
          (Real.coe_toNNReal r hr.le)
      _ = _ := (mul_assoc _ _ _).symm

theorem reflectedForcedRunningCost_path_integrable_ae
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    ∀ᵐ ω ∂brownianDyadicMeasure, IntegrableOn (fun r : ℝ =>
      reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength r.toNNReal ω)
      (Ioi (0 : ℝ)) :=
  (reflectedForcedRunningCost_joint_integrable hg hx).prod_left_ae

theorem reflectedForcedRunningCost_integral_integrable
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    Integrable (fun ω => ∫ r in Ioi (0 : ℝ),
      reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength r.toNNReal ω)
      brownianDyadicMeasure :=
  (reflectedForcedRunningCost_joint_integrable hg hx).integral_prod_right

theorem reflectedForcedRunningCost_expectation_integrable
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    IntegrableOn (fun r : ℝ =>
      reflectedAtomicValueExpectation g P.length P.diffusivity x P.site P.strength r.toNNReal)
      (Ioi (0 : ℝ)) :=
  (reflectedForcedRunningCost_joint_integrable hg hx).integral_prod_left

theorem reflectedForcedRunningCost_expectation_tendsto_zero
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    Tendsto (reflectedAtomicValueExpectation g P.length P.diffusivity x P.site P.strength)
      atTop (𝓝 0) := by
  obtain ⟨c, C, _hc, _hC, hb⟩ := reflectedPrincipal_survival_uniform_bounds P
  have ht : Tendsto (fun T : ℝ≥0 => T.val) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have he : Tendsto (fun T : ℝ≥0 => Real.exp (-P.principalValue * T.val)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (ht.const_mul_atTop P.principalValue_pos)
    simpa only [Function.comp_def, neg_mul] using h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun T => ?_))
    (by simpa only [mul_zero] using he.const_mul (‖forcedKinkSource P g hg‖ * C))
  calc
    _ ≤ ∫ ω, ‖reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength T ω‖
        ∂brownianDyadicMeasure := norm_integral_le_integral_norm _
    _ ≤ ‖forcedKinkSource P g hg‖ *
        reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength T :=
      reflectedForcedRunningCost_integral_norm_le hg x T
    _ ≤ ‖forcedKinkSource P g hg‖ * (C * Real.exp (-P.principalValue * T.val)) :=
      mul_le_mul_of_nonneg_left (hb x hx T).2 (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

theorem reflectedForcedRunningCost_expected_time_tendsto (hu : WeakForcedEquation P g u)
    (hg : ContinuousOn g (Icc 0 P.length)) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    Tendsto (fun T : ℝ≥0 => ∫ r in (0 : ℝ)..T.val,
      reflectedAtomicValueExpectation g P.length P.diffusivity x P.site P.strength r.toNNReal)
      atTop (𝓝 (u x)) := by
  have hc : ContinuousOn u (Icc 0 P.length) := by
    simpa only [uIcc_of_le P.length_pos.le] using hu.energy.continuousOn
  have h := (reflectedForcedRunningCost_expectation_tendsto_zero hc hx).const_sub (u x)
  have he (T : ℝ≥0) := reflectedForcedRunningCost_expected_time_finite hu hg x T
  simp only [reflectedFold_eq_self P.length P.length_pos x hx] at he
  simpa only [he, sub_zero] using h

end TimeTraps.Probability
