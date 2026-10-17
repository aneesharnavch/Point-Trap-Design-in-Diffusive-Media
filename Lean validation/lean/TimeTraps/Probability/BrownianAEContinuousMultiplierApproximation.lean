module

public import TimeTraps.Probability.BrownianAEContinuousMultiplier

@[expose] public section

/-! Actual left-step association for an almost-everywhere raw-adapted
continuous multiplier. The original dyadic coefficients, rather than
their chosen measurable versions, occur in the finite stochastic sums.
Product-L² convergence and the original Itô isometry give convergence
to the actual product integral, including the zero horizon. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B H : ℝ≥0 → Ω → ℝ}
variable {P : Measure Ω} {M : ℝ≥0}

theorem brownianAEContinuousProductStep_integral_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (H t) P)
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (n : ℕ)
    (f : brownianIntegralSpace B hBm P) :
    brownianIntegral hB (brownianAEContinuousProductStep hBm hH M T n f) =ᵐ[P]
      brownianStepIntegral (fun t ω => brownianIntegralUpTo hB t f ω) (brownianDyadicGrid T n)
        (fun i => H (brownianDyadicGrid T n i.castSucc)) :=
  brownianAEPastStepIntegrand_integral_ae hB
    (brownianDyadicGrid T n) (brownianDyadicGrid_monotone T n)
    (fun i => H (brownianDyadicGrid T n i.castSucc))
    (fun i => hH (brownianDyadicGrid T n i.castSucc))
    (fun i => hb (brownianDyadicGrid T n i.castSucc)) f

theorem brownianAEContinuousProductStep_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (H t) P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (T : ℝ≥0)
    (f : brownianIntegralSpace B hBm P) (hf : brownianTimeCutoff B hBm P T f = f) :
    Tendsto (fun n => brownianAEContinuousProductStep hBm hH M T n f) atTop
      (𝓝 (brownianAEContinuousMultiplier hB hBm hH hjoint hb hcont f)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hlim := brownianAdaptedContinuousMultiplier_tendsto
    (brownianSquareProcess_measurable hjoint T)
    (fun n => brownianAdaptedContinuous_step_measurable
      (fun _t => hjoint.comp (measurable_const.prodMk measurable_id)) T n)
    (brownianAdaptedContinuousMultiplier_cutoff_bound hb T)
    (brownianAdaptedContinuousMultiplier_step_bound hb T)
    (brownianAdaptedContinuous_step_tendsto_ae hcont T)
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P))
  have he (n : ℕ) : brownianAdaptedContinuousMultiplierAmbient
      (brownianAdaptedContinuous_step_measurable
        (fun _t => hjoint.comp (measurable_const.prodMk measurable_id)) T n)
      (brownianAdaptedContinuousMultiplier_step_bound hb T n)
      (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =
      ((brownianAEContinuousProductStep hBm hH M T n f : brownianIntegralSpace B hBm P) :
        Lp ℝ 2 ((volume : Measure ℝ).prod P)) := by
    apply Lp.ext
    exact (brownianAdaptedContinuousMultiplierAmbient_coe _ _ _).trans
      (brownianAEContinuousProductStep_coe hBm hH hb T n f).symm
  have hsupport := brownianTimeCutoff_sub_coe (show (0 : ℝ≥0) ≤ T from zero_le) f
  rw [hf, brownianTimeCutoff_zero] at hsupport
  change ((f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) - 0 :
    Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P] _ at hsupport
  rw [sub_zero] at hsupport
  have ht : brownianAdaptedContinuousMultiplierAmbient
      (brownianSquareProcess_measurable hjoint T)
      (brownianAdaptedContinuousMultiplier_cutoff_bound hb T)
      (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =
      (brownianAEContinuousMultiplier hB hBm hH hjoint hb hcont f :
        Lp ℝ 2 ((volume : Measure ℝ).prod P)) := by
    apply Lp.ext
    filter_upwards [brownianAdaptedContinuousMultiplierAmbient_coe
      (brownianSquareProcess_measurable hjoint T)
      (brownianAdaptedContinuousMultiplier_cutoff_bound hb T)
      (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)),
      brownianAEContinuousMultiplier_coe hB hBm hH hjoint hb hcont f, hsupport]
      with p hc hr hs
    rw [hc, hr]
    by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
    · change ((Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * H p.1.toNNReal p.2) * _ = _
      rw [Set.indicator_of_mem hp, one_mul]
    · have hw : p ∉ brownianTimeWindow 0 T := hp
      rw [Set.indicator_of_notMem hw] at hs
      rw [hs, mul_zero, mul_zero]
  apply tendsto_subtype_rng.mpr
  simpa only [he, ht] using hlim

theorem brownianAEContinuousProductStepIntegral_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (H t) P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (T : ℝ≥0)
    (f : brownianIntegralSpace B hBm P) (hf : brownianTimeCutoff B hBm P T f = f) :
    Tendsto (fun n => brownianIntegral hB (brownianAEContinuousProductStep hBm hH M T n f)) atTop
      (𝓝 (brownianIntegral hB (brownianAEContinuousMultiplier hB hBm hH hjoint hb hcont f))) :=
  (brownianIntegral hB).continuous.continuousAt.tendsto.comp
    (brownianAEContinuousProductStep_tendsto hB hBm hH hjoint hb hcont T f hf)

end TimeTraps.Probability

end
