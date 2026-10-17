module

public import TimeTraps.Probability.BrownianIntegralPastMultiplierStep

@[expose] public section

/-! Left dyadic association converges to the actual continuous-process
multiplier. Finite support is expressed by equality to the existing time
cutoff and supplies the domination argument's exact limiting coefficient. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B H : ℝ≥0 → Ω → ℝ}
variable {P : Measure Ω} {M : ℝ≥0}

def brownianAdaptedContinuousProductStep (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (n : ℕ)
    (f : brownianIntegralSpace B hBm P) : brownianIntegralSpace B hBm P :=
  brownianPastStepIntegrand (brownianDyadicGrid T n) (brownianDyadicGrid_monotone T n)
    (fun i => H (brownianDyadicGrid T n i.castSucc))
    (fun i => hH (brownianDyadicGrid T n i.castSucc))
    (fun i => hb (brownianDyadicGrid T n i.castSucc)) f

theorem brownianAdaptedContinuousProductStep_coe (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (n : ℕ)
    (f : brownianIntegralSpace B hBm P) :
    ((brownianAdaptedContinuousProductStep hBm hH hb T n f : brownianIntegralSpace B hBm P) :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      (fun p => brownianSquareStepProcess H T n p * (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p) :=
  brownianPastStepIntegrand_coe _ _ _ _ _ _

theorem brownianAdaptedContinuousProductStep_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (T : ℝ≥0)
    (f : brownianIntegralSpace B hBm P) (hf : brownianTimeCutoff B hBm P T f = f) :
    Tendsto (fun n => brownianAdaptedContinuousProductStep hBm hH hb T n f) atTop
      (𝓝 (brownianAdaptedContinuousMultiplier hB hBm hH hjoint hb hcont f)) := by
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
      ((brownianAdaptedContinuousProductStep hBm hH hb T n f : brownianIntegralSpace B hBm P) :
        Lp ℝ 2 ((volume : Measure ℝ).prod P)) := by
    apply Lp.ext
    exact (brownianAdaptedContinuousMultiplierAmbient_coe _ _ _).trans
      (brownianAdaptedContinuousProductStep_coe hBm hH hb T n f).symm
  have hsupport := brownianTimeCutoff_sub_coe (show (0 : ℝ≥0) ≤ T from zero_le) f
  rw [hf, brownianTimeCutoff_zero] at hsupport
  change ((f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) - 0 :
    Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P] _ at hsupport
  rw [sub_zero] at hsupport
  have ht : brownianAdaptedContinuousMultiplierAmbient
      (brownianSquareProcess_measurable hjoint T)
      (brownianAdaptedContinuousMultiplier_cutoff_bound hb T)
      (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =
      (brownianAdaptedContinuousMultiplier hB hBm hH hjoint hb hcont f :
        Lp ℝ 2 ((volume : Measure ℝ).prod P)) := by
    apply Lp.ext
    filter_upwards [brownianAdaptedContinuousMultiplierAmbient_coe
      (brownianSquareProcess_measurable hjoint T)
      (brownianAdaptedContinuousMultiplier_cutoff_bound hb T)
      (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)),
      brownianAdaptedContinuousMultiplier_coe hB hBm hH hjoint hb hcont f, hsupport]
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

theorem brownianAdaptedContinuousProductStepIntegral_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (T : ℝ≥0)
    (f : brownianIntegralSpace B hBm P) (hf : brownianTimeCutoff B hBm P T f = f) :
    Tendsto (fun n => brownianIntegral hB (brownianAdaptedContinuousProductStep hBm hH hb T n f)) atTop
      (𝓝 (brownianIntegral hB (brownianAdaptedContinuousMultiplier hB hBm hH hjoint hb hcont f))) :=
  (brownianIntegral hB).continuous.continuousAt.tendsto.comp
    (brownianAdaptedContinuousProductStep_tendsto hB hBm hH hjoint hb hcont T f hf)

end TimeTraps.Probability

end
