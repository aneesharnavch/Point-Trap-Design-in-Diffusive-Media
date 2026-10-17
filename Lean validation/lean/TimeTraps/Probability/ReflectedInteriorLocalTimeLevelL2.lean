module

public import TimeTraps.Probability.ReflectedInteriorLocalTimeLevelProcess
public import TimeTraps.Probability.ReflectedInteriorKinkIntegrandPath

@[expose] public section

/-! Level continuity holds in the actual closed integrand space and in
L2 of continuous compact-time paths, using the proved maximal extension. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem reflectedInteriorKinkIntegrand_process_ae (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    (reflectedInteriorKinkIntegrand hB hBm hjoint L hL a ha x hσ T : Lp ℝ 2 (volume.prod P))
      =ᵐ[volume.prod P] reflectedInteriorKinkProcess B L a x σ T := by
  apply (reflectedInteriorKinkIntegrand_coe hB hBm hjoint L hL a ha x hσ T).trans
  apply Eventually.of_forall
  intro p
  unfold reflectedInteriorKinkProcess brownianSquareProcess reflectedInteriorKinkCoefficient
    reflectedInteriorTanakaSlope
  ring

theorem reflectedInteriorKinkIntegrand_level_tendsto (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) {u : ℕ → ℝ} {a : ℝ} (huI : ∀ n, u n ∈ Ioo 0 L)
    (ha : a ∈ Ioo 0 L) (hu : Tendsto u atTop (𝓝 a)) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Tendsto (fun n => reflectedInteriorKinkIntegrand hB hBm hjoint L hL (u n) (huI n) x hσ T)
      atTop (𝓝 (reflectedInteriorKinkIntegrand hB hBm hjoint L hL a ha x hσ T)) := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  let hF (b : ℝ) := reflectedInteriorKinkProcess_memLp (P := P) hjoint L hL b x hσ T
  have hdom : MemLp (fun p : ℝ × Ω => σ * brownianIntervalIndicator 0 T p.1) 2 (volume.prod P) := by
    have hm := brownianElementaryProcess_memLp (P := P) 0 T
      (show Measurable (fun _ : Ω => σ) from measurable_const) (memLp_const σ)
    change MemLp (fun p : ℝ × Ω => brownianIntervalIndicator 0 T p.1 * σ) 2 (volume.prod P) at hm
    convert hm using 1
    funext p
    exact mul_comm _ _
  have ht := brownianPredictableDensity_toLp_tendsto (fun n => hF (u n)) (hF a) hdom
    (fun n => Eventually.of_forall (reflectedInteriorKinkProcess_bound L hL (u n) x hσ T))
    (Eventually.of_forall (reflectedInteriorKinkProcess_bound L hL a x hσ T))
    (reflectedInteriorKinkProcess_level_tendsto_ae hB.toIsPreBrownianReal hjoint L hL ha hu x hσ T)
  have he (b : ℝ) (hb : b ∈ Ioo 0 L) : (hF b).toLp (reflectedInteriorKinkProcess B L b x σ T) =
      (reflectedInteriorKinkIntegrand hB hBm hjoint L hL b hb x hσ T : Lp ℝ 2 (volume.prod P)) := by
    apply Lp.ext
    exact (hF b).coeFn_toLp.trans
      (reflectedInteriorKinkIntegrand_process_ae hB hBm hjoint L hL b hb x hσ T).symm
  apply tendsto_subtype_rng.mpr
  simpa only [he a ha, fun n => he (u n) (huI n)] using ht

theorem reflectedInteriorKinkIntegrand_level_continuous (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Continuous (fun a : Ioo (0 : ℝ) L =>
      reflectedInteriorKinkIntegrand hB hBm hjoint L hL a.val a.property x hσ T) := by
  apply continuous_iff_seqContinuous.mpr
  intro u a hu
  exact reflectedInteriorKinkIntegrand_level_tendsto hB hBm hjoint L hL
    (fun n => (u n).property) a.property (continuous_subtype_val.tendsto a |>.comp hu) x hσ T

theorem reflectedInteriorKinkCompactL2_level_continuous (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Continuous (fun a : Ioo (0 : ℝ) L => brownianIntegralContinuousL2 T
      (reflectedInteriorKinkIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable L hL a.val a.property x hσ T)) :=
  (brownianIntegralContinuousL2 T).continuous.comp
    (reflectedInteriorKinkIntegrand_level_continuous brownianDyadicPath_isBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL x hσ T)

end TimeTraps.Probability
