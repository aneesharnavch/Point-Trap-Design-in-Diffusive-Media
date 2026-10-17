module

public import TimeTraps.Probability.BrownianIntegralMartingaleIncrements
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-! Strong continuity of the actual product-L² cutoff. Away from the
null time slice at the limiting time, its pointwise indicator is locally
constant. The square of its difference is dominated by the original
integrable square, including at time zero. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem brownianTimePast_indicator_eventually (f : ℝ × Ω → ℝ) {t : ℝ≥0}
    {p : ℝ × Ω} (hp : p.1 ≠ t.val) :
    ∀ᶠ s in 𝓝 t, (brownianTimePast s).indicator f p = (brownianTimePast t).indicator f p := by
  have hv : Tendsto (fun s : ℝ≥0 => s.val) (𝓝 t) (𝓝 t.val) :=
    continuous_subtype_val.continuousAt
  rcases lt_or_gt_of_ne hp with hlt | hgt
  · filter_upwards [hv.eventually (lt_mem_nhds hlt)] with s hs
    have hps : p ∈ brownianTimePast s := hs.le
    have hpt : p ∈ brownianTimePast t := hlt.le
    rw [indicator_of_mem hps, indicator_of_mem hpt]
  · filter_upwards [hv.eventually (gt_mem_nhds hgt)] with s hs
    have hps : p ∉ brownianTimePast s := not_le.mpr hs
    have hpt : p ∉ brownianTimePast t := not_le.mpr hgt
    rw [indicator_of_notMem hps, indicator_of_notMem hpt]

theorem brownianTimePast_indicator_sub_sq_bound (f : ℝ × Ω → ℝ)
    (s t : ℝ≥0) (p : ℝ × Ω) :
    ‖((brownianTimePast s).indicator f p - (brownianTimePast t).indicator f p) ^ 2‖ ≤ f p ^ 2 := by
  by_cases hs : p ∈ brownianTimePast s <;> by_cases ht : p ∈ brownianTimePast t <;>
    simp [hs, ht, norm_pow, Real.norm_eq_abs, sq_abs, sq_nonneg]

theorem brownianTimePast_indicator_sub_sq_tendsto (P : Measure Ω)
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) (t : ℝ≥0) :
    Tendsto (fun s => ∫ p, ((brownianTimePast s).indicator f p -
      (brownianTimePast t).indicator f p) ^ 2 ∂volume.prod P) (𝓝 t) (𝓝 0) := by
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ t.val := by simp [ae_iff]
  have hlim : ∀ᵐ p : ℝ × Ω ∂(volume : Measure ℝ).prod P,
      Tendsto (fun s => ((brownianTimePast s).indicator f p -
        (brownianTimePast t).indicator f p) ^ 2) (𝓝 t) (𝓝 (0 : ℝ)) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := P)).ae hne]
      with p hp
    have he : (fun s => ((brownianTimePast s).indicator f p -
        (brownianTimePast t).indicator f p) ^ 2) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [brownianTimePast_indicator_eventually (f : ℝ × Ω → ℝ) hp] with s hs
      rw [hs, sub_self, zero_pow (by norm_num)]
    exact (tendsto_congr' he).mpr tendsto_const_nhds
  have h := tendsto_integral_filter_of_dominated_convergence
    (F := fun s p => ((brownianTimePast s).indicator f p -
      (brownianTimePast t).indicator f p) ^ 2) (f := fun _ => (0 : ℝ))
    (μ := (volume : Measure ℝ).prod P) (fun p => f p ^ 2)
    (Eventually.of_forall (fun s =>
      (((Lp.memLp f).1.indicator (brownianTimePast_measurable s)).sub
        ((Lp.memLp f).1.indicator (brownianTimePast_measurable t))).pow 2))
    (Eventually.of_forall (fun s => Eventually.of_forall
      (brownianTimePast_indicator_sub_sq_bound (f : ℝ × Ω → ℝ) s t)))
    (Lp.memLp f).integrable_sq hlim
  simpa only [integral_zero] using h

theorem brownianTimeCutoffAmbient_sub_norm_sq (P : Measure Ω)
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) (s t : ℝ≥0) :
    ‖brownianTimeCutoffAmbient P s f - brownianTimeCutoffAmbient P t f‖ ^ 2 =
      ∫ p, ((brownianTimePast s).indicator f p - (brownianTimePast t).indicator f p) ^ 2
        ∂volume.prod P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (brownianTimeCutoffAmbient P s f)
    (brownianTimeCutoffAmbient P t f), brownianTimeCutoffAmbient_coe P s f,
    brownianTimeCutoffAmbient_coe P t f] with p hsub hs ht
  rw [Real.inner_apply, hsub, Pi.sub_apply, hs, ht, pow_two]

theorem brownianTimeCutoffAmbient_continuous (P : Measure Ω)
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :
    Continuous (fun t => brownianTimeCutoffAmbient P t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun s =>
      ‖brownianTimeCutoffAmbient P s f - brownianTimeCutoffAmbient P t f‖ ^ 2)
      (𝓝 t) (𝓝 (0 : ℝ)) := by
    simpa only [brownianTimeCutoffAmbient_sub_norm_sq] using
      brownianTimePast_indicator_sub_sq_tendsto P f t
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

end TimeTraps.Probability
