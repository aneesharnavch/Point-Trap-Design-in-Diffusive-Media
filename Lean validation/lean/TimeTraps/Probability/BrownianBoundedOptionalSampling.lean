module

public import TimeTraps.Probability.BrownianBoundedOptionalSamplingApproximation

@[expose] public section

/-! Bounded optional sampling for the actual continuous integral in the
completed, right-continuous Brownian filtration. Arbitrary finite-valued
stopping times are approached from above by the proved countable grids. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable (f : BrownianIntegrand) {τ : BrownianCompletedSample → ℝ≥0} {T : ℝ≥0}

theorem brownianCompletedIntegralPath_stopped_stronglyMeasurable
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    StronglyMeasurable[hτ.measurableSpace] (fun ω => brownianCompletedIntegralPath f (τ ω) ω) := by
  have hp := (brownianCompletedIntegralPath_rightCont_stronglyAdapted f).isStronglyProgressive_of_continuous
    (brownianCompletedIntegralPath_continuous f)
  exact (measurable_stoppedValue hp hτ).stronglyMeasurable

theorem brownianCompletedIntegralPath_stopped_integrable
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) (hbound : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω => brownianCompletedIntegralPath f (τ ω) ω) brownianCompletedMeasure := by
  apply (brownianCompletedIntegralPath_compact_bound_integrable f T).mono'
    ((brownianCompletedIntegralPath_stopped_stronglyMeasurable f hτ).mono
      hτ.measurableSpace_le).aestronglyMeasurable
  exact Eventually.of_forall (fun ω =>
    (brownianIntegralGlobalCompactPath f T ω).norm_coe_le_norm ⟨τ ω, ⟨bot_le, hbound ω⟩⟩)

theorem brownianCompletedIntegralPath_stopped_setIntegral
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) (hbound : ∀ ω, τ ω ≤ T)
    {A : Set BrownianCompletedSample} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ ω in A, brownianCompletedIntegralPath f (τ ω) ω ∂brownianCompletedMeasure) =
      ∫ ω in A, brownianCompletedIntegralPath f T ω ∂brownianCompletedMeasure := by
  let τn : ℕ → BrownianCompletedSample → ℝ≥0 := fun n ω => boundedStoppingUpperGrid n (τ ω)
  have hstop (n : ℕ) : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τn n ω : WithTop ℝ≥0)) := boundedStoppingUpperGrid_isStoppingTime hτ n
  have hbn (n : ℕ) (ω : BrownianCompletedSample) : τn n ω ≤ T + 1 :=
    boundedStoppingUpperGrid_le_bound hbound n ω
  have hbn' (n : ℕ) (ω : BrownianCompletedSample) : (τn n ω : WithTop ℝ≥0) ≤ (T + 1 : ℝ≥0) := by
    exact_mod_cast hbn n ω
  have hn_eq (n : ℕ) :
      (∫ ω in A, brownianCompletedIntegralPath f (τn n ω) ω ∂brownianCompletedMeasure) =
        ∫ ω in A, brownianCompletedIntegralPath f (T + 1) ω ∂brownianCompletedMeasure := by
    have hle : (fun ω => (τ ω : WithTop ℝ≥0)) ≤ (fun ω => (τn n ω : WithTop ℝ≥0)) := by
      intro ω
      change (τ ω : WithTop ℝ≥0) ≤ (boundedStoppingUpperGrid n (τ ω) : WithTop ℝ≥0)
      exact_mod_cast (boundedStoppingUpperGrid_bounds n (τ ω)).1
    have hAn := hτ.measurableSpace_mono (hstop n) hle A hA
    have hs := (brownianCompletedIntegralPath_rightCont_martingale f).stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hstop n) (hbn' n)
        (boundedStoppingUpperGrid_countable_range τ n)
    have hs' : (fun ω => brownianCompletedIntegralPath f (τn n ω) ω) =ᵐ[brownianCompletedMeasure]
        brownianCompletedMeasure[brownianCompletedIntegralPath f (T + 1) | (hstop n).measurableSpace] := by
      exact hs
    exact (integral_congr_ae (hs'.filter_mono ae_restrict_le)).trans
      (setIntegral_condExp (hstop n).measurableSpace_le
        (brownianCompletedIntegralPath_integrable f (T + 1)) hAn)
  have hlim : Tendsto
      (fun n => ∫ ω in A, brownianCompletedIntegralPath f (τn n ω) ω ∂brownianCompletedMeasure)
      atTop (𝓝 (∫ ω in A, brownianCompletedIntegralPath f (τ ω) ω ∂brownianCompletedMeasure)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun ω : BrownianCompletedSample => ‖brownianIntegralGlobalCompactPath f (T + 1) ω‖)
    · intro n
      exact (brownianCompletedIntegralPath_stopped_integrable f (hstop n) (hbn n)).aestronglyMeasurable.restrict
    · exact (brownianCompletedIntegralPath_compact_bound_integrable f (T + 1)).integrableOn
    · intro n
      exact Eventually.of_forall (fun ω => (brownianIntegralGlobalCompactPath f (T + 1) ω).norm_coe_le_norm ⟨τn n ω, ⟨bot_le, hbn n ω⟩⟩)
    · exact Eventually.of_forall (fun ω =>
        (brownianCompletedIntegralPath_continuous f ω).continuousAt.tendsto.comp
          (boundedStoppingUpperGrid_tendsto (τ ω)))
  have he := tendsto_nhds_unique hlim (tendsto_const_nhds.congr (fun n => (hn_eq n).symm))
  have hbound' (ω : BrownianCompletedSample) : (τ ω : WithTop ℝ≥0) ≤ T := by
    exact_mod_cast hbound ω
  have hAT := hτ.measurableSpace_le_of_le_const hbound' A hA
  exact he.trans ((brownianCompletedIntegralPath_rightCont_martingale f).setIntegral_eq
    (show T ≤ T + 1 by simp) hAT).symm

theorem brownianCompletedIntegralPath_optionalSampling
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) (hbound : ∀ ω, τ ω ≤ T) :
    brownianCompletedMeasure[brownianCompletedIntegralPath f T | hτ.measurableSpace]
      =ᵐ[brownianCompletedMeasure] (fun ω => brownianCompletedIntegralPath f (τ ω) ω) := by
  apply (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le
    (brownianCompletedIntegralPath_integrable f T) _ _
    (brownianCompletedIntegralPath_stopped_stronglyMeasurable f hτ).aestronglyMeasurable).symm
  · intro A _ _
    exact (brownianCompletedIntegralPath_stopped_integrable f hτ hbound).integrableOn
  · intro A hA _
    exact brownianCompletedIntegralPath_stopped_setIntegral f hτ hbound hA

end TimeTraps.Probability
