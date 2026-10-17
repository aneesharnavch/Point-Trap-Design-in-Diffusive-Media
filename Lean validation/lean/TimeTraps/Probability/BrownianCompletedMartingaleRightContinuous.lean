module

public import TimeTraps.Probability.BrownianCompletedMartingale
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Right-continuous augmentation for the actual continuous integral.
Conditional identities follow by taking times down to the conditioning
time, dominated by the proved integrable compact path supremum. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem brownianCompletedIntegralPath_continuous (f : BrownianIntegrand)
    (ω : BrownianCompletedSample) : Continuous (fun t => brownianCompletedIntegralPath f t ω) :=
  brownianIntegralGlobalPath_continuous f ω

theorem brownianCompletedIntegralPath_compact_bound_integrable (f : BrownianIntegrand) (T : ℝ≥0) :
    Integrable (fun ω : BrownianCompletedSample => ‖brownianIntegralGlobalCompactPath f T ω‖)
      brownianCompletedMeasure :=
  completedMeasure_integrable brownianDyadicMeasure
    ((brownianIntegralGlobalCompactPath_memLp f T).norm.integrable (by norm_num))

theorem brownianCompletedIntegralPath_setIntegral_tendsto_right (f : BrownianIntegrand)
    {s t : ℝ≥0} (hst : s < t) (A : Set BrownianCompletedSample) :
    Tendsto (fun u => ∫ ω in A, brownianCompletedIntegralPath f u ω ∂brownianCompletedMeasure)
      (𝓝[>] s) (𝓝 (∫ ω in A, brownianCompletedIntegralPath f s ω ∂brownianCompletedMeasure)) := by
  have hb : ∀ᶠ u in 𝓝[>] s, u ≤ t :=
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hst)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun ω : BrownianCompletedSample => ‖brownianIntegralGlobalCompactPath f t ω‖)
  · exact Eventually.of_forall (fun u =>
      (brownianCompletedIntegralPath_integrable f u).aestronglyMeasurable.restrict)
  · filter_upwards [hb] with u hu
    exact Eventually.of_forall (fun ω =>
      (brownianIntegralGlobalCompactPath f t ω).norm_coe_le_norm ⟨u, ⟨bot_le, hu⟩⟩)
  · exact (brownianCompletedIntegralPath_compact_bound_integrable f t).integrableOn
  · exact Eventually.of_forall (fun ω =>
      (brownianCompletedIntegralPath_continuous f ω).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)

theorem brownianCompletedIntegralPath_rightCont_stronglyAdapted (f : BrownianIntegrand) :
    StronglyAdapted brownianCompletedFiltration.rightCont (brownianCompletedIntegralPath f) :=
  fun s => (brownianCompletedIntegralPath_stronglyAdapted f s).mono
    (brownianCompletedFiltration.le_rightCont s)

theorem brownianCompletedIntegralPath_rightCont_setIntegral (f : BrownianIntegrand)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set BrownianCompletedSample}
    (hA : MeasurableSet[brownianCompletedFiltration.rightCont s] A) :
    (∫ ω in A, brownianCompletedIntegralPath f s ω ∂brownianCompletedMeasure) =
      ∫ ω in A, brownianCompletedIntegralPath f t ω ∂brownianCompletedMeasure := by
  rcases hst.eq_or_lt with rfl | hst
  · rfl
  have he : ∀ᶠ u in 𝓝[>] s,
      (∫ ω in A, brownianCompletedIntegralPath f u ω ∂brownianCompletedMeasure) =
        ∫ ω in A, brownianCompletedIntegralPath f t ω ∂brownianCompletedMeasure := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hst)] with u hsu hut
    have hle : brownianCompletedFiltration.rightCont s ≤ brownianCompletedFiltration u := by
      rw [Filtration.rightCont_eq]
      exact iInf_le_of_le u (iInf_le _ hsu)
    exact brownianCompletedIntegralPath_setIntegral f hut (hle A hA)
  exact tendsto_nhds_unique (brownianCompletedIntegralPath_setIntegral_tendsto_right f hst A)
    (tendsto_const_nhds.congr' (he.mono (fun _ h => h.symm)))

theorem brownianCompletedIntegralPath_rightCont_condExp (f : BrownianIntegrand)
    {s t : ℝ≥0} (hst : s ≤ t) :
    brownianCompletedMeasure[brownianCompletedIntegralPath f t | brownianCompletedFiltration.rightCont s]
      =ᵐ[brownianCompletedMeasure] brownianCompletedIntegralPath f s := by
  apply (ae_eq_condExp_of_forall_setIntegral_eq (brownianCompletedFiltration.rightCont.le s)
    (brownianCompletedIntegralPath_integrable f t) _ _
    (brownianCompletedIntegralPath_rightCont_stronglyAdapted f s).aestronglyMeasurable).symm
  · intro A _ _
    exact (brownianCompletedIntegralPath_integrable f s).integrableOn
  · intro A hA _
    exact brownianCompletedIntegralPath_rightCont_setIntegral f hst hA

theorem brownianCompletedIntegralPath_rightCont_martingale (f : BrownianIntegrand) :
    Martingale (brownianCompletedIntegralPath f) brownianCompletedFiltration.rightCont
      brownianCompletedMeasure :=
  ⟨brownianCompletedIntegralPath_rightCont_stronglyAdapted f,
    fun _ _ hst => brownianCompletedIntegralPath_rightCont_condExp f hst⟩

end TimeTraps.Probability
