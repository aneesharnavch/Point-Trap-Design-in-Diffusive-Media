module

public import TimeTraps.Probability.BrownianCompletedMartingaleMeasure

@[expose] public section

/-! The actual continuous Brownian integral is a martingale on the
explicit ambient-null augmentation of the original Brownian filtration.
Its sample values are unchanged by the change of measurable space. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

abbrev BrownianCompletedSample := NullMeasurableSpace (ℕ → ℝ) brownianDyadicMeasure

def brownianCompletedMeasure : Measure BrownianCompletedSample := brownianDyadicMeasure.completion

instance brownianCompletedMeasure_probability : IsProbabilityMeasure brownianCompletedMeasure :=
  completedMeasure_probability brownianDyadicMeasure

def brownianCompletedFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace BrownianCompletedSample) :=
  positiveTimeChangeCompletedFiltration brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure

def brownianCompletedIntegralPath (f : BrownianIntegrand) (t : ℝ≥0)
    (ω : BrownianCompletedSample) : ℝ := brownianIntegralGlobalPath f t ω

theorem brownianCompletedIntegralPath_stronglyAdapted (f : BrownianIntegrand) :
    StronglyAdapted brownianCompletedFiltration (brownianCompletedIntegralPath f) := by
  intro t
  have h := brownianIntegralGlobalPath_raw_aestronglyMeasurable f t
  exact (h.stronglyMeasurable_mk.measurable.eventuallyMeasurable_of_eventuallyEq
    h.ae_eq_mk).stronglyMeasurable

theorem brownianCompletedIntegralPath_integrable (f : BrownianIntegrand) (t : ℝ≥0) :
    Integrable (brownianCompletedIntegralPath f t) brownianCompletedMeasure := by
  apply completedMeasure_integrable brownianDyadicMeasure
  exact ((brownianStochasticIntegralProcess_martingale f).integrable t).congr
    (brownianIntegralGlobalPath_martingale_ae f t).symm

theorem brownianCompletedIntegralPath_setIntegral (f : BrownianIntegrand)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set BrownianCompletedSample}
    (hA : MeasurableSet[brownianCompletedFiltration s] A) :
    (∫ ω in A, brownianCompletedIntegralPath f s ω ∂brownianCompletedMeasure) =
      ∫ ω in A, brownianCompletedIntegralPath f t ω ∂brownianCompletedMeasure := by
  obtain ⟨C, hC, he⟩ := hA
  have hCm := brownianFiltration.le s C hC
  have hec : A =ᵐ[brownianCompletedMeasure] C := he
  rw [setIntegral_congr_set hec, setIntegral_congr_set hec]
  calc
    _ = ∫ ω in C, brownianIntegralGlobalPath f s ω ∂brownianDyadicMeasure :=
      completedMeasure_setIntegral brownianDyadicMeasure
        (brownianIntegralGlobalPath_measurable f s).aestronglyMeasurable hCm
    _ = ∫ ω in C, brownianStochasticIntegralProcess f s ω ∂brownianDyadicMeasure :=
      integral_congr_ae ((brownianIntegralGlobalPath_martingale_ae f s).filter_mono ae_restrict_le)
    _ = ∫ ω in C, brownianStochasticIntegralProcess f t ω ∂brownianDyadicMeasure :=
      (brownianStochasticIntegralProcess_martingale f).setIntegral_eq hst hC
    _ = ∫ ω in C, brownianIntegralGlobalPath f t ω ∂brownianDyadicMeasure := integral_congr_ae
      ((brownianIntegralGlobalPath_martingale_ae f t).symm.filter_mono ae_restrict_le)
    _ = _ := (completedMeasure_setIntegral brownianDyadicMeasure
      (brownianIntegralGlobalPath_measurable f t).aestronglyMeasurable hCm).symm

theorem brownianCompletedIntegralPath_condExp (f : BrownianIntegrand)
    {s t : ℝ≥0} (hst : s ≤ t) :
    brownianCompletedMeasure[brownianCompletedIntegralPath f t | brownianCompletedFiltration s]
      =ᵐ[brownianCompletedMeasure] brownianCompletedIntegralPath f s := by
  apply (ae_eq_condExp_of_forall_setIntegral_eq (brownianCompletedFiltration.le s)
    (brownianCompletedIntegralPath_integrable f t) _ _
    (brownianCompletedIntegralPath_stronglyAdapted f s).aestronglyMeasurable).symm
  · intro A _ _
    exact (brownianCompletedIntegralPath_integrable f s).integrableOn
  · intro A hA _
    exact brownianCompletedIntegralPath_setIntegral f hst hA

theorem brownianCompletedIntegralPath_martingale (f : BrownianIntegrand) :
    Martingale (brownianCompletedIntegralPath f) brownianCompletedFiltration brownianCompletedMeasure :=
  ⟨brownianCompletedIntegralPath_stronglyAdapted f,
    fun _ _ hst => brownianCompletedIntegralPath_condExp f hst⟩

end TimeTraps.Probability

end
