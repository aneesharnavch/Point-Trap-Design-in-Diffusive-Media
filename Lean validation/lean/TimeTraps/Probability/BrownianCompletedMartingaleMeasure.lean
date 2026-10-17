module

public import TimeTraps.Probability.ReflectedPositiveTimeChangeStopping
public import TimeTraps.Probability.BrownianIntegralContinuousGlobalCompact

@[expose] public section

/-! Transport of integrable functions and their integrals to the actual
completed measure. The identity map has the original measure as its
pushforward; no measurable embedding in the reverse direction is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)

theorem completedMeasure_identity_preserving :
    @MeasurePreserving (NullMeasurableSpace Ω P) Ω _ mΩ
      (fun ω => ω) P.completion P := by
  have hm : @Measurable (NullMeasurableSpace Ω P) Ω _ mΩ (fun ω => ω) :=
    fun _ hs => hs.nullMeasurableSet
  refine ⟨hm, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hm hs]
  rfl

theorem completedMeasure_probability [IsProbabilityMeasure P] :
    IsProbabilityMeasure P.completion :=
  ⟨measure_univ (μ := P)⟩

theorem completedMeasure_integrable {f : Ω → ℝ} (hf : Integrable f P) :
    Integrable (fun ω : NullMeasurableSpace Ω P => f ω) P.completion :=
  (completedMeasure_identity_preserving P).integrable_comp_of_integrable hf

theorem completedMeasure_integral {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) :
    (∫ ω : NullMeasurableSpace Ω P, f ω ∂P.completion) = ∫ ω, f ω ∂P := by
  have hp := completedMeasure_identity_preserving P
  have hm : AEStronglyMeasurable f
      (@Measure.map (NullMeasurableSpace Ω P) Ω _ mΩ (fun ω => ω) P.completion) := by
    rw [hp.map_eq]
    exact hf
  exact (hp.map_eq ▸ integral_map hp.measurable.aemeasurable hm).symm

theorem completedMeasure_setIntegral {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    {s : Set Ω} (hs : MeasurableSet s) :
    (∫ ω : NullMeasurableSpace Ω P in (fun ω : NullMeasurableSpace Ω P => (ω : Ω)) ⁻¹' s, f ω ∂P.completion) = ∫ ω in s, f ω ∂P := by
  have hsc : MeasurableSet ((fun ω : NullMeasurableSpace Ω P => (ω : Ω)) ⁻¹' s) :=
    (completedMeasure_identity_preserving P).measurable hs
  calc
    _ = ∫ ω : NullMeasurableSpace Ω P, s.indicator f ω ∂P.completion :=
      (integral_indicator (μ := P.completion) (f := fun ω : NullMeasurableSpace Ω P => f ω) hsc).symm
    _ = ∫ ω, s.indicator f ω ∂P := completedMeasure_integral P (hf.indicator hs)
    _ = _ := integral_indicator hs

end TimeTraps.Probability
