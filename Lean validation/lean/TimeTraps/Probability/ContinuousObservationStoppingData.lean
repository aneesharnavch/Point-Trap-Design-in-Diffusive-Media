module

public import TimeTraps.Probability.BrownianBoundedOptionalSamplingApproximation

@[expose] public section

/-! Stopped continuous adapted real observations are measurable in the
actual stopping sigma algebra. A uniform observation bound derives their
integrability for every finite-valued stopping time. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}

theorem finiteStoppingTime_add {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) (h : ℝ≥0) :
    IsStoppingTime ℱ (fun ω => ((τ ω + h : ℝ≥0) : WithTop ℝ≥0)) := by
  intro s
  by_cases hs : h ≤ s
  · have he : {ω | ((τ ω + h : ℝ≥0) : WithTop ℝ≥0) ≤ s} =
        {ω | (τ ω : WithTop ℝ≥0) ≤ (s - h : ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe]
      exact (le_tsub_iff_right hs).symm
    rw [he]
    exact (ℱ.mono tsub_le_self) _ (hτ (s - h))
  · have he : {ω | ((τ ω + h : ℝ≥0) : WithTop ℝ≥0) ≤ s} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_empty_iff_false, iff_false]
      exact fun hh => hs ((le_add_of_nonneg_left bot_le).trans hh)
    rw [he]
    exact @MeasurableSet.empty _ (ℱ s)

theorem continuousObservation_stopped_stronglyMeasurable
    (X : ℝ≥0 → Ω → ℝ) (hX : StronglyAdapted ℱ X)
    (hc : ∀ ω, Continuous (fun t => X t ω)) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    StronglyMeasurable[hτ.measurableSpace] (fun ω => X (τ ω) ω) :=
  (measurable_stoppedValue (hX.isStronglyProgressive_of_continuous hc) hτ).stronglyMeasurable

theorem continuousObservation_stopped_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℝ≥0 → Ω → ℝ) (hX : StronglyAdapted ℱ X)
    (hc : ∀ ω, Continuous (fun t => X t ω)) {C : ℝ} (hb : ∀ t ω, ‖X t ω‖ ≤ C)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    Integrable (fun ω => X (τ ω) ω) μ :=
  Integrable.of_bound
    ((continuousObservation_stopped_stronglyMeasurable X hX hc hτ).mono hτ.measurableSpace_le).aestronglyMeasurable
    C (Eventually.of_forall (fun ω => hb (τ ω) ω))

end TimeTraps.Probability
