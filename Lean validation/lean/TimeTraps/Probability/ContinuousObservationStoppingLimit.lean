module

public import TimeTraps.Probability.ContinuousObservationStoppingCountable

@[expose] public section

/-! Continuous bounded observations pass from the genuine upper stopping
grids to every finite-valued stopping time by dominated convergence. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}

theorem continuousObservation_upper_setIntegral_tendsto (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℝ≥0 → Ω → ℝ) (hX : StronglyAdapted ℱ X)
    (hc : ∀ ω, Continuous (fun t => X t ω)) {C : ℝ} (hb : ∀ t ω, ‖X t ω‖ ≤ C)
    (h : ℝ≥0) {τ : Ω → ℝ≥0} (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω) :
    Tendsto (fun n => ∫ ω in A, X (boundedStoppingUpperGrid n (τ ω) + h) ω ∂μ)
      atTop (𝓝 (∫ ω in A, X (τ ω + h) ω ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => C)
  · intro n
    exact (continuousObservation_stopped_integrable μ X hX hc hb
      (finiteStoppingTime_add (boundedStoppingUpperGrid_isStoppingTime hτ n) h)).aestronglyMeasurable.restrict
  · exact integrable_const _
  · exact fun n => Eventually.of_forall (fun ω => hb _ ω)
  · exact Eventually.of_forall (fun ω => (hc ω).continuousAt.tendsto.comp
      ((boundedStoppingUpperGrid_tendsto (τ ω)).add_const h))

theorem continuousObservation_stopping_setIntegral (μ : Measure Ω) [IsFiniteMeasure μ]
    (F G : ℝ≥0 → Ω → ℝ) (hF : StronglyAdapted ℱ F) (hG : StronglyAdapted ℱ G)
    (hcF : ∀ ω, Continuous (fun t => F t ω)) (hcG : ∀ ω, Continuous (fun t => G t ω))
    {CF CG : ℝ} (hbF : ∀ t ω, ‖F t ω‖ ≤ CF) (hbG : ∀ t ω, ‖G t ω‖ ≤ CG)
    (h : ℝ≥0)
    (hdet : ∀ s, ∀ A : Set Ω, MeasurableSet[ℱ s] A →
      (∫ ω in A, G s ω ∂μ) = ∫ ω in A, F (s + h) ω ∂μ)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ ω in A, G (τ ω) ω ∂μ) = ∫ ω in A, F (τ ω + h) ω ∂μ := by
  have he (n : ℕ) : (∫ ω in A, G (boundedStoppingUpperGrid n (τ ω)) ω ∂μ) =
      ∫ ω in A, F (boundedStoppingUpperGrid n (τ ω) + h) ω ∂μ := by
    have hstop := boundedStoppingUpperGrid_isStoppingTime hτ n
    have hle : (fun ω => (τ ω : WithTop ℝ≥0)) ≤
        (fun ω => (boundedStoppingUpperGrid n (τ ω) : WithTop ℝ≥0)) :=
      fun ω => WithTop.coe_le_coe.mpr (boundedStoppingUpperGrid_bounds n (τ ω)).1
    have hc : (range (fun ω => boundedStoppingUpperGrid n (τ ω))).Countable := by
      apply (countable_range (fun k : ℕ => (k : ℝ≥0) / ((n : ℝ≥0) + 1))).mono
      rintro _ ⟨ω, rfl⟩
      exact ⟨⌈τ ω * ((n : ℝ≥0) + 1)⌉₊, rfl⟩
    exact continuousObservation_countable_setIntegral μ F G hF hG hcF hcG hbF hbG h hdet hstop hc
      (hτ.measurableSpace_mono hstop hle A hA)
  have hl := continuousObservation_upper_setIntegral_tendsto μ G hG hcG hbG 0 hτ A
  simp only [add_zero] at hl
  have hr := continuousObservation_upper_setIntegral_tendsto μ F hF hcF hbF h hτ A
  exact tendsto_nhds_unique hl (hr.congr (fun n => (he n).symm))

theorem continuousObservation_stopping_condExp (μ : Measure Ω) [IsFiniteMeasure μ]
    (F G : ℝ≥0 → Ω → ℝ) (hF : StronglyAdapted ℱ F) (hG : StronglyAdapted ℱ G)
    (hcF : ∀ ω, Continuous (fun t => F t ω)) (hcG : ∀ ω, Continuous (fun t => G t ω))
    {CF CG : ℝ} (hbF : ∀ t ω, ‖F t ω‖ ≤ CF) (hbG : ∀ t ω, ‖G t ω‖ ≤ CG)
    (h : ℝ≥0)
    (hdet : ∀ s, ∀ A : Set Ω, MeasurableSet[ℱ s] A →
      (∫ ω in A, G s ω ∂μ) = ∫ ω in A, F (s + h) ω ∂μ)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    μ[fun ω => F (τ ω + h) ω | hτ.measurableSpace] =ᵐ[μ] fun ω => G (τ ω) ω := by
  apply (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le
    (continuousObservation_stopped_integrable μ F hF hcF hbF (finiteStoppingTime_add hτ h))
    (fun _ _ _ => (continuousObservation_stopped_integrable μ G hG hcG hbG hτ).integrableOn)
    (fun _ hA _ => continuousObservation_stopping_setIntegral μ F G hF hG hcF hcG hbF hbG h hdet hτ hA)
    (continuousObservation_stopped_stronglyMeasurable G hG hcG hτ).aestronglyMeasurable).symm

end TimeTraps.Probability
