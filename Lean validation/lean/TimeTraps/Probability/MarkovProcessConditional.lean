module

public import TimeTraps.Probability.MarkovProcessHistoryIntegral
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Process.Filtration

@[expose] public section

/-! Deterministic-time Markov conditional expectations derived solely
from the chronological finite-dimensional laws. Conditioning is on the
entire raw history; bounded signed Borel observations are retained. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal

variable {Ω α : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace α]

theorem process_condExp_of_finite_laws_lt (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : ℝ≥0 → Kernel α α) [∀ t, IsMarkovKernel (K t)] (x : α)
    (X : ℝ≥0 → Ω → α) (hX : ∀ t, Measurable (X t))
    (hLaw : ∀ I : Finset ℝ≥0, μ.map (fun ω (r : I) => X r.val ω) = markovObservationFamily K x I)
    {s t : ℝ≥0} (hst : s < t) (f : α → ℝ) (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C) :
    μ[fun ω => f (X t ω) | processHistorySigma X s] =ᵐ[μ]
      fun ω => ∫ z, f z ∂K (t - s) (X s ω) := by
  have hm : processHistorySigma X s ≤ mΩ := (processHistory_measurable X hX s).comap_le
  have hfi : Integrable (fun ω => f (X t ω)) μ :=
    Integrable.of_bound (hf.comp (hX t)).aestronglyMeasurable C
      (Eventually.of_forall (fun ω => hC (X t ω)))
  have hgi : Integrable (fun ω => ∫ z, f z ∂K (t - s) (X s ω)) μ :=
    Integrable.of_bound (hf.stronglyMeasurable.integral_kernel.comp_measurable (hX s)).aestronglyMeasurable C
      (Eventually.of_forall (fun ω => kernel_integral_bound (K (t - s)) f hC (X s ω)))
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm hfi (fun _ _ _ => hgi.integrableOn) ?_ ?_).symm
  · intro S hS _
    exact (process_history_setIntegral μ K x X hX hLaw hst f hf hC0 hC hS).symm
  · exact (hf.stronglyMeasurable.integral_kernel.comp_measurable
      (processHistory_current_measurable X s)).aestronglyMeasurable

theorem process_condExp_of_finite_laws (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : ℝ≥0 → Kernel α α) [∀ t, IsMarkovKernel (K t)] (hzero : K 0 = Kernel.id) (x : α)
    (X : ℝ≥0 → Ω → α) (hX : ∀ t, Measurable (X t))
    (hLaw : ∀ I : Finset ℝ≥0, μ.map (fun ω (r : I) => X r.val ω) = markovObservationFamily K x I)
    {s t : ℝ≥0} (hst : s ≤ t) (f : α → ℝ) (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C) :
    μ[fun ω => f (X t ω) | processHistorySigma X s] =ᵐ[μ]
      fun ω => ∫ z, f z ∂K (t - s) (X s ω) := by
  rcases lt_or_eq_of_le hst with hst | rfl
  · exact process_condExp_of_finite_laws_lt μ K x X hX hLaw hst f hf hC0 hC
  · have hm : processHistorySigma X s ≤ mΩ := (processHistory_measurable X hX s).comap_le
    have hfm : StronglyMeasurable[processHistorySigma X s] (fun ω => f (X s ω)) :=
      hf.stronglyMeasurable.comp_measurable (processHistory_current_measurable X s)
    have hfi : Integrable (fun ω => f (X s ω)) μ :=
      Integrable.of_bound (hf.comp (hX s)).aestronglyMeasurable C
        (Eventually.of_forall (fun ω => hC (X s ω)))
    rw [condExp_of_stronglyMeasurable hm hfm hfi]
    apply Eventually.of_forall
    intro ω
    change f (X s ω) = ∫ z, f z ∂K (s - s) (X s ω)
    rw [tsub_self, hzero, Kernel.id_apply, integral_dirac' f _ hf.stronglyMeasurable]

theorem process_natural_condExp_of_finite_laws
    [TopologicalSpace α] [TopologicalSpace.MetrizableSpace α] [BorelSpace α]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : ℝ≥0 → Kernel α α) [∀ t, IsMarkovKernel (K t)] (hzero : K 0 = Kernel.id) (x : α)
    (X : ℝ≥0 → Ω → α) (hX : ∀ t, StronglyMeasurable (X t))
    (hLaw : ∀ I : Finset ℝ≥0, μ.map (fun ω (r : I) => X r.val ω) = markovObservationFamily K x I)
    {s t : ℝ≥0} (hst : s ≤ t) (f : α → ℝ) (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C) :
    μ[fun ω => f (X t ω) | Filtration.natural X hX s] =ᵐ[μ]
      fun ω => ∫ z, f z ∂K (t - s) (X s ω) := by
  rw [Filtration.natural_eq_comap]
  exact process_condExp_of_finite_laws μ K hzero x X (fun t => (hX t).measurable) hLaw hst f hf hC0 hC

end TimeTraps.Probability
