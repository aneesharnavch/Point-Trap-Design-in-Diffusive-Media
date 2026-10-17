module

public import TimeTraps.Probability.MarkovProcessFiniteCylinder
public import TimeTraps.Probability.FiniteHistoryIntegralExtension

@[expose] public section

/-! The finite-dimensional transition laws determine the signed
conditional set-integrals on the entire raw past sigma algebra. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

def processHistory (X : ℝ≥0 → Ω → α) (s : ℝ≥0) (ω : Ω) (r : Iic s) : α := X r.val ω

abbrev processHistorySigma (X : ℝ≥0 → Ω → α) (s : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (processHistory X s) inferInstance

theorem processHistory_measurable (X : ℝ≥0 → Ω → α) (hX : ∀ t, Measurable (X t)) (s : ℝ≥0) :
    Measurable (processHistory X s) := measurable_pi_lambda _ (fun r => hX r.val)

omit [MeasurableSpace Ω] in
theorem processHistory_current_measurable (X : ℝ≥0 → Ω → α) (s : ℝ≥0) :
    Measurable[processHistorySigma X s] (X s) :=
  (measurable_pi_apply (⟨s, by simp⟩ : Iic s)).comp (comap_measurable (processHistory X s))

theorem process_history_setIntegral (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : ℝ≥0 → Kernel α α) [∀ t, IsMarkovKernel (K t)] (x : α)
    (X : ℝ≥0 → Ω → α) (hX : ∀ t, Measurable (X t))
    (hLaw : ∀ I : Finset ℝ≥0, μ.map (fun ω (r : I) => X r.val ω) = markovObservationFamily K x I)
    {s t : ℝ≥0} (hst : s < t) (f : α → ℝ) (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C)
    {S : Set Ω} (hS : MeasurableSet[processHistorySigma X s] S) :
    (∫ ω in S, f (X t ω) ∂μ) = ∫ ω in S, (∫ z, f z ∂K (t - s) (X s ω)) ∂μ := by
  have hfi : Integrable (fun ω => f (X t ω)) μ :=
    Integrable.of_bound (hf.comp (hX t)).aestronglyMeasurable C
      (Eventually.of_forall (fun ω => hC (X t ω)))
  have hgi : Integrable (fun ω => ∫ z, f z ∂K (t - s) (X s ω)) μ :=
    Integrable.of_bound (hf.stronglyMeasurable.integral_kernel.comp_measurable (hX s)).aestronglyMeasurable C
      (Eventually.of_forall (fun ω => kernel_integral_bound (K (t - s)) f hC (X s ω)))
  have hu : (∫ ω, f (X t ω) ∂μ) = ∫ ω, (∫ z, f z ∂K (t - s) (X s ω)) ∂μ := by
    have h := process_indexed_past_setIntegral μ K x X hX hLaw (∅ : Finset ℝ≥0) id
      (s := s) (by simp) hst f hf hC0 hC (S := univ) MeasurableSet.univ
    simpa only [preimage_univ, setIntegral_univ] using h
  apply setIntegral_eq_of_finite_history μ (processHistory X s) (processHistory_measurable X hX s)
    hfi hgi hu ?_ hS
  intro I A hA
  exact process_indexed_past_setIntegral μ K x X hX hLaw I (fun r : Iic s => r.val)
    (fun r _ => r.property) hst f hf hC0 hC hA

end TimeTraps.Probability
