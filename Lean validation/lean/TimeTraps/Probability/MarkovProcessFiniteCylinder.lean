module

public import TimeTraps.Probability.MarkovProcessFiniteLaw
public import TimeTraps.Probability.KernelConditionalIntegral

@[expose] public section

/-! The actual finite observation laws give the Markov set-integral
identity on arbitrary finite past cylinders, including repeated labels. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

theorem process_finite_past_setIntegral (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : ℝ≥0 → Kernel α α) [∀ t, IsMarkovKernel (K t)] (x : α)
    (X : ℝ≥0 → Ω → α) (hX : ∀ t, Measurable (X t))
    (hLaw : ∀ I : Finset ℝ≥0, μ.map (fun ω (r : I) => X r.val ω) = markovObservationFamily K x I)
    (I : Finset ℝ≥0) {s t : ℝ≥0} (hs : s ∈ I) (hmax : ∀ u ∈ I, u ≤ s) (hst : s < t)
    (f : α → ℝ) (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C)
    {S : Set (I → α)} (hS : MeasurableSet S) :
    (∫ ω in (fun ω (r : I) => X r.val ω) ⁻¹' S, f (X t ω) ∂μ) =
      ∫ ω in (fun ω (r : I) => X r.val ω) ⁻¹' S, (∫ z, f z ∂K (t - s) (X s ω)) ∂μ := by
  exact kernel_pair_bounded_setIntegral μ (fun ω (r : I) => X r.val ω) (X t)
    (measurable_pi_lambda _ (fun r => hX r.val)) (hX t)
    ((K (t - s)).comap (fun q => q ⟨s, hs⟩) (measurable_pi_apply _))
    (process_finite_past_future_law μ K x X hX hLaw I hs hmax hst) f hf hC0 hC hS

theorem process_indexed_past_setIntegral {ι : Type*} (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : ℝ≥0 → Kernel α α) [∀ t, IsMarkovKernel (K t)] (x : α)
    (X : ℝ≥0 → Ω → α) (hX : ∀ t, Measurable (X t))
    (hLaw : ∀ I : Finset ℝ≥0, μ.map (fun ω (r : I) => X r.val ω) = markovObservationFamily K x I)
    (I : Finset ι) (τ : ι → ℝ≥0) {s t : ℝ≥0} (hmax : ∀ i ∈ I, τ i ≤ s) (hst : s < t)
    (f : α → ℝ) (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C)
    {S : Set (I → α)} (hS : MeasurableSet S) :
    (∫ ω in (fun ω (r : I) => X (τ r.val) ω) ⁻¹' S, f (X t ω) ∂μ) =
      ∫ ω in (fun ω (r : I) => X (τ r.val) ω) ⁻¹' S, (∫ z, f z ∂K (t - s) (X s ω)) ∂μ := by
  classical
  let J : Finset ℝ≥0 := insert s (I.image τ)
  have hsJ : s ∈ J := Finset.mem_insert_self _ _
  have hJ : ∀ u ∈ J, u ≤ s := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact le_rfl
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact hmax i hi
  let R : (J → α) → (I → α) := fun q i => q
    ⟨τ i.val, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩)⟩
  have hR : Measurable R := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  exact process_finite_past_setIntegral μ K x X hX hLaw J hsJ hJ hst f hf hC0 hC (hR hS)

end TimeTraps.Probability
