module

public import TimeTraps.Probability.MarkovOccupationKacData

@[expose] public section

/-! The finite-time signed Kac occupation-product identity, derived from
joint measurability, bounded continuous tests and the actual chronological
two-time law. No stochastic conditional identity is included as a premise. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [TopologicalSpace α] [BorelSpace α] [SecondCountableTopology α] [CompactSpace α]

omit [SecondCountableTopology α] in
theorem markovOccupationKac_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℝ≥0 → Ω → α) (hX : Measurable (Function.uncurry X))
    (f g : C(α, ℝ)) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => (∫ s in 0..T, f (X s.toNNReal ω)) *
      (∫ t in 0..T, g (X t.toNNReal ω))) μ := by
  simpa only [intervalIntegral.integral_of_le hT] using
    occupationProduct_integrable μ (volume.restrict (Ioc 0 T))
      (fun s ω => f (X s.toNNReal ω)) (fun t ω => g (X t.toNNReal ω))
      (occupationObservation_measurable X hX f) (occupationObservation_measurable X hX g)
      (fun _ _ => f.norm_coe_le_norm _) (fun _ _ => g.norm_coe_le_norm _)

theorem markovOccupationKac_ordered (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℝ≥0 → Ω → α) (hX : Measurable (Function.uncurry X))
    (hPair : ∀ s t : ℝ≥0, s < t → μ.map (fun ω => (X s ω, X t ω)) =
      (K s x) ⊗ₘ K (t - s)) (f g : C(α, ℝ)) {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, (∫ s in 0..T, f (X s.toNNReal ω)) * (∫ t in 0..T, g (X t.toNNReal ω)) ∂μ) =
      orderedTimeIntegral (volume.restrict (Ioc 0 T))
        (fun p => markovOccupationPair K x f g p.1.toNNReal p.2.toNNReal) +
      orderedTimeIntegral (volume.restrict (Ioc 0 T))
        (fun p => markovOccupationPair K x g f p.1.toNNReal p.2.toNNReal) := by
  have h := occupationProduct_interval_ordered μ (fun s ω => f (X s.toNNReal ω))
    (fun t ω => g (X t.toNNReal ω))
    (occupationObservation_measurable X hX f) (occupationObservation_measurable X hX g)
    (fun _ _ => f.norm_coe_le_norm _) (fun _ _ => g.norm_coe_le_norm _) hT
  exact h.trans (congrArg₂ (· + ·)
    (markovOccupationPair_ordered_replacement K x μ X hX hPair f g T).2
    (markovOccupationPair_ordered_replacement K x μ X hX hPair g f T).2)

theorem markovOccupationKac (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℝ≥0 → Ω → α) (hX : Measurable (Function.uncurry X))
    (hPair : ∀ s t : ℝ≥0, s < t → μ.map (fun ω => (X s ω, X t ω)) =
      (K s x) ⊗ₘ K (t - s)) (f g : C(α, ℝ)) {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, (∫ s in 0..T, f (X s.toNNReal ω)) * (∫ t in 0..T, g (X t.toNNReal ω)) ∂μ) =
      (∫ s in 0..T, ∫ t in 0..T, if s < t then
        markovOccupationPair K x f g s.toNNReal t.toNNReal else 0) +
      (∫ s in 0..T, ∫ t in 0..T, if s < t then
        markovOccupationPair K x g f s.toNNReal t.toNNReal else 0) := by
  rw [markovOccupationKac_ordered K x μ X hX hPair f g hT]
  simp_rw [intervalIntegral.integral_of_le hT]
  exact congrArg₂ (· + ·)
    (integral_prod _ (markovOccupationPair_ordered_replacement K x μ X hX hPair f g T).1)
    (integral_prod _ (markovOccupationPair_ordered_replacement K x μ X hX hPair g f T).1)

theorem markovOccupationKac_square (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℝ≥0 → Ω → α) (hX : Measurable (Function.uncurry X))
    (hPair : ∀ s t : ℝ≥0, s < t → μ.map (fun ω => (X s ω, X t ω)) =
      (K s x) ⊗ₘ K (t - s)) (f : C(α, ℝ)) {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, (∫ s in 0..T, f (X s.toNNReal ω)) ^ 2 ∂μ) =
      2 * ∫ s in 0..T, ∫ t in 0..T, if s < t then
        markovOccupationPair K x f f s.toNNReal t.toNNReal else 0 := by
  simpa only [pow_two, two_mul] using markovOccupationKac K x μ X hX hPair f f hT

end TimeTraps.Probability
