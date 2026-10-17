module

public import TimeTraps.Probability.MarkovOccupationKac
public import TimeTraps.Probability.OccupationProductTriangle

@[expose] public section

/-! The signed Kac identity with its conventional chronological limits.
All inner kernel integrals and ordered time integrals have been justified
by the earlier joint-product integrability argument. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [TopologicalSpace α] [BorelSpace α] [SecondCountableTopology α] [CompactSpace α]

theorem markovOccupationKac_upperTriangle (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℝ≥0 → Ω → α) (hX : Measurable (Function.uncurry X))
    (hPair : ∀ s t : ℝ≥0, s < t → μ.map (fun ω => (X s ω, X t ω)) =
      (K s x) ⊗ₘ K (t - s)) (f g : C(α, ℝ)) {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, (∫ s in 0..T, f (X s.toNNReal ω)) * (∫ t in 0..T, g (X t.toNNReal ω)) ∂μ) =
      (∫ s in 0..T, ∫ t in s..T, markovOccupationPair K x f g s.toNNReal t.toNNReal) +
      (∫ s in 0..T, ∫ t in s..T, markovOccupationPair K x g f s.toNNReal t.toNNReal) := by
  exact (markovOccupationKac_ordered K x μ X hX hPair f g hT).trans (congrArg₂ (· + ·)
    (orderedTimeIntegral_eq_upperTriangle _ hT
      (markovOccupationPair_ordered_replacement K x μ X hX hPair f g T).1)
    (orderedTimeIntegral_eq_upperTriangle _ hT
      (markovOccupationPair_ordered_replacement K x μ X hX hPair g f T).1))

theorem markovOccupationKac_square_upperTriangle (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℝ≥0 → Ω → α) (hX : Measurable (Function.uncurry X))
    (hPair : ∀ s t : ℝ≥0, s < t → μ.map (fun ω => (X s ω, X t ω)) =
      (K s x) ⊗ₘ K (t - s)) (f : C(α, ℝ)) {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, (∫ s in 0..T, f (X s.toNNReal ω)) ^ 2 ∂μ) =
      2 * ∫ s in 0..T, ∫ t in s..T, markovOccupationPair K x f f s.toNNReal t.toNNReal := by
  simpa only [pow_two, two_mul] using markovOccupationKac_upperTriangle K x μ X hX hPair f f hT

end TimeTraps.Probability
