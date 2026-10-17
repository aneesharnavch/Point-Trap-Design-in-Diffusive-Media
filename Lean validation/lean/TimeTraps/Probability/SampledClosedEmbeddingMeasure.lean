module

public import TimeTraps.Probability.SampledClosedEmbeddingPath

@[expose] public section

/-! Measurability and simultaneous recovery of the state-valued path
constructed by inverting the closed coordinate embedding. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical

variable {Ω K E : Type*} [MeasurableSpace Ω] [TopologicalSpace K]
  [MeasurableSpace K] [BorelSpace K] [NormedAddCommGroup E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
variable {c : K → E} {X : ℕ → Ω → K} {P : Measure Ω} {C : ℝ}

theorem sampledEmbeddedPath_measurable (hc : IsClosedEmbedding c) (x₀ : K)
    (hX : ∀ i, StronglyMeasurable (fun ω => c (X i ω))) (t : ℝ≥0) :
    Measurable (fun ω => sampledEmbeddedPath hc x₀ (fun i => X i ω) t) := by
  apply hc.measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun ω => c (sampledEmbeddedPath hc x₀ (fun i => X i ω) t))
  simp only [sampledEmbeddedPath_coordinates]
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.ite (sampledFourthDyadicRegular_measurableSet hX)
  · apply StronglyMeasurable.limUnder
    intro n
    exact hX _
  · exact stronglyMeasurable_const

omit [MeasurableSpace K] [BorelSpace K] [MeasurableSpace E] [BorelSpace E] in
theorem sampledEmbeddedPath_recovers_ae [IsFiniteMeasure P]
    (hc : IsClosedEmbedding c) (x₀ : K)
    (hcons : ∀ᵐ ω ∂P, ∀ i j, brownianDyadicTime i = brownianDyadicTime j → X i ω = X j ω)
    (hi : ∀ s t, Integrable (fun ω => dist (c (X s ω)) (c (X t ω)) ^ 4) P)
    (hb : ∀ s t, (∫ ω, dist (c (X s ω)) (c (X t ω)) ^ 4 ∂P) ≤
      C * dist (brownianDyadicTime s) (brownianDyadicTime t) ^ 2) :
    ∀ᵐ ω ∂P, ∀ i, sampledEmbeddedPath hc x₀ (fun j => X j ω) (brownianDyadicTime i) = X i ω := by
  have hcons' : ∀ᵐ ω ∂P, ∀ i j, brownianDyadicTime i = brownianDyadicTime j →
      c (X i ω) = c (X j ω) :=
    hcons.mono (fun ω hω i j hij => congrArg c (hω i j hij))
  filter_upwards [sampledFourthDyadic_regular_ae hcons' hi hb] with ω hω
  exact sampledEmbeddedPath_recovers hc x₀ hω

omit [BorelSpace K] [MeasurableSpace E] [BorelSpace E] in
theorem sampledEmbeddedPath_grid_hasLaw [IsFiniteMeasure P]
    (hc : IsClosedEmbedding c) (x₀ : K)
    (hcons : ∀ᵐ ω ∂P, ∀ i j, brownianDyadicTime i = brownianDyadicTime j → X i ω = X j ω)
    (hi : ∀ s t, Integrable (fun ω => dist (c (X s ω)) (c (X t ω)) ^ 4) P)
    (hb : ∀ s t, (∫ ω, dist (c (X s ω)) (c (X t ω)) ^ 4 ∂P) ≤
      C * dist (brownianDyadicTime s) (brownianDyadicTime t) ^ 2)
    (I : Finset ℕ) {ν : Measure (I → K)} (hν : HasLaw (fun ω (i : I) => X i ω) ν P) :
    HasLaw (fun ω (i : I) => sampledEmbeddedPath hc x₀ (fun j => X j ω) (brownianDyadicTime i)) ν P := by
  apply hν.congr
  filter_upwards [sampledEmbeddedPath_recovers_ae hc x₀ hcons hi hb] with ω hω
  exact funext (fun i => hω i)

end TimeTraps.Probability
