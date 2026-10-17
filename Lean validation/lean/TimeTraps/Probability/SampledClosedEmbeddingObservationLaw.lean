module

public import TimeTraps.Probability.SampledClosedEmbeddingAddedTime
public import TimeTraps.Probability.DenseAugmentedObservationTimes

@[expose] public section

/-! Exact arbitrary-time laws of the reconstructed path. An augmented
countable law contains both the dense observations and the desired times;
moment continuity identifies those additional observations with the path. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical

variable {K E : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
variable {c : K → E}

theorem sampledEmbeddedPath_observation_law (hc : IsClosedEmbedding c) (x₀ : K)
    (τ : ℕ → ℝ≥0) (μgrid μaug μtarget : Measure (ℕ → K)) [IsFiniteMeasure μaug]
    (hgrid : μaug.map (fun q i => q (Nat.pair 0 i)) = μgrid)
    (hadded : μaug.map (fun q i => q (Nat.pair 1 i)) = μtarget)
    (hr : ∀ᵐ q ∂μgrid, FourthDyadicRegular (c ∘ q)) {C : ℝ}
    (hi : ∀ i j, Integrable (fun q => dist (c (q (Nat.pair 0 i))) (c (q (Nat.pair 1 j))) ^ 4) μaug)
    (hb : ∀ i j, (∫ q, dist (c (q (Nat.pair 0 i))) (c (q (Nat.pair 1 j))) ^ 4 ∂μaug) ≤
      C * dist (brownianDyadicTime i) (τ j) ^ 2) :
    μgrid.map (fun q j => sampledEmbeddedPath hc x₀ q (τ j)) = μtarget := by
  have hmg : Measurable (fun q : ℕ → K => fun i => q (Nat.pair 0 i)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hr' : ∀ᵐ q ∂μaug, FourthDyadicRegular (fun i => c (q (Nat.pair 0 i))) := by
    rw [← hgrid] at hr
    exact ae_of_ae_map hmg.aemeasurable hr
  have he := sampledEmbeddedPath_added_times_ae hc x₀ hr' τ
    (fun j q => q (Nat.pair 1 j)) hi hb
  have hm : Measurable (fun q : ℕ → K => fun j => sampledEmbeddedPath hc x₀ q (τ j)) := by
    apply measurable_pi_lambda
    intro j
    exact sampledEmbeddedPath_measurable hc x₀
      (fun i => (hc.continuous.measurable.comp (measurable_pi_apply i)).stronglyMeasurable) (τ j)
  rw [← hgrid, Measure.map_map hm hmg, ← hadded]
  apply Measure.map_congr
  filter_upwards [he] with q hq
  exact funext hq

end TimeTraps.Probability
