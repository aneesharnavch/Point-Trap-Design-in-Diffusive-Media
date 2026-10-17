module

public import TimeTraps.Probability.GraphConservativeContinuousRegular
public import TimeTraps.Probability.GraphConservativeSampledReindex
public import TimeTraps.Probability.SampledClosedEmbeddingObservationLaw

@[expose] public section

/-! The constructed continuous graph path has exactly the original
chronological transition law at every countable family of real times.
All moment, consistency and augmented-law inputs are derived from the
original conservative graph operator. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory TimeTraps.Probability TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_observations
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (τ : ℕ → ℝ≥0) :
    (P.continuousPathLaw hκ x).map (fun p i => p (τ i)) = P.sampledPathLaw hκ τ x := by
  let σ := denseAugmentedObservationTime τ
  let inst := P.sampledPathLaw_probability hκ σ x
  have hg : (P.sampledPathLaw hκ σ x).map (fun q i => q (Nat.pair 0 i)) =
      P.sampledPathLaw hκ brownianDyadicTime x := by
    have h := P.sampledPathLaw_reindex hκ σ (Nat.pair 0) x
    have he : σ ∘ Nat.pair 0 = brownianDyadicTime := by
      funext i
      exact denseAugmentedObservationTime_grid τ i
    simpa only [he, Function.comp_def] using h
  have ha : (P.sampledPathLaw hκ σ x).map (fun q i => q (Nat.pair 1 i)) =
      P.sampledPathLaw hκ τ x := by
    have h := P.sampledPathLaw_reindex hκ σ (Nat.pair 1) x
    have he : σ ∘ Nat.pair 1 = τ := by
      funext i
      exact denseAugmentedObservationTime_added τ i
    simpa only [he, Function.comp_def] using h
  obtain ⟨C, _hC, hb⟩ := P.sampledPathLaw_coordinate_dist_fourth_bound hκ
  have hi := fun i j => (hb σ x (Nat.pair 0 i) (Nat.pair 1 j)).1
  have hbound : ∀ i j, (∫ q, dist (P.geometry.smoothCoordinates (q (Nat.pair 0 i)))
      (P.geometry.smoothCoordinates (q (Nat.pair 1 j))) ^ 4 ∂P.sampledPathLaw hκ σ x) ≤
        C * dist (brownianDyadicTime i) (τ j) ^ 2 := by
    intro i j
    simpa only [σ, denseAugmentedObservationTime_grid, denseAugmentedObservationTime_added]
      using (hb σ x (Nat.pair 0 i) (Nat.pair 1 j)).2
  rw [P.continuousPathLaw_eval]
  exact sampledEmbeddedPath_observation_law P.geometry.smoothCoordinates_closedEmbedding x τ
    (P.sampledPathLaw hκ brownianDyadicTime x) (P.sampledPathLaw hκ σ x)
    (P.sampledPathLaw hκ τ x) hg ha (P.sampledPathLaw_dyadic_regular hκ x) hi hbound

end TimeTraps.Analysis
