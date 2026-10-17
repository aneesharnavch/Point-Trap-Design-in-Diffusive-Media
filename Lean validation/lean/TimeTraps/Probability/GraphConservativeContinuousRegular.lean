module

public import TimeTraps.Probability.GraphConservativeContinuousLawData
public import TimeTraps.Analysis.GraphConservativeCoordinateSampledMoment
public import TimeTraps.Probability.ProjectiveObservationEqualTimes

@[expose] public section

/-! The original graph transition laws satisfy the actual vector moment
condition. Hence the continuous reconstruction recovers every dense
observation on one probability-one event; no moment premise remains. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory TimeTraps.Probability TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.sampledPathLaw_coordinate_dist_fourth_bound
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℕ → ℝ≥0) (x : GraphRealization P.geometry) (i j : ℕ),
      Integrable (fun q => dist (P.geometry.smoothCoordinates (q i))
        (P.geometry.smoothCoordinates (q j)) ^ 4) (P.sampledPathLaw hκ τ x) ∧
      (∫ q, dist (P.geometry.smoothCoordinates (q i))
        (P.geometry.smoothCoordinates (q j)) ^ 4 ∂P.sampledPathLaw hκ τ x) ≤
          C * dist (τ i) (τ j) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := P.sampledPathLaw_coordinate_vector_fourth_bound hκ
  refine ⟨C, hC, fun τ x i j => ?_⟩
  have h := hb τ x j i
  rw [dist_comm (τ j) (τ i)] at h
  simpa only [dist_eq_norm] using h

theorem GraphShiftedContactOperatorProblem.sampledPathLaw_dyadic_regular
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) :
    ∀ᵐ q ∂P.sampledPathLaw hκ brownianDyadicTime x,
      FourthDyadicRegular (P.geometry.smoothCoordinates ∘ q) := by
  let inst := P.sampledPathLaw_probability hκ brownianDyadicTime x
  obtain ⟨C, _hC, hb⟩ := P.sampledPathLaw_coordinate_dist_fourth_bound hκ
  have hcons := projectiveObservation_equal_times_all brownianDyadicTime
    (P.sampledPathLaw_isProjectiveLimit hκ brownianDyadicTime x)
  exact sampledFourthDyadic_regular_ae
    (hcons.mono (fun q hq i j hij => congrArg P.geometry.smoothCoordinates (hq i j hij)))
    (fun i j => (hb brownianDyadicTime x i j).1)
    (fun i j => (hb brownianDyadicTime x i j).2)

theorem GraphShiftedContactOperatorProblem.reconstructedPath_recovers_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) :
    ∀ᵐ q ∂P.sampledPathLaw hκ brownianDyadicTime x, ∀ i,
      P.geometry.reconstructedPath x q (brownianDyadicTime i) = q i :=
  (P.sampledPathLaw_dyadic_regular hκ x).mono
    (fun _q hq => sampledEmbeddedPath_recovers P.geometry.smoothCoordinates_closedEmbedding x hq)

end TimeTraps.Analysis
