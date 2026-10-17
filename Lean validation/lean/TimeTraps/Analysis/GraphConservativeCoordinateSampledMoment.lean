module

public import TimeTraps.Analysis.GraphConservativeCoordinateFourthProcess
public import TimeTraps.Analysis.GraphConservativeMomentSampled

@[expose] public section

/-! The actual sampled conservative graph law satisfies the required
vector fourth-increment estimate. Its uniform constant is the finite sum
of the proved scalar coordinate constants, for all starts and time labels. -/

namespace TimeTraps.Analysis

open MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.sampledPathLaw_coordinate_vector_fourth_bound
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℕ → ℝ≥0) (x : GraphRealization P.geometry) (i j : ℕ),
      Integrable (fun q => ‖P.geometry.smoothCoordinates (q j) -
        P.geometry.smoothCoordinates (q i)‖ ^ 4) (P.sampledPathLaw hκ τ x) ∧
      (∫ q, ‖P.geometry.smoothCoordinates (q j) -
        P.geometry.smoothCoordinates (q i)‖ ^ 4 ∂P.sampledPathLaw hκ τ x) ≤
          C * dist (τ i) (τ j) ^ 2 := by
  classical
  choose C hC using fun k : GraphCoordinateIndex V E =>
    P.sampledPathLaw_coordinate_fourth_bound hκ (graphCoordinateProjection k)
  refine ⟨∑ k, C k, Finset.sum_nonneg (fun k _ => (hC k).1), ?_⟩
  intro τ x i j
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun q : ℕ → GraphRealization P.geometry => P.geometry.smoothCoordinates (q n))
      (P.sampledPathLaw hκ τ x) :=
    (P.geometry.smoothCoordinates_continuous.measurable.comp (measurable_pi_apply n)).aestronglyMeasurable
  have hi : ∀ k : GraphCoordinateIndex V E, Integrable (fun q =>
      (graphCoordinateProjection k (P.geometry.smoothCoordinates (q j)) -
        graphCoordinateProjection k (P.geometry.smoothCoordinates (q i))) ^ 4)
      (P.sampledPathLaw hκ τ x) := fun k => ((hC k).2 τ x i j).1
  refine ⟨graphCoordinateProjection_fourth_integrable (P.sampledPathLaw hκ τ x) _ _ (hm j) (hm i) hi, ?_⟩
  exact graphCoordinateProjection_fourth_integral_bound (P.sampledPathLaw hκ τ x) _ _
    (hm j) (hm i) hi C (dist (τ i) (τ j) ^ 2) (fun k => ((hC k).2 τ x i j).2)

end TimeTraps.Analysis
