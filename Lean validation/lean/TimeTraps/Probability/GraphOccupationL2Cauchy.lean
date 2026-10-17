module

public import TimeTraps.Probability.GraphOccupationL2Data

@[expose] public section

/-! Mean-square occupation estimates imply convergence in the actual
complete L2 space of the constructed graph path law. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory Filter TimeTraps.Probability TimeTraps.Graph
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupationL2_cauchy_of_square_bound
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : ℕ → C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0)
    {e : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ n m, (∫ p, (graphOccupation P.geometry (f n) T p -
      graphOccupation P.geometry (f m) T p) ^ 2 ∂P.continuousPathLaw hκ x) ≤ C * (e n + e m)) :
    CauchySeq (fun n => P.occupationL2 hκ x (f n) T) := by
  apply cauchySeq_of_norm_sub_sq_le hC he
  intro n m
  rw [P.occupationL2_sub_norm_sq]
  exact hb n m

theorem GraphShiftedContactOperatorProblem.occupationL2_limit_of_square_bound
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : ℕ → C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0)
    {e : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ n m, (∫ p, (graphOccupation P.geometry (f n) T p -
      graphOccupation P.geometry (f m) T p) ^ 2 ∂P.continuousPathLaw hκ x) ≤ C * (e n + e m)) :
    ∃ L : Lp ℝ 2 (P.continuousPathLaw hκ x),
      Tendsto (fun n => P.occupationL2 hκ x (f n) T) atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete (P.occupationL2_cauchy_of_square_bound hκ x f T hC he hb)

end TimeTraps.Analysis
