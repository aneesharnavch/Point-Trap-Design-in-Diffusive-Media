module

public import TimeTraps.Probability.MarkovSampledPathReindex
public import TimeTraps.Probability.GraphConservativeSampledLaw

@[expose] public section

/-! Reindexing consistency of the original conservative graph's actual
countably sampled law, including arbitrary repeated labels. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory TimeTraps.Probability TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.sampledPathLaw_reindex
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (τ : ℕ → ℝ≥0) (r : ℕ → ℕ) (x : GraphRealization P.geometry) :
    (P.sampledPathLaw hκ τ x).map (fun q => q ∘ r) =
      P.sampledPathLaw hκ (τ ∘ r) x := by
  let inst : ∀ t, IsMarkovKernel (P.realizedTransition t) :=
    fun t => P.realizedTransition_isMarkov hκ t
  let : Nonempty (GraphRealization P.geometry) := ⟨x⟩
  exact markovSampledPathLaw_reindex P.realizedTransition P.realizedTransition_add τ r x

end TimeTraps.Analysis
