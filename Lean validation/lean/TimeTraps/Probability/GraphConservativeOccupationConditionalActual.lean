module

public import TimeTraps.Probability.GraphConservativeOccupationConditional
public import TimeTraps.Probability.GraphConservativeMarkov

@[expose] public section

/-! The conditional occupation identity under the actual graph path law,
with its transition premise discharged by the proved raw-history Markov theorem. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupation_condExp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ))
    {s H : ℝ≥0} (hsH : s ≤ H) :
    (P.continuousPathLaw hκ x)[graphOccupation P.geometry f H |
        graphContinuousNaturalFiltration P.geometry s] =ᵐ[P.continuousPathLaw hκ x]
      (fun p => graphOccupation P.geometry f s p + P.occupationPotential f (H.val - s.val) (p s)) := by
  apply P.occupation_condExp_of_transition hκ x f (graphContinuousNaturalFiltration P.geometry)
    (Filtration.stronglyAdapted_natural _) hsH
  intro r hsr
  exact P.continuousPathLaw_markov hκ x hsr f

end TimeTraps.Analysis
