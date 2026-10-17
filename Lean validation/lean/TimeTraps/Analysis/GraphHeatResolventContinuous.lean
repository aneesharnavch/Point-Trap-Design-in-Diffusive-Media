module

public import TimeTraps.Analysis.GraphHeatResolventLaplace
public import TimeTraps.Analysis.BoundedContinuousLaplacePrimitive
public import TimeTraps.Analysis.GraphConservativeVariationIntertwining
public import TimeTraps.Probability.GraphConservativeOccupationPotentialData

@[expose] public section

/-! The discount-one resolvent of actual continuous graph observations
is the original full-H1 weak solution. Its finite-time primitive has the
same Laplace transform. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.realizedFellerLaplaceOne_integrable
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ)) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) • P.realizedFeller t.toNNReal f) (Ioi 0) :=
  boundedContinuousLaplaceOne_integrable
    ((P.realizedFeller_strong_continuous f).comp continuous_real_toNNReal)
    (fun t _ => P.realizedFeller_norm_le t.toNNReal f)

theorem GraphShiftedContactOperatorProblem.realizedFellerLaplaceOne_eq_solution
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ)) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t) • P.realizedFeller t.toNNReal f) =
      P.realizedSolutionL (graphConservativeContinuousStateL P.geometry f) := by
  apply graphConservativeContinuousStateL_injective P.geometry
  rw [← (graphConservativeContinuousStateL P.geometry).integral_comp_comm
    (P.realizedFellerLaplaceOne_integrable f), P.continuousState_solution]
  simp only [map_smul, P.continuousState_feller]
  exact P.heatLaplaceOne_eq_inverse _

theorem GraphShiftedContactOperatorProblem.occupationPotentialLaplaceOne_integrable
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ)) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) • P.occupationPotential f t) (Ioi 0) :=
  boundedContinuousLaplacePrimitive_integrable
    ((P.realizedFeller_strong_continuous f).comp continuous_real_toNNReal)
    (fun t _ => P.realizedFeller_norm_le t.toNNReal f)

theorem GraphShiftedContactOperatorProblem.occupationPotentialLaplaceOne_eq_solution
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ)) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t) • P.occupationPotential f t) =
      P.realizedSolutionL (graphConservativeContinuousStateL P.geometry f) := by
  exact (boundedContinuousLaplacePrimitive_eq
    ((P.realizedFeller_strong_continuous f).comp continuous_real_toNNReal)
    (fun t _ => P.realizedFeller_norm_le t.toNNReal f)).trans
    (P.realizedFellerLaplaceOne_eq_solution f)

theorem GraphShiftedContactOperatorProblem.occupationPotentialLaplaceOne_apply
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (a : GraphRealization P.geometry) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t) * P.occupationPotential f t a) =
      P.realizedSolutionL (graphConservativeContinuousStateL P.geometry f) a := by
  have h := congrArg (fun g : C(GraphRealization P.geometry, ℝ) => g a)
    (P.occupationPotentialLaplaceOne_eq_solution f)
  rw [ContinuousMap.integral_apply (P.occupationPotentialLaplaceOne_integrable f)] at h
  exact h

end TimeTraps.Analysis
