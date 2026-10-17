module

public import TimeTraps.Probability.GraphConservativeNaturalFiltration
public import TimeTraps.Probability.MarkovProcessConditional

@[expose] public section

/-! The constructed conservative continuous graph process is Markov at
every deterministic time for its full raw natural filtration. The law
and transition are the independently constructed physical graph objects. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory TimeTraps.Probability TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_markov_borel
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) {s t : ℝ≥0} (hst : s ≤ t)
    (f : GraphRealization P.geometry → ℝ) (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C) :
    (P.continuousPathLaw hκ x)[fun p : GraphContinuousPath P.geometry => f (p t) |
        graphContinuousNaturalFiltration P.geometry s] =ᵐ[P.continuousPathLaw hκ x]
      fun p => ∫ z, f z ∂P.realizedTransition (t - s) (p s) := by
  let inst := P.continuousPathLaw_probability hκ x
  let instK : ∀ u, IsMarkovKernel (P.realizedTransition u) := fun u => P.realizedTransition_isMarkov hκ u
  rw [graphContinuousNaturalFiltration_eq_history]
  exact process_condExp_of_finite_laws (P.continuousPathLaw hκ x) P.realizedTransition
    P.realizedTransition_zero x (fun t (p : GraphContinuousPath P.geometry) => p t)
    (fun t => (continuous_eval_const t).measurable)
    (fun I => P.continuousPathLaw_finite_observations hκ x I) hst f hf hC0 hC

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_markov
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) {s t : ℝ≥0} (hst : s ≤ t)
    (f : C(GraphRealization P.geometry, ℝ)) :
    (P.continuousPathLaw hκ x)[fun p : GraphContinuousPath P.geometry => f (p t) |
        graphContinuousNaturalFiltration P.geometry s] =ᵐ[P.continuousPathLaw hκ x]
      fun p => P.realizedFeller (t - s) f (p s) := by
  apply (P.continuousPathLaw_markov_borel hκ x hst f f.continuous.measurable
    (norm_nonneg f) (fun z => f.norm_coe_le_norm z)).trans
  exact Eventually.of_forall (fun p => (P.realizedFeller_apply (t - s) f (p s)).symm)

end TimeTraps.Analysis
