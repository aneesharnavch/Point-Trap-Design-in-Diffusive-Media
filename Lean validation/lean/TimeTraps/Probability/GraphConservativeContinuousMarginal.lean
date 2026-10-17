module

public import TimeTraps.Probability.GraphConservativeContinuousFiniteLaw

@[expose] public section

/-! Actual single-time transition laws and the prescribed initial state
of the constructed continuous graph process. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory TimeTraps.Probability TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_marginal
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (t : ℝ≥0) :
    (P.continuousPathLaw hκ x).map (fun p => p t) = P.realizedTransition t x := by
  let inst : ∀ u, IsMarkovKernel (P.realizedTransition u) :=
    fun u => P.realizedTransition_isMarkov hκ u
  have hpair := P.continuousPathLaw_pair hκ x (show t < t + 1 by simp)
  have he := congrArg (fun ν : Measure (GraphRealization P.geometry × GraphRealization P.geometry) => ν.fst) hpair
  rw [Measure.fst_compProd] at he
  change ((P.continuousPathLaw hκ x).map (fun p => (p t, p (t + 1)))).map Prod.fst = _ at he
  rw [Measure.map_map measurable_fst
    (((continuous_eval_const t).prodMk (continuous_eval_const (t + 1))).measurable)] at he
  exact he

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_initial
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) : ∀ᵐ p ∂P.continuousPathLaw hκ x, p 0 = x := by
  have h : HasLaw (fun p : GraphContinuousPath P.geometry => p 0) (Measure.dirac x)
      (P.continuousPathLaw hκ x) := by
    refine ⟨(continuous_eval_const 0).measurable.aemeasurable, ?_⟩
    rw [P.continuousPathLaw_marginal hκ x 0, P.realizedTransition_zero, Kernel.id_apply]
  exact h.ae_eq_of_dirac

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_observation_integral
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (t : ℝ≥0) (f : C(GraphRealization P.geometry, ℝ)) :
    (∫ p, f (p t) ∂P.continuousPathLaw hκ x) = P.realizedFeller t f x := by
  rw [P.realizedFeller_apply, ← P.continuousPathLaw_marginal hκ x t]
  exact (integral_map (continuous_eval_const t).measurable.aemeasurable
    f.continuous.aestronglyMeasurable).symm

end TimeTraps.Analysis
