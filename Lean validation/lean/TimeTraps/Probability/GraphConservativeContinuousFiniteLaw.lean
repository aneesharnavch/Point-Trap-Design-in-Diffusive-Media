module

public import TimeTraps.Probability.GraphConservativeContinuousLaw
public import TimeTraps.Probability.CountableObservationFiniteLaw

@[expose] public section

/-! Every finite set of observations of the constructed continuous graph
path has the original chronologically composed graph transition law. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory TimeTraps.Probability TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_finite_observations
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (I : Finset ℝ≥0) :
    (P.continuousPathLaw hκ x).map (fun p (i : I) => p i) = P.timeObservationLaw x I := by
  apply finite_laws_of_countable_projective_observations 0 (P.continuousPathLaw hκ x)
    (fun t p => p t) (P.timeObservationLaw x) (fun t => (continuous_eval_const t).measurable)
  intro τ
  rw [P.continuousPathLaw_observations hκ x τ]
  exact P.sampledPathLaw_isProjectiveLimit hκ τ x

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_pair
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) {s t : ℝ≥0} (hst : s < t) :
    (P.continuousPathLaw hκ x).map (fun p => (p s, p t)) =
      (P.realizedTransition s x) ⊗ₘ P.realizedTransition (t - s) := by
  let inst : ∀ u, IsMarkovKernel (P.realizedTransition u) :=
    fun u => P.realizedTransition_isMarkov hκ u
  have h := P.continuousPathLaw_finite_observations hκ x {s, t}
  have hm : Measurable (fun q : ({s, t} : Finset ℝ≥0) → GraphRealization P.geometry =>
      (q ⟨s, by simp⟩, q ⟨t, by simp⟩)) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have he := congrArg (fun ν => ν.map
    (fun q : ({s, t} : Finset ℝ≥0) → GraphRealization P.geometry =>
      (q ⟨s, by simp⟩, q ⟨t, by simp⟩))) h
  rw [Measure.map_map hm (measurable_pi_lambda _ (fun i => (continuous_eval_const i.val).measurable))] at he
  exact he.trans (markovObservationFamily_pair_map P.realizedTransition x hst)

end TimeTraps.Analysis
