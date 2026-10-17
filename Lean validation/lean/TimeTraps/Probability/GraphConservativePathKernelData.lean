module

public import TimeTraps.Probability.GraphConservativeContinuousFiniteLaw
public import TimeTraps.Probability.ProjectiveFamilyMeasurable

@[expose] public section

/-! Every finite and countably sampled graph path law depends measurably
on its actual starting point. The projective limit is the already
constructed law, and its finite marginals are the original kernels. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory TimeTraps.Probability TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.timeObservationLaw_measurable
    (P : GraphShiftedContactOperatorProblem V E) (I : Finset ℝ≥0) :
    Measurable (fun x => P.timeObservationLaw x I) :=
  (markovObservationKernel P.realizedTransition I).measurable

theorem GraphShiftedContactOperatorProblem.observationFamilyPullback_measurable
    (P : GraphShiftedContactOperatorProblem V E) (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    Measurable (fun x => observationFamilyPullback τ (P.timeObservationLaw x) I) :=
  (Measure.measurable_map (observationPullbackState τ I) (observationPullbackState_measurable τ I)).comp
    (P.timeObservationLaw_measurable (I.image τ))

theorem GraphShiftedContactOperatorProblem.sampledPathLaw_measurable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) (τ : ℕ → ℝ≥0) :
    Measurable (P.sampledPathLaw hκ τ) := by
  let inst : ∀ x, IsProbabilityMeasure (P.sampledPathLaw hκ τ x) :=
    fun x => P.sampledPathLaw_probability hκ τ x
  exact projectiveLimit_family_measurable (P.sampledPathLaw hκ τ)
    (fun x => observationFamilyPullback τ (P.timeObservationLaw x))
    (P.sampledPathLaw_isProjectiveLimit hκ τ) (P.observationFamilyPullback_measurable τ)

end TimeTraps.Analysis
