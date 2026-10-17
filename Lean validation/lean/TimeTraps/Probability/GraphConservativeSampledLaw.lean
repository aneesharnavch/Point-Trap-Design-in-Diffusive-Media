module

public import TimeTraps.Probability.GraphConservativeFiniteLaw
public import TimeTraps.Probability.MarkovSampledPathLaw

@[expose] public section

/-! Genuine finite-set and countably sampled probability laws of the
original conservative graph heat transition. All consistency statements
are proved from the actual kernel, with no graph-process premise. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory TimeTraps.Probability TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.timeObservationLaw
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphRealization P.geometry)
    (I : Finset ℝ≥0) : Measure (I → GraphRealization P.geometry) :=
  markovObservationFamily P.realizedTransition x I

theorem GraphShiftedContactOperatorProblem.timeObservationLaw_eq
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphRealization P.geometry)
    (I : Finset ℝ≥0) :
    P.timeObservationLaw x I =
      (P.finiteObservationLaw x (observationDurations 0 (I.sort (· ≤ ·)))).map (observationState I) :=
  Kernel.map_apply _ (observationState_measurable I) x

theorem GraphShiftedContactOperatorProblem.timeObservationLaw_probability
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (I : Finset ℝ≥0) :
    IsProbabilityMeasure (P.timeObservationLaw x I) := by
  let inst : ∀ t, IsMarkovKernel (P.realizedTransition t) := fun t => P.realizedTransition_isMarkov hκ t
  exact markovObservationFamily_probability P.realizedTransition x I

theorem GraphShiftedContactOperatorProblem.timeObservationLaw_projective
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) :
    IsProjectiveMeasureFamily (α := fun _ => GraphRealization P.geometry) (P.timeObservationLaw x) := by
  let inst : ∀ t, IsMarkovKernel (P.realizedTransition t) := fun t => P.realizedTransition_isMarkov hκ t
  exact markovObservationFamily_projective P.realizedTransition P.realizedTransition_add x

noncomputable def GraphShiftedContactOperatorProblem.sampledPathLaw
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (τ : ℕ → ℝ≥0) (x : GraphRealization P.geometry) : Measure (ℕ → GraphRealization P.geometry) := by
  let inst : ∀ t, IsMarkovKernel (P.realizedTransition t) := fun t => P.realizedTransition_isMarkov hκ t
  let : Nonempty (GraphRealization P.geometry) := ⟨x⟩
  exact markovSampledPathLaw P.realizedTransition τ x

theorem GraphShiftedContactOperatorProblem.sampledPathLaw_probability
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (τ : ℕ → ℝ≥0) (x : GraphRealization P.geometry) :
    IsProbabilityMeasure (P.sampledPathLaw hκ τ x) := by
  let inst : ∀ t, IsMarkovKernel (P.realizedTransition t) := fun t => P.realizedTransition_isMarkov hκ t
  let : Nonempty (GraphRealization P.geometry) := ⟨x⟩
  unfold sampledPathLaw
  exact markovSampledPathLaw_probability P.realizedTransition τ x

theorem GraphShiftedContactOperatorProblem.sampledPathLaw_isProjectiveLimit
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (τ : ℕ → ℝ≥0) (x : GraphRealization P.geometry) :
    IsProjectiveLimit (P.sampledPathLaw hκ τ x)
      (observationFamilyPullback τ (P.timeObservationLaw x)) := by
  let inst : ∀ t, IsMarkovKernel (P.realizedTransition t) := fun t => P.realizedTransition_isMarkov hκ t
  let : Nonempty (GraphRealization P.geometry) := ⟨x⟩
  exact markovSampledPathLaw_isProjectiveLimit P.realizedTransition P.realizedTransition_add τ x

end TimeTraps.Analysis
