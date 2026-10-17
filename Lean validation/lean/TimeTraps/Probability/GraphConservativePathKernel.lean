module

public import TimeTraps.Probability.GraphConservativePathKernelData

@[expose] public section

/-! The original continuous graph path laws form a genuine measurable
probability kernel in the starting point. Dense path observations recover
the full path Borel space, rather than assuming kernel measurability. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory TopologicalSpace TimeTraps.Probability TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_measurable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) :
    Measurable (P.continuousPathLaw hκ) := by
  apply measure_family_measurable_of_embedding (P.continuousPathLaw hκ)
    (graphContinuousPathSample P.geometry) (graphContinuousPathSample_measurableEmbedding P.geometry)
  have he : (fun x => (P.continuousPathLaw hκ x).map (graphContinuousPathSample P.geometry)) =
      P.sampledPathLaw hκ (denseSeq ℝ≥0) :=
    funext (fun x => P.continuousPathLaw_observations hκ x (denseSeq ℝ≥0))
  rw [he]
  exact P.sampledPathLaw_measurable hκ (denseSeq ℝ≥0)

noncomputable def GraphShiftedContactOperatorProblem.continuousPathKernel
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) :
    Kernel (GraphRealization P.geometry) (GraphContinuousPath P.geometry) :=
  ⟨P.continuousPathLaw hκ, P.continuousPathLaw_measurable hκ⟩

theorem GraphShiftedContactOperatorProblem.continuousPathKernel_apply
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) :
    P.continuousPathKernel hκ x = P.continuousPathLaw hκ x := rfl

instance GraphShiftedContactOperatorProblem.continuousPathKernel_isMarkov
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) :
    IsMarkovKernel (P.continuousPathKernel hκ) :=
  ⟨fun x => P.continuousPathLaw_probability hκ x⟩

theorem GraphShiftedContactOperatorProblem.continuousPathKernel_finite_observations
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (I : Finset ℝ≥0) :
    (P.continuousPathKernel hκ).map (fun p (i : I) => p i) =
      markovObservationKernel P.realizedTransition I := by
  have hm : Measurable (fun p : GraphContinuousPath P.geometry => fun i : I => p i.val) :=
    measurable_pi_lambda _ (fun i => (continuous_eval_const i.val).measurable)
  ext x : 1
  exact (Kernel.map_apply _ hm x).trans (P.continuousPathLaw_finite_observations hκ x I)

end TimeTraps.Analysis
