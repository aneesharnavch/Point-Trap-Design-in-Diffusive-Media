module

public import TimeTraps.Probability.GraphConservativeContinuousPathSpace
public import TimeTraps.Probability.GraphConservativeSampledLaw

@[expose] public section

/-! The probability law obtained by applying the proved measurable
continuous-path reconstruction to the actual countably sampled graph law.
Identification of its transition laws is proved separately. -/

namespace TimeTraps.Analysis

open MeasureTheory ProbabilityTheory TimeTraps.Probability TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.continuousPathLaw
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) : Measure (GraphContinuousPath P.geometry) :=
  (P.sampledPathLaw hκ brownianDyadicTime x).map (P.geometry.reconstructedFullPath x)

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_probability
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) : IsProbabilityMeasure (P.continuousPathLaw hκ x) := by
  let inst := P.sampledPathLaw_probability hκ brownianDyadicTime x
  exact Measure.isProbabilityMeasure_map (P.geometry.reconstructedFullPath_measurable x).aemeasurable

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_eval
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (τ : ℕ → ℝ≥0) :
    (P.continuousPathLaw hκ x).map (fun p i => p (τ i)) =
      (P.sampledPathLaw hκ brownianDyadicTime x).map
        (fun q i => P.geometry.reconstructedPath x q (τ i)) :=
  Measure.map_map (measurable_pi_lambda _ (fun _ => (continuous_eval_const _).measurable))
    (P.geometry.reconstructedFullPath_measurable x)

end TimeTraps.Analysis
