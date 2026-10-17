module

public import TimeTraps.Probability.GraphBorelResolventData
public import TimeTraps.Probability.GraphConservativeContinuousMarginal
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section

/-! Joint time/state measurability for bounded Borel transition tests is
derived from the actual measurable continuous-path kernel and its proved
single-time laws. It is not a Feller continuity assumption on the test. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.borelTransition_observation_integral
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (t : ℝ≥0) (f : GraphRealization P.geometry → ℝ) (hf : Measurable f) :
    (∫ p, f (p t) ∂P.continuousPathLaw hκ x) = ∫ z, f z ∂P.realizedTransition t x := by
  rw [← P.continuousPathLaw_marginal hκ x t]
  exact (integral_map (continuous_eval_const t).measurable.aemeasurable hf.aestronglyMeasurable).symm

theorem GraphShiftedContactOperatorProblem.borelTransition_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (f : GraphRealization P.geometry → ℝ) (hf : Measurable f) :
    Measurable (fun q : ℝ≥0 × GraphRealization P.geometry => ∫ z, f z ∂P.realizedTransition q.1 q.2) := by
  let K : Kernel (ℝ≥0 × GraphRealization P.geometry) (GraphContinuousPath P.geometry) :=
    (P.continuousPathKernel hκ).comap
    (Prod.snd : ℝ≥0 × GraphRealization P.geometry → GraphRealization P.geometry) measurable_snd
  have hm : StronglyMeasurable (fun q : (ℝ≥0 × GraphRealization P.geometry) × GraphContinuousPath P.geometry =>
      f (q.2 q.1.1)) := by
    apply (hf.comp ?_).stronglyMeasurable
    fun_prop
  have hi := hm.integral_kernel_prod_right' (κ := K)
  have he : (fun q : ℝ≥0 × GraphRealization P.geometry => ∫ p, f (p q.1) ∂K q) =
      (fun q => ∫ z, f z ∂P.realizedTransition q.1 q.2) := by
    funext q
    exact P.borelTransition_observation_integral hκ q.2 q.1 f hf
  rw [← he]
  exact hi.measurable

theorem GraphShiftedContactOperatorProblem.borelTransition_norm_le
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (f : GraphRealization P.geometry → ℝ) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C)
    (t : ℝ≥0) (x : GraphRealization P.geometry) :
    ‖∫ z, f z ∂P.realizedTransition t x‖ ≤ C := by
  let instK := P.realizedTransition_isMarkov hκ t
  simpa [measureReal_def] using
    (norm_integral_le_of_norm_le_const (μ := P.realizedTransition t x) (Filter.Eventually.of_forall hC))

end TimeTraps.Analysis
