module

public import TimeTraps.Probability.GraphConservativeFuturePathCylinder

@[expose] public section

/-! The entire future path, restricted to any event in the stopped past,
has the actual starting-state path kernel. This is proved from finite
products, not assumed as a restart property. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal BoundedContinuousFunction

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.futurePath_stopping_map_eq
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry) (fun p => (τ p : WithTop ℝ≥0)))
    {A : Set (GraphContinuousPath P.geometry)} (hA : MeasurableSet[hτ.measurableSpace] A) :
    ((P.continuousPathLaw hκ x).restrict A).map (fun p => graphContinuousPathShift P.geometry (τ p) p) =
      (((P.continuousPathLaw hκ x).restrict A) ⊗ₘ P.stoppedPathKernel hκ hτ).map Prod.snd := by
  let inst := P.continuousPathLaw_probability hκ x
  apply graphMarkovPath_measure_ext
  intro w
  rw [integral_map (graphContinuousPathShift_stopped_measurable P.geometry hτ).aemeasurable
    (graphMarkovPathProduct P.geometry w).continuous.measurable.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable
      (graphMarkovPathProduct P.geometry w).continuous.measurable.aestronglyMeasurable]
  exact P.futurePathProduct_setIntegral hκ x w hτ hA

theorem GraphShiftedContactOperatorProblem.futurePath_borel_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry) (fun p => (τ p : WithTop ℝ≥0)))
    {g : GraphContinuousPath P.geometry → ℝ} (hg : Measurable g)
    {C : ℝ} (hb : ∀ p, ‖g p‖ ≤ C) :
    Integrable (fun p => g (graphContinuousPathShift P.geometry (τ p) p)) (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact Integrable.of_bound (hg.comp
    (graphContinuousPathShift_stopped_measurable P.geometry hτ)).aestronglyMeasurable
      C (Eventually.of_forall (fun p => hb _))

theorem GraphShiftedContactOperatorProblem.stoppedPathKernel_borel_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry) (fun p => (τ p : WithTop ℝ≥0)))
    (ν : Measure (GraphContinuousPath P.geometry)) [IsFiniteMeasure ν]
    {g : GraphContinuousPath P.geometry → ℝ} (hg : Measurable g)
    {C : ℝ} (hb : ∀ p, ‖g p‖ ≤ C) :
    Integrable (fun q => g q.2) (ν ⊗ₘ P.stoppedPathKernel hκ hτ) :=
  Integrable.of_bound (hg.comp measurable_snd).aestronglyMeasurable C
    (Eventually.of_forall (fun q => hb q.2))

theorem GraphShiftedContactOperatorProblem.futurePath_borel_setIntegral
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry) (fun p => (τ p : WithTop ℝ≥0)))
    {g : GraphContinuousPath P.geometry → ℝ} (hg : Measurable g)
    {C : ℝ} (hb : ∀ p, ‖g p‖ ≤ C)
    {A : Set (GraphContinuousPath P.geometry)} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ p in A, g (graphContinuousPathShift P.geometry (τ p) p) ∂P.continuousPathLaw hκ x) =
      ∫ p in A, (∫ q, g q ∂P.continuousPathLaw hκ (p (τ p))) ∂P.continuousPathLaw hκ x := by
  let inst := P.continuousPathLaw_probability hκ x
  calc
    _ = ∫ q, g q ∂((P.continuousPathLaw hκ x).restrict A).map
        (fun p => graphContinuousPathShift P.geometry (τ p) p) :=
      (integral_map (graphContinuousPathShift_stopped_measurable P.geometry hτ).aemeasurable
        hg.aestronglyMeasurable).symm
    _ = ∫ q, g q ∂(((P.continuousPathLaw hκ x).restrict A) ⊗ₘ P.stoppedPathKernel hκ hτ).map Prod.snd :=
      congrArg (fun ν => ∫ q, g q ∂ν) (P.futurePath_stopping_map_eq hκ x hτ hA)
    _ = _ := (integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable).trans
      (Measure.integral_compProd (P.stoppedPathKernel_borel_integrable hκ hτ
        ((P.continuousPathLaw hκ x).restrict A) hg hb))

end TimeTraps.Analysis
