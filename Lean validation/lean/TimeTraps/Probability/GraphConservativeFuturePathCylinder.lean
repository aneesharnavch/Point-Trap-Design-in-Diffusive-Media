module

public import TimeTraps.Probability.GraphConservativeFuturePathMeasure
public import TimeTraps.Probability.GraphConservativeMarkovAbsolute
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! The actual path law restarted from the stopped state is a genuine
kernel. Its finite products agree with the stopped future products;
all composition-product integrability is proved before Fubini. -/

noncomputable section
namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal BoundedContinuousFunction

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem graphMarkovPathProduct_future (G : MetricGraph V E)
    (w : GraphMarkovWord G) (t : ℝ≥0) (p : GraphContinuousPath G) :
    graphMarkovPathProduct G w (graphContinuousPathShift G t p) =
      graphMarkovAbsoluteCylinder G w t p := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp only [graphMarkovPathProduct, List.map_cons, List.prod_cons,
        BoundedContinuousFunction.mul_apply, graphMarkovAbsoluteCylinder] at ih ⊢
      rw [ih]
      rfl

variable [Nonempty E]

def GraphShiftedContactOperatorProblem.stoppedPathKernel
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry) (fun p => (τ p : WithTop ℝ≥0))) :
    Kernel (GraphContinuousPath P.geometry) (GraphContinuousPath P.geometry) :=
  (P.continuousPathKernel hκ).comap (fun p => p (τ p))
    ((graphContinuousPath_stopped_measurable P.geometry hτ).mono hτ.measurableSpace_le le_rfl)

instance GraphShiftedContactOperatorProblem.stoppedPathKernel_isMarkov
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry) (fun p => (τ p : WithTop ℝ≥0))) :
    IsMarkovKernel (P.stoppedPathKernel hκ hτ) := by
  unfold stoppedPathKernel
  infer_instance

theorem GraphShiftedContactOperatorProblem.stoppedPathKernel_apply
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry) (fun p => (τ p : WithTop ℝ≥0)))
    (p : GraphContinuousPath P.geometry) :
    P.stoppedPathKernel hκ hτ p = P.continuousPathLaw hκ (p (τ p)) := rfl

theorem GraphShiftedContactOperatorProblem.stoppedPathKernel_product_integral
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry) (fun p => (τ p : WithTop ℝ≥0)))
    (w : GraphMarkovWord P.geometry) (p : GraphContinuousPath P.geometry) :
    (∫ q, graphMarkovPathProduct P.geometry w q ∂P.stoppedPathKernel hκ hτ p) =
      P.markovAbsoluteKernel w (p (τ p)) := by
  rw [P.stoppedPathKernel_apply]
  have he := P.markovAbsoluteCylinder_expectation hκ (p (τ p)) w
  simpa only [← graphMarkovPathProduct_future, graphContinuousPathShift_zero] using he

theorem GraphShiftedContactOperatorProblem.stoppedPathKernel_test_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry) (fun p => (τ p : WithTop ℝ≥0)))
    (ν : Measure (GraphContinuousPath P.geometry)) [IsFiniteMeasure ν]
    (g : GraphContinuousPath P.geometry →ᵇ ℝ) :
    Integrable (fun q => g q.2) (ν ⊗ₘ P.stoppedPathKernel hκ hτ) :=
  Integrable.of_bound (g.continuous.measurable.comp measurable_snd).aestronglyMeasurable
    ‖g‖ (Eventually.of_forall (fun q => g.norm_coe_le_norm q.2))

theorem GraphShiftedContactOperatorProblem.futurePathProduct_setIntegral
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (w : GraphMarkovWord P.geometry)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry) (fun p => (τ p : WithTop ℝ≥0)))
    {A : Set (GraphContinuousPath P.geometry)} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ p in A, graphMarkovPathProduct P.geometry w (graphContinuousPathShift P.geometry (τ p) p)
      ∂P.continuousPathLaw hκ x) =
      ∫ q, graphMarkovPathProduct P.geometry w q.2
        ∂((P.continuousPathLaw hκ x).restrict A ⊗ₘ P.stoppedPathKernel hκ hτ) := by
  let inst := P.continuousPathLaw_probability hκ x
  rw [Measure.integral_compProd (P.stoppedPathKernel_test_integrable hκ hτ
    ((P.continuousPathLaw hκ x).restrict A) (graphMarkovPathProduct P.geometry w))]
  have he := P.markovAbsoluteCylinder_condExp hκ x w hτ
  calc
    _ = ∫ p in A, P.markovAbsoluteKernel w (p (τ p)) ∂P.continuousPathLaw hκ x := by
      simp only [graphMarkovPathProduct_future]
      exact (setIntegral_condExp hτ.measurableSpace_le
        (P.markovAbsoluteCylinder_integrable hκ x w hτ) hA).symm.trans
          (integral_congr_ae (he.filter_mono ae_restrict_le))
    _ = _ := integral_congr_ae (Eventually.of_forall
      (fun p => (P.stoppedPathKernel_product_integral hκ hτ w p).symm))

end TimeTraps.Analysis
end
