module

public import TimeTraps.Probability.GraphConservativeFuturePathLaw
public import TimeTraps.Probability.KernelConditionalIntegral

@[expose] public section

/-! Whole-path strong Markov for the constructed conservative graph
diffusion. Every bounded Borel functional of the entire future path is
allowed, at every finite-valued stopping time of the raw natural filtration. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_future_strongMarkov
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry) (fun p => (τ p : WithTop ℝ≥0)))
    {g : GraphContinuousPath P.geometry → ℝ} (hg : Measurable g)
    {C : ℝ} (hb : ∀ p, ‖g p‖ ≤ C) :
    (P.continuousPathLaw hκ x)[(fun p => g (graphContinuousPathShift P.geometry (τ p) p)) |
      hτ.measurableSpace] =ᵐ[P.continuousPathLaw hκ x]
        (fun p => ∫ q, g q ∂P.continuousPathKernel hκ (p (τ p))) := by
  let inst := P.continuousPathLaw_probability hκ x
  have hsm : StronglyMeasurable[hτ.measurableSpace]
      (fun p => ∫ q, g q ∂P.continuousPathKernel hκ (p (τ p))) :=
    (hg.stronglyMeasurable.integral_kernel.measurable.comp
      (graphContinuousPath_stopped_measurable P.geometry hτ)).stronglyMeasurable
  have hi : Integrable (fun p => ∫ q, g q ∂P.continuousPathKernel hκ (p (τ p)))
      (P.continuousPathLaw hκ x) :=
    Integrable.of_bound (hsm.mono hτ.measurableSpace_le).aestronglyMeasurable C
      (Eventually.of_forall (fun p => kernel_integral_bound (P.continuousPathKernel hκ) g hb _))
  apply (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le
    (P.futurePath_borel_integrable hκ x hτ hg hb) _ _ hsm.aestronglyMeasurable).symm
  · exact fun _ _ _ => hi.integrableOn
  · exact fun _ hA _ => (P.futurePath_borel_setIntegral hκ x hτ hg hb hA).symm

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_future_markov
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (s : ℝ≥0)
    {g : GraphContinuousPath P.geometry → ℝ} (hg : Measurable g)
    {C : ℝ} (hb : ∀ p, ‖g p‖ ≤ C) :
    (P.continuousPathLaw hκ x)[(fun p => g (graphContinuousPathShift P.geometry s p)) |
      graphContinuousNaturalFiltration P.geometry s] =ᵐ[P.continuousPathLaw hκ x]
        (fun p => ∫ q, g q ∂P.continuousPathKernel hκ (p s)) := by
  have he := P.continuousPathLaw_future_strongMarkov hκ x
    (isStoppingTime_const (graphContinuousNaturalFiltration P.geometry) s) hg hb
  simpa only [IsStoppingTime.measurableSpace_const] using he

end TimeTraps.Analysis
