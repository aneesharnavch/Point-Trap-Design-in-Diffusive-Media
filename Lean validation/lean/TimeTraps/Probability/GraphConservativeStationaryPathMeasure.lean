module

public import TimeTraps.Probability.GraphConservativePathKernel
public import TimeTraps.Probability.GraphConservativeContinuousMarginal
public import TimeTraps.Probability.GraphConservativeReversibility
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! The genuine conservative path law with unnormalized graph-length
initial distribution. Its finite mixture, signed Fubini formula and
stationary marginals are derived from the actual path kernel. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def GraphShiftedContactOperatorProblem.stationaryPathMeasure
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0) :
    Measure (GraphContinuousPath P.geometry) :=
  P.continuousPathKernel h0 ∘ₘ P.geometry.lengthMeasure

instance GraphShiftedContactOperatorProblem.stationaryPathMeasure_finite
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0) :
    IsFiniteMeasure (P.stationaryPathMeasure h0) := by
  unfold stationaryPathMeasure
  infer_instance

theorem GraphShiftedContactOperatorProblem.stationaryPathMeasure_integral
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    {F : GraphContinuousPath P.geometry → ℝ} (hF : Integrable F (P.stationaryPathMeasure h0)) :
    (∫ p, F p ∂P.stationaryPathMeasure h0) =
      ∫ x, (∫ p, F p ∂P.continuousPathLaw h0 x) ∂P.geometry.lengthMeasure := by
  change Integrable F (P.continuousPathKernel h0 ∘ₘ P.geometry.lengthMeasure) at hF
  rw [Measure.comp_eq_comp_const_apply] at hF
  rw [stationaryPathMeasure, Measure.comp_eq_comp_const_apply]
  exact Kernel.integral_comp hF

theorem GraphShiftedContactOperatorProblem.stationaryPathMeasure_integrable_integral
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    {F : GraphContinuousPath P.geometry → ℝ} (hF : Integrable F (P.stationaryPathMeasure h0)) :
    Integrable (fun x => ∫ p, F p ∂P.continuousPathLaw h0 x) P.geometry.lengthMeasure := by
  change Integrable F (P.continuousPathKernel h0 ∘ₘ P.geometry.lengthMeasure) at hF
  rw [Measure.comp_eq_comp_const_apply] at hF
  exact hF.integral_comp

theorem GraphShiftedContactOperatorProblem.stationaryPathMeasure_bounded_integrable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    {F : GraphContinuousPath P.geometry → ℝ} (hF : Measurable F)
    {C : ℝ} (hC : ∀ p, ‖F p‖ ≤ C) : Integrable F (P.stationaryPathMeasure h0) :=
  (integrable_const C).mono' hF.aestronglyMeasurable (Eventually.of_forall hC)

theorem GraphShiftedContactOperatorProblem.stationaryPathMeasure_marginal
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0) (t : ℝ≥0) :
    (P.stationaryPathMeasure h0).map (fun p => p t) = P.geometry.lengthMeasure := by
  have hm : Measurable (fun p : GraphContinuousPath P.geometry => p t) :=
    (continuous_eval_const t).measurable
  have hk : (P.continuousPathKernel h0).map (fun p => p t) = P.realizedTransition t := by
    ext x : 1
    rw [Kernel.map_apply _ hm x]
    exact P.continuousPathLaw_marginal h0 x t
  rw [stationaryPathMeasure, Measure.map_comp _ _ hm, hk]
  exact (P.realizedTransition_length_invariant h0 t).def

theorem GraphShiftedContactOperatorProblem.stationaryPathMeasure_univ
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0) :
    P.stationaryPathMeasure h0 univ = P.geometry.lengthMeasure univ := by
  have hh := congrArg (fun ν : Measure (GraphRealization P.geometry) => ν univ)
    (P.stationaryPathMeasure_marginal h0 0)
  rw [Measure.map_apply (continuous_eval_const (0 : ℝ≥0)).measurable MeasurableSet.univ,
    preimage_univ] at hh
  exact hh

end TimeTraps.Analysis
