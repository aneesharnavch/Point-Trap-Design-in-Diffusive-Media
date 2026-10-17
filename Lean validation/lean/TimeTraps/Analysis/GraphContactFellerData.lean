module

public import TimeTraps.Analysis.GraphContactRealizedHeatTransition
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! The actual variable-conductance graph transition acts on continuous
functions, preserves positivity and contracts the uniform norm. All
integrals use its previously constructed physical length density. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem GraphContactOperatorProblem.realizedHeatIntegral_continuous
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (f : C(GraphRealization P.geometry, ℝ)) :
    Continuous (fun x => ∫ y, P.realizedHeatKernel t ht x y * f y ∂P.geometry.lengthMeasure) := by
  have hc : Continuous (fun q : GraphRealization P.geometry × GraphRealization P.geometry =>
      P.realizedHeatKernel t ht q.1 q.2 * f q.2) :=
    (P.realizedHeatKernel_continuous t ht).mul (f.continuous.comp continuous_snd)
  have h := continuous_parametric_integral_of_continuous (μ := P.geometry.lengthMeasure)
    (f := fun x y => P.realizedHeatKernel t ht x y * f y)
    hc (s := univ) isCompact_univ
  simpa only [Measure.restrict_univ] using h

noncomputable def GraphContactOperatorProblem.realizedHeatC
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (f : C(GraphRealization P.geometry, ℝ)) : C(GraphRealization P.geometry, ℝ) :=
  ⟨fun x => ∫ y, P.realizedHeatKernel t ht x y * f y ∂P.geometry.lengthMeasure,
    P.realizedHeatIntegral_continuous t ht f⟩

theorem GraphContactOperatorProblem.realizedHeatC_apply
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (f : C(GraphRealization P.geometry, ℝ)) (x : GraphRealization P.geometry) :
    P.realizedHeatC t ht f x = ∫ y, f y ∂P.realizedHeatTransition t ht x :=
  (P.realizedHeatTransition_integral t ht x f).symm

theorem GraphContactOperatorProblem.realizedHeatC_integrable
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (f : C(GraphRealization P.geometry, ℝ)) (x : GraphRealization P.geometry) :
    Integrable f (P.realizedHeatTransition t ht x) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem GraphContactOperatorProblem.realizedHeatC_point_bound
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (f : C(GraphRealization P.geometry, ℝ)) (x : GraphRealization P.geometry) :
    ‖P.realizedHeatC t ht f x‖ ≤ ‖f‖ := by
  rw [P.realizedHeatC_apply]
  have hm : (P.realizedHeatTransition t ht x).real univ ≤ 1 :=
    (ENNReal.toReal_mono ENNReal.one_ne_top (P.realizedHeatTransition_mass_le_one t ht x)).trans_eq
      ENNReal.toReal_one
  calc
    _ ≤ ‖f‖ * (P.realizedHeatTransition t ht x).real univ :=
      norm_integral_le_of_norm_le_const (Eventually.of_forall (fun y => f.norm_coe_le_norm y))
    _ ≤ ‖f‖ := by nlinarith [norm_nonneg f]

theorem GraphContactOperatorProblem.realizedHeatC_norm_le
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (f : C(GraphRealization P.geometry, ℝ)) : ‖P.realizedHeatC t ht f‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg f)).mpr (P.realizedHeatC_point_bound t ht f)

theorem GraphContactOperatorProblem.realizedHeatC_nonneg
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (f : C(GraphRealization P.geometry, ℝ)) (hf : ∀ y, 0 ≤ f y) (x : GraphRealization P.geometry) :
    0 ≤ P.realizedHeatC t ht f x := by
  rw [P.realizedHeatC_apply]
  exact integral_nonneg hf

end TimeTraps.Analysis
