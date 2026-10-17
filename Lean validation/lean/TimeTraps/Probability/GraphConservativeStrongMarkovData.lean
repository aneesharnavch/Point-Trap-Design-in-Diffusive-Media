module

public import TimeTraps.Probability.GraphConservativeMarkov
public import TimeTraps.Probability.ContinuousObservationStoppingData

@[expose] public section

/-! Actual graph continuous observations satisfy the measurability,
integrability and deterministic set-integral hypotheses required for
passing to finite-valued stopping times. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

omit [Nonempty E] in
theorem graphObservation_stronglyAdapted (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) :
    StronglyAdapted (graphContinuousNaturalFiltration G) (fun t (p : GraphContinuousPath G) => f (p t)) :=
  fun t => f.continuous.comp_stronglyMeasurable (graphContinuousPath_current_measurable G t).stronglyMeasurable

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_transition_setIntegral
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ))
    (s h : ℝ≥0) {A : Set (GraphContinuousPath P.geometry)}
    (hA : MeasurableSet[graphContinuousNaturalFiltration P.geometry s] A) :
    (∫ p in A, P.realizedFeller h f (p s) ∂P.continuousPathLaw hκ x) =
      ∫ p in A, f (p (s + h)) ∂P.continuousPathLaw hκ x := by
  let inst := P.continuousPathLaw_probability hκ x
  have hi : Integrable (fun p : GraphContinuousPath P.geometry => f (p (s + h)))
      (P.continuousPathLaw hκ x) :=
    Integrable.of_bound (f.continuous.comp (continuous_eval_const (s + h))).aestronglyMeasurable
      ‖f‖ (Eventually.of_forall (fun p => f.norm_coe_le_norm _))
  have hc := P.continuousPathLaw_markov hκ x (show s ≤ s + h from le_add_of_nonneg_right bot_le) f
  simp only [add_tsub_cancel_left] at hc
  exact (integral_congr_ae (hc.symm.filter_mono ae_restrict_le)).trans
    (setIntegral_condExp ((graphContinuousNaturalFiltration P.geometry).le s) hi hA)

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_stopped_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ))
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry)
      (fun p => (τ p : WithTop ℝ≥0))) :
    Integrable (fun p : GraphContinuousPath P.geometry => f (p (τ p))) (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact continuousObservation_stopped_integrable (P.continuousPathLaw hκ x)
    (fun t (p : GraphContinuousPath P.geometry) => f (p t)) (graphObservation_stronglyAdapted P.geometry f)
    (fun p => f.continuous.comp p.continuous) (fun _ p => f.norm_coe_le_norm _) hτ

end TimeTraps.Analysis
