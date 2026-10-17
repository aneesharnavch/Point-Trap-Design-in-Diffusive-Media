module

public import TimeTraps.Probability.GraphBorelResolventLaplace

@[expose] public section

/-! The conditional continuation sections are jointly measurable in the
raw past sigma algebra and genuinely product-integrable. The bounded
Borel test remains arbitrary. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.borelDiscountedConditional_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (f : GraphRealization P.geometry → ℝ) (hf : Measurable f) (α : ℝ) (s : ℝ≥0) :
    @StronglyMeasurable (ℝ × GraphContinuousPath P.geometry) ℝ _
      (MeasurableSpace.prod inferInstance (graphContinuousNaturalFiltration P.geometry s))
      (fun q => Real.exp (-α * (q.1 - (s : ℝ))) *
        ∫ z, f z ∂P.realizedTransition (q.1 - (s : ℝ)).toNNReal (q.2 s)) := by
  let : MeasurableSpace (GraphContinuousPath P.geometry) := graphContinuousNaturalFiltration P.geometry s
  have hp : Measurable (fun q : ℝ × GraphContinuousPath P.geometry =>
      ((q.1 - (s : ℝ)).toNNReal, q.2 s)) :=
    (measurable_fst.sub_const (s : ℝ)).real_toNNReal.prodMk
      ((graphContinuousPath_current_measurable P.geometry s).comp measurable_snd)
  have he : Measurable (fun q : ℝ × GraphContinuousPath P.geometry => Real.exp (-α * (q.1 - (s : ℝ)))) := by
    fun_prop
  exact (he.mul ((P.borelTransition_jointlyMeasurable hκ f hf).comp hp)).stronglyMeasurable

theorem GraphShiftedContactOperatorProblem.borelDiscountedConditional_product_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : GraphRealization P.geometry → ℝ) (hf : Measurable f)
    {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) {α : ℝ} (hα : 0 < α) (s : ℝ≥0) :
    Integrable (fun q : ℝ × GraphContinuousPath P.geometry => Real.exp (-α * (q.1 - (s : ℝ))) *
      ∫ z, f z ∂P.realizedTransition (q.1 - (s : ℝ)).toNNReal (q.2 s))
      ((volume.restrict (Ioi (s : ℝ))).prod (P.continuousPathLaw hκ x)) := by
  let inst := P.continuousPathLaw_probability hκ x
  have hm := (P.borelDiscountedConditional_jointlyMeasurable hκ f hf α s).mono
    (sup_le_sup le_rfl (MeasurableSpace.comap_mono ((graphContinuousNaturalFiltration P.geometry).le s)))
  apply (((reflectedDiscounted_exponential_integrable hα (s : ℝ)).mul_const C).comp_fst
    (P.continuousPathLaw hκ x)).mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro q
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (P.borelTransition_norm_le hκ f hC _ _) (Real.exp_pos _).le

end TimeTraps.Analysis
