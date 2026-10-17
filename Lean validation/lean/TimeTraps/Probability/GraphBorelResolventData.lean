module

public import TimeTraps.Probability.GraphConservativeMarkov
public import TimeTraps.Probability.GraphConservativePathKernel
public import TimeTraps.Probability.ReflectedDiscountedData

@[expose] public section

/-! Literal discounted ordinary-time occupation for bounded Borel graph
observables. No continuity or agreement of edge traces at vertices is
required; exponential domination proves genuine product integrability. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.borelDiscountedFuture
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphRealization P.geometry → ℝ)
    (α : ℝ) (s : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  ∫ r in Ioi (s : ℝ), Real.exp (-α * (r - (s : ℝ))) * f (p r.toNNReal)

omit [Nonempty E] in
theorem GraphShiftedContactOperatorProblem.borelDiscountedFuture_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) (α : ℝ) (s : ℝ≥0) :
    Measurable (fun q : ℝ × GraphContinuousPath P.geometry =>
      Real.exp (-α * (q.1 - (s : ℝ))) * f (q.2 q.1.toNNReal)) := by
  have hX : Measurable (fun q : ℝ × GraphContinuousPath P.geometry => q.2 q.1.toNNReal) := by
    fun_prop
  have he : Measurable (fun q : ℝ × GraphContinuousPath P.geometry => Real.exp (-α * (q.1 - (s : ℝ)))) := by
    fun_prop
  exact he.mul (hf.comp hX)

theorem GraphShiftedContactOperatorProblem.borelDiscountedFuture_product_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) {α : ℝ} (hα : 0 < α) (s : ℝ≥0) :
    Integrable (fun q : ℝ × GraphContinuousPath P.geometry =>
      Real.exp (-α * (q.1 - (s : ℝ))) * f (q.2 q.1.toNNReal))
      ((volume.restrict (Ioi (s : ℝ))).prod (P.continuousPathLaw hκ x)) := by
  let inst := P.continuousPathLaw_probability hκ x
  apply (((reflectedDiscounted_exponential_integrable hα (s : ℝ)).mul_const C).comp_fst
    (P.continuousPathLaw hκ x)).mono'
      (P.borelDiscountedFuture_jointlyMeasurable f hf α s).aestronglyMeasurable
  apply Eventually.of_forall
  intro q
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hC _) (Real.exp_pos _).le

theorem GraphShiftedContactOperatorProblem.borelDiscountedFuture_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) {α : ℝ} (hα : 0 < α) (s : ℝ≥0) :
    Integrable (P.borelDiscountedFuture f α s) (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact (P.borelDiscountedFuture_product_integrable hκ x f hf hC hα s).integral_prod_right

end TimeTraps.Analysis
