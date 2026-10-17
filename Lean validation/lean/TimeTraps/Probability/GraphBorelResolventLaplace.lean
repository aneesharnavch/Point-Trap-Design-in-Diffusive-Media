module

public import TimeTraps.Probability.GraphBorelResolventTransition

@[expose] public section

/-! The transition Laplace integral for an arbitrary bounded Borel test.
Its measurability and its equality to the actual discounted path payoff
are proved before any elliptic identification. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.borelTransitionLaplace
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphRealization P.geometry → ℝ)
    (α : ℝ) (x : GraphRealization P.geometry) : ℝ :=
  ∫ r in Ioi (0 : ℝ), Real.exp (-α * r) * ∫ z, f z ∂P.realizedTransition r.toNNReal x

theorem GraphShiftedContactOperatorProblem.borelTransitionLaplace_measurable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (f : GraphRealization P.geometry → ℝ) (hf : Measurable f) (α : ℝ) :
    Measurable (P.borelTransitionLaplace f α) := by
  have ht : Measurable (fun q : ℝ × GraphRealization P.geometry =>
      ∫ z, f z ∂P.realizedTransition q.1.toNNReal q.2) :=
    (P.borelTransition_jointlyMeasurable hκ f hf).comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hw : Measurable (fun q : ℝ × GraphRealization P.geometry => Real.exp (-α * q.1)) := by fun_prop
  exact (hw.mul ht).stronglyMeasurable.integral_prod_left'.measurable

theorem GraphShiftedContactOperatorProblem.borelTransitionLaplace_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (f : GraphRealization P.geometry → ℝ) (hf : Measurable f) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C)
    {α : ℝ} (hα : 0 < α) (x : GraphRealization P.geometry) :
    IntegrableOn (fun r : ℝ => Real.exp (-α * r) * ∫ z, f z ∂P.realizedTransition r.toNNReal x) (Ioi 0) := by
  have hm : Measurable (fun r : ℝ => ∫ z, f z ∂P.realizedTransition r.toNNReal x) :=
    (P.borelTransition_jointlyMeasurable hκ f hf).comp (measurable_real_toNNReal.prodMk measurable_const)
  apply ((exp_neg_integrableOn_Ioi 0 hα).mul_const C).mono'
    (((by fun_prop : Measurable (fun r : ℝ => Real.exp (-α * r))).mul hm).aestronglyMeasurable)
  apply Eventually.of_forall
  intro r
  simp only [Pi.mul_apply]
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (P.borelTransition_norm_le hκ f hC _ x) (Real.exp_pos _).le

theorem GraphShiftedContactOperatorProblem.borelDiscountedFuture_mean_zero
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) {α : ℝ} (hα : 0 < α) :
    (∫ p, P.borelDiscountedFuture f α 0 p ∂P.continuousPathLaw hκ x) = P.borelTransitionLaplace f α x := by
  let inst := P.continuousPathLaw_probability hκ x
  unfold borelDiscountedFuture borelTransitionLaplace
  simp only [NNReal.coe_zero, sub_zero]
  have hi := P.borelDiscountedFuture_product_integrable hκ x f hf hC hα 0
  simp only [NNReal.coe_zero, sub_zero] at hi
  rw [← integral_integral_swap hi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun r => by
    dsimp only
    rw [integral_const_mul, P.borelTransition_observation_integral hκ x r.toNNReal f hf])

end TimeTraps.Analysis
