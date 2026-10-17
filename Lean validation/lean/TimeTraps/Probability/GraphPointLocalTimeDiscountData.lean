module

public import TimeTraps.Probability.GraphPointLocalTimeDiscountIntegrable

@[expose] public section

/-! The raw exponential average of the actual terminal martingales and
its integrable terminal random variable. Both are defined independently
of an initial state; the averaged process is raw adapted. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedTotal
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (α : ℝ)
    (p : GraphContinuousPath P.geometry) : ℝ :=
  α * ∫ H in Ioi (0 : ℝ), Real.exp (-(α * H)) * P.pointLocalTime a H.toNNReal p

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedTerminal
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (α : ℝ)
    (t : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  α * ∫ H in Ioi (0 : ℝ), Real.exp (-(α * H)) * P.pointLocalTimeTerminalProcess a H.toNNReal t p

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedTotal_measurable
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (α : ℝ) :
    Measurable (P.pointLocalTimeDiscountedTotal a α) := by
  have hl : StronglyMeasurable (fun q : ℝ × GraphContinuousPath P.geometry =>
      P.pointLocalTime a q.1.toNNReal q.2) :=
    ((P.pointLocalTime_jointlyMeasurable a).comp
      (measurable_fst.real_toNNReal.prodMk measurable_snd)).stronglyMeasurable
  have hw : StronglyMeasurable (fun q : ℝ × GraphContinuousPath P.geometry => Real.exp (-(α * q.1))) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).stronglyMeasurable.comp_measurable measurable_fst
  have hm := hw.mul hl
  exact (hm.integral_prod_left' (μ := volume.restrict (Ioi (0 : ℝ)))).measurable.const_mul α

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedTotal_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) {α : ℝ} (hα : 0 < α) :
    Integrable (P.pointLocalTimeDiscountedTotal a α) (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact (P.pointLocalTimeDiscount_product_integrable hκ x a hα).integral_prod_right.const_mul α

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedTerminal_stronglyAdapted
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (α : ℝ) :
    StronglyAdapted (graphContinuousNaturalFiltration P.geometry) (P.pointLocalTimeDiscountedTerminal a α) := by
  intro t
  let : MeasurableSpace (GraphContinuousPath P.geometry) := graphContinuousNaturalFiltration P.geometry t
  exact ((P.pointLocalTimeDiscountTerminal_jointlyMeasurable a α t).integral_prod_left'
    (μ := volume.restrict (Ioi (0 : ℝ)))).const_mul α

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedTerminal_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) {α : ℝ} (hα : 0 < α) (t : ℝ≥0) :
    Integrable (P.pointLocalTimeDiscountedTerminal a α t) (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact (P.pointLocalTimeDiscountTerminal_product_integrable hκ x a hα t).integral_prod_right.const_mul α

end TimeTraps.Analysis
