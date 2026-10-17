module

public import TimeTraps.Analysis.GraphHeatPointResolventL2

@[expose] public section

/-! The source resolvent accepts bounded Borel observations on the actual
graph realization. The original length measure and independent edge L2
representatives give its pointwise weak-solution interpretation. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter InnerProductSpace

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def GraphShiftedContactOperatorProblem.borelResolventOne
    (P : GraphShiftedContactOperatorProblem V E) (g : GraphRealization P.geometry → ℝ)
    (a : GraphRealization P.geometry) : ℝ :=
  ∫ y, g y * P.pointLocalTimeDiscountedPotential a 1 y ∂P.geometry.lengthMeasure

omit [Nonempty E] in
theorem graphLengthMeasure_integral_bounded (G : MetricGraph V E)
    {g : GraphRealization G → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ y, ‖g y‖ ≤ C) :
    (∫ y, g y ∂G.lengthMeasure) = ∑ e, ∫ x in Ioo (0 : ℝ) (G.length e), g (G.edgePointClamped e x) := by
  have hi (e : E) : Integrable g (G.edgeLengthMeasure e) :=
    (integrable_const C).mono' hg.aestronglyMeasurable (Eventually.of_forall hC)
  rw [MetricGraph.lengthMeasure, integral_finsetSum_measure (fun e _ => hi e)]
  exact Finset.sum_congr rfl (fun e _ => G.edgeLengthMeasure_integral e g hg)

theorem GraphShiftedContactOperatorProblem.borelResolventOne_integrable
    (P : GraphShiftedContactOperatorProblem V E) {g : GraphRealization P.geometry → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ y, ‖g y‖ ≤ C) (a : GraphRealization P.geometry) :
    Integrable (fun y => g y * P.pointLocalTimeDiscountedPotential a 1 y) P.geometry.lengthMeasure := by
  let r := graphRealizedSobolev P.geometry (P.pointResolventSolution a)
  have hm : Measurable (fun y => g y * r y) := hg.mul r.continuous.measurable
  have hi : Integrable (fun y => g y * r y) P.geometry.lengthMeasure := by
    apply (integrable_const (C * ‖r‖)).mono' hm.aestronglyMeasurable
    apply Eventually.of_forall
    intro y
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (r.norm_coe_le_norm y) ((norm_nonneg (g y)).trans (hC y)))
  simpa only [P.pointLocalTimeDiscountedPotential_one_eq] using hi

theorem GraphShiftedContactOperatorProblem.borelResolventOne_eq_solution
    (P : GraphShiftedContactOperatorProblem V E) {g : GraphRealization P.geometry → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ y, ‖g y‖ ≤ C) (f : GraphL2Product P.geometry)
    (hf : ∀ e, f e =ᵐ[volume.restrict (Ioo (0 : ℝ) (P.geometry.length e))]
      (fun y => g (P.geometry.edgePointClamped e y))) (a : GraphRealization P.geometry) :
    P.borelResolventOne g a = P.realizedSolutionL f a := by
  let r := graphRealizedSobolev P.geometry (P.pointResolventSolution a)
  have hm : Measurable (fun y => g y * r y) := hg.mul r.continuous.measurable
  have hb (y) : ‖g y * r y‖ ≤ C * ‖r‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (r.norm_coe_le_norm y) ((norm_nonneg (g y)).trans (hC y)))
  unfold borelResolventOne
  simp only [P.pointLocalTimeDiscountedPotential_one_eq]
  rw [graphLengthMeasure_integral_bounded P.geometry hm hb,
    P.realizedSolutionL_pointResolvent_integral]
  apply Finset.sum_congr rfl
  intro e _
  rw [intervalIntegral.integral_of_le (P.geometry.length_pos e).le, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [hf e] with y hy
  rw [hy, P.pointLocalTimeDiscountedPotential_one_eq]

end TimeTraps.Analysis
