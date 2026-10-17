module

public import TimeTraps.Analysis.GraphHeatResolventBorel

@[expose] public section

/-! The actual discount-one point kernel maps bounded Borel sources to
bounded continuous functions, with continuity derived by domination. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.borelResolventOne_continuous
    (P : GraphShiftedContactOperatorProblem V E) {g : GraphRealization P.geometry → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ y, ‖g y‖ ≤ C) : Continuous (P.borelResolventOne g) := by
  have hK := P.pointLocalTimeDiscountedPotential_continuous (q := 1) (by norm_num)
  let K : C(GraphRealization P.geometry × GraphRealization P.geometry, ℝ) :=
    ⟨fun z => P.pointLocalTimeDiscountedPotential z.2 1 z.1, hK⟩
  have hm (a : GraphRealization P.geometry) : AEStronglyMeasurable
      (fun y => g y * P.pointLocalTimeDiscountedPotential a 1 y) P.geometry.lengthMeasure :=
    (P.borelResolventOne_integrable hg hC a).aestronglyMeasurable
  have hb (a : GraphRealization P.geometry) : ∀ᵐ y ∂P.geometry.lengthMeasure,
      ‖g y * P.pointLocalTimeDiscountedPotential a 1 y‖ ≤ C * ‖K‖ := by
    apply Eventually.of_forall
    intro y
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (K.norm_coe_le_norm (y, a)) ((norm_nonneg (g y)).trans (hC y)))
  have hc : ∀ᵐ y ∂P.geometry.lengthMeasure, Continuous
      (fun a => g y * P.pointLocalTimeDiscountedPotential a 1 y) := by
    apply Eventually.of_forall
    intro y
    have hp : Continuous (fun a : GraphRealization P.geometry => (y, a)) :=
      continuous_const.prodMk continuous_id
    have hh := hK.comp hp
    exact hh.const_mul (g y)
  exact continuous_of_dominated hm hb (integrable_const _) hc

theorem GraphShiftedContactOperatorProblem.borelResolventOne_bounded
    (P : GraphShiftedContactOperatorProblem V E) {g : GraphRealization P.geometry → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ y, ‖g y‖ ≤ C) :
    ∃ B : ℝ, ∀ a, ‖P.borelResolventOne g a‖ ≤ B := by
  let r : C(GraphRealization P.geometry, ℝ) := ⟨P.borelResolventOne g, P.borelResolventOne_continuous hg hC⟩
  exact ⟨‖r‖, fun a => r.norm_coe_le_norm a⟩

end TimeTraps.Analysis
