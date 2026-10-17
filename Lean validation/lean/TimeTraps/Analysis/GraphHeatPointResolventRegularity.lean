module

public import TimeTraps.Analysis.GraphHeatPointResolventData
public import TimeTraps.Probability.GraphPointLocalTimeDiscountEnvelope

@[expose] public section

/-! Exponential integrability and continuity of the literal discounted
point potential, derived from the actual graph heat bound. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter TimeTraps.Probability

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPotential_integrable
    (P : GraphShiftedContactOperatorProblem V E) (a x : GraphRealization P.geometry)
    {q : ℝ} (hq : 0 < q) :
    IntegrableOn (fun H : ℝ => Real.exp (-(q * H)) * P.realizedHeatPointPotential x a H) (Ioi 0) := by
  obtain ⟨C, _, hb⟩ := P.realizedHeatPointPotential_global_bound
  have hp := P.realizedHeatPointPotential_joint_continuous.comp
    (show Continuous (fun H : ℝ => ((x, a), H)) from continuous_const.prodMk continuous_id)
  have he : Continuous (fun H : ℝ => Real.exp (-(q * H))) := by fun_prop
  have hm := he.mul hp
  apply ((graphPointDiscount_envelope_integrable hq).const_mul C).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
  change ‖Real.exp (-(q * H)) * P.realizedHeatPointPotential x a H‖ ≤
    C * (Real.exp (-(q * H)) * (H + 2 * Real.sqrt H))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hb H hH.le x a).2.1)]
  nlinarith [(mul_le_mul_of_nonneg_left (hb H hH.le x a).2.2 (Real.exp_pos (-(q * H))).le)]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPotential_continuous
    (P : GraphShiftedContactOperatorProblem V E) {q : ℝ} (hq : 0 < q) :
    Continuous (fun z : GraphRealization P.geometry × GraphRealization P.geometry =>
      P.pointLocalTimeDiscountedPotential z.2 q z.1) := by
  obtain ⟨C, _, hb⟩ := P.realizedHeatPointPotential_global_bound
  have hm (z : GraphRealization P.geometry × GraphRealization P.geometry) :=
    (P.pointLocalTimeDiscountedPotential_integrable z.2 z.1 hq).aestronglyMeasurable
  have hbound (z : GraphRealization P.geometry × GraphRealization P.geometry) :
      ∀ᵐ H ∂volume.restrict (Ioi (0 : ℝ)),
        ‖Real.exp (-(q * H)) * P.realizedHeatPointPotential z.1 z.2 H‖ ≤
          C * (Real.exp (-(q * H)) * (H + 2 * Real.sqrt H)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hb H hH.le z.1 z.2).2.1)]
    nlinarith [mul_le_mul_of_nonneg_left (hb H hH.le z.1 z.2).2.2 (Real.exp_pos (-(q * H))).le]
  have hc : ∀ᵐ H ∂volume.restrict (Ioi (0 : ℝ)), Continuous
      (fun z : GraphRealization P.geometry × GraphRealization P.geometry =>
        Real.exp (-(q * H)) * P.realizedHeatPointPotential z.1 z.2 H) := by
    apply Eventually.of_forall
    intro H
    have hm : Continuous (fun z : GraphRealization P.geometry × GraphRealization P.geometry => (z, H)) :=
      continuous_id.prodMk continuous_const
    have hU := P.realizedHeatPointPotential_joint_continuous.comp hm
    exact hU.const_mul (Real.exp (-(q * H)))
  exact (continuous_of_dominated hm hbound
    ((graphPointDiscount_envelope_integrable hq).const_mul C) hc).const_mul q

end TimeTraps.Analysis
