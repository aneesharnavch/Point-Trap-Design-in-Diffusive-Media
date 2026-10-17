module

public import TimeTraps.Probability.ReversibleResistanceTransitionRegularity

@[expose] public section

/-! Finite physical-interval pairings of the actual transition
expectation. Their boundedness and time continuity are proved directly
from the constructed diffusion, before any invariant measure is asserted. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology BoundedContinuousFunction

def reversibleResistanceLengthMeasure (A : IntervalMedium) : Measure (Icc A.source.left A.source.right) :=
  volume.comap Subtype.val

instance reversibleResistanceLengthMeasure_finite (A : IntervalMedium) :
    IsFiniteMeasure (reversibleResistanceLengthMeasure A) where
  measure_univ_lt_top := by
    rw [reversibleResistanceLengthMeasure, comap_subtype_coe_apply measurableSet_Icc,
      image_univ, Subtype.range_coe]
    exact isCompact_Icc.measure_lt_top

theorem reversibleResistanceLengthMeasure_integral (A : IntervalMedium) (f : ℝ → ℝ) :
    (∫ x, f x.val ∂reversibleResistanceLengthMeasure A) =
      ∫ x in A.source.left..A.source.right, f x := by
  rw [reversibleResistanceLengthMeasure, integral_subtype_comap measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le A.source.increasing.le]

def reversibleResistanceWeightedTransition (A : IntervalMedium)
    (w : C(Icc A.source.left A.source.right, ℝ)) (g : ℝ →ᵇ ℝ) (t : ℝ≥0) : ℝ :=
  ∫ x, w x * reversibleResistanceTransition A t g x.val ∂reversibleResistanceLengthMeasure A

theorem reversibleResistanceWeightedTransition_integrable (A : IntervalMedium)
    (w : C(Icc A.source.left A.source.right, ℝ)) (g : ℝ →ᵇ ℝ) (t : ℝ≥0) :
    Integrable (fun x => w x * reversibleResistanceTransition A t g x.val)
      (reversibleResistanceLengthMeasure A) := by
  apply (integrable_const (‖w‖ * ‖g‖)).mono'
    ((w.continuous.measurable.mul (reversibleResistanceTransition_measurable_interval A t g.measurable)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  change ‖w x * reversibleResistanceTransition A t g x.val‖ ≤ ‖w‖ * ‖g‖
  rw [norm_mul]
  exact mul_le_mul (w.norm_coe_le_norm x)
    (reversibleResistanceTransition_bound A t g.norm_coe_le_norm x.val) (norm_nonneg _) (norm_nonneg _)

theorem reversibleResistanceWeightedTransition_continuous (A : IntervalMedium)
    (w : C(Icc A.source.left A.source.right, ℝ)) (g : ℝ →ᵇ ℝ) :
    Continuous (reversibleResistanceWeightedTransition A w g) := by
  apply continuous_of_dominated
    (fun t => (reversibleResistanceWeightedTransition_integrable A w g t).aestronglyMeasurable)
    (fun t => Eventually.of_forall (fun x => ?_)) (integrable_const (‖w‖ * ‖g‖))
    (Eventually.of_forall (fun x => (reversibleResistanceTransition_continuous_time A x.property
      g.continuous.continuousOn).const_mul (w x)))
  rw [norm_mul]
  exact mul_le_mul (w.norm_coe_le_norm x)
    (reversibleResistanceTransition_bound A t g.norm_coe_le_norm x.val) (norm_nonneg _) (norm_nonneg _)

theorem reversibleResistanceWeightedTransition_bound (A : IntervalMedium)
    (w : C(Icc A.source.left A.source.right, ℝ)) (g : ℝ →ᵇ ℝ) (t : ℝ≥0) :
    ‖reversibleResistanceWeightedTransition A w g t‖ ≤
      (‖w‖ * ‖g‖) * (reversibleResistanceLengthMeasure A).real univ := by
  apply norm_integral_le_of_norm_le_const
  apply Eventually.of_forall
  intro x
  rw [norm_mul]
  exact mul_le_mul (w.norm_coe_le_norm x)
    (reversibleResistanceTransition_bound A t g.norm_coe_le_norm x.val) (norm_nonneg _) (norm_nonneg _)

end TimeTraps.Probability

end
