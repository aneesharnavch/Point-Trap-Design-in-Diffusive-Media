module

public import TimeTraps.Probability.BrownianLocalTimeSampleOrder

@[expose] public section

/-! A countable grid-order event is jointly measurable in level and
outcome. Fubini therefore gives one full-probability event on which the
grid values are ordered for almost every spatial level. No intersection
over an uncountable family of level events is used. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

def brownianLocalTimeGridOrdered (a : ℝ) (ω : ℕ → ℝ) : Prop :=
  ∀ i j : ℕ, brownianDyadicTime i ≤ brownianDyadicTime j →
    brownianDyadicLocalTimeJointVersion a (brownianDyadicTime i) ω ≤
      brownianDyadicLocalTimeJointVersion a (brownianDyadicTime j) ω

theorem brownianDyadicLocalTimeJointVersion_timeSlice_measurable (t : ℝ≥0) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => brownianDyadicLocalTimeJointVersion p.1 t p.2) := by
  have hm := brownianLocalTimeJointVersion_timeSlice_measurable
    brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable t
  change Measurable (fun p : ℝ × (ℕ → ℝ) => brownianDyadicLocalTimeJointVersion p.1 t p.2) at hm
  exact hm

theorem brownianLocalTimeGridOrdered_measurableSet :
    MeasurableSet {p : ℝ × (ℕ → ℝ) | brownianLocalTimeGridOrdered p.1 p.2} := by
  simp only [brownianLocalTimeGridOrdered, ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
    MeasurableSet.iInter (fun _h => measurableSet_le
      (brownianDyadicLocalTimeJointVersion_timeSlice_measurable (brownianDyadicTime i))
      (brownianDyadicLocalTimeJointVersion_timeSlice_measurable (brownianDyadicTime j)))))

theorem brownianLocalTimeGridOrdered_ae (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, brownianLocalTimeGridOrdered a ω := by
  filter_upwards [brownianLocalTimeSampleAgreement_ae a] with ω hω
  intro i j hij
  rw [hω i, hω j]
  exact brownianLocalTimeGlobalPath_monotone a ω hij

theorem brownianLocalTimeGridOrdered_product_ae :
    ∀ᵐ p ∂(volume : Measure ℝ).prod brownianDyadicMeasure,
      brownianLocalTimeGridOrdered p.1 p.2 :=
  (Measure.ae_prod_iff_ae_ae brownianLocalTimeGridOrdered_measurableSet).mpr
    (Eventually.of_forall brownianLocalTimeGridOrdered_ae)

theorem brownianLocalTimeGridOrdered_spatial_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ᵐ a ∂(volume : Measure ℝ),
      brownianLocalTimeGridOrdered a ω :=
  (Measure.ae_ae_comm (μ := (volume : Measure ℝ)) (ν := brownianDyadicMeasure)
    (p := brownianLocalTimeGridOrdered) brownianLocalTimeGridOrdered_measurableSet).mp
      (Eventually.of_forall brownianLocalTimeGridOrdered_ae)

end TimeTraps.Probability
