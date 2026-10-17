module

public import TimeTraps.Probability.GraphPointLocalTimeMartingaleData

@[expose] public section

/-! Horizon and sample measurability of the literal terminal process in
its raw past sigma algebra. Clamped scalar approximants, rather than a
future-dependent path convention, establish the local-time part. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.pointLocalTime_clamped_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (t : ℝ≥0) :
    @Measurable (ℝ × GraphContinuousPath P.geometry) ℝ
      (MeasurableSpace.prod inferInstance (graphContinuousNaturalFiltration P.geometry t)) _
      (fun q => P.pointLocalTime a (min t q.1.toNNReal) q.2) := by
  let : MeasurableSpace (GraphContinuousPath P.geometry) := graphContinuousNaturalFiltration P.geometry t
  change Measurable (graphLocalTimeScalarLimit (fun n (q : ℝ × GraphContinuousPath P.geometry) =>
    P.localTimeApproximant a n q.2 (min t q.1.toNNReal)))
  apply graphLocalTimeScalarLimit_measurable
  intro n
  apply (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (u := fun (H : ℝ) (p : GraphContinuousPath P.geometry) =>
      P.localTimeApproximant a n p (min t H.toNNReal)) ?_ ?_).measurable
  · intro p
    exact (P.localTimeApproximant a n p).continuous.comp
      (continuous_const.min continuous_real_toNNReal)
  · intro H
    exact (P.localTimeApproximant_stronglyAdapted a n (min t H.toNNReal)).mono
      ((graphContinuousNaturalFiltration P.geometry).mono (min_le_left _ _))

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalProcess_horizon_stronglyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (t : ℝ≥0) :
    @StronglyMeasurable (ℝ × GraphContinuousPath P.geometry) ℝ _
      (MeasurableSpace.prod inferInstance (graphContinuousNaturalFiltration P.geometry t))
      (fun q => P.pointLocalTimeTerminalProcess a q.1.toNNReal t q.2) := by
  let : MeasurableSpace (GraphContinuousPath P.geometry) := graphContinuousNaturalFiltration P.geometry t
  have hX : StronglyMeasurable (fun q : ℝ × GraphContinuousPath P.geometry => q.2 (min t q.1.toNNReal)) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun (H : ℝ) (p : GraphContinuousPath P.geometry) => p (min t H.toNNReal))
    · intro p
      exact p.continuous.comp (continuous_const.min continuous_real_toNNReal)
    · intro H
      exact (graphContinuousPath_past_measurable P.geometry (min_le_left t H.toNNReal)).stronglyMeasurable
  have htime : StronglyMeasurable (fun q : ℝ × GraphContinuousPath P.geometry =>
      q.1.toNNReal.val - (min t q.1.toNNReal).val) := by
    exact ((NNReal.continuous_coe.comp continuous_real_toNNReal).sub
      (NNReal.continuous_coe.comp (continuous_const.min continuous_real_toNNReal))).stronglyMeasurable.comp_measurable measurable_fst
  have hpot := P.realizedHeatPointPotential_joint_continuous.comp_stronglyMeasurable
    ((hX.prodMk (stronglyMeasurable_const (b := a))).prodMk htime)
  exact (P.pointLocalTime_clamped_jointlyMeasurable a t).stronglyMeasurable.add hpot

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountTerminal_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (α : ℝ) (t : ℝ≥0) :
    @StronglyMeasurable (ℝ × GraphContinuousPath P.geometry) ℝ _
      (MeasurableSpace.prod inferInstance (graphContinuousNaturalFiltration P.geometry t))
      (fun q => Real.exp (-(α * q.1)) * P.pointLocalTimeTerminalProcess a q.1.toNNReal t q.2) := by
  let : MeasurableSpace (GraphContinuousPath P.geometry) := graphContinuousNaturalFiltration P.geometry t
  exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).stronglyMeasurable).comp_measurable
    measurable_fst).mul (P.pointLocalTimeTerminalProcess_horizon_stronglyMeasurable a t)

end TimeTraps.Analysis
