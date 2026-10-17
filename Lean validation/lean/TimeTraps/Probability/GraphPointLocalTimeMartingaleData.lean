module

public import TimeTraps.Probability.GraphPointLocalTimeNormalization
public import TimeTraps.Probability.GraphPointLocalTimeMartingalePotential

@[expose] public section

/-! The literal raw-adapted graph point-local-time terminal process.
Its correction is the genuine original heat point potential. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTimeTerminalProcess
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (H t : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  P.pointLocalTime a (min t H) p +
    P.realizedHeatPointPotential (p (min t H)) a (H.val - (min t H).val)

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalProcess_stronglyAdapted
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (H : ℝ≥0) :
    StronglyAdapted (graphContinuousNaturalFiltration P.geometry) (P.pointLocalTimeTerminalProcess a H) := by
  intro t
  have hX : StronglyMeasurable[graphContinuousNaturalFiltration P.geometry t]
      (fun p : GraphContinuousPath P.geometry => p (min t H)) :=
    (graphContinuousPath_past_measurable P.geometry (min_le_left t H)).stronglyMeasurable
  exact ((P.pointLocalTime_stronglyAdapted a (min t H)).mono
    ((graphContinuousNaturalFiltration P.geometry).mono (min_le_left t H))).add
      ((P.pointMartingalePotentialState a (H.val - (min t H).val)).continuous.comp_stronglyMeasurable hX)

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalProcess_continuous_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (H : ℝ≥0) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, Continuous (fun t => P.pointLocalTimeTerminalProcess a H t p) := by
  filter_upwards [P.pointLocalTime_regular_ae hκ x a] with p hp
  have hc : Continuous (fun t : ℝ≥0 => min t H) := continuous_id.min continuous_const
  have hq := P.realizedHeatPointPotential_joint_continuous.comp
    (show Continuous (fun t : ℝ≥0 => ((p (min t H), a), H.val - (min t H).val)) from
      ((p.continuous.comp hc).prodMk continuous_const).prodMk
        (continuous_const.sub (NNReal.continuous_coe.comp hc)))
  exact (hp.1.comp hc).add hq

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalProcess_of_horizon_le
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    {H t : ℝ≥0} (hHt : H ≤ t) :
    P.pointLocalTimeTerminalProcess a H t = P.pointLocalTime a H := by
  funext p
  simp only [pointLocalTimeTerminalProcess, min_eq_right hHt, sub_self,
    realizedHeatPointPotential, intervalIntegral.integral_same, add_zero]

end TimeTraps.Analysis
