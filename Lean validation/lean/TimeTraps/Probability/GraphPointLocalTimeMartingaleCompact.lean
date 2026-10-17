module

public import TimeTraps.Probability.GraphPointLocalTimeMartingale
public import TimeTraps.Probability.ContinuousMartingaleMaximal

@[expose] public section

/-! The point-local-time terminal martingale has a genuine measurable
compact continuous version. One event identifies every time with the
raw adapted process; Doob yields its actual compact-time L2 bound. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTimeTerminalCompactPath
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (H : ℝ≥0)
    (p : GraphContinuousPath P.geometry) : C(Icc (0 : ℝ≥0) H, ℝ) := by
  have hq := P.realizedHeatPointPotential_joint_continuous.comp
    (show Continuous (fun t : Icc (0 : ℝ≥0) H => ((p t.val, a), H.val - t.val.val)) from
      ((p.continuous.comp continuous_subtype_val).prodMk continuous_const).prodMk
        (continuous_const.sub (NNReal.continuous_coe.comp continuous_subtype_val)))
  exact ⟨fun t => P.pointLocalTimePath a p t.val + P.realizedHeatPointPotential (p t.val) a (H.val - t.val.val),
    ((P.pointLocalTimePath a p).continuous.comp continuous_subtype_val).add hq⟩

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalCompactPath_eq_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (H : ℝ≥0) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ t : Icc (0 : ℝ≥0) H,
      P.pointLocalTimeTerminalCompactPath a H p t = P.pointLocalTimeTerminalProcess a H t.val p := by
  filter_upwards [P.pointLocalTime_eq_path_ae hκ x a] with p hp
  intro t
  change P.pointLocalTimePath a p t.val + _ = P.pointLocalTime a (min t.val H) p + _
  rw [min_eq_left t.property.2, hp t.val]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalCompactPath_stronglyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (H : ℝ≥0) :
    StronglyMeasurable (P.pointLocalTimeTerminalCompactPath a H) := by
  let : Nonempty (Icc (0 : ℝ≥0) H) := ⟨⟨0, by simp⟩⟩
  apply compactPath_stronglyMeasurable
  intro t
  exact ((continuous_eval_const t.val).measurable.comp (P.pointLocalTimePath_measurable a)).add
    ((P.pointMartingalePotentialState a (H.val - t.val.val)).continuous.measurable.comp
      (continuous_eval_const t.val).measurable)

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalCompactPath_terminal
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (H : ℝ≥0)
    (p : GraphContinuousPath P.geometry) :
    P.pointLocalTimeTerminalCompactPath a H p ⟨H, by simp⟩ = P.pointLocalTimePath a p H := by
  simp only [pointLocalTimeTerminalCompactPath, ContinuousMap.coe_mk, sub_self,
    realizedHeatPointPotential, intervalIntegral.integral_same, add_zero]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalCompactPath_maximal
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (H : ℝ≥0) :
    MemLp (P.pointLocalTimeTerminalCompactPath a H) 2 (P.continuousPathLaw hκ x) ∧
      (∫ p, ‖P.pointLocalTimeTerminalCompactPath a H p‖ ^ 2 ∂P.continuousPathLaw hκ x) ≤
        4 * ∫ p, P.pointLocalTime a H p ^ 2 ∂P.continuousPathLaw hκ x := by
  let inst := P.continuousPathLaw_probability hκ x
  have h := continuousMartingale_compact_maximal (P.pointLocalTimeTerminalProcess_martingale hκ x a H)
    (P.pointLocalTimeTerminalProcess_memLp hκ x a H) H (P.pointLocalTimeTerminalCompactPath a H)
    (P.pointLocalTimeTerminalCompactPath_stronglyMeasurable a H).aestronglyMeasurable
    (fun t => (P.pointLocalTimeTerminalCompactPath_eq_ae hκ x a H).mono (fun _ hp => hp t))
  simpa only [P.pointLocalTimeTerminalProcess_of_horizon_le a (le_refl H)] using h

end TimeTraps.Analysis
