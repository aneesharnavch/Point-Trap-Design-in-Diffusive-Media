module

public import TimeTraps.Probability.GraphConservativeOccupationConditional
public import TimeTraps.Probability.GraphConservativeNaturalFiltration
public import TimeTraps.Probability.GraphOccupationCompactBound

@[expose] public section

/-! An explicit continuous version of the terminal-occupation conditional
expectations, stopped at the chosen horizon. All definitions retain the
literal graph path and raw past sigma-algebras. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.occupationTerminalProcess
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (H t : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  graphOccupation P.geometry f (min t H) p +
    P.occupationPotential f (H.val - (min t H).val) (p (min t H))

theorem GraphShiftedContactOperatorProblem.occupationTerminalProcess_continuous
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (H : ℝ≥0) (p : GraphContinuousPath P.geometry) :
    Continuous (fun t => P.occupationTerminalProcess f H t p) := by
  have hc : Continuous (fun t : ℝ≥0 => min t H) := continuous_id.min continuous_const
  exact ((graphOccupation_time_continuous P.geometry f p).comp hc).add
    ((P.occupationPotential_joint_continuous f).comp
      ((continuous_const.sub (NNReal.continuous_coe.comp hc)).prodMk (p.continuous.comp hc)))

theorem GraphShiftedContactOperatorProblem.occupationTerminalProcess_stronglyAdapted
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (H : ℝ≥0) :
    StronglyAdapted (graphContinuousNaturalFiltration P.geometry) (P.occupationTerminalProcess f H) := by
  intro t
  have hX : StronglyAdapted (graphContinuousNaturalFiltration P.geometry)
      (fun s (p : GraphContinuousPath P.geometry) => p s) := Filtration.stronglyAdapted_natural _
  exact ((P.occupation_prefix_stronglyMeasurable _ hX f (min t H)).mono
    ((graphContinuousNaturalFiltration P.geometry).mono (min_le_left t H))).add
    (((P.occupationPotential f (H.val - (min t H).val)).continuous.comp_stronglyMeasurable
      ((hX (min t H)).mono ((graphContinuousNaturalFiltration P.geometry).mono (min_le_left t H)))))

theorem GraphShiftedContactOperatorProblem.occupationTerminalProcess_norm_le
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (H t : ℝ≥0) (p : GraphContinuousPath P.geometry) :
    ‖P.occupationTerminalProcess f H t p‖ ≤ H.val * ‖f‖ := by
  have hrH : (min t H).val ≤ H.val := min_le_right t H
  have hp := (P.occupationPotential f (H.val - (min t H).val)).norm_coe_le_norm (p (min t H))
  calc
    _ ≤ ‖graphOccupation P.geometry f (min t H) p‖ +
        ‖P.occupationPotential f (H.val - (min t H).val) (p (min t H))‖ := norm_add_le _ _
    _ ≤ (min t H).val * ‖f‖ + (H.val - (min t H).val) * ‖f‖ :=
      add_le_add (graphOccupation_norm_le P.geometry f (min t H) p)
        (hp.trans (P.occupationPotential_norm_le f (sub_nonneg.mpr hrH)))
    _ = _ := by ring

theorem GraphShiftedContactOperatorProblem.occupationTerminalProcess_of_horizon_le
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    {H t : ℝ≥0} (hHt : H ≤ t) :
    P.occupationTerminalProcess f H t = graphOccupation P.geometry f H := by
  funext p
  simp only [occupationTerminalProcess, min_eq_right hHt, sub_self, occupationPotential,
    intervalIntegral.integral_same, ContinuousMap.zero_apply, add_zero]

end TimeTraps.Analysis
