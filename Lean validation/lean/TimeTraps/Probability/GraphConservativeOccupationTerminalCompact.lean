module

public import TimeTraps.Probability.GraphConservativeOccupationTerminalData
public import TimeTraps.Probability.GraphOccupationCompactMeasurable

@[expose] public section

/-! The literal terminal-occupation martingale as a measurable compact
continuous path. Its endpoint is the original occupation random variable. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.occupationTerminalCompactPath
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (H : ℝ≥0) (p : GraphContinuousPath P.geometry) : C(Icc (0 : ℝ≥0) H, ℝ) :=
  ⟨fun t => P.occupationTerminalProcess f H t.val p,
    (P.occupationTerminalProcess_continuous f H p).comp continuous_subtype_val⟩

theorem GraphShiftedContactOperatorProblem.occupationTerminalCompactPath_stronglyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ)) (H : ℝ≥0) :
    StronglyMeasurable (P.occupationTerminalCompactPath f H) := by
  let : Nonempty (Icc (0 : ℝ≥0) H) := ⟨⟨0, by simp⟩⟩
  apply compactPath_stronglyMeasurable
  intro t
  exact (((P.occupationTerminalProcess_stronglyAdapted f H t.val).mono
    ((graphContinuousNaturalFiltration P.geometry).le t.val)).measurable)

theorem GraphShiftedContactOperatorProblem.occupationTerminalCompactPath_norm_le
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (H : ℝ≥0) (p : GraphContinuousPath P.geometry) :
    ‖P.occupationTerminalCompactPath f H p‖ ≤ H.val * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg H.coe_nonneg (norm_nonneg f))).mpr
  intro t
  exact P.occupationTerminalProcess_norm_le f H t.val p

theorem GraphShiftedContactOperatorProblem.occupationTerminalCompactPath_memLp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (H : ℝ≥0) :
    MemLp (P.occupationTerminalCompactPath f H) 2 (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact MemLp.of_bound (P.occupationTerminalCompactPath_stronglyMeasurable f H).aestronglyMeasurable
    (H.val * ‖f‖) (Eventually.of_forall (P.occupationTerminalCompactPath_norm_le f H))

theorem GraphShiftedContactOperatorProblem.occupationTerminalCompactPath_terminal
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (H : ℝ≥0) (p : GraphContinuousPath P.geometry) :
    P.occupationTerminalCompactPath f H p ⟨H, by simp⟩ = graphOccupation P.geometry f H p :=
  congrFun (P.occupationTerminalProcess_of_horizon_le f (le_refl H)) p

end TimeTraps.Analysis
