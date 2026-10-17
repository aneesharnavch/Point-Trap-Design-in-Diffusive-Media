module

public import TimeTraps.Probability.GraphConservativeOccupationUniformData
public import TimeTraps.Probability.GraphConservativeOccupationTerminal
public import TimeTraps.Probability.GraphOccupationCompactL2
public import TimeTraps.Probability.ContinuousMartingaleMaximal

@[expose] public section

/-! Actual compact-time graph occupation control. The martingale maximal
estimate is discharged for the explicit terminal process, and a uniform
potential error bounds the full occupation curve in mean square. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupationTerminalCompact_second_moment
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (H : ℝ≥0) :
    (∫ p, ‖P.occupationTerminalCompactPath f H p‖ ^ 2 ∂P.continuousPathLaw hκ x) ≤
      4 * ∫ p, graphOccupation P.geometry f H p ^ 2 ∂P.continuousPathLaw hκ x := by
  let inst := P.continuousPathLaw_probability hκ x
  have h := continuousMartingale_compact_maximal (P.occupationTerminalProcess_martingale hκ x f H)
    (P.occupationTerminalProcess_memLp hκ x f H) H (P.occupationTerminalCompactPath f H)
    (P.occupationTerminalCompactPath_stronglyMeasurable f H).aestronglyMeasurable
    (fun _ => EventuallyEq.rfl)
  simpa only [P.occupationTerminalProcess_of_horizon_le f (le_refl H)] using h.2

theorem GraphShiftedContactOperatorProblem.occupationCompact_second_moment_bound
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (H : ℝ≥0)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hU : ∀ r ∈ Icc (0 : ℝ) H.val, ∀ y, |P.occupationPotential f r y| ≤ ε) :
    (∫ p, ‖graphOccupationCompactPath P.geometry f H p‖ ^ 2 ∂P.continuousPathLaw hκ x) ≤
      8 * (∫ p, graphOccupation P.geometry f H p ^ 2 ∂P.continuousPathLaw hκ x) + 2 * ε ^ 2 := by
  let inst := P.continuousPathLaw_probability hκ x
  have hA := (P.occupationCompact_memLp hκ x f H).norm
  have hM := (P.occupationTerminalCompactPath_memLp hκ x f H).norm
  have hiA := (memLp_two_iff_integrable_sq hA.aestronglyMeasurable).mp hA
  have hiM := (memLp_two_iff_integrable_sq hM.aestronglyMeasurable).mp hM
  calc
    _ ≤ ∫ p, (2 * ‖P.occupationTerminalCompactPath f H p‖ ^ 2 + 2 * ε ^ 2)
          ∂P.continuousPathLaw hκ x :=
      integral_mono hiA ((hiM.const_mul 2).add (integrable_const _))
        (P.occupationCompact_sq_le_terminal f H hε hU)
    _ = 2 * (∫ p, ‖P.occupationTerminalCompactPath f H p‖ ^ 2 ∂P.continuousPathLaw hκ x) + 2 * ε ^ 2 := by
      rw [integral_add (hiM.const_mul 2) (integrable_const _), integral_const_mul]
      simp
    _ ≤ _ := by linarith [P.occupationTerminalCompact_second_moment hκ x f H]

end TimeTraps.Analysis
