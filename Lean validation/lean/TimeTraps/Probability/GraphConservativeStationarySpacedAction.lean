module

public import TimeTraps.Probability.GraphConservativeStationarySpacing
public import TimeTraps.Analysis.GraphShiftedContactFellerConservative

@[expose] public section

/-! The explicit terminal heat acts on the genuine constant one state.
Operator-word reversal therefore gives equality of stationary cylinder
expectations at reversed observation times. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.heatWordSpaced_apply_one
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (s T : ℝ≥0) (w : GraphMarkovWord P.geometry) :
    P.heatWordApply (graphMarkovSpacedLetters s T w) 1 =
      P.markovCylinderKernel (graphMarkovDurations s w) := by
  induction w generalizing s with
  | nil =>
    change P.realizedFeller (T - s) (ContinuousMap.const _ (1 : ℝ)) = ContinuousMap.const _ 1
    exact P.realizedFeller_one h0 (T - s)
  | cons a w ih =>
    rcases a with ⟨t, f⟩
    change P.realizedFeller (t - s) (f * P.heatWordApply (graphMarkovSpacedLetters t T w) 1) =
      P.realizedFeller (t - s) (f * P.markovCylinderKernel (graphMarkovDurations t w))
    rw [ih t]

theorem GraphShiftedContactOperatorProblem.markovCylinder_length_reverse
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (w : GraphMarkovWord P.geometry) (T : ℝ≥0) (hw : ∀ a ∈ w, a.1 ≤ T) :
    (∫ x, P.markovCylinderKernel (graphMarkovDurations 0 w) x ∂P.geometry.lengthMeasure) =
      ∫ x, P.markovCylinderKernel
        (graphMarkovDurations 0 (w.reverse.map (fun a => (T - a.1, a.2)))) x
          ∂P.geometry.lengthMeasure := by
  have he := P.heatWordApply_reverse h0 (graphMarkovSpacedLetters 0 T w) 1 1
  rw [graphMarkovSpacedLetters_reverse w T hw, P.heatWordSpaced_apply_one h0,
    P.heatWordSpaced_apply_one h0] at he
  simpa only [ContinuousMap.one_apply, one_mul] using he

omit [Fintype V] [Fintype E] [Nonempty E] in
theorem graphMarkov_reverse_times_pairwise {G : MetricGraph V E}
    (w : GraphMarkovWord G) (T : ℝ≥0) (hw : w.Pairwise (fun a b => a.1 ≤ b.1)) :
    (w.reverse.map (fun a => (T - a.1, a.2))).Pairwise (fun a b => a.1 ≤ b.1) := by
  rw [List.pairwise_map]
  exact hw.reverse.imp (fun hab => tsub_le_tsub_left hab T)

end TimeTraps.Analysis
