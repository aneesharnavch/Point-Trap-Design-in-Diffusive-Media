module

public import TimeTraps.Probability.GraphConservativeOccupationTerminalCompact

@[expose] public section

/-! The actual compact occupation curve differs from its terminal
martingale by the literal remaining potential. Uniformly small
potentials therefore reduce uniform occupation control to Doob's bound. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupationCompact_norm_le_terminal
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (H : ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε)
    (hU : ∀ r ∈ Icc (0 : ℝ) H.val, ∀ y, |P.occupationPotential f r y| ≤ ε)
    (p : GraphContinuousPath P.geometry) :
    ‖graphOccupationCompactPath P.geometry f H p‖ ≤ ‖P.occupationTerminalCompactPath f H p‖ + ε := by
  apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _) hε)).mpr
  intro t
  have htH : t.val ≤ H := t.property.2
  have hr : H.val - t.val.val ∈ Icc (0 : ℝ) H.val :=
    ⟨sub_nonneg.mpr htH, sub_le_self _ t.val.coe_nonneg⟩
  have he : graphOccupation P.geometry f t.val p =
      P.occupationTerminalCompactPath f H p t - P.occupationPotential f (H.val - t.val.val) (p t.val) := by
    change _ = (graphOccupation P.geometry f (min t.val H) p +
      P.occupationPotential f (H.val - (min t.val H).val) (p (min t.val H))) - _
    rw [min_eq_left htH]
    ring
  change ‖graphOccupation P.geometry f t.val p‖ ≤ _
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add
    ((P.occupationTerminalCompactPath f H p).norm_coe_le_norm t) (hU _ hr _))

theorem GraphShiftedContactOperatorProblem.occupationCompact_sq_le_terminal
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (H : ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε)
    (hU : ∀ r ∈ Icc (0 : ℝ) H.val, ∀ y, |P.occupationPotential f r y| ≤ ε)
    (p : GraphContinuousPath P.geometry) :
    ‖graphOccupationCompactPath P.geometry f H p‖ ^ 2 ≤
      2 * ‖P.occupationTerminalCompactPath f H p‖ ^ 2 + 2 * ε ^ 2 := by
  have h := P.occupationCompact_norm_le_terminal f H hε hU p
  have hA := norm_nonneg (graphOccupationCompactPath P.geometry f H p)
  have hM := norm_nonneg (P.occupationTerminalCompactPath f H p)
  nlinarith [sq_nonneg (‖P.occupationTerminalCompactPath f H p‖ - ε)]

end TimeTraps.Analysis
