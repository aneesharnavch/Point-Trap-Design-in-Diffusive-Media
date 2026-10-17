module

public import TimeTraps.Probability.GraphOccupationCompactL2

@[expose] public section

/-! Exact difference norms in the Banach-valued occupation L2 space.
The uniform compact-time square is integrable, and is the actual L2
distance used in the subsequent uniform-time construction. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupationCompactL2_sub
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    P.occupationCompactL2 hκ x (f - g) T =
      P.occupationCompactL2 hκ x f T - P.occupationCompactL2 hκ x g T := by
  apply Lp.ext
  filter_upwards [P.occupationCompactL2_coe hκ x (f - g) T,
    P.occupationCompactL2_coe hκ x f T, P.occupationCompactL2_coe hκ x g T,
    Lp.coeFn_sub (P.occupationCompactL2 hκ x f T) (P.occupationCompactL2 hκ x g T)] with p hd hf hg hs
  rw [hs]
  change _ = P.occupationCompactL2 hκ x f T p - P.occupationCompactL2 hκ x g T p
  rw [hd, hf, hg]
  exact graphOccupationCompactPath_sub P.geometry f g T p

theorem GraphShiftedContactOperatorProblem.occupationCompactL2_sub_norm_sq
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    ‖P.occupationCompactL2 hκ x f T - P.occupationCompactL2 hκ x g T‖ ^ 2 =
      ∫ p, ‖graphOccupationCompactPath P.geometry f T p -
        graphOccupationCompactPath P.geometry g T p‖ ^ 2 ∂P.continuousPathLaw hκ x := by
  rw [← P.occupationCompactL2_sub, P.occupationCompactL2_norm_sq]
  exact integral_congr_ae (Eventually.of_forall (fun p => by
    dsimp only
    rw [graphOccupationCompactPath_sub]))

theorem GraphShiftedContactOperatorProblem.occupationCompactL2_sub_norm_sq_sup
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    ‖P.occupationCompactL2 hκ x f T - P.occupationCompactL2 hκ x g T‖ ^ 2 =
      ∫ p, (⨆ t : Icc (0 : ℝ≥0) T,
        |graphOccupation P.geometry f t.val p - graphOccupation P.geometry g t.val p|) ^ 2
          ∂P.continuousPathLaw hκ x := by
  rw [P.occupationCompactL2_sub_norm_sq]
  exact integral_congr_ae (Eventually.of_forall (fun p => by
    dsimp only
    rw [graphOccupationCompactPath_sub_norm_eq]))

theorem GraphShiftedContactOperatorProblem.occupationCompact_sub_norm_sq_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    Integrable (fun p => ‖graphOccupationCompactPath P.geometry f T p -
      graphOccupationCompactPath P.geometry g T p‖ ^ 2) (P.continuousPathLaw hκ x) := by
  have h := ((P.occupationCompact_memLp hκ x f T).sub
    (P.occupationCompact_memLp hκ x g T)).norm
  exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mp h

end TimeTraps.Analysis
