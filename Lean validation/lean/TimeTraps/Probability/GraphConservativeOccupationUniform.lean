module

public import TimeTraps.Probability.GraphConservativeOccupationMaximal
public import TimeTraps.Probability.GraphOccupationCompactDifference
public import TimeTraps.Probability.OccupationPotentialCauchyBound

@[expose] public section

/-! Uniform-in-time mean-square control of nonnegative graph occupation
approximants by their true semigroup-potential error. The terminal Kac
bound and the continuous martingale maximal theorem are both derived
for the actual continuous graph law. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupationCompact_difference_square_bound
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ))
    (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y) (H : ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε)
    (hU : ∀ r ∈ Icc (0 : ℝ) H.val, ∀ y, |P.occupationPotential (f - g) r y| ≤ ε) :
    (∫ p, ‖graphOccupationCompactPath P.geometry f H p -
        graphOccupationCompactPath P.geometry g H p‖ ^ 2 ∂P.continuousPathLaw hκ x) ≤
      16 * ε * P.occupationPotential (f + g) H.val x + 2 * ε ^ 2 := by
  have hM := P.occupationCompact_second_moment_bound hκ x (f - g) H hε hU
  have hB := P.occupation_difference_square_bound hκ x f g hf hg H.coe_nonneg hU
  simp only [graphOccupationCompactPath_sub] at hM
  have he : (∫ p, graphOccupation P.geometry (f - g) H p ^ 2 ∂P.continuousPathLaw hκ x) =
      ∫ p : GraphContinuousPath P.geometry,
        ((∫ s in 0..H.val, f (p s.toNNReal)) - (∫ s in 0..H.val, g (p s.toNNReal))) ^ 2
          ∂P.continuousPathLaw hκ x := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro p
    have hd := congrArg (fun q : C(Icc (0 : ℝ≥0) H, ℝ) => q ⟨H, by simp⟩)
      (graphOccupationCompactPath_sub P.geometry f g H p)
    simp only [ContinuousMap.sub_apply, graphOccupationCompactPath_apply, graphOccupation] at hd
    exact congrArg (fun z : ℝ => z ^ 2) hd
  rw [he] at hM
  apply hM.trans
  calc
    _ ≤ 8 * (2 * ε * P.occupationPotential (f + g) H.val x) + 2 * ε ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hB (show (0 : ℝ) ≤ 8 by norm_num)) (le_refl (2 * ε ^ 2))
    _ = _ := by ring

theorem GraphShiftedContactOperatorProblem.occupationCompactL2_difference_bound
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ))
    (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y) (H : ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε)
    (hU : ∀ r ∈ Icc (0 : ℝ) H.val, ∀ y, |P.occupationPotential (f - g) r y| ≤ ε) :
    ‖P.occupationCompactL2 hκ x f H - P.occupationCompactL2 hκ x g H‖ ^ 2 ≤
      16 * ε * P.occupationPotential (f + g) H.val x + 2 * ε ^ 2 := by
  rw [P.occupationCompactL2_sub_norm_sq]
  exact P.occupationCompact_difference_square_bound hκ x f g hf hg H hε hU

theorem GraphShiftedContactOperatorProblem.occupation_sup_difference_square_bound
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f g : C(GraphRealization P.geometry, ℝ))
    (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y) (H : ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε)
    (hU : ∀ r ∈ Icc (0 : ℝ) H.val, ∀ y, |P.occupationPotential (f - g) r y| ≤ ε) :
    (∫ p, (⨆ t : Icc (0 : ℝ≥0) H,
      |graphOccupation P.geometry f t.val p - graphOccupation P.geometry g t.val p|) ^ 2
        ∂P.continuousPathLaw hκ x) ≤
      16 * ε * P.occupationPotential (f + g) H.val x + 2 * ε ^ 2 := by
  rw [← P.occupationCompactL2_sub_norm_sq_sup]
  exact P.occupationCompactL2_difference_bound hκ x f g hf hg H hε hU

end TimeTraps.Analysis
