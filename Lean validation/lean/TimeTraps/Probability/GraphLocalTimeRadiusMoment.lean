module

public import TimeTraps.Probability.GraphLocalTimeRadius
public import TimeTraps.Probability.GraphConservativeOccupationUniform
public import TimeTraps.Probability.GraphOccupationPotentialCauchy

@[expose] public section

/-! The single deterministic radius schedule has geometric compact-path
increment moments, uniformly in every initial and target graph point.
This supplies measure-independent almost-sure reconstruction data. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.localTimeRadius_difference_potential
    (P : GraphShiftedContactOperatorProblem V E) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) ((n : ℝ) + 1)) (x a : GraphRealization P.geometry) :
    |P.occupationPotential (P.geometry.pointBump a (P.localTimeRadius (n + 1)) -
      P.geometry.pointBump a (P.localTimeRadius n)) t x| ≤ 2 * graphLocalTimeError n := by
  rw [P.occupationPotential_sub, ContinuousMap.sub_apply]
  have ht' : t ∈ Icc (0 : ℝ) (((n + 1 : ℕ) : ℝ) + 1) := by
    constructor
    · exact ht.1
    · push_cast
      linarith [ht.2]
  calc
    _ = |(P.occupationPotential (P.geometry.pointBump a (P.localTimeRadius (n + 1))) t x -
        P.realizedHeatPointPotential x a t) -
        (P.occupationPotential (P.geometry.pointBump a (P.localTimeRadius n)) t x -
        P.realizedHeatPointPotential x a t)| := by congr 1; ring
    _ ≤ |P.occupationPotential (P.geometry.pointBump a (P.localTimeRadius (n + 1))) t x -
        P.realizedHeatPointPotential x a t| +
        |P.occupationPotential (P.geometry.pointBump a (P.localTimeRadius n)) t x -
        P.realizedHeatPointPotential x a t| := abs_sub _ _
    _ ≤ graphLocalTimeError (n + 1) + graphLocalTimeError n :=
      add_le_add (P.localTimeRadius_potential_error (n + 1) ht' x a)
        (P.localTimeRadius_potential_error n ht x a)
    _ ≤ 2 * graphLocalTimeError n := by linarith [graphLocalTimeError_succ_le n]

theorem GraphShiftedContactOperatorProblem.localTimeRadius_difference_moment
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ≥0) (x a : GraphRealization P.geometry) (n : ℕ),
      (H : ℝ) ≤ (n : ℝ) + 1 →
      (∫ p, ‖graphOccupationCompactPath P.geometry (P.geometry.pointBump a (P.localTimeRadius (n + 1))) H p -
        graphOccupationCompactPath P.geometry (P.geometry.pointBump a (P.localTimeRadius n)) H p‖ ^ 2
          ∂P.continuousPathLaw hκ x) ≤
        (64 * C * ((H : ℝ) + 2 * Real.sqrt H) + 8) * graphLocalTimeError n := by
  obtain ⟨C, hC, hb⟩ := P.occupationPotential_pointBump_bound
  refine ⟨C, hC, ?_⟩
  intro H x a n hH
  let f := P.geometry.pointBump a (P.localTimeRadius (n + 1))
  let g := P.geometry.pointBump a (P.localTimeRadius n)
  have hU : ∀ t ∈ Icc (0 : ℝ) (H : ℝ), ∀ y,
      |P.occupationPotential (f - g) t y| ≤ 2 * graphLocalTimeError n := by
    intro t ht y
    exact P.localTimeRadius_difference_potential n ⟨ht.1, ht.2.trans hH⟩ y a
  have hM := P.occupationCompact_difference_square_bound hκ x f g
    (fun y => P.geometry.pointBump_nonneg a y _) (fun y => P.geometry.pointBump_nonneg a y _)
    H (mul_nonneg zero_le_two (graphLocalTimeError_pos n).le) hU
  have hB : P.occupationPotential (f + g) (H : ℝ) x ≤ 2 * (C * ((H : ℝ) + 2 * Real.sqrt (H : ℝ))) := by
    rw [P.occupationPotential_add, ContinuousMap.add_apply, two_mul]
    exact add_le_add (hb (H : ℝ) H.coe_nonneg a x (P.localTimeRadius (n + 1))).2
      (hb (H : ℝ) H.coe_nonneg a x (P.localTimeRadius n)).2
  have he0 := (graphLocalTimeError_pos n).le
  have he1 := graphLocalTimeError_le_one n
  have he2 : graphLocalTimeError n ^ 2 ≤ graphLocalTimeError n := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr he1)]
  apply hM.trans
  have hprod := mul_le_mul_of_nonneg_left hB
    (show 0 ≤ 16 * (2 * graphLocalTimeError n) by positivity)
  calc
    _ ≤ 16 * (2 * graphLocalTimeError n) * (2 * (C * ((H : ℝ) + 2 * Real.sqrt (H : ℝ)))) +
        2 * (2 * graphLocalTimeError n) ^ 2 := add_le_add hprod le_rfl
    _ = 64 * C * ((H : ℝ) + 2 * Real.sqrt (H : ℝ)) * graphLocalTimeError n +
        8 * graphLocalTimeError n ^ 2 := by ring
    _ ≤ 64 * C * ((H : ℝ) + 2 * Real.sqrt (H : ℝ)) * graphLocalTimeError n +
        8 * graphLocalTimeError n := add_le_add le_rfl (mul_le_mul_of_nonneg_left he2 (by norm_num))
    _ = _ := by ring

end TimeTraps.Analysis
