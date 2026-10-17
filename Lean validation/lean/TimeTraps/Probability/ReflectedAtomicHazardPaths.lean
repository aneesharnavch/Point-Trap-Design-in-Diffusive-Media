module

public import TimeTraps.Probability.ReflectedAtomicHazardData

@[expose] public section

/-! On one event for the finite collection of labels, the actual hazard
is continuous, nondecreasing, and starts at zero; its exponential weight
is continuous, nonincreasing, and starts at one. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

theorem reflectedAtomicHazard_paths_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Continuous (fun t => reflectedAtomicHazard L D x a κ t ω) ∧
      Monotone (fun t => reflectedAtomicHazard L D x a κ t ω) ∧
      reflectedAtomicHazard L D x a κ 0 ω = 0 ∧
      Continuous (fun t => reflectedAtomicSurvival L D x a κ t ω) ∧
      Antitone (fun t => reflectedAtomicSurvival L D x a κ t ω) ∧
      reflectedAtomicSurvival L D x a κ 0 ω = 1 := by
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L (a i))
  filter_upwards [hall] with ω hω
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hc : Continuous (fun t => reflectedAtomicHazard L D x a κ t ω) := by
    unfold reflectedAtomicHazard weightedContactHazard reflectedInteriorOccupationCoefficient
    exact continuous_finsetSum Finset.univ (fun i _ =>
      ((reflectedInteriorCorrection_continuous hσ hL (hω i)).div_const _).const_mul _)
  have hm : Monotone (fun t => reflectedAtomicHazard L D x a κ t ω) := by
    intro s t hst
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hκ i)
    exact div_le_div_of_nonneg_right
      (reflectedInteriorCorrection_monotone hσ hL (hω i) hst) (sq_nonneg _)
  have hz : reflectedAtomicHazard L D x a κ 0 ω = 0 := by
    unfold reflectedAtomicHazard weightedContactHazard reflectedInteriorOccupationCoefficient
    simp only [reflectedInteriorCorrection_zero hσ (hω _), zero_div, mul_zero, Finset.sum_const_zero]
  refine ⟨hc, hm, hz, Real.continuous_exp.comp hc.neg, ?_, ?_⟩
  · intro s t hst
    exact Real.exp_le_exp.mpr (neg_le_neg (hm hst))
  · simp only [reflectedAtomicSurvival, hz, neg_zero, Real.exp_zero]

end TimeTraps.Probability
