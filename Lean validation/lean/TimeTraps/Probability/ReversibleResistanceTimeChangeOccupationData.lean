module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeSubstitution
public import TimeTraps.Probability.ReflectedFoldOccupationTests
public import TimeTraps.Analysis.ReversibleResistanceCoordinateOccupationIntegrable

@[expose] public section

/-! The candidate physical occupation density is the actual reflected
occupation field at the random inverse horizon, multiplied by the original
speed density. Its construction precedes the occupation identity. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal

noncomputable def reversibleResistanceOccupationDensity (A : IntervalMedium) (x : ℝ)
    (T : ℝ≥0) (ω : ℕ → ℝ) (z : ℝ) : ℝ :=
  (Ioo A.source.left A.source.right).indicator (fun z => A.source.density z *
    foldedOccupationDensity A.resistanceLength 1 (A.resistance x)
      (reversibleResistanceInversePath A x T ω) ω (A.resistance z)) z

theorem reversibleResistanceOccupationDensity_nonneg (A : IntervalMedium) (x : ℝ)
    (T : ℝ≥0) (ω : ℕ → ℝ) (z : ℝ) :
    0 ≤ reversibleResistanceOccupationDensity A x T ω z := by
  by_cases hz : z ∈ Ioo A.source.left A.source.right
  · rw [reversibleResistanceOccupationDensity, indicator_of_mem hz]
    exact mul_nonneg (A.source.positive z (Ioo_subset_Icc_self hz)).le ENNReal.toReal_nonneg
  · rw [reversibleResistanceOccupationDensity, indicator_of_notMem hz]

theorem reversibleResistanceSpeed_bound (A : IntervalMedium) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |A.resistanceSpeed y| ≤ C := by
  let q : C(Icc A.source.left A.source.right, ℝ) :=
    ⟨fun z => A.conductance z * A.source.density z,
      (A.conductance_continuous.mul A.source.continuous).domRestrict⟩
  refine ⟨‖q‖, norm_nonneg q, fun y => ?_⟩
  have h := q.norm_coe_le_norm ⟨A.resistanceInverse y, A.resistanceInverse_mem y⟩
  exact h

theorem reversibleResistanceReference_weighted_occupation (A : IntervalMedium) (x : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ (g : ℝ → ℝ), Measurable g →
      ∀ M : ℝ, (∀ z, |g z| ≤ M) → ∀ T : ℝ≥0,
        Integrable (fun y => g (A.resistanceInverse y) * A.resistanceSpeed y *
          foldedOccupationDensity A.resistanceLength 1 (A.resistance x)
            (reversibleResistanceInversePath A x T ω) ω y) volume ∧
        (∫ y, g (A.resistanceInverse y) * A.resistanceSpeed y *
          foldedOccupationDensity A.resistanceLength 1 (A.resistance x)
            (reversibleResistanceInversePath A x T ω) ω y) =
          ∫ t in (0 : ℝ)..T.val, g (reversibleResistancePath A x t.toNNReal ω) := by
  filter_upwards [brownianLocalTimeTimeMeasureRegular_all_times_ae,
    reversibleResistancePath_integral_substitution A x] with ω hω hsub
  intro g hg M hb T
  obtain ⟨C, hC, hc⟩ := reversibleResistanceSpeed_bound A
  have hq : Measurable (fun y => g (A.resistanceInverse y) * A.resistanceSpeed y) :=
    (hg.comp A.resistanceInverse_continuous.measurable).mul A.resistanceSpeed_continuous.measurable
  have hbound (y : ℝ) : |g (A.resistanceInverse y) * A.resistanceSpeed y| ≤ M * C := by
    rw [abs_mul]
    exact mul_le_mul (hb _) (hc y) (abs_nonneg _) ((abs_nonneg (g 0)).trans (hb 0))
  have hi := foldedOccupationDensity_bounded_occupation A.resistanceLength
    A.resistanceLength_pos 1 zero_lt_one (A.resistance x)
      (hω (reversibleResistanceInversePath A x T ω)) hq hbound
  exact ⟨hi.1, hi.2.2.trans (hsub g T).symm⟩

end TimeTraps.Probability
