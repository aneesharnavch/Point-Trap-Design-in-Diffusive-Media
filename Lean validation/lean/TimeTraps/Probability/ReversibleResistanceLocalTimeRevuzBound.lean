module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeSpatialVersion
public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentLevel

@[expose] public section

/-! Uniform local-time moment bounds needed to integrate over all starting
states in the physical Revuz test. The clock cap and moment constant are
independent of the starting state and of the spatial level. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistanceInversePath_bounded_all_starts (A : IntervalMedium) (T : ℝ≥0) :
    ∃ S : ℝ≥0, ∀ x ω, reversibleResistanceInversePath A x T ω ≤ S := by
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) A.resistanceLength).Nonempty from ⟨0, le_rfl, A.resistanceLength_pos.le⟩)
      A.resistanceSpeed_continuous.continuousOn
  let m : ℝ≥0 := ⟨A.resistanceSpeed y, (A.resistanceSpeed_pos y).le⟩
  refine ⟨T / m, fun x => ?_⟩
  exact reflectedPositiveTimeInversePath_bound A.resistanceLength A.resistanceLength_pos
    1 (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun z _ => A.resistanceSpeed_pos z) m (A.resistanceSpeed_pos y) (fun z hz => hmin hz) T

theorem reversibleResistanceLocalTime_le_reference_ae (A : IntervalMedium) (x a : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S) :
    ∀ᵐ ω ∂brownianDyadicMeasure, reversibleResistanceLocalTime A x a T ω ≤
      reflectedInteriorOccupationCoefficient (A.resistance x) (Real.sqrt (2 * 1))
        A.resistanceLength (A.resistance a) S ω := by
  filter_upwards [reflectedInteriorLocalTimeRegular_ae (A.resistance x) (Real.sqrt (2 * 1))
    A.resistanceLength (A.resistance a)] with ω hω
  exact div_le_div_of_nonneg_right
    (reflectedInteriorCorrection_monotone (Real.sqrt_pos.mpr (by norm_num)) A.resistanceLength_pos hω (hS ω))
      (sq_nonneg _)

theorem reversibleResistanceLocalTime_memLp_two (A : IntervalMedium) (x a : ℝ) (T : ℝ≥0) :
    MemLp (reversibleResistanceLocalTime A x a T) 2 brownianDyadicMeasure := by
  obtain ⟨S, hS⟩ := reversibleResistanceInversePath_bounded A x T
  let q : (ℕ → ℝ) → ℝ≥0 × (ℕ → ℝ) := fun ω => (T, ω)
  have hq : Measurable q := measurable_const.prodMk measurable_id
  have hm := (reversibleResistanceLocalTime_jointlyMeasurable A x a).comp hq
  dsimp only [Function.comp_def, q] at hm
  apply (reflectedInteriorOccupationCoefficient_memLp A.resistanceLength A.resistanceLength_pos
    1 zero_lt_one (A.resistance x) (A.resistance a) S).mono' hm.aestronglyMeasurable
  filter_upwards [reversibleResistanceLocalTime_le_reference_ae A x a T S hS] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (reversibleResistanceLocalTime_nonneg A x a T ω)] using hω

theorem reversibleResistanceLocalTime_secondMoment_bound (A : IntervalMedium) (x a : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S) :
    (∫ ω, reversibleResistanceLocalTime A x a T ω ^ 2 ∂brownianDyadicMeasure) ≤
      3 * A.resistanceLength ^ 2 + 6 * S.val + 3 * (S.val / A.resistanceLength) ^ 2 := by
  calc
    _ ≤ ∫ ω, reflectedInteriorOccupationCoefficient (A.resistance x) (Real.sqrt (2 * 1))
        A.resistanceLength (A.resistance a) S ω ^ 2 ∂brownianDyadicMeasure := by
      apply integral_mono_ae (reversibleResistanceLocalTime_memLp_two A x a T).integrable_sq
        (reflectedInteriorOccupationCoefficient_memLp A.resistanceLength A.resistanceLength_pos
          1 zero_lt_one (A.resistance x) (A.resistance a) S).integrable_sq
      filter_upwards [reversibleResistanceLocalTime_le_reference_ae A x a T S hS] with ω hω
      exact pow_le_pow_left₀ (reversibleResistanceLocalTime_nonneg A x a T ω) hω 2
    _ ≤ _ := by
      simpa only [one_mul, mul_one, one_pow, div_one] using
        reflectedInteriorOccupationCoefficient_secondMoment_uniform_bound A.resistanceLength A.resistanceLength_pos
          1 zero_lt_one (A.resistance x) (A.resistance a) S

theorem reversibleResistanceLocalTime_mean_bound (A : IntervalMedium) (x a : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S) :
    (∫ ω, reversibleResistanceLocalTime A x a T ω ∂brownianDyadicMeasure) ≤
      1 + (3 * A.resistanceLength ^ 2 + 6 * S.val + 3 * (S.val / A.resistanceLength) ^ 2) := by
  have hm := reversibleResistanceLocalTime_memLp_two A x a T
  have hi : (∫ ω, reversibleResistanceLocalTime A x a T ω ∂brownianDyadicMeasure) ≤
      1 + ∫ ω, reversibleResistanceLocalTime A x a T ω ^ 2 ∂brownianDyadicMeasure := by
    calc
      _ ≤ ∫ ω, 1 + reversibleResistanceLocalTime A x a T ω ^ 2 ∂brownianDyadicMeasure := by
        apply integral_mono (hm.integrable (by norm_num)) ((integrable_const 1).add hm.integrable_sq)
        intro ω
        change reversibleResistanceLocalTime A x a T ω ≤ 1 + reversibleResistanceLocalTime A x a T ω ^ 2
        nlinarith [sq_nonneg (reversibleResistanceLocalTime A x a T ω - 1)]
      _ = _ := by rw [integral_add (integrable_const 1) hm.integrable_sq]; simp
  have hb := reversibleResistanceLocalTime_secondMoment_bound A x a T S hS
  linarith

end TimeTraps.Probability
