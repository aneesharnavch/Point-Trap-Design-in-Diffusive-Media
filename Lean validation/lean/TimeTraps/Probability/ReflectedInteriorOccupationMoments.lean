module

public import TimeTraps.Probability.ReflectedInteriorLocalTimeData
public import TimeTraps.Probability.ReflectedItoRegulatorMoments

@[expose] public section

/-! Square integrability of the actual periodized interior correction and
its occupation-scaled coefficient, derived from the shifted regulators. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem reflectedInteriorCorrection_memLp (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) (T : ℝ≥0) :
    MemLp (reflectedInteriorCorrection x (Real.sqrt (2 * D)) L a T) 2 brownianDyadicMeasure :=
  (reflectedLowerRegulator_memLp L hL D hD (x - a) T).add
    (reflectedLowerRegulator_memLp L hL D hD (x + a) T)

theorem reflectedInteriorOccupationCoefficient_memLp (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) (T : ℝ≥0) :
    MemLp (reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a T)
      2 brownianDyadicMeasure := by
  change MemLp (fun ω => reflectedInteriorCorrection x (Real.sqrt (2 * D)) L a T ω /
    (Real.sqrt (2 * D)) ^ 2) 2 brownianDyadicMeasure
  simpa only [div_eq_mul_inv] using
    (reflectedInteriorCorrection_memLp L hL D hD x a T).mul_const ((Real.sqrt (2 * D)) ^ 2)⁻¹

end TimeTraps.Probability
