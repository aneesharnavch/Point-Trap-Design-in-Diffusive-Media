module

public import TimeTraps.Analysis.CompactHeatGroundRemainder
public import TimeTraps.Analysis.GeneralIntervalPointHeat
public import TimeTraps.Spectral.IntervalHeatGroundRemainderGap

@[expose] public section

/-! The actual analytic interval heat evolution has an L2 remainder
controlled by the second enumerated eigenvalue after its principal mode
is removed. The original physical Rayleigh value is the first rate;
the complete enumeration and its strict first gap are derived. This
file does not identify the heat operator with a stochastic expectation. -/

namespace TimeTraps.Spectral

open TimeTraps.Analysis
open scoped NNReal

variable {n : ℕ}

theorem SpectralProblem.interval_heat_ground_remainder_le (P : SpectralProblem n)
    (t : ℝ≥0) (f : IntervalSobolevL2 0 P.length) :
    ‖P.intervalPointProblem.compactPositiveInverse.heatSemigroup t f -
      (Real.exp (-P.principalValue * t.val) *
        inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)) f) •
          P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)‖ ≤
      Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * t.val) *
        ‖f - inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)) f •
          P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)‖ := by
  let := P.intervalPointProblem.infinite_spectralIndex
  have hb := P.intervalPointProblem.compactPositiveInverse.heatSemigroup_ground_remainder_le t f
  have hc (i : CompactSpectralIndex P.intervalPointProblem.inverse) :
      compactHeatCoefficient t i = Real.exp (-i.1⁻¹ * t.val) := by
    unfold compactHeatCoefficient
    congr 1
    simp only [div_eq_mul_inv, neg_mul]
    exact congrArg Neg.neg (mul_comm (t : ℝ) i.1⁻¹)
  change ‖P.intervalPointProblem.compactPositiveInverse.heatSemigroup t f -
      (compactHeatCoefficient t (P.intervalPointProblem.spectralEnumeration 0) *
        inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)) f) •
          P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)‖ ≤
      compactHeatCoefficient t (P.intervalPointProblem.spectralEnumeration 1) *
        ‖f - inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)) f •
          P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)‖ at hb
  simpa only [hc, P.interval_first_eigenvalue] using hb

theorem SpectralProblem.interval_heatCurve_ground_remainder_le (P : SpectralProblem n)
    {t : ℝ} (ht : 0 ≤ t) (f : IntervalSobolevL2 0 P.length) :
    ‖P.intervalPointProblem.heatCurve f t -
      (Real.exp (-P.principalValue * t) *
        inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)) f) •
          P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)‖ ≤
      Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * t) *
        ‖f - inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)) f •
          P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)‖ := by
  let phi := P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)
  let Q : ℝ → Prop := fun s =>
    ‖P.intervalPointProblem.compactPositiveInverse.heatSemigroup t.toNNReal f -
      (Real.exp (-P.principalValue * s) * inner ℝ phi f) • phi‖ ≤
      Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * s) *
        ‖f - inner ℝ phi f • phi‖
  have hb : Q (t.toNNReal : ℝ) := P.interval_heat_ground_remainder_le t.toNNReal f
  exact (congrArg Q (Real.coe_toNNReal t ht)).mp hb

end TimeTraps.Spectral
