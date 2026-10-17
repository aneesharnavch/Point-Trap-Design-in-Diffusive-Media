module

public import TimeTraps.Spectral.NetworkOperatorHeatPositive

@[expose] public section

/-! Quantitative L2 decay with the independently defined network Rayleigh
principal value. The coefficient bound uses its proved equality with
the least operator eigenvalue; Parseval transfers it to every L2 state. -/

namespace TimeTraps.Spectral

open TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem SpectralNetwork.heat_coefficient_gap_bound (P : SpectralNetwork V E)
    (t : ℝ≥0) (i : CompactSpectralIndex P.operatorInverse) :
    Real.exp (-(t : ℝ) / i.1) ≤ Real.exp (-P.principalValue * (t : ℝ)) := by
  apply Real.exp_le_exp.mpr
  calc
    -(t : ℝ) / i.1 = -(i.1⁻¹ * (t : ℝ)) := by ring
    _ ≤ -(P.principalValue * (t : ℝ)) :=
      neg_le_neg (mul_le_mul_of_nonneg_right (P.principal_le_operator_eigenvalue i) t.property)
    _ = -P.principalValue * (t : ℝ) := by ring

theorem SpectralNetwork.heat_norm_sq_gap_bound (P : SpectralNetwork V E)
    (t : ℝ≥0) (x : GraphL2Product P.geometry) :
    ‖P.heatSemigroup t x‖ ^ 2 ≤ Real.exp (-P.principalValue * (t : ℝ)) ^ 2 * ‖x‖ ^ 2 := by
  have hb (i : CompactSpectralIndex P.operatorInverse) :
      (inner ℝ (P.eigenbasis i) (P.heatSemigroup t x)) ^ 2 ≤
        Real.exp (-P.principalValue * (t : ℝ)) ^ 2 * (inner ℝ (P.eigenbasis i) x) ^ 2 := by
    rw [P.heatSemigroup_inner, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have he := P.heat_coefficient_gap_bound t i
    nlinarith [Real.exp_pos (-(t : ℝ) / i.1), Real.exp_pos (-P.principalValue * (t : ℝ))]
  exact hasSum_le hb (P.eigenbasis_parseval (P.heatSemigroup t x))
    ((P.eigenbasis_parseval x).mul_left (Real.exp (-P.principalValue * (t : ℝ)) ^ 2))

theorem SpectralNetwork.heat_norm_gap_bound (P : SpectralNetwork V E)
    (t : ℝ≥0) (x : GraphL2Product P.geometry) :
    ‖P.heatSemigroup t x‖ ≤ Real.exp (-P.principalValue * (t : ℝ)) * ‖x‖ := by
  have hb := P.heat_norm_sq_gap_bound t x
  have hp : 0 ≤ Real.exp (-P.principalValue * (t : ℝ)) * ‖x‖ :=
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  rw [← mul_pow] at hb
  exact (sq_le_sq₀ (norm_nonneg _) hp).mp hb

theorem SpectralNetwork.heatCurve_norm_gap_bound (P : SpectralNetwork V E)
    (x : GraphL2Product P.geometry) {t : ℝ} (ht : 0 ≤ t) :
    ‖P.heatCurve x t‖ ≤ Real.exp (-P.principalValue * t) * ‖x‖ := by
  simpa only [SpectralNetwork.heatCurve, CompactPositiveInverse.heatCurve,
    SpectralNetwork.heatSemigroup, Real.coe_toNNReal t ht] using P.heat_norm_gap_bound t.toNNReal x

end TimeTraps.Spectral
