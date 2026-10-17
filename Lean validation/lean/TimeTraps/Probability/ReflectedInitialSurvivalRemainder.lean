module

public import TimeTraps.Probability.ReflectedInitialSurvivalData

@[expose] public section

/-! The exact density-survival remainder is a pairing of the two
orthogonal ground-mode remainders. Cauchy--Schwarz and the derived
second spectral bound retain the sharper two-projection estimate. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ}

noncomputable def reflectedInitialGroundRemainder (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length) : IntervalSobolevL2 0 P.length :=
  r - inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)) r •
    P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)

theorem reflectedInitialGroundRemainder_norm_le (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length) : ‖reflectedInitialGroundRemainder P r‖ ≤ ‖r‖ := by
  let phi := P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)
  have hn : ‖phi‖ = 1 := P.intervalPointProblem.eigenbasis.orthonormal.norm_eq_one _
  have he : ‖reflectedInitialGroundRemainder P r‖ ^ 2 =
      ‖r‖ ^ 2 - (inner ℝ phi r) ^ 2 := by
    change ‖r - inner ℝ phi r • phi‖ ^ 2 = _
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hn, mul_one,
      Real.norm_eq_abs, sq_abs, real_inner_comm r phi]
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [sq_nonneg (inner ℝ phi r)]

theorem reflectedSurvivalGroundRemainder_norm_le (P : SpectralProblem n) :
    ‖reflectedSurvivalGroundRemainder P‖ ≤ Real.sqrt P.length :=
  (reflectedInitialGroundRemainder_norm_le P (reflectedSurvivalOne P)).trans_eq
    (reflectedSurvivalOne_norm P)

theorem reflectedKilledInterval_survival_remainder_orthogonal (P : SpectralProblem n)
    (T : ℝ≥0) :
    inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0))
      (reflectedKilledIntervalL2Operator P T (reflectedSurvivalOne P) -
        (Real.exp (-P.principalValue * T.val) *
          inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0))
            (reflectedSurvivalOne P)) •
          P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)) = 0 := by
  have hc : compactHeatCoefficient T (P.intervalPointProblem.spectralEnumeration 0) =
      Real.exp (-P.principalValue * T.val) := by
    calc
      _ = Real.exp (-(P.intervalPointProblem.spectralEnumeration 0).1⁻¹ * T.val) := by
        unfold compactHeatCoefficient
        apply congrArg Real.exp
        change -T.val / (P.intervalPointProblem.spectralEnumeration 0).1 =
          -(P.intervalPointProblem.spectralEnumeration 0).1⁻¹ * T.val
        rw [div_eq_mul_inv]
        exact (neg_mul _ _).trans ((congrArg Neg.neg (mul_comm _ _)).trans (neg_mul _ _).symm)
      _ = _ := congrArg (fun ev : ℝ => Real.exp (-ev * T.val)) P.interval_first_eigenvalue
  have he := P.intervalPointProblem.compactPositiveInverse.heatSemigroup_inner T
    (reflectedSurvivalOne P) (P.intervalPointProblem.spectralEnumeration 0)
  change inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0))
    (P.intervalPointProblem.compactPositiveInverse.heatSemigroup T (reflectedSurvivalOne P)) =
      compactHeatCoefficient T (P.intervalPointProblem.spectralEnumeration 0) *
        inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0))
          (reflectedSurvivalOne P) at he
  rw [← reflectedKilledIntervalL2Operator_eq_heat, hc] at he
  rw [inner_sub_right, he, real_inner_smul_right, real_inner_self_eq_norm_sq,
    P.intervalPointProblem.eigenbasis.orthonormal.norm_eq_one, one_pow, mul_one, sub_self]

theorem reflectedInitialSurvival_remainder_inner (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) :
    inner ℝ r
      (reflectedKilledIntervalL2Operator P T (reflectedSurvivalOne P) -
        (Real.exp (-P.principalValue * T.val) *
          inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0))
            (reflectedSurvivalOne P)) •
          P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)) =
      reflectedInitialSurvival P r T -
        Real.exp (-P.principalValue * T.val) * reflectedInitialSurvivalFirstCoefficient P r := by
  rw [inner_sub_right, real_inner_smul_right, ← reflectedInitialSurvival_eq_inner]
  unfold reflectedInitialSurvivalFirstCoefficient
  ring

theorem reflectedInitialSurvival_remainder_le (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) :
    |reflectedInitialSurvival P r T -
      Real.exp (-P.principalValue * T.val) * reflectedInitialSurvivalFirstCoefficient P r| ≤
      Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * T.val) *
        ‖reflectedInitialGroundRemainder P r‖ * ‖reflectedSurvivalGroundRemainder P‖ := by
  let R := reflectedKilledIntervalL2Operator P T (reflectedSurvivalOne P) -
    (Real.exp (-P.principalValue * T.val) *
      inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0))
        (reflectedSurvivalOne P)) •
      P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)
  have ho : inner ℝ (P.intervalPointProblem.eigenbasis
      (P.intervalPointProblem.spectralEnumeration 0)) R = 0 :=
    reflectedKilledInterval_survival_remainder_orthogonal P T
  have hp : inner ℝ r R = inner ℝ (reflectedInitialGroundRemainder P r) R := by
    rw [reflectedInitialGroundRemainder, inner_sub_left, real_inner_smul_left, ho, mul_zero, sub_zero]
  rw [← reflectedInitialSurvival_remainder_inner]
  change |inner ℝ r R| ≤ _
  rw [hp, ← Real.norm_eq_abs]
  calc
    _ ≤ ‖reflectedInitialGroundRemainder P r‖ * ‖R‖ := norm_inner_le_norm _ _
    _ ≤ ‖reflectedInitialGroundRemainder P r‖ *
        (Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * T.val) *
          ‖reflectedSurvivalGroundRemainder P‖) :=
      mul_le_mul_of_nonneg_left (reflectedKilledInterval_survival_ground_remainder_le P T)
        (norm_nonneg _)
    _ = _ := by ring

theorem reflectedInitialSurvival_remainder_sqrt_le (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) :
    |reflectedInitialSurvival P r T -
      Real.exp (-P.principalValue * T.val) * reflectedInitialSurvivalFirstCoefficient P r| ≤
      Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * T.val) *
        ‖r‖ * Real.sqrt P.length := by
  apply (reflectedInitialSurvival_remainder_le P r T).trans
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (reflectedInitialGroundRemainder_norm_le P r) (Real.exp_pos _).le)
    (reflectedSurvivalGroundRemainder_norm_le P) (norm_nonneg _)
    (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))

end TimeTraps.Probability
