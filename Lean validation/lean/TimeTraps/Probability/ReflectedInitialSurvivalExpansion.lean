module

public import TimeTraps.Probability.ReflectedInitialSurvivalRemainder

@[expose] public section

/-! The source survival series for arbitrary L² initial weights, followed
by the positive leading coefficient and second-eigenvalue expansion for
every nonnegative nonzero L² density. The survival definition averages
the paper's actual first-attainment probabilities. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ}

theorem reflectedInitialSurvival_hasSum (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) :
    HasSum (fun i : CompactSpectralIndex P.intervalPointProblem.inverse =>
      Real.exp (-i.1⁻¹ * T.val) * inner ℝ r (P.intervalPointProblem.eigenbasis i) *
        inner ℝ (P.intervalPointProblem.eigenbasis i) (reflectedSurvivalOne P))
      (reflectedInitialSurvival P r T) := by
  have h := (reflectedKilledIntervalL2Operator_hasSum P T (reflectedSurvivalOne P)).mapL (innerSL ℝ r)
  change HasSum _ (inner ℝ r (reflectedKilledIntervalL2Operator P T (reflectedSurvivalOne P))) at h
  rw [← reflectedInitialSurvival_eq_inner] at h
  apply h.congr
  intro s
  apply Finset.sum_congr rfl
  intro i _hi
  change inner ℝ r ((compactHeatCoefficient T i *
    inner ℝ (P.intervalPointProblem.eigenbasis i) (reflectedSurvivalOne P)) •
      P.intervalPointProblem.eigenbasis i) = _
  rw [real_inner_smul_right]
  have hc : compactHeatCoefficient T i = Real.exp (-i.1⁻¹ * T.val) := by
    unfold compactHeatCoefficient
    apply congrArg Real.exp
    change -T.val / i.1 = -i.1⁻¹ * T.val
    rw [div_eq_mul_inv]
    exact (neg_mul _ _).trans ((congrArg Neg.neg (mul_comm _ _)).trans (neg_mul _ _).symm)
  rw [hc]
  ring

theorem reflectedInitialSurvival_hasSum_enumeration (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) :
    HasSum (fun k : ℕ =>
      Real.exp (-(P.intervalPointProblem.spectralEnumeration k).1⁻¹ * T.val) *
        inner ℝ r (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration k)) *
          inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration k))
            (reflectedSurvivalOne P)) (reflectedInitialSurvival P r T) :=
  P.intervalPointProblem.spectralEnumeration.hasSum_iff.mpr (reflectedInitialSurvival_hasSum P r T)

theorem reflectedInitialSurvival_series (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) :
    reflectedInitialSurvival P r T = ∑' k : ℕ,
      Real.exp (-(P.intervalPointProblem.spectralEnumeration k).1⁻¹ * T.val) *
        inner ℝ r (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration k)) *
          inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration k))
            (reflectedSurvivalOne P) :=
  (reflectedInitialSurvival_hasSum_enumeration P r T).tsum_eq.symm

theorem reflectedInitialSurvival_expansion (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length)
    (hr : ∀ᵐ x ∂volume.restrict (Ioo 0 P.length), 0 ≤ r x) (hne : r ≠ 0) :
    0 < reflectedInitialSurvivalFirstCoefficient P r ∧
      P.principalValue < (P.intervalPointProblem.spectralEnumeration 1).1⁻¹ ∧
      Asymptotics.IsBigO atTop
        (fun T : ℝ≥0 => reflectedInitialSurvival P r T -
          Real.exp (-P.principalValue * T.val) * reflectedInitialSurvivalFirstCoefficient P r)
        (fun T : ℝ≥0 => Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * T.val)) := by
  refine ⟨reflectedInitialSurvivalFirstCoefficient_pos P r hr hne, ?_, ?_⟩
  · simpa only [P.interval_first_eigenvalue] using P.interval_first_lt_second_eigenvalue
  · apply Asymptotics.IsBigO.of_bound (‖r‖ * Real.sqrt P.length)
    apply Eventually.of_forall
    intro T
    have hb := reflectedInitialSurvival_remainder_sqrt_le P r T
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm, mul_left_comm, mul_assoc] using hb

end TimeTraps.Probability
