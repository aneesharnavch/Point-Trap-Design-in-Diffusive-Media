module

public import TimeTraps.Probability.ReflectedRobinInitialSurvivalRemainder

@[expose] public section

/-! The source survival series for arbitrary L² initial weights, followed
by the positive leading coefficient and second-eigenvalue expansion for
every nonnegative nonzero L² density. The survival definition averages
the paper's actual first-attainment probabilities. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ}

theorem reflectedRobinInitialSurvival_hasSum (P : RobinProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) :
    HasSum (fun i : CompactSpectralIndex P.intervalPointProblem.inverse =>
      Real.exp (-i.1⁻¹ * T.val) * inner ℝ r (P.intervalPointProblem.eigenbasis i) *
        inner ℝ (P.intervalPointProblem.eigenbasis i) (reflectedRobinSurvivalOne P))
      (reflectedRobinInitialSurvival P r T) := by
  have h := (reflectedRobinKilledIntervalL2Operator_hasSum P T (reflectedRobinSurvivalOne P)).mapL (innerSL ℝ r)
  change HasSum _ (inner ℝ r (reflectedRobinKilledIntervalL2Operator P T (reflectedRobinSurvivalOne P))) at h
  rw [← reflectedRobinInitialSurvival_eq_inner] at h
  apply h.congr
  intro s
  apply Finset.sum_congr rfl
  intro i _hi
  change inner ℝ r ((compactHeatCoefficient T i *
    inner ℝ (P.intervalPointProblem.eigenbasis i) (reflectedRobinSurvivalOne P)) •
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

theorem reflectedRobinInitialSurvival_hasSum_enumeration (P : RobinProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) :
    HasSum (fun k : ℕ =>
      Real.exp (-(P.intervalPointProblem.spectralEnumeration k).1⁻¹ * T.val) *
        inner ℝ r (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration k)) *
          inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration k))
            (reflectedRobinSurvivalOne P)) (reflectedRobinInitialSurvival P r T) :=
  P.intervalPointProblem.spectralEnumeration.hasSum_iff.mpr (reflectedRobinInitialSurvival_hasSum P r T)

theorem reflectedRobinInitialSurvival_series (P : RobinProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) :
    reflectedRobinInitialSurvival P r T = ∑' k : ℕ,
      Real.exp (-(P.intervalPointProblem.spectralEnumeration k).1⁻¹ * T.val) *
        inner ℝ r (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration k)) *
          inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration k))
            (reflectedRobinSurvivalOne P) :=
  (reflectedRobinInitialSurvival_hasSum_enumeration P r T).tsum_eq.symm

theorem reflectedRobinInitialSurvival_expansion (P : RobinProblem n)
    (r : IntervalSobolevL2 0 P.length)
    (hr : ∀ᵐ x ∂volume.restrict (Ioo 0 P.length), 0 ≤ r x) (hne : r ≠ 0) :
    0 < reflectedRobinInitialSurvivalFirstCoefficient P r ∧
      P.principalValue < (P.intervalPointProblem.spectralEnumeration 1).1⁻¹ ∧
      Asymptotics.IsBigO atTop
        (fun T : ℝ≥0 => reflectedRobinInitialSurvival P r T -
          Real.exp (-P.principalValue * T.val) * reflectedRobinInitialSurvivalFirstCoefficient P r)
        (fun T : ℝ≥0 => Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * T.val)) := by
  refine ⟨reflectedRobinInitialSurvivalFirstCoefficient_pos P r hr hne, ?_, ?_⟩
  · simpa only [P.interval_first_eigenvalue] using P.interval_first_lt_second_eigenvalue
  · apply Asymptotics.IsBigO.of_bound (‖r‖ * Real.sqrt P.length)
    apply Eventually.of_forall
    intro T
    have hb := reflectedRobinInitialSurvival_remainder_sqrt_le P r T
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm, mul_left_comm, mul_assoc] using hb

end TimeTraps.Probability
