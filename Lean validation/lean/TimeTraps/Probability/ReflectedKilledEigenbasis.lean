module

public import TimeTraps.Probability.ReflectedKilledL2Interval
public import TimeTraps.Probability.ReflectedWeakEigenstateExpectation

@[expose] public section

/-! The independently constructed killed L² operator acts on every
physical eigenmode by its proved exponential factor. Continuous-input
expectations and the same-function measure normalization identify the
actual H¹ representatives with their L² eigenvectors. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral IntervalSobolevSpace
open scoped NNReal ENNReal Topology

variable {n : ℕ} {P : SpectralProblem n} {ev : ℝ} {u : ℝ → ℝ}

theorem reflectedKilledExpectation_weak_profile (hu : WeakEigenEquation P ev u)
    (T : ℝ≥0) (x : ℝ) :
    reflectedKilledExpectation P T hu.kinkProfile x =
      reflectedAtomicValueExpectation u P.length P.diffusivity x P.site P.strength T := by
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω => congrArg
    (fun z : ℝ => reflectedAtomicSurvival P.length P.diffusivity x P.site P.strength T ω * z)
    (hu.kinkProfile_extension
      (foldedTrajectory_mem P.length P.length_pos P.diffusivity x brownianDyadicPath T ω)))

theorem reflectedWeakEigenstate_profile_intervalL2 (hu : WeakEigenEquation P ev u) :
    reflectedUniformL2Equiv P.length P.length_pos
      (reflectedFellerToL2 P.length P.length_pos hu.kinkProfile) =
        (ofEnergy hu.energy P.length_pos).state := by
  apply Lp.ext
  filter_upwards [reflectedUniformL2Equiv_coe P.length P.length_pos
    (reflectedFellerToL2 P.length P.length_pos hu.kinkProfile),
    (reflectedUniformLaw_ae_iff P.length P.length_pos _).mp
      (reflectedFellerToL2_coe P.length P.length_pos hu.kinkProfile),
    (ofEnergy_spec hu.energy P.length_pos).1, ae_restrict_mem measurableSet_Ioo] with x he hf hs hx
  exact he.trans (hf.trans ((hu.kinkProfile_extension (Ioo_subset_Icc_self hx)).trans hs.symm))

theorem reflectedKilledIntervalL2Operator_weak_eigenstate (hu : WeakEigenEquation P ev u)
    (T : ℝ≥0) :
    reflectedKilledIntervalL2Operator P T (ofEnergy hu.energy P.length_pos).state =
      Real.exp (-ev * T.val) • (ofEnergy hu.energy P.length_pos).state := by
  have he := reflectedKilledIntervalL2Operator_continuous_coe P T hu.kinkProfile
  rw [reflectedWeakEigenstate_profile_intervalL2 hu] at he
  apply Lp.ext
  filter_upwards [he, Lp.coeFn_smul (Real.exp (-ev * T.val)) (ofEnergy hu.energy P.length_pos).state,
    (ofEnergy_spec hu.energy P.length_pos).1, ae_restrict_mem measurableSet_Ioo] with x hk hs huval hx
  rw [hk, hs]
  change reflectedKilledExpectation P T hu.kinkProfile x =
    Real.exp (-ev * T.val) * (ofEnergy hu.energy P.length_pos).state x
  rw [huval]
  rw [reflectedKilledExpectation_weak_profile hu T x]
  exact reflectedWeakEigenstate_expectation_at_start hu (Ioo_subset_Icc_self hx) T

theorem reflectedKilledIntervalL2Operator_eigenbasis (P : SpectralProblem n)
    (T : ℝ≥0) (i : CompactSpectralIndex P.intervalPointProblem.inverse) :
    reflectedKilledIntervalL2Operator P T (P.intervalPointProblem.eigenbasis i) =
      Real.exp (-i.1⁻¹ * T.val) • P.intervalPointProblem.eigenbasis i := by
  have he := reflectedKilledIntervalL2Operator_weak_eigenstate (P.interval_eigenbasis_weak i) T
  have hu : ofEnergy (P.interval_eigenbasis_weak i).energy P.length_pos =
      P.intervalPointProblem.eigenstate i :=
    ofEnergy_representative (P.intervalPointProblem.eigenstate i) P.length_pos
  rw [hu, P.intervalPointProblem.eigenstate_state] at he
  exact he

end TimeTraps.Probability
