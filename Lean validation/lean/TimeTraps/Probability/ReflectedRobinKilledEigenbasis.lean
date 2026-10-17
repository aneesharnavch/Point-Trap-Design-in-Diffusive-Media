module

public import TimeTraps.Probability.ReflectedRobinKilledL2Interval
public import TimeTraps.Probability.ReflectedRobinEigenExpectation

@[expose] public section

/-! The independently constructed killed L² operator acts on every
physical eigenmode by its proved exponential factor. Continuous-input
expectations and the same-function measure normalization identify the
actual H¹ representatives with their L² eigenvectors. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral IntervalSobolevSpace
open scoped NNReal ENNReal Topology

variable {n : ℕ} {P : RobinProblem n} {ev : ℝ} {u : ℝ → ℝ}

noncomputable def reflectedRobinEigenstateProfile (hu : RobinWeakEigenEquation P ev u) :
    C(Icc (0 : ℝ) P.length, ℝ) where
  toFun x := u x
  continuous_toFun := by
    have hc := hu.energy.continuousOn
    rw [uIcc_of_le P.length_pos.le] at hc
    exact continuousOn_iff_continuous_domRestrict.mp hc

theorem reflectedRobinEigenstateProfile_extension (hu : RobinWeakEigenEquation P ev u)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    reflectedFellerExtension P.length P.length_pos (reflectedRobinEigenstateProfile hu) x = u x :=
  reflectedFellerExtension_on_interval P.length P.length_pos (reflectedRobinEigenstateProfile hu) ⟨x, hx⟩

theorem reflectedRobinKilledExpectation_physical (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) :
    reflectedRobinKilledExpectation P T f x =
      ∫ ω, reflectedRobinSurvival P.length P.diffusivity x P.site P.strength P.betaLeft P.betaRight T ω *
        reflectedFellerExtension P.length P.length_pos f
          (foldedTrajectory P.length P.diffusivity x brownianDyadicPath T ω) ∂brownianDyadicMeasure := by
  simp only [reflectedRobinKilledExpectation, reflectedRobinKilledValue, reflectedAtomicWeightedValue,
    reflectedRobinSurvival_eq_atomic P.length P.diffusivity_pos]

theorem reflectedRobinKilledExpectation_weak_profile (hu : RobinWeakEigenEquation P ev u)
    (T : ℝ≥0) (x : ℝ) :
    reflectedRobinKilledExpectation P T (reflectedRobinEigenstateProfile hu) x =
      ∫ ω, reflectedRobinSurvival P.length P.diffusivity x P.site P.strength P.betaLeft P.betaRight T ω *
        u (foldedTrajectory P.length P.diffusivity x brownianDyadicPath T ω) ∂brownianDyadicMeasure := by
  rw [reflectedRobinKilledExpectation_physical]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω => congrArg
    (fun z : ℝ => reflectedRobinSurvival P.length P.diffusivity x P.site P.strength P.betaLeft P.betaRight T ω * z)
    (reflectedRobinEigenstateProfile_extension hu
      (foldedTrajectory_mem P.length P.length_pos P.diffusivity x brownianDyadicPath T ω)))

theorem reflectedRobinWeakEigenstate_profile_intervalL2 (hu : RobinWeakEigenEquation P ev u) :
    reflectedUniformL2Equiv P.length P.length_pos
      (reflectedFellerToL2 P.length P.length_pos (reflectedRobinEigenstateProfile hu)) =
        (ofEnergy hu.energy P.length_pos).state := by
  apply Lp.ext
  filter_upwards [reflectedUniformL2Equiv_coe P.length P.length_pos
    (reflectedFellerToL2 P.length P.length_pos (reflectedRobinEigenstateProfile hu)),
    (reflectedUniformLaw_ae_iff P.length P.length_pos _).mp
      (reflectedFellerToL2_coe P.length P.length_pos (reflectedRobinEigenstateProfile hu)),
    (ofEnergy_spec hu.energy P.length_pos).1, ae_restrict_mem measurableSet_Ioo] with x he hf hs hx
  exact he.trans (hf.trans ((reflectedRobinEigenstateProfile_extension hu (Ioo_subset_Icc_self hx)).trans hs.symm))

theorem reflectedRobinKilledIntervalL2Operator_weak_eigenstate (hu : RobinWeakEigenEquation P ev u)
    (T : ℝ≥0) :
    reflectedRobinKilledIntervalL2Operator P T (ofEnergy hu.energy P.length_pos).state =
      Real.exp (-ev * T.val) • (ofEnergy hu.energy P.length_pos).state := by
  have he := reflectedRobinKilledIntervalL2Operator_continuous_coe P T (reflectedRobinEigenstateProfile hu)
  rw [reflectedRobinWeakEigenstate_profile_intervalL2 hu] at he
  apply Lp.ext
  filter_upwards [he, Lp.coeFn_smul (Real.exp (-ev * T.val)) (ofEnergy hu.energy P.length_pos).state,
    (ofEnergy_spec hu.energy P.length_pos).1, ae_restrict_mem measurableSet_Ioo] with x hk hs huval hx
  rw [hk, hs]
  change reflectedRobinKilledExpectation P T (reflectedRobinEigenstateProfile hu) x =
    Real.exp (-ev * T.val) * (ofEnergy hu.energy P.length_pos).state x
  rw [huval]
  rw [reflectedRobinKilledExpectation_weak_profile hu T x]
  exact reflectedRobinWeakEigenstate_expectation_at_start hu (Ioo_subset_Icc_self hx) T

theorem reflectedRobinKilledIntervalL2Operator_eigenbasis (P : RobinProblem n)
    (T : ℝ≥0) (i : CompactSpectralIndex P.intervalPointProblem.inverse) :
    reflectedRobinKilledIntervalL2Operator P T (P.intervalPointProblem.eigenbasis i) =
      Real.exp (-i.1⁻¹ * T.val) • P.intervalPointProblem.eigenbasis i := by
  have he := reflectedRobinKilledIntervalL2Operator_weak_eigenstate (P.interval_eigenbasis_weak i) T
  have hu : ofEnergy (P.interval_eigenbasis_weak i).energy P.length_pos =
      P.intervalPointProblem.eigenstate i :=
    ofEnergy_representative (P.intervalPointProblem.eigenstate i) P.length_pos
  rw [hu, P.intervalPointProblem.eigenstate_state] at he
  exact he

end TimeTraps.Probability
