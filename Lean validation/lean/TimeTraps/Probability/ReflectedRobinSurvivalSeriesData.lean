module

public import TimeTraps.Probability.ReflectedRobinKilledPointExpansion
public import TimeTraps.Probability.ReflectedAttainmentSurvivalExpansion

@[expose] public section

/-! The constant-one L2 input represents actual combined endpoint and
interior survival. The spectral coefficients are the integrals of the
same original full-H1 Robin eigenstates. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral IntervalSobolevSpace
open scoped NNReal ENNReal Topology

variable {n : ℕ}

noncomputable def reflectedRobinSurvivalOne (P : RobinProblem n) : IntervalSobolevL2 0 P.length :=
  reflectedUniformL2Equiv P.length P.length_pos
    (reflectedFellerToL2 P.length P.length_pos (ContinuousMap.const _ (1 : ℝ)))

theorem reflectedRobinSurvivalOne_coe (P : RobinProblem n) :
    (reflectedRobinSurvivalOne P : ℝ → ℝ) =ᵐ[volume.restrict (Ioo 0 P.length)] (fun _ => 1) := by
  have h₁ := reflectedUniformL2Equiv_coe P.length P.length_pos
    (reflectedFellerToL2 P.length P.length_pos (ContinuousMap.const _ (1 : ℝ)))
  have h₂ := (reflectedUniformLaw_ae_iff P.length P.length_pos _).mp
    (reflectedFellerToL2_coe P.length P.length_pos (ContinuousMap.const _ (1 : ℝ)))
  exact h₁.trans h₂

theorem reflectedRobinSurvivalOne_eigenbasis_inner (P : RobinProblem n)
    (i : CompactSpectralIndex P.intervalPointProblem.inverse) :
    inner ℝ (P.intervalPointProblem.eigenbasis i) (reflectedRobinSurvivalOne P) =
      ∫ y in (0 : ℝ)..P.length, (P.intervalPointProblem.eigenstate i).representative P.length_pos y := by
  have hb : (P.intervalPointProblem.eigenbasis i : ℝ → ℝ) =ᵐ[volume.restrict (Ioo 0 P.length)]
      (P.intervalPointProblem.eigenstate i).representative P.length_pos := by
    have h := ((P.intervalPointProblem.eigenstate i).representative_spec P.length_pos).2.1
    rw [P.intervalPointProblem.eigenstate_state] at h
    exact h
  rw [L2.inner_def, intervalIntegral.integral_of_le P.length_pos.le, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [hb, reflectedRobinSurvivalOne_coe P] with y hφ h1
  rw [hφ, h1]
  simp only [Real.inner_apply, mul_one]

theorem reflectedRobinKilledPointEvaluation_survival (P : RobinProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    reflectedRobinKilledPointEvaluation P T hT x (reflectedRobinSurvivalOne P) =
      reflectedAtomicMeanSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T := by
  rw [reflectedRobinSurvivalOne, reflectedRobinKilledPointEvaluation_continuous_input]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => mul_one _)

end TimeTraps.Probability
