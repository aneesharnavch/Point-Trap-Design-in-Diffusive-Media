module

public import TimeTraps.Probability.ReflectedKilledPointSemigroup
public import TimeTraps.Spectral.IntervalHeatGroundRemainder

@[expose] public section

/-! The constant-one L² input represents literal survival. Its first
spectral coefficient is the integral of the actual H¹ first mode, so
the leading survival coefficient is positive at every physical start,
independently of the arbitrary sign of the chosen Hilbert basis vector. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral IntervalSobolevSpace
open scoped NNReal ENNReal Topology

variable {n : ℕ}

noncomputable def reflectedSurvivalOne (P : SpectralProblem n) : IntervalSobolevL2 0 P.length :=
  reflectedUniformL2Equiv P.length P.length_pos
    (reflectedFellerToL2 P.length P.length_pos (ContinuousMap.const _ (1 : ℝ)))

noncomputable def reflectedSurvivalFirstCoefficient (P : SpectralProblem n) (x : ℝ) : ℝ :=
  (P.intervalPointProblem.eigenstate (P.intervalPointProblem.spectralEnumeration 0)).representative
    P.length_pos x * ∫ y in (0 : ℝ)..P.length,
      (P.intervalPointProblem.eigenstate (P.intervalPointProblem.spectralEnumeration 0)).representative
        P.length_pos y

noncomputable def reflectedSurvivalGroundRemainder (P : SpectralProblem n) : IntervalSobolevL2 0 P.length :=
  reflectedSurvivalOne P -
    inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0))
      (reflectedSurvivalOne P) • P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)

theorem reflectedSurvivalOne_coe (P : SpectralProblem n) :
    (reflectedSurvivalOne P : ℝ → ℝ) =ᵐ[volume.restrict (Ioo 0 P.length)] (fun _ => 1) := by
  have h₁ := reflectedUniformL2Equiv_coe P.length P.length_pos
    (reflectedFellerToL2 P.length P.length_pos (ContinuousMap.const _ (1 : ℝ)))
  have h₂ := (reflectedUniformLaw_ae_iff P.length P.length_pos _).mp
    (reflectedFellerToL2_coe P.length P.length_pos (ContinuousMap.const _ (1 : ℝ)))
  exact h₁.trans h₂

theorem reflectedSurvivalOne_eigenbasis_inner (P : SpectralProblem n)
    (i : CompactSpectralIndex P.intervalPointProblem.inverse) :
    inner ℝ (P.intervalPointProblem.eigenbasis i) (reflectedSurvivalOne P) =
      ∫ y in (0 : ℝ)..P.length, (P.intervalPointProblem.eigenstate i).representative P.length_pos y := by
  have hb : (P.intervalPointProblem.eigenbasis i : ℝ → ℝ) =ᵐ[volume.restrict (Ioo 0 P.length)]
      (P.intervalPointProblem.eigenstate i).representative P.length_pos := by
    have h := ((P.intervalPointProblem.eigenstate i).representative_spec P.length_pos).2.1
    rw [P.intervalPointProblem.eigenstate_state] at h
    exact h
  rw [L2.inner_def, intervalIntegral.integral_of_le P.length_pos.le, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [hb, reflectedSurvivalOne_coe P] with y hφ h1
  rw [hφ, h1]
  simp only [Real.inner_apply, mul_one]

theorem reflectedKilledPointEvaluation_survival (P : SpectralProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    reflectedKilledPointEvaluation P T hT x (reflectedSurvivalOne P) =
      reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength T := by
  rw [reflectedSurvivalOne, reflectedKilledPointEvaluation_continuous_input]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => mul_one _)

theorem reflectedSurvivalFirstCoefficient_pos (P : SpectralProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) : 0 < reflectedSurvivalFirstCoefficient P x :=
  P.interval_first_survival_coefficient_pos hx

end TimeTraps.Probability
