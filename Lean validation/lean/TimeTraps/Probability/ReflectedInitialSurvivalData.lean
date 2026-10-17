module

public import TimeTraps.Probability.ReflectedAttainmentSurvivalExpansion

@[expose] public section

/-! Survival averaged against an arbitrary Lebesgue L² initial density.
The definition integrates literal first-attainment probabilities, and
its equality with the killed-operator pairing is proved from the actual
continuous-input representative. Signed L² weights are allowed in the
identities; positivity is stated separately for nonzero densities. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ}

noncomputable def reflectedInitialSurvival (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) : ℝ :=
  ∫ x, r x * reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity
    x P.site P.strength T ∂volume.restrict (Ioo 0 P.length)

noncomputable def reflectedInitialSurvivalFirstCoefficient (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length) : ℝ :=
  inner ℝ r (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)) *
    inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0))
      (reflectedSurvivalOne P)

theorem reflectedKilledInterval_survival_coe (P : SpectralProblem n) (T : ℝ≥0) :
    (reflectedKilledIntervalL2Operator P T (reflectedSurvivalOne P) : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo 0 P.length)]
        (fun x => reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity
          x P.site P.strength T) := by
  have hc := reflectedKilledIntervalL2Operator_continuous_coe P T (ContinuousMap.const _ (1 : ℝ))
  refine hc.trans (Eventually.of_forall (fun x => ?_))
  change reflectedKilledExpectation P T (ContinuousMap.const _ (1 : ℝ)) x =
    reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity x P.site P.strength T
  simp only [reflectedAtomicAttainmentSurvivalProbability_eq P.length P.length_pos P.diffusivity
    P.diffusivity_pos x P.site P.strength (fun i => (P.strength_pos i).le),
    reflectedAtomicSurvivalProbability_eq P.length P.length_pos P.diffusivity
      P.diffusivity_pos x P.site P.strength (fun i => (P.strength_pos i).le)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => mul_one _)

theorem reflectedInitialSurvival_integrable (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) :
    Integrable (fun x => r x * reflectedAtomicAttainmentSurvivalProbability P.length
      P.diffusivity x P.site P.strength T) (volume.restrict (Ioo 0 P.length)) := by
  apply (L2.integrable_inner (𝕜 := ℝ) r
    (reflectedKilledIntervalL2Operator P T (reflectedSurvivalOne P))).congr
  filter_upwards [reflectedKilledInterval_survival_coe P T] with x hx
  simp only [Real.inner_apply, hx]

theorem reflectedInitialSurvival_eq_inner (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) :
    reflectedInitialSurvival P r T =
      inner ℝ r (reflectedKilledIntervalL2Operator P T (reflectedSurvivalOne P)) := by
  rw [reflectedInitialSurvival, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [reflectedKilledInterval_survival_coe P T] with x hx
  simp only [Real.inner_apply, hx]

theorem reflectedSurvivalOne_norm_sq (P : SpectralProblem n) :
    ‖reflectedSurvivalOne P‖ ^ 2 = P.length := by
  have hi : ‖reflectedSurvivalOne P‖ ^ 2 = ∫ y in (0 : ℝ)..P.length, (1 : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def,
      intervalIntegral.integral_of_le P.length_pos.le, integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [reflectedSurvivalOne_coe P] with x hx
    simp only [hx, Real.inner_apply, mul_one]
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using hi

theorem reflectedSurvivalOne_norm (P : SpectralProblem n) :
    ‖reflectedSurvivalOne P‖ = Real.sqrt P.length := by
  exact (Real.sqrt_sq (norm_nonneg (reflectedSurvivalOne P))).symm.trans
    (congrArg Real.sqrt (reflectedSurvivalOne_norm_sq P))

theorem reflectedInitialSurvivalFirstCoefficient_integral (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length) :
    reflectedInitialSurvivalFirstCoefficient P r =
      ∫ x, r x * reflectedSurvivalFirstCoefficient P x ∂volume.restrict (Ioo 0 P.length) := by
  have hb := ((P.intervalPointProblem.eigenstate
    (P.intervalPointProblem.spectralEnumeration 0)).representative_spec P.length_pos).2.1
  rw [P.intervalPointProblem.eigenstate_state] at hb
  rw [reflectedInitialSurvivalFirstCoefficient, reflectedSurvivalOne_eigenbasis_inner,
    L2.inner_def, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [hb] with x hx
  simp only [Real.inner_apply, hx, reflectedSurvivalFirstCoefficient]
  ring

theorem reflectedInitialSurvivalFirstCoefficient_integrable (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length) :
    Integrable (fun x => r x * reflectedSurvivalFirstCoefficient P x)
      (volume.restrict (Ioo 0 P.length)) := by
  have hb := ((P.intervalPointProblem.eigenstate
    (P.intervalPointProblem.spectralEnumeration 0)).representative_spec P.length_pos).2.1
  rw [P.intervalPointProblem.eigenstate_state] at hb
  apply ((L2.integrable_inner (𝕜 := ℝ) r
    (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0))).mul_const
      (∫ y in (0 : ℝ)..P.length, (P.intervalPointProblem.eigenstate
        (P.intervalPointProblem.spectralEnumeration 0)).representative P.length_pos y)).congr
  filter_upwards [hb] with x hx
  simp only [Real.inner_apply, hx, reflectedSurvivalFirstCoefficient]
  ring

theorem reflectedInitialSurvivalFirstCoefficient_pos (P : SpectralProblem n)
    (r : IntervalSobolevL2 0 P.length)
    (hr : ∀ᵐ x ∂volume.restrict (Ioo 0 P.length), 0 ≤ r x) (hne : r ≠ 0) :
    0 < reflectedInitialSurvivalFirstCoefficient P r := by
  rw [reflectedInitialSurvivalFirstCoefficient_integral]
  have hn : 0 ≤ᵐ[volume.restrict (Ioo 0 P.length)]
      (fun x => r x * reflectedSurvivalFirstCoefficient P x) := by
    filter_upwards [hr, ae_restrict_mem measurableSet_Ioo] with x hx hmem
    exact mul_nonneg hx (reflectedSurvivalFirstCoefficient_pos P (Ioo_subset_Icc_self hmem)).le
  apply lt_of_le_of_ne (integral_nonneg_of_ae hn)
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn
    (reflectedInitialSurvivalFirstCoefficient_integrable P r)).mp he.symm
  apply hne
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hz, ae_restrict_mem measurableSet_Ioo] with x hx hmem
  exact (mul_eq_zero.mp hx).resolve_right
    (ne_of_gt (reflectedSurvivalFirstCoefficient_pos P (Ioo_subset_Icc_self hmem)))

end TimeTraps.Probability
