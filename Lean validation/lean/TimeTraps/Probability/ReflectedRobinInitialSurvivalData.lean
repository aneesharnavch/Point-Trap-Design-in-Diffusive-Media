module

public import TimeTraps.Probability.ReflectedRobinAttainmentSurvivalExpansion

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

noncomputable def reflectedRobinInitialSurvival (P : RobinProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) : ℝ :=
  ∫ x, r x * reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity
    x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ∂volume.restrict (Ioo 0 P.length)

noncomputable def reflectedRobinInitialSurvivalFirstCoefficient (P : RobinProblem n)
    (r : IntervalSobolevL2 0 P.length) : ℝ :=
  inner ℝ r (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)) *
    inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0))
      (reflectedRobinSurvivalOne P)

theorem reflectedRobinKilledInterval_survival_coe (P : RobinProblem n) (T : ℝ≥0) :
    (reflectedRobinKilledIntervalL2Operator P T (reflectedRobinSurvivalOne P) : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo 0 P.length)]
        (fun x => reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity
          x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T) := by
  have hc := reflectedRobinKilledIntervalL2Operator_continuous_coe P T (ContinuousMap.const _ (1 : ℝ))
  refine hc.trans (Eventually.of_forall (fun x => ?_))
  change reflectedRobinKilledExpectation P T (ContinuousMap.const _ (1 : ℝ)) x =
    reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T
  simp only [reflectedAtomicAttainmentSurvivalProbability_eq P.length P.length_pos P.diffusivity
    P.diffusivity_pos x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg),
    reflectedAtomicSurvivalProbability_eq P.length P.length_pos P.diffusivity
      P.diffusivity_pos x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => mul_one _)

theorem reflectedRobinInitialSurvival_integrable (P : RobinProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) :
    Integrable (fun x => r x * reflectedAtomicAttainmentSurvivalProbability P.length
      P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T) (volume.restrict (Ioo 0 P.length)) := by
  apply (L2.integrable_inner (𝕜 := ℝ) r
    (reflectedRobinKilledIntervalL2Operator P T (reflectedRobinSurvivalOne P))).congr
  filter_upwards [reflectedRobinKilledInterval_survival_coe P T] with x hx
  simp only [Real.inner_apply, hx]

theorem reflectedRobinInitialSurvival_eq_inner (P : RobinProblem n)
    (r : IntervalSobolevL2 0 P.length) (T : ℝ≥0) :
    reflectedRobinInitialSurvival P r T =
      inner ℝ r (reflectedRobinKilledIntervalL2Operator P T (reflectedRobinSurvivalOne P)) := by
  rw [reflectedRobinInitialSurvival, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [reflectedRobinKilledInterval_survival_coe P T] with x hx
  simp only [Real.inner_apply, hx]

theorem reflectedRobinSurvivalOne_norm_sq (P : RobinProblem n) :
    ‖reflectedRobinSurvivalOne P‖ ^ 2 = P.length := by
  have hi : ‖reflectedRobinSurvivalOne P‖ ^ 2 = ∫ y in (0 : ℝ)..P.length, (1 : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def,
      intervalIntegral.integral_of_le P.length_pos.le, integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [reflectedRobinSurvivalOne_coe P] with x hx
    simp only [hx, Real.inner_apply, mul_one]
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using hi

theorem reflectedRobinSurvivalOne_norm (P : RobinProblem n) :
    ‖reflectedRobinSurvivalOne P‖ = Real.sqrt P.length := by
  exact (Real.sqrt_sq (norm_nonneg (reflectedRobinSurvivalOne P))).symm.trans
    (congrArg Real.sqrt (reflectedRobinSurvivalOne_norm_sq P))

theorem reflectedRobinInitialSurvivalFirstCoefficient_integral (P : RobinProblem n)
    (r : IntervalSobolevL2 0 P.length) :
    reflectedRobinInitialSurvivalFirstCoefficient P r =
      ∫ x, r x * reflectedRobinSurvivalFirstCoefficient P x ∂volume.restrict (Ioo 0 P.length) := by
  have hb := ((P.intervalPointProblem.eigenstate
    (P.intervalPointProblem.spectralEnumeration 0)).representative_spec P.length_pos).2.1
  rw [P.intervalPointProblem.eigenstate_state] at hb
  rw [reflectedRobinInitialSurvivalFirstCoefficient, reflectedRobinSurvivalOne_eigenbasis_inner,
    L2.inner_def, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [hb] with x hx
  simp only [Real.inner_apply, hx, reflectedRobinSurvivalFirstCoefficient]
  ring

theorem reflectedRobinInitialSurvivalFirstCoefficient_integrable (P : RobinProblem n)
    (r : IntervalSobolevL2 0 P.length) :
    Integrable (fun x => r x * reflectedRobinSurvivalFirstCoefficient P x)
      (volume.restrict (Ioo 0 P.length)) := by
  have hb := ((P.intervalPointProblem.eigenstate
    (P.intervalPointProblem.spectralEnumeration 0)).representative_spec P.length_pos).2.1
  rw [P.intervalPointProblem.eigenstate_state] at hb
  apply ((L2.integrable_inner (𝕜 := ℝ) r
    (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0))).mul_const
      (∫ y in (0 : ℝ)..P.length, (P.intervalPointProblem.eigenstate
        (P.intervalPointProblem.spectralEnumeration 0)).representative P.length_pos y)).congr
  filter_upwards [hb] with x hx
  simp only [Real.inner_apply, hx, reflectedRobinSurvivalFirstCoefficient]
  ring

theorem reflectedRobinInitialSurvivalFirstCoefficient_pos (P : RobinProblem n)
    (r : IntervalSobolevL2 0 P.length)
    (hr : ∀ᵐ x ∂volume.restrict (Ioo 0 P.length), 0 ≤ r x) (hne : r ≠ 0) :
    0 < reflectedRobinInitialSurvivalFirstCoefficient P r := by
  rw [reflectedRobinInitialSurvivalFirstCoefficient_integral]
  have hn : 0 ≤ᵐ[volume.restrict (Ioo 0 P.length)]
      (fun x => r x * reflectedRobinSurvivalFirstCoefficient P x) := by
    filter_upwards [hr, ae_restrict_mem measurableSet_Ioo] with x hx hmem
    exact mul_nonneg hx (reflectedRobinSurvivalFirstCoefficient_pos P (Ioo_subset_Icc_self hmem)).le
  apply lt_of_le_of_ne (integral_nonneg_of_ae hn)
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn
    (reflectedRobinInitialSurvivalFirstCoefficient_integrable P r)).mp he.symm
  apply hne
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hz, ae_restrict_mem measurableSet_Ioo] with x hx hmem
  exact (mul_eq_zero.mp hx).resolve_right
    (ne_of_gt (reflectedRobinSurvivalFirstCoefficient_pos P (Ioo_subset_Icc_self hmem)))

end TimeTraps.Probability
