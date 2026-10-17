module

public import TimeTraps.Spectral.RobinOperatorGround

@[expose] public section

/-! Simplicity of the original positive interval ground state makes the
first two enumerated eigenvalues strictly different. The actual H1 first
mode is a nonzero scalar multiple of the positive physical ground state;
its point value times its spatial integral is therefore positive,
independently of the arbitrary sign of the Hilbert basis vector. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ}

theorem RobinProblem.interval_principal_eigenstate_proportional (P : RobinProblem n)
    (G : PositiveRobinEigenstate P P.principalValue)
    (i : CompactSpectralIndex P.intervalPointProblem.inverse) (hi : i.1⁻¹ = P.principalValue) :
    ∃ c : ℝ, c ≠ 0 ∧ EqOn
      ((P.intervalPointProblem.eigenstate i).representative P.length_pos)
      (fun x => c * G.state x) (Icc 0 P.length) := by
  have he := P.interval_eigenbasis_weak i
  rw [hi] at he
  have hm : 0 < P.squareMass ((P.intervalPointProblem.eigenstate i).representative P.length_pos) := by
    rw [P.interval_squareMass, P.intervalPointProblem.eigenstate_state,
      P.intervalPointProblem.eigenbasis.orthonormal.norm_eq_one, one_pow]
    exact zero_lt_one
  exact (G.unique_nonzero_scalar_of_quadraticForm_eq he.energy hm he.self_quadraticForm).exists

theorem RobinProblem.interval_first_eigenstate_proportional (P : RobinProblem n)
    (G : PositiveRobinEigenstate P P.principalValue) :
    ∃ c : ℝ, c ≠ 0 ∧ EqOn
      ((P.intervalPointProblem.eigenstate (P.intervalPointProblem.spectralEnumeration 0)).representative
        P.length_pos) (fun x => c * G.state x) (Icc 0 P.length) :=
  P.interval_principal_eigenstate_proportional G _ P.interval_first_eigenvalue

theorem RobinProblem.interval_first_lt_second_eigenvalue (P : RobinProblem n) :
    (P.intervalPointProblem.spectralEnumeration 0).1⁻¹ <
      (P.intervalPointProblem.spectralEnumeration 1).1⁻¹ := by
  apply lt_of_le_of_ne (P.intervalPointProblem.spectralEnumeration_monotone (by omega))
  intro he
  obtain ⟨G, _⟩ := P.principal_eigenstate_exists
  let i := P.intervalPointProblem.spectralEnumeration 0
  let j := P.intervalPointProblem.spectralEnumeration 1
  obtain ⟨c, hc, hci⟩ := P.interval_first_eigenstate_proportional G
  change EqOn ((P.intervalPointProblem.eigenstate i).representative P.length_pos)
    (fun x => c * G.state x) (Icc 0 P.length) at hci
  have hj : j.1⁻¹ = P.principalValue := he.symm.trans P.interval_first_eigenvalue
  obtain ⟨d, hd, hdj⟩ := P.interval_principal_eigenstate_proportional G j hj
  have hij : i ≠ j := by
    intro h
    have h01 := P.intervalPointProblem.spectralEnumeration.injective h
    norm_num at h01
  have horth := P.intervalPointProblem.eigenbasis.orthonormal.inner_eq_zero hij
  have hp : inner ℝ (P.intervalPointProblem.eigenbasis i) (P.intervalPointProblem.eigenbasis j) =
      (c * d) * P.squareMass G.state := by
    calc
      _ = inner ℝ (P.intervalPointProblem.eigenstate i).state
          (P.intervalPointProblem.eigenstate j).state := by
        rw [P.intervalPointProblem.eigenstate_state, P.intervalPointProblem.eigenstate_state]
      _ = ∫ x in (0 : ℝ)..P.length,
          (P.intervalPointProblem.eigenstate i).representative P.length_pos x *
          (P.intervalPointProblem.eigenstate j).representative P.length_pos x :=
        state_inner _ _ P.length_pos
      _ = _ := by
        change (∫ x in (0 : ℝ)..P.length, _) =
          (c * d) * ∫ x in (0 : ℝ)..P.length, G.state x ^ 2
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr_Ioo_of_le P.length_pos.le
        intro x hx
        change (P.intervalPointProblem.eigenstate i).representative P.length_pos x *
          (P.intervalPointProblem.eigenstate j).representative P.length_pos x = c * d * G.state x ^ 2
        rw [hci (Ioo_subset_Icc_self hx), hdj (Ioo_subset_Icc_self hx)]
        ring
  exact (mul_ne_zero (mul_ne_zero hc hd) G.squareMass_pos.ne') (hp.symm.trans horth)

theorem RobinProblem.interval_first_survival_coefficient_pos (P : RobinProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    0 < (P.intervalPointProblem.eigenstate (P.intervalPointProblem.spectralEnumeration 0)).representative
        P.length_pos x *
      ∫ y in (0 : ℝ)..P.length,
        (P.intervalPointProblem.eigenstate (P.intervalPointProblem.spectralEnumeration 0)).representative
          P.length_pos y := by
  obtain ⟨G, _⟩ := P.principal_eigenstate_exists
  obtain ⟨c, hc, hphi⟩ := P.interval_first_eigenstate_proportional G
  have hG : ContinuousOn G.state (Icc (0 : ℝ) P.length) := by
    simpa only [uIcc_of_le P.length_pos.le] using G.energy.continuousOn
  have hiG : 0 < ∫ y in (0 : ℝ)..P.length, G.state y := by
    apply intervalIntegral.integral_pos P.length_pos hG
    · intro y hy
      exact (G.positive y (Ioc_subset_Icc_self hy)).le
    · exact ⟨0, ⟨le_rfl, P.length_pos.le⟩, G.positive 0 ⟨le_rfl, P.length_pos.le⟩⟩
  have hi : (∫ y in (0 : ℝ)..P.length,
      (P.intervalPointProblem.eigenstate (P.intervalPointProblem.spectralEnumeration 0)).representative
        P.length_pos y) = c * ∫ y in (0 : ℝ)..P.length, G.state y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le P.length_pos.le
    intro y hy
    exact hphi (Ioo_subset_Icc_self hy)
  rw [hphi hx, hi]
  have hpos := mul_pos (mul_pos (sq_pos_of_ne_zero hc) (G.positive x hx)) hiG
  convert! hpos using 1
  ring

end TimeTraps.Spectral
