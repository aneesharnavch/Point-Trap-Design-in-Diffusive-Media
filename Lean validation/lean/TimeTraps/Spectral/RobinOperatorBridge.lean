module

public import TimeTraps.Spectral.RobinOperatorData
public import TimeTraps.Spectral.RobinUniqueness
public import TimeTraps.Analysis.GeneralIntervalPointEigenEquivalence
public import TimeTraps.Analysis.CompactInverseEigenvalue

@[expose] public section

/-! The full original Robin weak equation is the actual operator equation,
for both bundled representatives and arbitrary physical H1 states. Every
operator eigenvalue belongs to the independently defined Rayleigh class. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

variable {n : ℕ}

theorem RobinWeakEigenEquation.congr {P : RobinProblem n} {ev : ℝ} {u w : ℝ → ℝ}
    (h : RobinWeakEigenEquation P ev u) (huw : EqOn u w (Icc 0 P.length)) :
    RobinWeakEigenEquation P ev w := by
  refine ⟨?_, ?_⟩
  · apply h.energy.congr
    simpa only [uIcc_of_le P.length_pos.le] using huw
  · intro v hv
    rw [← P.operator_pointForm,
      intervalPointForm_congr P.diffusivity P.operatorStrength P.operatorSite
        P.length_pos.le P.intervalPointProblem.site_mem huw.symm (fun _ _ => rfl),
      P.operator_pointForm]
    calc
      _ = ev * ∫ x in (0 : ℝ)..P.length, u x * v x := h.weak_form v hv
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr_Ioo_of_le P.length_pos.le
        intro x hx
        change u x * v x = w x * v x
        rw [huw (Ioo_subset_Icc_self hx)]

theorem RobinProblem.interval_operator_weak_iff (P : RobinProblem n)
    (u : IntervalSobolevSpace 0 P.length) (ev : ℝ) :
    (u.state, ev • u.state) ∈ P.intervalPointProblem.operator.graph ↔
      RobinWeakEigenEquation P ev (u.representative P.length_pos) := by
  rw [P.intervalPointProblem.operator_eigen_iff_physical]
  change (∀ v : ℝ → ℝ, IntervalEnergy v 0 P.length →
    intervalPointForm P.diffusivity P.operatorStrength P.operatorSite 0 P.length
      (u.representative P.length_pos) v =
        ev * ∫ x in (0 : ℝ)..P.length, u.representative P.length_pos x * v x) ↔ _
  simp_rw [P.operator_pointForm]
  exact ⟨fun h => ⟨(u.representative_spec P.length_pos).1, h⟩,
    fun h => h.weak_form⟩

theorem RobinProblem.interval_operator_ofEnergy_iff (P : RobinProblem n)
    {u : ℝ → ℝ} (hu : IntervalEnergy u 0 P.length) (ev : ℝ) :
    ((ofEnergy hu P.length_pos).state, ev • (ofEnergy hu P.length_pos).state) ∈
      P.intervalPointProblem.operator.graph ↔ RobinWeakEigenEquation P ev u := by
  rw [P.interval_operator_weak_iff]
  exact ⟨fun h => h.congr (representative_ofEnergy hu P.length_pos),
    fun h => h.congr (representative_ofEnergy hu P.length_pos).symm⟩

theorem RobinProblem.interval_eigenbasis_weak (P : RobinProblem n)
    (i : CompactSpectralIndex P.intervalPointProblem.inverse) :
    RobinWeakEigenEquation P i.1⁻¹
      ((P.intervalPointProblem.eigenstate i).representative P.length_pos) := by
  apply (P.interval_operator_weak_iff _ _).mp
  rw [P.intervalPointProblem.eigenstate_state]
  exact P.intervalPointProblem.eigenbasis_operator_graph i

theorem RobinProblem.interval_eigenvalue_rayleigh (P : RobinProblem n)
    (i : CompactSpectralIndex P.intervalPointProblem.inverse) : i.1⁻¹ ∈ P.rayleighValues := by
  let u := P.intervalPointProblem.eigenstate i
  have he := P.interval_eigenbasis_weak i
  have hm : 0 < P.squareMass (u.representative P.length_pos) := by
    rw [P.interval_squareMass, P.intervalPointProblem.eigenstate_state]
    exact sq_pos_of_pos (norm_pos_iff.mpr
      (P.intervalPointProblem.eigenbasis.orthonormal.ne_zero i))
  refine ⟨u.representative P.length_pos, he.energy, hm, ?_⟩
  rw [he.self_quadraticForm, mul_div_cancel_right₀ _ hm.ne']

theorem RobinProblem.principal_le_interval_eigenvalue (P : RobinProblem n)
    (i : CompactSpectralIndex P.intervalPointProblem.inverse) : P.principalValue ≤ i.1⁻¹ :=
  P.rayleigh_minimum.2 (P.interval_eigenvalue_rayleigh i)

end TimeTraps.Spectral
