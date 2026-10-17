module

public import TimeTraps.Spectral.DirichletUniquenessRegularity

@[expose] public section

/-! Natural reflecting boundary conditions follow from the actual admissible
H1 tests. Together with the selected zero traces, they give the full strong
form equivalent to the independent weak eigenvalue equation. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis

theorem DirichletWeakEigenEquation.right_natural_flux {P : DirichletInterval}
    {ev : ℝ} {u j : ℝ → ℝ} (hu : DirichletWeakEigenEquation P ev u)
    (hj : EdgeEquation (fun _ => P.diffusivity) (fun x => ev * u x) 0 P.length u j)
    (he : P.ends = .left) : j P.length = 0 := by
  have hv : IntervalEnergy (fun x : ℝ => x) 0 P.length :=
    intervalEnergy_of_continuous_derivative P.length_pos.le continuousOn_id continuousOn_const
      (fun x _ => hasDerivAt_id x)
  have ht : P.admissible (fun x : ℝ => x) := ⟨hv, by simp [DirichletInterval.zeroTraces, he]⟩
  have hc : ContinuousOn u (Icc (0 : ℝ) P.length) := hj.state_continuous
  have h₁ := hu.weak_form _ ht
  have h₂ := hj.green_identity_energy P.length_pos.le (continuousOn_const.mul hc)
    (fun _ _ => P.diffusivity_pos.ne') hv
  simp only [mul_assoc, intervalIntegral.integral_const_mul, mul_zero, sub_zero] at h₂
  have hz : j P.length * P.length = 0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_right P.length_pos.ne'

theorem DirichletWeakEigenEquation.left_natural_flux {P : DirichletInterval}
    {ev : ℝ} {u j : ℝ → ℝ} (hu : DirichletWeakEigenEquation P ev u)
    (hj : EdgeEquation (fun _ => P.diffusivity) (fun x => ev * u x) 0 P.length u j)
    (he : P.ends = .right) : j 0 = 0 := by
  have hv : IntervalEnergy (fun x : ℝ => P.length - x) 0 P.length :=
    intervalEnergy_of_continuous_derivative P.length_pos.le
      (continuousOn_const.sub continuousOn_id) continuousOn_const
      (fun x _ => (hasDerivAt_id x).const_sub P.length)
  have ht : P.admissible (fun x : ℝ => P.length - x) :=
    ⟨hv, by simp [DirichletInterval.zeroTraces, he]⟩
  have hc : ContinuousOn u (Icc (0 : ℝ) P.length) := hj.state_continuous
  have h₁ := hu.weak_form _ ht
  have h₂ := hj.green_identity_energy P.length_pos.le (continuousOn_const.mul hc)
    (fun _ _ => P.diffusivity_pos.ne') hv
  simp only [mul_assoc, intervalIntegral.integral_const_mul, sub_self, mul_zero,
    add_zero, sub_zero] at h₂
  have hz : j 0 * P.length = 0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_right P.length_pos.ne'

theorem dirichlet_weak_iff_strong {P : DirichletInterval} {ev : ℝ} {u : ℝ → ℝ} :
    DirichletWeakEigenEquation P ev u ↔ P.admissible u ∧
      ∃ j : ℝ → ℝ, EdgeEquation (fun _ => P.diffusivity) (fun x => ev * u x) 0 P.length u j ∧
        (P.ends = .left → j P.length = 0) ∧ (P.ends = .right → j 0 = 0) := by
  constructor
  · intro hu
    obtain ⟨j, hj⟩ := hu.to_strong
    exact ⟨hu.admissible, j, hj, hu.right_natural_flux hj, hu.left_natural_flux hj⟩
  · rintro ⟨hu, j, hj, hright, hleft⟩
    refine ⟨hu, ?_⟩
    intro v hv
    have hgreen := hj.green_identity_energy P.length_pos.le
      (continuousOn_const.mul hj.state_continuous) (fun _ _ => P.diffusivity_pos.ne') hv.1
    simp only [mul_assoc, intervalIntegral.integral_const_mul] at hgreen
    have hb : j P.length * v P.length - j 0 * v 0 = 0 := by
      have ht := hv.2
      cases he : P.ends with
      | left =>
        simp only [DirichletInterval.zeroTraces, he] at ht
        simp [hright he, ht]
      | right =>
        simp only [DirichletInterval.zeroTraces, he] at ht
        simp [hleft he, ht]
      | both =>
        simp only [DirichletInterval.zeroTraces, he] at ht
        simp [ht.1, ht.2]
    linarith

end TimeTraps.Spectral
