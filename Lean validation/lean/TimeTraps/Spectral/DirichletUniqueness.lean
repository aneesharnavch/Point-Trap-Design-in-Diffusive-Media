module

public import TimeTraps.Spectral.DirichletUniquenessRegularity
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Uniqueness of every signed principal H1 weak state. A Wronskian vanishes
at an absorbing endpoint, the quotient is constant only on the open interval,
and continuity extends proportionality to the two boundary traces. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis

theorem DirichletInterval.groundState_physical_edgeEquation (P : DirichletInterval) :
    EdgeEquation (fun _ => P.diffusivity) (fun x => P.principalValue * P.groundState x)
      0 P.length P.groundState (fun x => P.diffusivity * P.groundSlope x) := by
  refine ⟨(dirichletCosine_continuous _ _).continuousOn,
    continuousOn_const.mul (dirichletCosineSlope_continuous _ _).continuousOn, ?_, ?_⟩
  · intro x _
    rw [mul_div_cancel_left₀ _ P.diffusivity_pos.ne']
    exact dirichletCosine_hasDerivAt _ _ _
  · intro x _
    have hd := (dirichletCosineSlope_hasDerivAt P.waveNumber P.center x).const_mul P.diffusivity
    change HasDerivAt (fun t => P.diffusivity * P.groundSlope t)
      (P.diffusivity * (-(P.waveNumber ^ 2) * P.groundState x)) x at hd
    rw [P.principalValue_eq]
    convert hd using 1
    ring

theorem dirichlet_wronskian_constant {D ev l r : ℝ} {u j v k : ℝ → ℝ}
    (hD : D ≠ 0)
    (hu : EdgeEquation (fun _ => D) (fun x => ev * u x) l r u j)
    (hv : EdgeEquation (fun _ => D) (fun x => ev * v x) l r v k) :
    ∀ x ∈ Icc l r, u x * k x - v x * j x = u l * k l - v l * j l := by
  let W := fun x => u x * k x - v x * j x
  have hc : ContinuousOn W (Icc l r) :=
    (hu.state_continuous.mul hv.flux_continuous).sub
      (hv.state_continuous.mul hu.flux_continuous)
  have hd : ∀ x ∈ Ioo l r, HasDerivAt W 0 x := by
    intro x hx
    have h := ((hu.state_derivative x hx).mul (hv.flux_derivative x hx)).sub
      ((hv.state_derivative x hx).mul (hu.flux_derivative x hx))
    change HasDerivAt W
      ((j x / D * k x + u x * (-(ev * v x))) -
        (k x / D * j x + v x * (-(ev * u x)))) x at h
    convert h using 1
    field_simp [hD]
    ring
  intro x hx
  have he := integral_derivative_to_point hc (g := fun _ => 0) continuousOn_const hd hx
  simp only [intervalIntegral.integral_zero] at he
  exact (sub_eq_zero.mp he.symm)

theorem DirichletWeakEigenEquation.ground_wronskian_zero {P : DirichletInterval}
    {u j : ℝ → ℝ} (hu : DirichletWeakEigenEquation P P.principalValue u)
    (hj : EdgeEquation (fun _ => P.diffusivity) (fun x => P.principalValue * u x)
      0 P.length u j) :
    ∀ x ∈ Icc (0 : ℝ) P.length,
      u x * (P.diffusivity * P.groundSlope x) - P.groundState x * j x = 0 := by
  have hc := dirichlet_wronskian_constant P.diffusivity_pos.ne' hj
    P.groundState_physical_edgeEquation
  have hutr := hu.admissible.2
  have hvtr := P.groundState_admissible.2
  have hz : u 0 * (P.diffusivity * P.groundSlope 0) - P.groundState 0 * j 0 = 0 := by
    cases he : P.ends with
    | left =>
      simp only [DirichletInterval.zeroTraces, he] at hutr hvtr
      simp [hutr, hvtr]
    | right =>
      simp only [DirichletInterval.zeroTraces, he] at hutr hvtr
      have hr := hc P.length ⟨P.length_pos.le, le_rfl⟩
      simpa only [hutr, hvtr, zero_mul, sub_self] using hr.symm
    | both =>
      simp only [DirichletInterval.zeroTraces, he] at hutr hvtr
      simp [hutr.1, hvtr.1]
  exact fun x hx => (hc x hx).trans hz

theorem DirichletWeakEigenEquation.proportional {P : DirichletInterval} {u : ℝ → ℝ}
    (hu : DirichletWeakEigenEquation P P.principalValue u) :
    EqOn u (fun x => (u (P.length / 2) / P.groundState (P.length / 2)) * P.groundState x)
      (Icc 0 P.length) := by
  obtain ⟨j, hj⟩ := hu.to_strong
  have hW := hu.ground_wronskian_zero hj
  let Q := fun x => u x / P.groundState x
  have hd : ∀ x ∈ Ioo (0 : ℝ) P.length, HasDerivAt Q 0 x := by
    intro x hx
    have hpos := P.groundState_positive hx
    have h := (hj.state_derivative x hx).div
      (dirichletCosine_hasDerivAt P.waveNumber P.center x) hpos.ne'
    change HasDerivAt Q ((j x / P.diffusivity * P.groundState x -
      u x * P.groundSlope x) / P.groundState x ^ 2) x at h
    convert h using 1
    field_simp [P.diffusivity_pos.ne', hpos.ne']
    have hw := hW x (Ioo_subset_Icc_self hx)
    nlinarith
  have hm : P.length / 2 ∈ Ioo (0 : ℝ) P.length := ⟨by linarith [P.length_pos], by linarith [P.length_pos]⟩
  have hqo : ∀ x ∈ Ioo (0 : ℝ) P.length, Q x = Q (P.length / 2) := by
    intro x hx
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) P.length).isPreconnected
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hd t ht).deriv) hx hm
  have he : EqOn u
      (fun x => (u (P.length / 2) / P.groundState (P.length / 2)) * P.groundState x)
      (Ioo 0 P.length) := by
    intro x hx
    exact (div_eq_iff (P.groundState_positive hx).ne').mp (hqo x hx)
  apply he.of_subset_closure
  · simpa only [uIcc_of_le P.length_pos.le] using hu.admissible.1.continuousOn
  · exact continuousOn_const.mul (dirichletCosine_continuous _ _).continuousOn
  · exact Ioo_subset_Icc_self
  · rw [closure_Ioo P.length_pos.ne]

theorem DirichletWeakEigenEquation.unique_scalar {P : DirichletInterval} {u : ℝ → ℝ}
    (hu : DirichletWeakEigenEquation P P.principalValue u) :
    ∃! c : ℝ, EqOn u (fun x => c * P.groundState x) (Icc 0 P.length) := by
  refine ⟨u (P.length / 2) / P.groundState (P.length / 2), hu.proportional, ?_⟩
  intro c hc
  have hm : P.length / 2 ∈ Ioo (0 : ℝ) P.length := ⟨by linarith [P.length_pos], by linarith [P.length_pos]⟩
  apply (eq_div_iff (P.groundState_positive hm).ne').mpr
  exact (hc (Ioo_subset_Icc_self hm)).symm

theorem DirichletInterval.squareMass_of_eq_ground_scalar (P : DirichletInterval)
    {u : ℝ → ℝ} {c : ℝ} (h : EqOn u (fun x => c * P.groundState x) (Icc 0 P.length)) :
    P.squareMass u = c ^ 2 * P.squareMass P.groundState := by
  unfold DirichletInterval.squareMass
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  change u x ^ 2 = c ^ 2 * P.groundState x ^ 2
  rw [h (x := x) (by simpa only [uIcc_of_le P.length_pos.le] using hx), mul_pow]

theorem DirichletWeakEigenEquation.unique_nonzero_scalar {P : DirichletInterval} {u : ℝ → ℝ}
    (hu : DirichletWeakEigenEquation P P.principalValue u) (hm : 0 < P.squareMass u) :
    ∃! c : ℝ, c ≠ 0 ∧ EqOn u (fun x => c * P.groundState x) (Icc 0 P.length) := by
  obtain ⟨c, hc, huniq⟩ := hu.unique_scalar
  have hcn : c ≠ 0 := by
    intro hz
    have hmass := P.squareMass_of_eq_ground_scalar hc
    simp only [hz, zero_pow (by norm_num : 2 ≠ 0), zero_mul] at hmass
    exact hm.ne' hmass
  exact ⟨c, ⟨hcn, hc⟩, fun d hd => huniq d hd.2⟩

theorem DirichletWeakEigenEquation.eqOn_of_midpoint_value {P : DirichletInterval}
    {u v : ℝ → ℝ} (hu : DirichletWeakEigenEquation P P.principalValue u)
    (hv : DirichletWeakEigenEquation P P.principalValue v)
    (hm : u (P.length / 2) = v (P.length / 2)) : EqOn u v (Icc 0 P.length) := by
  intro x hx
  rw [hu.proportional hx, hv.proportional hx, hm]

theorem DirichletWeakEigenEquation.positive_of_midpoint_value_pos {P : DirichletInterval}
    {u : ℝ → ℝ} (hu : DirichletWeakEigenEquation P P.principalValue u)
    (hm : 0 < u (P.length / 2)) : ∀ x ∈ Ioo (0 : ℝ) P.length, 0 < u x := by
  have hmid : P.length / 2 ∈ Ioo (0 : ℝ) P.length := ⟨by linarith [P.length_pos], by linarith [P.length_pos]⟩
  intro x hx
  rw [hu.proportional (Ioo_subset_Icc_self hx)]
  exact mul_pos (div_pos hm (P.groundState_positive hmid)) (P.groundState_positive hx)

end TimeTraps.Spectral
