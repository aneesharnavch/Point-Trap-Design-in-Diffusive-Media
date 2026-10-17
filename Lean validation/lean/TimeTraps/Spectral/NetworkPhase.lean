module

public import TimeTraps.Spectral.NetworkRayleigh
public import TimeTraps.Spectral.PhaseJump

@[expose] public section

/-! Principal phases of positive physical network eigenstates. The Riccati
equation and positivity give affine phase evolution on every closed arc. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis

variable {V E : Type*} [Fintype E] {P : SpectralNetwork V E} {ev k : ℝ}

noncomputable def PositiveNetworkEigenstate.phase (F : PositiveNetworkEigenstate P ev)
    (k : ℝ) (e : E) (x : ℝ) : ℝ := Real.arctan (F.logSlope e x / k)

theorem PositiveNetworkEigenstate.phase_branch (F : PositiveNetworkEigenstate P ev)
    (k : ℝ) (e : E) (x : ℝ) :
    F.phase k e x ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
  ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩

theorem PositiveNetworkEigenstate.phase_continuous (F : PositiveNetworkEigenstate P ev)
    (k : ℝ) (e : E) : ContinuousOn (F.phase k e) (Icc 0 (P.length e)) :=
  Real.continuous_arctan.comp_continuousOn ((F.logSlope_continuous e).div_const k)

theorem PositiveNetworkEigenstate.phase_hasDerivAt (F : PositiveNetworkEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity)
    (e : E) {x : ℝ} (hx : x ∈ Ioo 0 (P.length e)) :
    HasDerivAt (F.phase k e) (-k) x := by
  have h := ((F.logSlope_hasDerivAt e hx).div_const k).arctan
  have he : 1 / (1 + (F.logSlope e x / k) ^ 2) *
      ((-(ev / P.diffusivity) - F.logSlope e x ^ 2) / k) = -k := by
    rw [← hk2]
    field_simp [ne_of_gt hk]
    ring
  rwa [he] at h

theorem PositiveNetworkEigenstate.phase_affine (F : PositiveNetworkEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity)
    (e : E) {x : ℝ} (hx : x ∈ Icc 0 (P.length e)) :
    F.phase k e x = F.phase k e 0 - k * x := by
  have h := integral_derivative_to_point (F.phase_continuous k e)
    (show ContinuousOn (fun _ : ℝ => -k) (Icc 0 (P.length e)) from continuousOn_const)
    (fun y hy => F.phase_hasDerivAt hk hk2 e hy) hx
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  linarith

end TimeTraps.Spectral
