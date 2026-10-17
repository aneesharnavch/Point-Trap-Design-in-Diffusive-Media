module

public import TimeTraps.Spectral.DirichletRayleigh

@[expose] public section

/-! Strong interior regularity derived from the actual restricted-test H1
equation. Reconstruction uses the signed continuous source ev*u and the
original endpoint values; its difference from u is an admissible H1 test. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis

theorem DirichletInterval.zeroTraces_of_both (P : DirichletInterval) {v : ℝ → ℝ}
    (h0 : v 0 = 0) (hL : v P.length = 0) : P.zeroTraces v := by
  cases he : P.ends <;> simp only [zeroTraces, he] <;> tauto

theorem DirichletWeakEigenEquation.eqOn_reconstructed {P : DirichletInterval}
    {ev : ℝ} {u : ℝ → ℝ} (hu : DirichletWeakEigenEquation P ev u) :
    EqOn u (edgeState (fun _ => P.diffusivity) (fun x => ev * u x)
      0 P.length (u 0) (u P.length)) (Icc 0 P.length) := by
  let f := fun x => ev * u x
  let w := edgeState (fun _ => P.diffusivity) f 0 P.length (u 0) (u P.length)
  have hc : ContinuousOn u (Icc (0 : ℝ) P.length) := by
    simpa only [uIcc_of_le P.length_pos.le] using hu.admissible.1.continuousOn
  have hf : ContinuousOn f (Icc (0 : ℝ) P.length) := continuousOn_const.mul hc
  have hD : ∀ x ∈ Icc (0 : ℝ) P.length, (fun _ => P.diffusivity) x ≠ 0 :=
    fun _ _ => P.diffusivity_pos.ne'
  have hw := reconstructed_edge_equation P.length_pos.le continuousOn_const hf hD
    (u 0) (u P.length)
  have hwE : IntervalEnergy w 0 P.length :=
    hw.state_energy P.length_pos.le continuousOn_const hD
  have hw0 : w 0 = u 0 := edgeState_left _ _ _ _ _ _
  have hwL : w P.length = u P.length := edgeState_right _ _ _ _ _ _
    (resistance_pos P.length_pos continuousOn_const (fun _ _ => P.diffusivity_pos)).ne'
  let δ := fun x => u x - w x
  have hδ : IntervalEnergy δ 0 P.length := hu.admissible.1.sub hwE
  have hδ0 : δ 0 = 0 := by dsimp only [δ]; rw [hw0, sub_self]
  have hδL : δ P.length = 0 := by dsimp only [δ]; rw [hwL, sub_self]
  have htest : P.admissible δ := ⟨hδ, P.zeroTraces_of_both hδ0 hδL⟩
  have h₁ := hu.weak_form δ htest
  have h₂ := hw.green_identity_energy P.length_pos.le hf hD hδ
  change (∫ x in (0 : ℝ)..P.length, P.diffusivity * deriv w x * deriv δ x) =
    (∫ x in (0 : ℝ)..P.length, ev * u x * δ x) +
      _ * δ P.length - _ * δ 0 at h₂
  rw [hδ0, hδL] at h₂
  simp only [mul_zero, add_zero, sub_zero, mul_assoc,
    intervalIntegral.integral_const_mul] at h₂
  have hpair : (∫ x in (0 : ℝ)..P.length, deriv δ x ^ 2) =
      (∫ x in (0 : ℝ)..P.length, deriv u x * deriv δ x) -
        (∫ x in (0 : ℝ)..P.length, deriv w x * deriv δ x) := by
    simpa only [one_mul, pow_two] using
      hu.admissible.1.bilinear_sub_left hwE hδ (a := fun _ => 1) continuousOn_const
  have hz : (∫ x in (0 : ℝ)..P.length, deriv δ x ^ 2) = 0 := by
    have hd := congrArg (fun r : ℝ => P.diffusivity * r) hpair
    have hprod : P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv δ x ^ 2) = 0 := by
      nlinarith [h₁, h₂]
    exact (mul_eq_zero.mp hprod).resolve_left P.diffusivity_pos.ne'
  have hconst := hδ.constant_of_energy_zero P.length_pos.le (a := fun _ => 1)
    continuousOn_const (fun _ _ => zero_lt_one) (by simpa only [one_mul] using hz)
  intro x hx
  have he := hconst x hx
  rw [hδ0] at he
  exact sub_eq_zero.mp he

theorem DirichletWeakEigenEquation.to_strong {P : DirichletInterval}
    {ev : ℝ} {u : ℝ → ℝ} (hu : DirichletWeakEigenEquation P ev u) :
    ∃ j : ℝ → ℝ, EdgeEquation (fun _ => P.diffusivity) (fun x => ev * u x)
      0 P.length u j := by
  have hc : ContinuousOn u (Icc (0 : ℝ) P.length) := by
    simpa only [uIcc_of_le P.length_pos.le] using hu.admissible.1.continuousOn
  have hw := reconstructed_edge_equation (f := fun x => ev * u x) P.length_pos.le continuousOn_const
    (continuousOn_const.mul hc) (fun _ _ => P.diffusivity_pos.ne') (u 0) (u P.length)
  exact ⟨_, hw.congr_state hu.eqOn_reconstructed⟩

end TimeTraps.Spectral
