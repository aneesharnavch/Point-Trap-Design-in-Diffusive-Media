module

public import TimeTraps.Spectral.NetworkOperatorForm
public import TimeTraps.Spectral.NetworkRayleigh

@[expose] public section

/-! Coercivity is derived from the original, independently proved network
Rayleigh minimum and the positive diffusion term. No Hilbert solution
operator or spectral theorem enters this estimate. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem SpectralNetwork.operatorForm_mass_lower (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) :
    P.principalValue * P.squareMass (P.operatorRep u) ≤ P.operatorForm u u := by
  let : Nonempty V := ⟨P.tail (Classical.choice inferInstance)⟩
  have hm : 0 ≤ P.squareMass (P.operatorRep u) := by
    rw [P.operator_squareMass]
    positivity
  by_cases hz : P.squareMass (P.operatorRep u) = 0
  · rw [hz, mul_zero]
    exact P.operatorForm_nonneg u
  · have hp : 0 < P.squareMass (P.operatorRep u) := lt_of_le_of_ne hm (Ne.symm hz)
    have hr : P.quadraticForm (P.operatorNodes u) (P.operatorRep u) /
        P.squareMass (P.operatorRep u) ∈ P.rayleighValues :=
      ⟨P.operatorNodes u, P.operatorRep u, P.operatorRep_energy u, hp, rfl⟩
    have h := (le_div_iff₀ hp).mp (P.rayleigh_minimum.2 hr)
    rwa [← P.operatorForm_self u] at h

theorem SpectralNetwork.operatorForm_derivative_lower (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) :
    P.diffusivity * (∑ e, ∫ x in (0 : ℝ)..P.length e, deriv (P.operatorRep u e) x ^ 2) ≤
      P.operatorForm u u := by
  rw [P.operatorForm_self, quadraticForm]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun v _ =>
    mul_nonneg (P.strength_pos v).le (sq_nonneg _))

theorem SpectralNetwork.operator_h1_control (P : SpectralNetwork V E)
    (u : GraphSobolevSpace P.geometry) :
    ‖u‖ ^ 2 ≤ (P.principalValue⁻¹ + P.diffusivity⁻¹) * P.operatorForm u u := by
  let : Nonempty V := ⟨P.tail (Classical.choice inferInstance)⟩
  have hm : P.squareMass (P.operatorRep u) ≤ P.operatorForm u u / P.principalValue := by
    apply (le_div_iff₀ P.principalValue_pos).mpr
    simpa only [mul_comm] using P.operatorForm_mass_lower u
  have hd : (∑ e, ∫ x in (0 : ℝ)..P.length e, deriv (P.operatorRep u e) x ^ 2) ≤
      P.operatorForm u u / P.diffusivity := by
    apply (le_div_iff₀ P.diffusivity_pos).mpr
    simpa only [mul_comm] using P.operatorForm_derivative_lower u
  rw [P.operator_norm_sq]
  calc
    _ ≤ P.operatorForm u u / P.principalValue + P.operatorForm u u / P.diffusivity := add_le_add hm hd
    _ = _ := by ring

noncomputable def SpectralNetwork.operatorCoercivityConstant (P : SpectralNetwork V E) : ℝ :=
  (P.principalValue⁻¹ + P.diffusivity⁻¹)⁻¹

theorem SpectralNetwork.operatorCoercivityConstant_pos (P : SpectralNetwork V E) :
    0 < P.operatorCoercivityConstant := by
  let : Nonempty V := ⟨P.tail (Classical.choice inferInstance)⟩
  exact inv_pos.mpr (add_pos (inv_pos.mpr P.principalValue_pos) (inv_pos.mpr P.diffusivity_pos))

theorem SpectralNetwork.operatorForm_coercive (P : SpectralNetwork V E) :
    @IsCoercive (GraphSobolevSpace P.geometry)
      (Submodule.seminormedAddCommGroup (graphSobolevSubspace P.geometry))
      (Submodule.normedSpace (graphSobolevSubspace P.geometry)) P.operatorForm := by
  let : Nonempty V := ⟨P.tail (Classical.choice inferInstance)⟩
  have hA : 0 < P.principalValue⁻¹ + P.diffusivity⁻¹ :=
    add_pos (inv_pos.mpr P.principalValue_pos) (inv_pos.mpr P.diffusivity_pos)
  refine ⟨P.operatorCoercivityConstant, P.operatorCoercivityConstant_pos, ?_⟩
  intro u
  have h := mul_le_mul_of_nonneg_left (P.operator_h1_control u) (inv_nonneg.mpr hA.le)
  rw [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul] at h
  simpa only [operatorCoercivityConstant, pow_two, mul_assoc] using h

end TimeTraps.Spectral
