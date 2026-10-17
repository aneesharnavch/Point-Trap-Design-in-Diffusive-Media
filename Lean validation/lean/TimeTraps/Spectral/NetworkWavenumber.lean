module

public import TimeTraps.Spectral.NetworkRayleigh
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! Wavenumber of the independent network Rayleigh minimum. -/

namespace TimeTraps.Spectral

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def SpectralNetwork.principalWavenumber (P : SpectralNetwork V E) : ℝ :=
  Real.sqrt (P.principalValue / P.diffusivity)

theorem SpectralNetwork.principalWavenumber_pos [Nonempty V] [Nonempty E] (P : SpectralNetwork V E) : 0 < P.principalWavenumber :=
  Real.sqrt_pos.2 (div_pos P.principalValue_pos P.diffusivity_pos)

theorem SpectralNetwork.principalWavenumber_sq [Nonempty V] [Nonempty E] (P : SpectralNetwork V E) :
    P.principalWavenumber ^ 2 = P.principalValue / P.diffusivity :=
  Real.sq_sqrt (div_pos P.principalValue_pos P.diffusivity_pos).le

theorem SpectralNetwork.principalValue_formula [Nonempty V] [Nonempty E] (P : SpectralNetwork V E) :
    P.principalValue = P.diffusivity * P.principalWavenumber ^ 2 := by
  rw [P.principalWavenumber_sq, mul_div_cancel₀ _ (ne_of_gt P.diffusivity_pos)]

theorem SpectralNetwork.principalWavenumber_eq_of_value [Nonempty V] [Nonempty E] (P : SpectralNetwork V E) {r : ℝ}
    (hr : 0 < r) (he : P.principalValue = P.diffusivity * r ^ 2) :
    P.principalWavenumber = r := by
  have hsq := P.principalWavenumber_sq
  rw [he, mul_div_cancel_left₀ _ (ne_of_gt P.diffusivity_pos)] at hsq
  nlinarith [P.principalWavenumber_pos]

end TimeTraps.Spectral
