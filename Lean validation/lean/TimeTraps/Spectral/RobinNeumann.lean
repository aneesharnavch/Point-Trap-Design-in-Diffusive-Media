module

public import TimeTraps.Spectral.RobinWeak
public import TimeTraps.Spectral.WeakEigenstate

@[expose] public section

/-! Setting both endpoint coefficients to zero recovers the independently
defined Neumann form, full Rayleigh class, principal value and weak equation. -/

namespace TimeTraps.Spectral

variable {n : ℕ}

theorem RobinProblem.quadraticForm_neumann (P : RobinProblem n)
    (hleft : P.betaLeft = 0) (hright : P.betaRight = 0) (v : ℝ → ℝ) :
    P.quadraticForm v = P.toSpectralProblem.quadraticForm v := by
  simp only [quadraticForm, hleft, hright, zero_mul, add_zero]

theorem RobinProblem.rayleighValues_neumann (P : RobinProblem n)
    (hleft : P.betaLeft = 0) (hright : P.betaRight = 0) :
    P.rayleighValues = P.toSpectralProblem.rayleighValues := by
  ext r
  unfold rayleighValues SpectralProblem.rayleighValues
  simp only [P.quadraticForm_neumann hleft hright, squareMass]

theorem RobinProblem.principalValue_neumann (P : RobinProblem n)
    (hleft : P.betaLeft = 0) (hright : P.betaRight = 0) :
    P.principalValue = P.toSpectralProblem.principalValue := by
  unfold principalValue SpectralProblem.principalValue
  rw [P.rayleighValues_neumann hleft hright]

theorem RobinProblem.weak_neumann_iff (P : RobinProblem n)
    (hleft : P.betaLeft = 0) (hright : P.betaRight = 0) (ev : ℝ) (u : ℝ → ℝ) :
    RobinWeakEigenEquation P ev u ↔ WeakEigenEquation P.toSpectralProblem ev u := by
  constructor
  · rintro ⟨he, hw⟩
    refine ⟨he, ?_⟩
    intro v hv
    simpa only [hleft, hright, zero_mul, add_zero] using hw v hv
  · rintro ⟨he, hw⟩
    refine ⟨he, ?_⟩
    intro v hv
    simpa only [hleft, hright, zero_mul, add_zero] using hw v hv

end TimeTraps.Spectral
