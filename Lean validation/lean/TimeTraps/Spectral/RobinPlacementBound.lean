module

public import TimeTraps.Spectral.RobinPrincipalBound
public import TimeTraps.Spectral.RobinPlacementProblem

@[expose] public section

/-! The independent physical Robin Rayleigh minimum at every admissible
placement is bounded by the independently constructed Robin capacity root. -/

namespace TimeTraps.Spectral

variable {n : ℕ}

theorem RobinPlacementProblem.arbitrary_upper_bound (C : RobinPlacementProblem n)
    (x : Fin n → ℝ) (hx : C.Admissible x) :
    (C.physical x hx).principalValue ≤ C.diffusivity * C.root ^ 2 :=
  (C.physical x hx).principalValue_le_root C.root_pos C.root_equation

end TimeTraps.Spectral
