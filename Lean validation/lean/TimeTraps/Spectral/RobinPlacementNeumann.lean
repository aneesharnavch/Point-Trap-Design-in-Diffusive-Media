module

public import TimeTraps.Spectral.RobinPlacementProblem

@[expose] public section

/-! Exact zero-endpoint recovery of the Neumann root and physical candidate sites. -/

namespace TimeTraps.Spectral

variable {n : ℕ}

theorem RobinPlacementProblem.root_neumann (C : RobinPlacementProblem n)
    (hleft : C.betaLeft = 0) (hright : C.betaRight = 0) :
    C.root = C.toPlacementProblem.root := by
  apply C.toPlacementProblem.eq_root C.root_pos
  have h := C.root_equation
  simpa only [hleft, hright, zero_div, Real.arctan_zero, add_zero, zero_add] using h

theorem RobinPlacementProblem.angle_neumann (C : RobinPlacementProblem n)
    (hleft : C.betaLeft = 0) (hright : C.betaRight = 0) :
    C.angle = C.toPlacementProblem.angle := by
  funext i
  unfold angle PlacementProblem.angle
  rw [C.root_neumann hleft hright]

theorem RobinPlacementProblem.cellLength_neumann (C : RobinPlacementProblem n)
    (hleft : C.betaLeft = 0) (hright : C.betaRight = 0) :
    C.cellLength = C.toPlacementProblem.cellLength := by
  funext i
  unfold cellLength PlacementProblem.cellLength
  rw [C.root_neumann hleft hright, C.angle_neumann hleft hright]

theorem RobinPlacementProblem.boundary_neumann (C : RobinPlacementProblem n)
    (hleft : C.betaLeft = 0) (hright : C.betaRight = 0) :
    C.boundary = C.toPlacementProblem.boundary := by
  funext e
  induction e using Fin.induction with
  | zero =>
    rw [C.boundary_zero, C.toPlacementProblem.boundary_zero]
    simp only [leftAngle, hleft, zero_div, Real.arctan_zero]
  | succ i ih =>
    rw [C.boundary_succ, C.toPlacementProblem.boundary_succ,
      C.cellLength_neumann hleft hright, ih]

theorem RobinPlacementProblem.candidateSite_neumann (C : RobinPlacementProblem n)
    (hleft : C.betaLeft = 0) (hright : C.betaRight = 0) :
    C.candidateSite = C.toPlacementProblem.optimalSite := by
  funext i
  unfold candidateSite PlacementProblem.optimalSite
  rw [C.boundary_neumann hleft hright, C.cellLength_neumann hleft hright]

end TimeTraps.Spectral
