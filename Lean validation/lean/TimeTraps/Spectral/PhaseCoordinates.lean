module

public import TimeTraps.Spectral.PhaseEquality
public import TimeTraps.Spectral.PlacementProblem

@[expose] public section

/-! Physical positions recovered from phase evolution and cumulative jumps. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Interval

variable {n : ℕ} {P : SpectralProblem n} {ev k : ℝ}

theorem PositiveEigenstate.phase_position_balance (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) (e : Fin (n + 1)) :
    k * P.geometry.node e.castSucc + E.phase k e 0 =
      absorptionPrefix (fun i => E.phase k i.succ 0 - E.phase k i.castSucc (P.shooting.gap i.castSucc)) e := by
  induction e using Fin.induction with
  | zero =>
    change k * P.geometry.node 0 + E.phase k 0 0 = _
    rw [P.geometry.node_first, P.geometry_left, E.phase_left, absorptionPrefix_zero, mul_zero, add_zero]
  | succ i ih =>
    have he := E.phase_affine hk hk2 i.castSucc ⟨(P.shooting.gap_pos i.castSucc).le, le_rfl⟩
    have hg := congrArg (fun t : ℝ => k * t) (P.shooting_gap i.castSucc)
    rw [hg] at he
    rw [absorptionPrefix_succ, ← ih]
    change k * P.geometry.node i.castSucc.succ + E.phase k i.succ 0 =
      k * P.geometry.node i.castSucc.castSucc + E.phase k i.castSucc 0 +
        (E.phase k i.succ 0 - E.phase k i.castSucc (P.shooting.gap i.castSucc))
    nlinarith

theorem PositiveEigenstate.phase_site_formula (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) (i : Fin n) :
    k * P.site i =
      absorptionPrefix (fun j => E.phase k j.succ 0 - E.phase k j.castSucc (P.shooting.gap j.castSucc)) i.castSucc -
        E.phase k i.castSucc (P.shooting.gap i.castSucc) := by
  have hp := E.phase_position_balance hk hk2 i.castSucc
  have he := E.phase_affine hk hk2 i.castSucc ⟨(P.shooting.gap_pos i.castSucc).le, le_rfl⟩
  have hg := congrArg (fun t : ℝ => k * t) (P.shooting_gap i.castSucc)
  rw [hg] at he
  have hsite : P.geometry.node i.castSucc.succ = P.site i := P.geometry_site i
  rw [hsite] at he
  nlinarith

theorem PlacementProblem.boundary_angle_sum (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.root * C.boundary e = absorptionPrefix (fun i => 2 * C.angle i) e := by
  induction e using Fin.induction with
  | zero => rw [C.boundary_zero, absorptionPrefix_zero, mul_zero]
  | succ i ih =>
    rw [C.boundary_succ, absorptionPrefix_succ, mul_add, ih]
    congr 1
    rw [PlacementProblem.cellLength, mul_div_cancel₀ _ (ne_of_gt C.root_pos)]

end TimeTraps.Spectral
