module

public import TimeTraps.Spectral.PlacementProblem

@[expose] public section

/-! Exact physical gap lengths and phase endpoints for the candidate placement. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Interval

variable {n : ℕ}

noncomputable def PlacementProblem.startAngle (C : PlacementProblem n) : Fin (n + 1) → ℝ :=
  Fin.cases 0 C.angle

noncomputable def PlacementProblem.endAngle (C : PlacementProblem n) : Fin (n + 1) → ℝ :=
  Fin.lastCases 0 C.angle

theorem PlacementProblem.startAngle_zero (C : PlacementProblem n) : C.startAngle 0 = 0 := rfl

theorem PlacementProblem.startAngle_succ (C : PlacementProblem n) (i : Fin n) :
    C.startAngle i.succ = C.angle i := by simp [startAngle]

theorem PlacementProblem.endAngle_last (C : PlacementProblem n) : C.endAngle (Fin.last n) = 0 := by
  simp [endAngle]

theorem PlacementProblem.endAngle_castSucc (C : PlacementProblem n) (i : Fin n) :
    C.endAngle i.castSucc = C.angle i := by simp [endAngle]

theorem PlacementProblem.startAngle_mem (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.startAngle e ∈ Ico (0 : ℝ) (Real.pi / 2) := by
  refine Fin.cases ?_ (fun i => ?_) e
  · rw [C.startAngle_zero]
    exact ⟨le_rfl, div_pos Real.pi_pos (by norm_num)⟩
  · rw [C.startAngle_succ]
    exact ⟨(C.angle_pos i).le, C.angle_lt i⟩

theorem PlacementProblem.endAngle_mem (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.endAngle e ∈ Ico (0 : ℝ) (Real.pi / 2) := by
  refine Fin.lastCases ?_ (fun i => ?_) e
  · rw [C.endAngle_last]
    exact ⟨le_rfl, div_pos Real.pi_pos (by norm_num)⟩
  · rw [C.endAngle_castSucc]
    exact ⟨(C.angle_pos i).le, C.angle_lt i⟩

theorem PlacementProblem.cell_half (C : PlacementProblem n) (i : Fin n) :
    C.cellLength i / 2 = C.angle i / C.root := by unfold cellLength; ring

theorem PlacementProblem.optimal_left_node (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.optimalPhysical.geometry.node e.castSucc = C.boundary e - C.startAngle e / C.root := by
  refine Fin.cases ?_ (fun i => ?_) e
  · change C.optimalPhysical.geometry.node 0 = _
    rw [C.optimalPhysical.geometry.node_first, C.optimalPhysical.geometry_left,
      C.boundary_zero, C.startAngle_zero, zero_div, sub_self]
  · change C.optimalPhysical.geometry.site i = _
    rw [C.optimalPhysical.geometry_site, C.boundary_succ, C.startAngle_succ]
    change C.optimalSite i = C.boundary i.castSucc + C.cellLength i - C.angle i / C.root
    unfold optimalSite cellLength
    ring

theorem PlacementProblem.optimal_right_node (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.optimalPhysical.geometry.node e.succ = C.boundary e + C.endAngle e / C.root := by
  refine Fin.lastCases ?_ (fun i => ?_) e
  · change C.optimalPhysical.geometry.node (Fin.last (n + 1)) = _
    rw [C.optimalPhysical.geometry.node_last, C.optimalPhysical.geometry_right,
      C.boundary_last, C.endAngle_last, zero_div, add_zero]
    rfl
  · change C.optimalPhysical.geometry.site i = _
    rw [C.optimalPhysical.geometry_site, C.endAngle_castSucc]
    change C.optimalSite i = C.boundary i.castSucc + C.angle i / C.root
    rw [optimalSite, C.cell_half]

theorem PlacementProblem.optimal_gap (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.optimalPhysical.shooting.gap e = (C.startAngle e + C.endAngle e) / C.root := by
  rw [C.optimalPhysical.shooting_gap, C.optimal_left_node, C.optimal_right_node]
  ring

theorem PlacementProblem.gap_phase_right (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.root * C.optimalPhysical.shooting.gap e - C.startAngle e = C.endAngle e := by
  rw [C.optimal_gap, mul_div_cancel₀ _ (ne_of_gt C.root_pos)]
  ring

theorem PlacementProblem.gap_phase_mem (C : PlacementProblem n) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (C.optimalPhysical.shooting.gap e)) :
    C.root * x - C.startAngle e ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have ha := C.startAngle_mem e
  have hb := C.endAngle_mem e
  have hleft := mul_nonneg C.root_pos.le hx.1
  have hright := mul_le_mul_of_nonneg_left hx.2 C.root_pos.le
  have hend := C.gap_phase_right e
  constructor <;> linarith [ha.2, hb.2]

theorem PlacementProblem.angle_reaction (C : PlacementProblem n) (i : Fin n) :
    2 * C.diffusivity * C.root * Real.sin (C.angle i) = C.strength i * Real.cos (C.angle i) := by
  have htan : Real.tan (C.angle i) = C.strength i / (2 * C.diffusivity * C.root) :=
    Real.tan_arctan _
  have hcos : Real.cos (C.angle i) ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [C.angle_pos i, Real.pi_pos], C.angle_lt i⟩)
  rw [Real.tan_eq_sin_div_cos] at htan
  field_simp [hcos, ne_of_gt C.diffusivity_pos, ne_of_gt C.root_pos] at htan
  nlinarith

end TimeTraps.Spectral
