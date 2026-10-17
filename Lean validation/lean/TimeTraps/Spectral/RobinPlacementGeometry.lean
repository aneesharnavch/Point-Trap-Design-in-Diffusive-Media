module

public import TimeTraps.Spectral.RobinPlacementProblem

@[expose] public section

/-! Exact physical gap lengths and phase endpoints for the candidate placement. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Interval

variable {n : ℕ}

noncomputable def RobinPlacementProblem.startAngle (C : RobinPlacementProblem n) : Fin (n + 1) → ℝ :=
  Fin.cases C.leftAngle C.angle

noncomputable def RobinPlacementProblem.endAngle (C : RobinPlacementProblem n) : Fin (n + 1) → ℝ :=
  Fin.lastCases C.rightAngle C.angle

theorem RobinPlacementProblem.startAngle_zero (C : RobinPlacementProblem n) : C.startAngle 0 = C.leftAngle := rfl

theorem RobinPlacementProblem.startAngle_succ (C : RobinPlacementProblem n) (i : Fin n) :
    C.startAngle i.succ = C.angle i := by simp [startAngle]

theorem RobinPlacementProblem.endAngle_last (C : RobinPlacementProblem n) : C.endAngle (Fin.last n) = C.rightAngle := by
  simp [endAngle]

theorem RobinPlacementProblem.endAngle_castSucc (C : RobinPlacementProblem n) (i : Fin n) :
    C.endAngle i.castSucc = C.angle i := by simp [endAngle]

theorem RobinPlacementProblem.startAngle_mem (C : RobinPlacementProblem n) (e : Fin (n + 1)) :
    C.startAngle e ∈ Ico (0 : ℝ) (Real.pi / 2) := by
  refine Fin.cases ?_ (fun i => ?_) e
  · rw [C.startAngle_zero]
    exact ⟨C.leftAngle_nonneg, C.leftAngle_lt⟩
  · rw [C.startAngle_succ]
    exact ⟨(C.angle_pos i).le, C.angle_lt i⟩

theorem RobinPlacementProblem.endAngle_mem (C : RobinPlacementProblem n) (e : Fin (n + 1)) :
    C.endAngle e ∈ Ico (0 : ℝ) (Real.pi / 2) := by
  refine Fin.lastCases ?_ (fun i => ?_) e
  · rw [C.endAngle_last]
    exact ⟨C.rightAngle_nonneg, C.rightAngle_lt⟩
  · rw [C.endAngle_castSucc]
    exact ⟨(C.angle_pos i).le, C.angle_lt i⟩

theorem RobinPlacementProblem.cell_half (C : RobinPlacementProblem n) (i : Fin n) :
    C.cellLength i / 2 = C.angle i / C.root := by unfold cellLength; ring

theorem RobinPlacementProblem.candidate_left_node (C : RobinPlacementProblem n) (e : Fin (n + 1)) :
    C.candidatePhysical.geometry.node e.castSucc = C.boundary e - C.startAngle e / C.root := by
  refine Fin.cases ?_ (fun i => ?_) e
  · change C.candidatePhysical.geometry.node 0 = _
    rw [C.candidatePhysical.geometry.node_first, C.candidatePhysical.geometry_left,
      C.boundary_zero, C.startAngle_zero, sub_self]
  · change C.candidatePhysical.geometry.site i = _
    rw [C.candidatePhysical.geometry_site, C.boundary_succ, C.startAngle_succ]
    change C.candidateSite i = C.boundary i.castSucc + C.cellLength i - C.angle i / C.root
    unfold candidateSite cellLength
    ring

theorem RobinPlacementProblem.candidate_right_node (C : RobinPlacementProblem n) (e : Fin (n + 1)) :
    C.candidatePhysical.geometry.node e.succ = C.boundary e + C.endAngle e / C.root := by
  refine Fin.lastCases ?_ (fun i => ?_) e
  · change C.candidatePhysical.geometry.node (Fin.last (n + 1)) = _
    rw [C.candidatePhysical.geometry.node_last, C.candidatePhysical.geometry_right,
      C.boundary_last, C.endAngle_last]
    change C.length = C.length - C.rightAngle / C.root + C.rightAngle / C.root
    ring
  · change C.candidatePhysical.geometry.site i = _
    rw [C.candidatePhysical.geometry_site, C.endAngle_castSucc]
    change C.candidateSite i = C.boundary i.castSucc + C.angle i / C.root
    rw [candidateSite, C.cell_half]

theorem RobinPlacementProblem.candidate_gap (C : RobinPlacementProblem n) (e : Fin (n + 1)) :
    C.candidatePhysical.shooting.gap e = (C.startAngle e + C.endAngle e) / C.root := by
  rw [C.candidatePhysical.shooting_gap, C.candidate_left_node, C.candidate_right_node]
  ring

theorem RobinPlacementProblem.gap_phase_right (C : RobinPlacementProblem n) (e : Fin (n + 1)) :
    C.root * C.candidatePhysical.shooting.gap e - C.startAngle e = C.endAngle e := by
  rw [C.candidate_gap, mul_div_cancel₀ _ (ne_of_gt C.root_pos)]
  ring

theorem RobinPlacementProblem.gap_phase_mem (C : RobinPlacementProblem n) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (C.candidatePhysical.shooting.gap e)) :
    C.root * x - C.startAngle e ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have ha := C.startAngle_mem e
  have hb := C.endAngle_mem e
  have hleft := mul_nonneg C.root_pos.le hx.1
  have hright := mul_le_mul_of_nonneg_left hx.2 C.root_pos.le
  have hend := C.gap_phase_right e
  constructor <;> linarith [ha.2, hb.2]

theorem RobinPlacementProblem.angle_reaction (C : RobinPlacementProblem n) (i : Fin n) :
    2 * C.diffusivity * C.root * Real.sin (C.angle i) = C.strength i * Real.cos (C.angle i) := by
  have htan : Real.tan (C.angle i) = C.strength i / (2 * C.diffusivity * C.root) :=
    Real.tan_arctan _
  have hcos : Real.cos (C.angle i) ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [C.angle_pos i, Real.pi_pos], C.angle_lt i⟩)
  rw [Real.tan_eq_sin_div_cos] at htan
  field_simp [hcos, ne_of_gt C.diffusivity_pos, ne_of_gt C.root_pos] at htan
  nlinarith

theorem RobinPlacementProblem.candidate_gap_first (C : RobinPlacementProblem n) :
    C.candidatePhysical.shooting.gap 0 =
      (C.leftAngle + C.angle ⟨0, C.count_pos⟩) / C.root := by
  rw [C.candidate_gap, C.startAngle_zero]
  have h0 : (0 : Fin (n + 1)) = (⟨0, C.count_pos⟩ : Fin n).castSucc := rfl
  rw [h0, C.endAngle_castSucc]

theorem RobinPlacementProblem.candidate_gap_interior (C : RobinPlacementProblem (n + 1)) (i : Fin n) :
    C.candidatePhysical.shooting.gap i.succ.castSucc =
      (C.angle i.castSucc + C.angle i.succ) / C.root := by
  rw [C.candidate_gap, C.endAngle_castSucc]
  change (C.startAngle i.castSucc.succ + C.angle i.succ) / C.root = _
  rw [C.startAngle_succ]

theorem RobinPlacementProblem.candidate_gap_last (C : RobinPlacementProblem (n + 1)) :
    C.candidatePhysical.shooting.gap (Fin.last (n + 1)) =
      (C.angle (Fin.last n) + C.rightAngle) / C.root := by
  rw [C.candidate_gap, C.endAngle_last]
  change (C.startAngle (Fin.last n).succ + C.rightAngle) / C.root = _
  rw [C.startAngle_succ]

theorem RobinPlacementProblem.leftAngle_reaction (C : RobinPlacementProblem n) :
    C.diffusivity * C.root * Real.sin C.leftAngle = C.betaLeft * Real.cos C.leftAngle := by
  have htan : Real.tan C.leftAngle = C.betaLeft / (C.diffusivity * C.root) := Real.tan_arctan _
  have hcos : Real.cos C.leftAngle ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [C.leftAngle_nonneg, Real.pi_pos], C.leftAngle_lt⟩)
  rw [Real.tan_eq_sin_div_cos] at htan
  field_simp [hcos, ne_of_gt C.diffusivity_pos, ne_of_gt C.root_pos] at htan
  nlinarith

theorem RobinPlacementProblem.rightAngle_reaction (C : RobinPlacementProblem n) :
    C.diffusivity * C.root * Real.sin C.rightAngle = C.betaRight * Real.cos C.rightAngle := by
  have htan : Real.tan C.rightAngle = C.betaRight / (C.diffusivity * C.root) := Real.tan_arctan _
  have hcos : Real.cos C.rightAngle ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [C.rightAngle_nonneg, Real.pi_pos], C.rightAngle_lt⟩)
  rw [Real.tan_eq_sin_div_cos] at htan
  field_simp [hcos, ne_of_gt C.diffusivity_pos, ne_of_gt C.root_pos] at htan
  nlinarith

end TimeTraps.Spectral
