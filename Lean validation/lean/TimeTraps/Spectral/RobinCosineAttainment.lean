module

public import TimeTraps.Spectral.RobinCosinePieces
public import TimeTraps.Spectral.RobinWeak

@[expose] public section

/-!
The cosine pieces give an actual global H1 eigenstate, including both Robin
boundary conditions and the original point reactions. The independent
Rayleigh identification proves the candidate's principal value is D*root^2.
Comparison with arbitrary placements and optimizer rigidity are separate.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval TimeTraps.Graph
open scoped Topology

variable {n : ℕ}

noncomputable def RobinPlacementProblem.cosineState (C : RobinPlacementProblem n) : ℝ → ℝ :=
  C.candidatePhysical.geometry.assembledState C.cosineNodes C.cosinePiece

theorem RobinPlacementProblem.cosineState_gap (C : RobinPlacementProblem n) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (C.candidatePhysical.shooting.gap e)) :
    C.cosineState (C.candidatePhysical.geometry.node e.castSucc + x) = C.cosinePiece e x :=
  C.candidatePhysical.geometry.assembledState_gap C.cosineGraphEnergy e hx

theorem RobinPlacementProblem.cosineState_energy (C : RobinPlacementProblem n) :
    IntervalEnergy C.cosineState 0 C.length :=
  C.candidatePhysical.geometry.assembledState_energy_of_piecewise C.cosineGraphEnergy
    (fun e => (C.cosineSlope_continuous e).continuousOn)
    (fun e x _ => C.cosinePiece_hasDerivAt e x)

theorem RobinPlacementProblem.cosineState_positive (C : RobinPlacementProblem n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) C.length) : 0 < C.cosineState x := by
  obtain ⟨e, he⟩ := C.candidatePhysical.geometry.gap_cover hx
  have ht : x - C.candidatePhysical.geometry.node e.castSucc ∈
      Icc (0 : ℝ) (C.candidatePhysical.shooting.gap e) :=
    ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
  have h := C.cosineState_gap e ht
  rw [add_sub_cancel] at h
  rw [h]
  exact C.cosinePiece_positive e ht

theorem RobinPlacementProblem.cosineState_zero (C : RobinPlacementProblem n) : C.cosineState 0 = Real.cos C.leftAngle := by
  have h := C.cosineState_gap 0 ⟨le_rfl, (C.candidatePhysical.shooting.gap_pos 0).le⟩
  rw [add_zero] at h
  change C.cosineState (C.candidatePhysical.geometry.node 0) = C.cosinePiece 0 0 at h
  rw [C.candidatePhysical.geometry.node_first, C.candidatePhysical.geometry_left,
    C.cosinePiece_start, C.startAngle_zero] at h
  exact h

theorem RobinPlacementProblem.cosineState_right (C : RobinPlacementProblem n) :
    C.cosineState C.length = Real.cos C.rightAngle := by
  have h := C.cosineState_gap (Fin.last n)
    ⟨(C.candidatePhysical.shooting.gap_pos (Fin.last n)).le, le_rfl⟩
  rw [C.candidatePhysical.shooting_gap, add_sub_cancel] at h
  change C.cosineState (C.candidatePhysical.geometry.node (Fin.last (n + 1))) =
    C.cosinePiece (Fin.last n) (C.candidatePhysical.shooting.gap (Fin.last n)) at h
  rw [C.candidatePhysical.geometry.node_last, C.candidatePhysical.geometry_right,
    C.cosinePiece_end, C.endAngle_last] at h
  exact h

theorem RobinPlacementProblem.cosineState_trap (C : RobinPlacementProblem n) (i : Fin n) :
    C.cosineState (C.candidateSite i) = C.cosinePiece i.castSucc (C.candidatePhysical.shooting.gap i.castSucc) := by
  have h := C.cosineState_gap i.castSucc ⟨(C.candidatePhysical.shooting.gap_pos i.castSucc).le, le_rfl⟩
  rw [C.candidatePhysical.shooting_gap, add_sub_cancel] at h
  change C.cosineState (C.candidatePhysical.geometry.site i) = _ at h
  rw [C.candidatePhysical.geometry_site] at h
  exact h

theorem RobinPlacementProblem.cosineState_gap_hasDerivAt (C : RobinPlacementProblem n)
    (e : Fin (n + 1)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (C.candidatePhysical.shooting.gap e)) :
    HasDerivAt (fun t => C.cosineState (C.candidatePhysical.geometry.node e.castSucc + t))
      (C.cosineSlope e x) x := by
  have he : (fun t => C.cosineState (C.candidatePhysical.geometry.node e.castSucc + t)) =ᶠ[nhds x]
      C.cosinePiece e := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact C.cosineState_gap e (Ioo_subset_Icc_self ht)
  exact (C.cosinePiece_hasDerivAt e x).congr_of_eventuallyEq he

noncomputable def RobinPlacementProblem.cosineEigenstate (C : RobinPlacementProblem n) :
    PositiveRobinEigenstate C.candidatePhysical (C.diffusivity * C.root ^ 2) where
  state := C.cosineState
  slope := C.cosineSlope
  energy := C.cosineState_energy
  positive := fun _ hx => C.cosineState_positive hx
  slope_continuous := fun e => (C.cosineSlope_continuous e).continuousOn
  state_derivative := fun e _ hx => C.cosineState_gap_hasDerivAt e hx
  slope_derivative := by
    intro e x hx
    change HasDerivAt (C.cosineSlope e)
      (-(C.diffusivity * C.root ^ 2 / C.diffusivity) * C.cosineState (C.candidatePhysical.geometry.node e.castSucc + x)) x
    rw [mul_div_cancel_left₀ _ (ne_of_gt C.diffusivity_pos), C.cosineState_gap e (Ioo_subset_Icc_self hx)]
    exact C.cosineSlope_hasDerivAt e x
  left_robin := by
    change C.diffusivity * C.cosineSlope 0 0 = C.betaLeft * C.cosineState 0
    rw [C.cosineState_zero]
    have h := C.cosineSlope_robin.1
    rw [C.cosinePiece_start, C.startAngle_zero] at h
    exact h
  right_robin := by
    change C.diffusivity * C.cosineSlope (Fin.last n) (C.candidatePhysical.shooting.gap (Fin.last n)) =
      -C.betaRight * C.cosineState C.length
    rw [C.cosineState_right]
    have h := C.cosineSlope_robin.2
    rw [C.cosinePiece_end, C.endAngle_last] at h
    exact h
  reaction_jump := by
    intro i
    change C.diffusivity * (C.cosineSlope i.succ 0 - C.cosineSlope i.castSucc (C.candidatePhysical.shooting.gap i.castSucc)) =
      C.strength i * C.cosineState (C.candidateSite i)
    rw [C.cosineState_trap]
    exact C.cosineSlope_jump i

theorem RobinPlacementProblem.candidate_principalValue (C : RobinPlacementProblem n) :
    C.candidatePhysical.principalValue = C.diffusivity * C.root ^ 2 :=
  C.cosineEigenstate.principalValue_eq

theorem RobinPlacementProblem.cosineState_weak (C : RobinPlacementProblem n) :
    RobinWeakEigenEquation C.candidatePhysical (C.diffusivity * C.root ^ 2) C.cosineState :=
  C.cosineEigenstate.to_weak

theorem RobinPlacementProblem.cosineState_physical_gap (C : RobinPlacementProblem n)
    (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Icc (C.candidatePhysical.geometry.node e.castSucc) (C.candidatePhysical.geometry.node e.succ)) :
    C.cosineState x = Real.cos (C.root * (x - C.boundary e)) := by
  have ht : x - C.candidatePhysical.geometry.node e.castSucc ∈
      Icc (0 : ℝ) (C.candidatePhysical.shooting.gap e) :=
    ⟨sub_nonneg.mpr hx.1, sub_le_sub_right hx.2 _⟩
  have h := C.cosineState_gap e ht
  rw [add_sub_cancel] at h
  rw [h, cosinePiece, C.candidate_left_node]
  congr 1
  field_simp [ne_of_gt C.root_pos]
  ring

theorem RobinPlacementProblem.boundary_gap_coordinate (C : RobinPlacementProblem n) (e : Fin (n + 1)) :
    C.startAngle e / C.root ∈ Icc (0 : ℝ) (C.candidatePhysical.shooting.gap e) := by
  rw [C.candidate_gap]
  constructor
  · exact div_nonneg (C.startAngle_mem e).1 C.root_pos.le
  · exact (div_le_div_iff_of_pos_right C.root_pos).mpr (le_add_of_nonneg_right (C.endAngle_mem e).1)

theorem RobinPlacementProblem.cosineState_boundary (C : RobinPlacementProblem n) (e : Fin (n + 1)) :
    C.cosineState (C.boundary e) = 1 := by
  have h := C.cosineState_gap e (C.boundary_gap_coordinate e)
  rw [C.candidate_left_node, sub_add_cancel, cosinePiece,
    mul_div_cancel₀ _ (ne_of_gt C.root_pos), sub_self, Real.cos_zero] at h
  exact h

theorem RobinPlacementProblem.cosineSlope_boundary (C : RobinPlacementProblem n) (e : Fin (n + 1)) :
    C.cosineSlope e (C.startAngle e / C.root) = 0 := by
  rw [cosineSlope, mul_div_cancel₀ _ (ne_of_gt C.root_pos), sub_self, Real.sin_zero, mul_zero]

theorem RobinPlacementProblem.cosineState_le_one (C : RobinPlacementProblem n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) C.length) : C.cosineState x ≤ 1 := by
  obtain ⟨e, he⟩ := C.candidatePhysical.geometry.gap_cover hx
  rw [C.cosineState_physical_gap e he]
  exact Real.cos_le_one _

end TimeTraps.Spectral
