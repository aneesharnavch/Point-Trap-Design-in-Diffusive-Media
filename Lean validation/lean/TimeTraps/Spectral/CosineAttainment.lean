module

public import TimeTraps.Spectral.CosinePieces

@[expose] public section

/-!
The cosine pieces give an actual global H1 eigenstate, including reflection
and the original point reactions. The independent Rayleigh identification
then proves attainment of the sharp spectral bound.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval TimeTraps.Graph
open scoped Topology

variable {n : ℕ}

noncomputable def PlacementProblem.cosineState (C : PlacementProblem n) : ℝ → ℝ :=
  C.optimalPhysical.geometry.assembledState C.cosineNodes C.cosinePiece

theorem PlacementProblem.cosineState_gap (C : PlacementProblem n) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (C.optimalPhysical.shooting.gap e)) :
    C.cosineState (C.optimalPhysical.geometry.node e.castSucc + x) = C.cosinePiece e x :=
  C.optimalPhysical.geometry.assembledState_gap C.cosineGraphEnergy e hx

theorem PlacementProblem.cosineState_energy (C : PlacementProblem n) :
    IntervalEnergy C.cosineState 0 C.length :=
  C.optimalPhysical.geometry.assembledState_energy_of_piecewise C.cosineGraphEnergy
    (fun e => (C.cosineSlope_continuous e).continuousOn)
    (fun e x _ => C.cosinePiece_hasDerivAt e x)

theorem PlacementProblem.cosineState_positive (C : PlacementProblem n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) C.length) : 0 < C.cosineState x := by
  obtain ⟨e, he⟩ := C.optimalPhysical.geometry.gap_cover hx
  have ht : x - C.optimalPhysical.geometry.node e.castSucc ∈
      Icc (0 : ℝ) (C.optimalPhysical.shooting.gap e) :=
    ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
  have h := C.cosineState_gap e ht
  rw [add_sub_cancel] at h
  rw [h]
  exact C.cosinePiece_positive e ht

theorem PlacementProblem.cosineState_zero (C : PlacementProblem n) : C.cosineState 0 = 1 := by
  have h := C.cosineState_gap 0 ⟨le_rfl, (C.optimalPhysical.shooting.gap_pos 0).le⟩
  rw [add_zero] at h
  change C.cosineState (C.optimalPhysical.geometry.node 0) = C.cosinePiece 0 0 at h
  rw [C.optimalPhysical.geometry.node_first, C.optimalPhysical.geometry_left,
    C.cosinePiece_start, C.startAngle_zero, Real.cos_zero] at h
  exact h

theorem PlacementProblem.cosineState_trap (C : PlacementProblem n) (i : Fin n) :
    C.cosineState (C.optimalSite i) = C.cosinePiece i.castSucc (C.optimalPhysical.shooting.gap i.castSucc) := by
  have h := C.cosineState_gap i.castSucc ⟨(C.optimalPhysical.shooting.gap_pos i.castSucc).le, le_rfl⟩
  rw [C.optimalPhysical.shooting_gap, add_sub_cancel] at h
  change C.cosineState (C.optimalPhysical.geometry.site i) = _ at h
  rw [C.optimalPhysical.geometry_site] at h
  exact h

theorem PlacementProblem.cosineState_gap_hasDerivAt (C : PlacementProblem n)
    (e : Fin (n + 1)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (C.optimalPhysical.shooting.gap e)) :
    HasDerivAt (fun t => C.cosineState (C.optimalPhysical.geometry.node e.castSucc + t))
      (C.cosineSlope e x) x := by
  have he : (fun t => C.cosineState (C.optimalPhysical.geometry.node e.castSucc + t)) =ᶠ[nhds x]
      C.cosinePiece e := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact C.cosineState_gap e (Ioo_subset_Icc_self ht)
  exact (C.cosinePiece_hasDerivAt e x).congr_of_eventuallyEq he

noncomputable def PlacementProblem.cosineEigenstate (C : PlacementProblem n) :
    PositiveEigenstate C.optimalPhysical (C.diffusivity * C.root ^ 2) where
  state := C.cosineState
  slope := C.cosineSlope
  energy := C.cosineState_energy
  positive := fun _ hx => C.cosineState_positive hx
  slope_continuous := fun e => (C.cosineSlope_continuous e).continuousOn
  state_derivative := fun e _ hx => C.cosineState_gap_hasDerivAt e hx
  slope_derivative := by
    intro e x hx
    change HasDerivAt (C.cosineSlope e)
      (-(C.diffusivity * C.root ^ 2 / C.diffusivity) * C.cosineState (C.optimalPhysical.geometry.node e.castSucc + x)) x
    rw [mul_div_cancel_left₀ _ (ne_of_gt C.diffusivity_pos), C.cosineState_gap e (Ioo_subset_Icc_self hx)]
    exact C.cosineSlope_hasDerivAt e x
  left_reflecting := C.cosineSlope_reflecting.1
  right_reflecting := C.cosineSlope_reflecting.2
  reaction_jump := by
    intro i
    change C.diffusivity * (C.cosineSlope i.succ 0 - C.cosineSlope i.castSucc (C.optimalPhysical.shooting.gap i.castSucc)) =
      C.strength i * C.cosineState (C.optimalSite i)
    rw [C.cosineState_trap]
    exact C.cosineSlope_jump i

theorem PlacementProblem.optimal_principalValue (C : PlacementProblem n) :
    C.optimalPhysical.principalValue = C.diffusivity * C.root ^ 2 :=
  C.cosineEigenstate.principalValue_eq

theorem PlacementProblem.cosineState_weak (C : PlacementProblem n) :
    WeakEigenEquation C.optimalPhysical (C.diffusivity * C.root ^ 2) C.cosineState :=
  C.cosineEigenstate.to_weak

theorem PlacementProblem.cosineState_physical_gap (C : PlacementProblem n)
    (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Icc (C.optimalPhysical.geometry.node e.castSucc) (C.optimalPhysical.geometry.node e.succ)) :
    C.cosineState x = Real.cos (C.root * (x - C.boundary e)) := by
  have ht : x - C.optimalPhysical.geometry.node e.castSucc ∈
      Icc (0 : ℝ) (C.optimalPhysical.shooting.gap e) :=
    ⟨sub_nonneg.mpr hx.1, sub_le_sub_right hx.2 _⟩
  have h := C.cosineState_gap e ht
  rw [add_sub_cancel] at h
  rw [h, cosinePiece, C.optimal_left_node]
  congr 1
  field_simp [ne_of_gt C.root_pos]
  ring

theorem PlacementProblem.boundary_gap_coordinate (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.startAngle e / C.root ∈ Icc (0 : ℝ) (C.optimalPhysical.shooting.gap e) := by
  rw [C.optimal_gap]
  constructor
  · exact div_nonneg (C.startAngle_mem e).1 C.root_pos.le
  · exact (div_le_div_iff_of_pos_right C.root_pos).mpr (le_add_of_nonneg_right (C.endAngle_mem e).1)

theorem PlacementProblem.cosineState_boundary (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.cosineState (C.boundary e) = 1 := by
  have h := C.cosineState_gap e (C.boundary_gap_coordinate e)
  rw [C.optimal_left_node, sub_add_cancel, cosinePiece,
    mul_div_cancel₀ _ (ne_of_gt C.root_pos), sub_self, Real.cos_zero] at h
  exact h

theorem PlacementProblem.cosineSlope_boundary (C : PlacementProblem n) (e : Fin (n + 1)) :
    C.cosineSlope e (C.startAngle e / C.root) = 0 := by
  rw [cosineSlope, mul_div_cancel₀ _ (ne_of_gt C.root_pos), sub_self, Real.sin_zero, mul_zero]

theorem PlacementProblem.cosineState_le_one (C : PlacementProblem n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) C.length) : C.cosineState x ≤ 1 := by
  obtain ⟨e, he⟩ := C.optimalPhysical.geometry.gap_cover hx
  rw [C.cosineState_physical_gap e he]
  exact Real.cos_le_one _

end TimeTraps.Spectral
