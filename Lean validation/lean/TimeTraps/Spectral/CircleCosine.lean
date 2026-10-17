module

public import TimeTraps.Spectral.CirclePlacement

@[expose] public section

/-! Exact positive cosine pieces on the physical gaps of the candidate placement. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis TimeTraps.Interval TimeTraps.Graph

variable {n : ℕ}

noncomputable def PlacementProblem.circleCosine (C : PlacementProblem n)
    (e : Fin n) (x : ℝ) : ℝ := Real.cos (C.root * x - C.angle e)

noncomputable def PlacementProblem.circleCosineSlope (C : PlacementProblem n)
    (e : Fin n) (x : ℝ) : ℝ := -C.root * Real.sin (C.root * x - C.angle e)

theorem PlacementProblem.circleCosine_continuous (C : PlacementProblem n) (e : Fin n) :
    Continuous (C.circleCosine e) := by unfold circleCosine; fun_prop

theorem PlacementProblem.circleCosineSlope_continuous (C : PlacementProblem n) (e : Fin n) :
    Continuous (C.circleCosineSlope e) := by unfold circleCosineSlope; fun_prop

theorem PlacementProblem.circleCosine_hasDerivAt (C : PlacementProblem n) (e : Fin n) (x : ℝ) :
    HasDerivAt (C.circleCosine e) (C.circleCosineSlope e x) x := by
  have h := (((hasDerivAt_id x).const_mul C.root).sub_const (C.angle e)).cos
  have he : -Real.sin (C.root * x - C.angle e) * (C.root * 1) = C.circleCosineSlope e x := by
    unfold circleCosineSlope
    ring
  change HasDerivAt (C.circleCosine e) (-Real.sin (C.root * x - C.angle e) * (C.root * 1)) x at h
  rwa [he] at h

theorem PlacementProblem.circleCosineSlope_hasDerivAt (C : PlacementProblem n) (e : Fin n) (x : ℝ) :
    HasDerivAt (C.circleCosineSlope e) (-(C.root ^ 2) * C.circleCosine e x) x := by
  have h := ((((hasDerivAt_id x).const_mul C.root).sub_const (C.angle e)).sin).const_mul (-C.root)
  have he : -C.root * (Real.cos (C.root * x - C.angle e) * (C.root * 1)) =
      -(C.root ^ 2) * C.circleCosine e x := by unfold circleCosine; ring
  change HasDerivAt (C.circleCosineSlope e)
    (-C.root * (Real.cos (C.root * x - C.angle e) * (C.root * 1))) x at h
  rwa [he] at h

theorem PlacementProblem.circleCosine_positive (C : PlacementProblem n) (e : Fin n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (C.optimalCircleGap e)) : 0 < C.circleCosine e x :=
  Real.cos_pos_of_mem_Ioo (C.circle_phase_mem e hx)

theorem PlacementProblem.circleCosine_start (C : PlacementProblem n) (e : Fin n) :
    C.circleCosine e 0 = Real.cos (C.angle e) := by
  simp [circleCosine, Real.cos_neg]

theorem PlacementProblem.circleCosine_end (C : PlacementProblem n) (e : Fin n) :
    C.circleCosine e (C.optimalCircleGap e) = Real.cos (C.angle (finRotate n e)) := by
  rw [circleCosine, C.circle_gap_phase, add_sub_cancel_left]

theorem PlacementProblem.circleCosineSlope_start (C : PlacementProblem n) (e : Fin n) :
    C.circleCosineSlope e 0 = C.root * Real.sin (C.angle e) := by
  simp [circleCosineSlope, Real.sin_neg]

theorem PlacementProblem.circleCosineSlope_end (C : PlacementProblem n) (e : Fin n) :
    C.circleCosineSlope e (C.optimalCircleGap e) = -C.root * Real.sin (C.angle (finRotate n e)) := by
  rw [circleCosineSlope, C.circle_gap_phase, add_sub_cancel_left]

theorem PlacementProblem.circleCosineEnergy (C : PlacementProblem n) :
    GraphEnergy C.optimalCircle.network.geometry (fun i => Real.cos (C.angle i)) C.circleCosine := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    exact intervalEnergy_of_continuous_derivative (C.optimalCircleGap_pos e).le
      (C.circleCosine_continuous e).continuousOn (C.circleCosineSlope_continuous e).continuousOn
      (fun x _ => C.circleCosine_hasDerivAt e x)
  · intro e
    exact C.circleCosine_start e
  · intro e
    exact C.circleCosine_end e

theorem PlacementProblem.circleCosine_vertex_balance (C : PlacementProblem n) (i : Fin n) :
    C.strength i * Real.cos (C.angle i) = vertexFlux (fun j : Fin n => j) (finRotate n)
      (fun e => C.diffusivity * C.circleCosineSlope e 0)
      (fun e => C.diffusivity * C.circleCosineSlope e (C.optimalCircleGap e)) i := by
  rw [cyclic_vertexFlux, C.circleCosineSlope_start, C.circleCosineSlope_end, Equiv.apply_symm_apply]
  have h := C.angle_reaction i
  linarith

noncomputable def PlacementProblem.circleCosineEigenstate (C : PlacementProblem n) :
    PositiveNetworkEigenstate C.optimalCircle.network (C.diffusivity * C.root ^ 2) where
  nodal := fun i => Real.cos (C.angle i)
  state := C.circleCosine
  slope := C.circleCosineSlope
  energy := C.circleCosineEnergy
  nodal_positive := fun i => Real.cos_pos_of_mem_Ioo
    ⟨by linarith [C.angle_pos i, Real.pi_pos], C.angle_lt i⟩
  positive := fun e _ hx => C.circleCosine_positive e hx
  slope_continuous := fun e => (C.circleCosineSlope_continuous e).continuousOn
  state_derivative := fun e x _ => C.circleCosine_hasDerivAt e x
  slope_derivative := by
    intro e x _
    change HasDerivAt (C.circleCosineSlope e)
      (-(C.diffusivity * C.root ^ 2 / C.diffusivity) * C.circleCosine e x) x
    rw [mul_div_cancel_left₀ _ (ne_of_gt C.diffusivity_pos)]
    exact C.circleCosineSlope_hasDerivAt e x
  vertex_balance := C.circleCosine_vertex_balance

theorem PlacementProblem.optimalCircle_principalValue (C : PlacementProblem n) :
    C.optimalCircle.network.principalValue = C.diffusivity * C.root ^ 2 := by
  let : Nonempty (Fin n) := ⟨⟨0, C.count_pos⟩⟩
  exact C.circleCosineEigenstate.principalValue_eq

end TimeTraps.Spectral
