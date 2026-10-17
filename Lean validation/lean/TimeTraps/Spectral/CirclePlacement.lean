module

public import TimeTraps.Spectral.CirclePrincipal
public import TimeTraps.Spectral.PlacementGeometry

@[expose] public section

/-! Independently admissible positive cyclic gaps and the candidate gaps fixed
by the prescribed capacity root. Their sum is exactly the circumference. -/

namespace TimeTraps.Spectral

open Set
open scoped BigOperators

variable {n : ℕ}

def PlacementProblem.AdmissibleCircle (C : PlacementProblem n) (g : Fin n → ℝ) : Prop :=
  (∀ i, 0 < g i) ∧ (∑ i, g i) = C.length

def PlacementProblem.circle (C : PlacementProblem n) (g : Fin n → ℝ) (hg : C.AdmissibleCircle g) :
    CircleProblem n where
  count_pos := C.count_pos
  length := C.length
  length_pos := C.length_pos
  diffusivity := C.diffusivity
  diffusivity_pos := C.diffusivity_pos
  gap := g
  gap_pos := hg.1
  gap_sum := hg.2
  strength := C.strength
  strength_pos := C.strength_pos

theorem PlacementProblem.circle_prescribed (C : PlacementProblem n) (g : Fin n → ℝ)
    (hg : C.AdmissibleCircle g) : (C.circle g hg).prescribed = C := rfl

noncomputable def PlacementProblem.optimalCircleGap (C : PlacementProblem n) (i : Fin n) : ℝ :=
  (C.angle i + C.angle (finRotate n i)) / C.root

theorem PlacementProblem.optimalCircleGap_pos (C : PlacementProblem n) (i : Fin n) :
    0 < C.optimalCircleGap i :=
  div_pos (add_pos (C.angle_pos i) (C.angle_pos _)) C.root_pos

theorem PlacementProblem.optimalCircleGap_cells (C : PlacementProblem n) (i : Fin n) :
    C.optimalCircleGap i = (C.cellLength i + C.cellLength (finRotate n i)) / 2 := by
  unfold optimalCircleGap cellLength
  ring

theorem PlacementProblem.optimalCircleGap_sum (C : PlacementProblem n) :
    (∑ i, C.optimalCircleGap i) = C.length := by
  unfold optimalCircleGap
  rw [← Finset.sum_div, Finset.sum_add_distrib, Equiv.sum_comp (finRotate n) C.angle]
  have he : (∑ i, C.angle i) + (∑ i, C.angle i) = C.length * C.root := by
    have h := C.root_equation
    change C.length * C.root = 2 * ∑ i, C.angle i at h
    linarith
  rw [he, mul_div_cancel_right₀ _ (ne_of_gt C.root_pos)]

theorem PlacementProblem.optimalCircleGap_admissible (C : PlacementProblem n) :
    C.AdmissibleCircle C.optimalCircleGap :=
  ⟨C.optimalCircleGap_pos, C.optimalCircleGap_sum⟩

noncomputable def PlacementProblem.optimalCircle (C : PlacementProblem n) : CircleProblem n :=
  C.circle C.optimalCircleGap C.optimalCircleGap_admissible

theorem PlacementProblem.circle_gap_phase (C : PlacementProblem n) (i : Fin n) :
    C.root * C.optimalCircleGap i = C.angle i + C.angle (finRotate n i) := by
  rw [optimalCircleGap, mul_div_cancel₀ _ (ne_of_gt C.root_pos)]

theorem PlacementProblem.circle_phase_mem (C : PlacementProblem n) (i : Fin n) {x : ℝ}
    (hx : x ∈ Icc 0 (C.optimalCircleGap i)) :
    C.root * x - C.angle i ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have hlo : 0 ≤ C.root * x := mul_nonneg C.root_pos.le hx.1
  have hhi : C.root * x ≤ C.root * C.optimalCircleGap i :=
    mul_le_mul_of_nonneg_left hx.2 C.root_pos.le
  rw [C.circle_gap_phase] at hhi
  constructor <;> linarith [C.angle_lt i, C.angle_lt (finRotate n i)]

theorem PlacementProblem.arbitrary_circle_upper_bound (C : PlacementProblem n)
    (g : Fin n → ℝ) (hg : C.AdmissibleCircle g) :
    (C.circle g hg).network.principalValue ≤ C.diffusivity * C.root ^ 2 :=
  (C.circle g hg).principalValue_le_root

end TimeTraps.Spectral
