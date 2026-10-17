module

public import TimeTraps.Spectral.CirclePhaseEquality
public import TimeTraps.Spectral.NetworkWavenumber
public import TimeTraps.Spectral.PlacementProblem

@[expose] public section

/-! The periodic phase bound bounds the independent principal value by the
unique capacity root determined only by length, diffusivity and strengths. -/

namespace TimeTraps.Spectral

open Set
open scoped BigOperators

variable {n : ℕ}

def CircleProblem.prescribed (C : CircleProblem n) : PlacementProblem n where
  count_pos := C.count_pos
  length := C.length
  length_pos := C.length_pos
  diffusivity := C.diffusivity
  diffusivity_pos := C.diffusivity_pos
  strength := C.strength
  strength_pos := C.strength_pos

theorem CircleProblem.principal_phase_bound (C : CircleProblem n) :
    C.length * C.network.principalWavenumber ≤
      2 * ∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * C.network.principalWavenumber)) := by
  let : Nonempty (Fin n) := ⟨⟨0, C.count_pos⟩⟩
  obtain ⟨F⟩ := C.network.principal_eigenstate_exists
  exact phase_global_bound F C.network.principalWavenumber_pos C.network.principalWavenumber_sq

theorem CircleProblem.principalWavenumber_le_root (C : CircleProblem n) :
    C.network.principalWavenumber ≤ C.prescribed.root := by
  let : Nonempty (Fin n) := ⟨⟨0, C.count_pos⟩⟩
  have hc (k : ℝ) : phaseCapacity Finset.univ (fun i => C.strength i / (2 * C.diffusivity)) k =
      2 * ∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * k)) := by
    simp only [phaseCapacity, div_div, Finset.mul_sum]
  exact le_capacity_root Finset.univ Finset.univ_nonempty (fun i => C.strength i / (2 * C.diffusivity))
    (fun i _ => div_pos (C.strength_pos i) (mul_pos (by norm_num) C.diffusivity_pos))
    C.length_pos C.network.principalWavenumber_pos C.prescribed.root_pos
    (by rw [hc]; exact C.prescribed.root_equation) (by rw [hc]; exact C.principal_phase_bound)

theorem CircleProblem.principalValue_le_root (C : CircleProblem n) :
    C.network.principalValue ≤ C.diffusivity * C.prescribed.root ^ 2 := by
  let : Nonempty (Fin n) := ⟨⟨0, C.count_pos⟩⟩
  rw [C.network.principalValue_formula]
  have h := C.principalWavenumber_le_root
  have hs : C.network.principalWavenumber ^ 2 ≤ C.prescribed.root ^ 2 := by
    nlinarith [C.network.principalWavenumber_pos]
  exact mul_le_mul_of_nonneg_left hs C.diffusivity_pos.le

end TimeTraps.Spectral
