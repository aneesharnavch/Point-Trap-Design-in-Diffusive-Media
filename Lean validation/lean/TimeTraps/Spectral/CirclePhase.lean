module

public import TimeTraps.Spectral.NetworkPhase

@[expose] public section

/-! The original reaction law gives phase jumps on the circle. Permutation
reindexing cancels all arc endpoints, including the wrap and one-trap loop. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ} {ev k : ℝ}

theorem cyclic_vertexFlux (n : ℕ) (j₀ j₁ : Fin n → ℝ) (v : Fin n) :
    vertexFlux (fun i : Fin n => i) (finRotate n) j₀ j₁ v =
      j₀ v - j₁ ((finRotate n).symm v) := by
  classical
  unfold vertexFlux incidenceLoad
  simp only [Finset.sum_add_distrib, ← (finRotate n).eq_symm_apply]
  simp [Finset.sum_ite_eq', sub_eq_add_neg]
  rw [Finset.sum_eq_single v]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hv
    exact (hv (Finset.mem_univ v)).elim

variable {C : CircleProblem n}

theorem CircleProblem.logSlope_jump (F : PositiveNetworkEigenstate C.network ev) (i : Fin n) :
    F.logSlope i 0 - F.logSlope ((finRotate n).symm i) (C.gap ((finRotate n).symm i)) =
      C.strength i / C.diffusivity := by
  have hb := F.vertex_balance i
  change C.strength i * F.nodal i = vertexFlux (fun j : Fin n => j) (finRotate n)
    (fun e => C.diffusivity * F.slope e 0) (fun e => C.diffusivity * F.slope e (C.gap e)) i at hb
  rw [cyclic_vertexFlux] at hb
  have ht : F.state i 0 = F.nodal i := F.energy.tail_value i
  have hh : F.state ((finRotate n).symm i) (C.gap ((finRotate n).symm i)) = F.nodal i := by
    simpa only [SpectralNetwork.geometry, CircleProblem.network, Equiv.apply_symm_apply] using
      F.energy.head_value ((finRotate n).symm i)
  unfold PositiveNetworkEigenstate.logSlope
  rw [ht, hh]
  field_simp [ne_of_gt (F.nodal_positive i), ne_of_gt C.diffusivity_pos]
  nlinarith

theorem CircleProblem.phase_tan_jump (F : PositiveNetworkEigenstate C.network ev) (i : Fin n) :
    Real.tan (F.phase k i 0) -
      Real.tan (F.phase k ((finRotate n).symm i) (C.gap ((finRotate n).symm i))) =
      C.strength i / (C.diffusivity * k) := by
  simp only [PositiveNetworkEigenstate.phase, Real.tan_arctan]
  rw [← sub_div, CircleProblem.logSlope_jump F i, div_div]

theorem CircleProblem.phase_jump_sharp (F : PositiveNetworkEigenstate C.network ev) (hk : 0 < k) (i : Fin n) :
    F.phase k i 0 - F.phase k ((finRotate n).symm i) (C.gap ((finRotate n).symm i)) ≤
      2 * Real.arctan (C.strength i / (2 * C.diffusivity * k)) ∧
    (F.phase k i 0 - F.phase k ((finRotate n).symm i) (C.gap ((finRotate n).symm i)) =
      2 * Real.arctan (C.strength i / (2 * C.diffusivity * k)) ↔
      F.phase k i 0 = -F.phase k ((finRotate n).symm i) (C.gap ((finRotate n).symm i))) := by
  have h := sharp_phase_jump (div_pos (C.strength_pos i) (mul_pos C.diffusivity_pos hk))
    (F.phase_branch k ((finRotate n).symm i) (C.gap ((finRotate n).symm i)))
    (F.phase_branch k i 0) (CircleProblem.phase_tan_jump F i)
  have he : C.strength i / (C.diffusivity * k) / 2 = C.strength i / (2 * C.diffusivity * k) := by ring
  rwa [he] at h

theorem CircleProblem.phase_sum (F : PositiveNetworkEigenstate C.network ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / C.diffusivity) :
    k * C.length = ∑ i : Fin n,
      (F.phase k i 0 - F.phase k ((finRotate n).symm i) (C.gap ((finRotate n).symm i))) := by
  have hperm := (finRotate n).symm.sum_comp (fun e => F.phase k e (C.gap e))
  rw [Finset.sum_sub_distrib, hperm, ← Finset.sum_sub_distrib]
  have he (e : Fin n) : F.phase k e 0 - F.phase k e (C.gap e) = k * C.gap e := by
    rw [F.phase_affine hk hk2 e ⟨(C.gap_pos e).le, le_rfl⟩]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, C.gap_sum]

theorem CircleProblem.phase_global_bound (F : PositiveNetworkEigenstate C.network ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / C.diffusivity) :
    C.length * k ≤ 2 * ∑ i, Real.arctan (C.strength i / (2 * C.diffusivity * k)) := by
  rw [mul_comm C.length, CircleProblem.phase_sum F hk hk2, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => (CircleProblem.phase_jump_sharp F hk i).1)

end TimeTraps.Spectral
