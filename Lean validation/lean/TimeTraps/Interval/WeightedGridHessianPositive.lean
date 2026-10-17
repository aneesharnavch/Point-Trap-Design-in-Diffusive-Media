module

public import TimeTraps.Interval.WeightedGridHessianConstant

@[expose] public section

/-! At constant weight and the equal grid, the actual Hessian acts as twice
the residual Jacobian. Its positive quadratic form is the scaled Dirichlet
energy. This does not assert convexity for arbitrary heterogeneous weights. -/

namespace TimeTraps.Interval

open Set
open scoped BigOperators

variable {n : ℕ}

theorem weightedGrid_nodal_sum (r : Fin n → ℝ) (v : Fin (n + 2)) :
    (∑ j : Fin n, (if v = j.castSucc.succ then (1 : ℝ) else 0) * r j) = nodalStrength r v := by
  classical
  refine Fin.cases ?_ (fun k => ?_) v
  · have hz (j : Fin n) : (0 : Fin (n + 2)) ≠ j.castSucc.succ := Ne.symm (Fin.succ_ne_zero _)
    simp only [hz, if_false, zero_mul, Finset.sum_const_zero, nodalStrength_first]
  · refine Fin.lastCases ?_ (fun i => ?_) k
    · change (∑ j : Fin n, (if (Fin.last n).succ = j.castSucc.succ then (1 : ℝ) else 0) * r j) =
        nodalStrength r (Fin.last (n + 1))
      have hn (j : Fin n) : Fin.last n ≠ j.castSucc := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_last, Fin.val_castSucc] at hv
        omega
      simp only [Fin.succ_inj, hn, if_false, zero_mul, Finset.sum_const_zero, nodalStrength_last]
    · change (∑ j : Fin n, (if i.castSucc.succ = j.castSucc.succ then (1 : ℝ) else 0) * r j) =
        nodalStrength r (trapNode i)
      simp only [Fin.succ_inj, Fin.castSucc_inj, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, nodalStrength_trap]

theorem weightedGridHessian_action (W : CellWeight) (q : Fin (n + 2) → ℝ) (r : Fin n → ℝ) (i : Fin n) :
    (∑ j, weightedGridHessian W q i j * r j) =
      weightedGridHessianEdge W (q i.castSucc.castSucc) (q i.castSucc.succ) * nodalStrength r i.castSucc.castSucc +
        weightedGridHessianDiagonal W (q i.castSucc.castSucc) (q i.castSucc.succ) (q i.succ.succ) * r i +
        weightedGridHessianEdge W (q i.castSucc.succ) (q i.succ.succ) * nodalStrength r i.succ.succ := by
  simp only [weightedGridHessian, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
    weightedGrid_nodal_sum]
  rw [show nodalStrength r i.castSucc.succ = r i from nodalStrength_trap r i]

theorem weightedGridHessian_uniform_action (W : CellWeight) (Ω : ℝ)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω) (r : Fin n → ℝ) (i : Fin n) :
    (∑ j, weightedGridHessian W (StrictPartition.uniform (n + 1) (Nat.succ_pos n)).point i j * r j) =
      2 * weightedGridUniformJacobian n Ω r i := by
  let Q := StrictPartition.uniform (n + 1) (Nat.succ_pos n)
  have hl : (Q.point i.castSucc.castSucc + Q.point i.castSucc.succ) / 2 ∈ Icc (0 : ℝ) 1 :=
    Ioo_subset_Icc_self (Q.closed.canonicalMidpoint_interior Q.strictMono i.castSucc)
  have hr : (Q.point i.castSucc.succ + Q.point i.succ.succ) / 2 ∈ Icc (0 : ℝ) 1 := by
    have hm := Q.closed.canonicalMidpoint_interior Q.strictMono i.succ
    change (Q.point i.succ.castSucc + Q.point i.succ.succ) / 2 ∈ Ioo (0 : ℝ) 1 at hm
    simpa only [Fin.castSucc_succ] using Ioo_subset_Icc_self hm
  rw [weightedGridHessian_action]
  change weightedGridHessianEdge W (Q.point i.castSucc.castSucc) (Q.point i.castSucc.succ) *
      nodalStrength r i.castSucc.castSucc +
      weightedGridHessianDiagonal W (Q.point i.castSucc.castSucc) (Q.point i.castSucc.succ) (Q.point i.succ.succ) * r i +
      weightedGridHessianEdge W (Q.point i.castSucc.succ) (Q.point i.succ.succ) * nodalStrength r i.succ.succ = _
  rw [weightedGridHessianEdge_constant W Ω hW hl, weightedGridHessianEdge_constant W Ω hW hr,
    weightedGridHessianDiagonal_constant W Ω hW hl hr]
  change _ = 2 * (Ω / (4 * ((n : ℝ) + 1)) * TimeTraps.Analysis.discreteSecondDifference (nodalStrength r) i)
  simp only [TimeTraps.Analysis.discreteSecondDifference, Fin.castSucc_succ,
    show nodalStrength r i.castSucc.succ = r i from nodalStrength_trap r i]
  dsimp only [Q, StrictPartition.uniform]
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem weightedGridHessian_uniform_energy (W : CellWeight) (Ω : ℝ)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω) (r : Fin n → ℝ) :
    (∑ i, r i * ∑ j,
      weightedGridHessian W (StrictPartition.uniform (n + 1) (Nat.succ_pos n)).point i j * r j) =
      Ω / (2 * ((n : ℝ) + 1)) *
        ∑ e : Fin (n + 1), (nodalStrength r e.succ - nodalStrength r e.castSucc) ^ 2 := by
  simp_rw [weightedGridHessian_uniform_action W Ω hW]
  have hsum : (∑ i, r i * (2 * weightedGridUniformJacobian n Ω r i)) =
      2 * ∑ i, r i * weightedGridUniformJacobian n Ω r i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, weightedGridUniformJacobian_energy]
  field_simp
  ring

theorem weightedGridHessian_uniform_positive (W : CellWeight) (Ω : ℝ) (hΩ : 0 < Ω)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω) (r : Fin n → ℝ) (hr : r ≠ 0) :
    0 < ∑ i, r i * ∑ j,
      weightedGridHessian W (StrictPartition.uniform (n + 1) (Nat.succ_pos n)).point i j * r j := by
  rw [weightedGridHessian_uniform_energy W Ω hW]
  apply mul_pos (div_pos hΩ (by positivity))
  apply lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact Ne.symm (fun hz => hr (weightedGrid_nodal_energy_zero r hz))

end TimeTraps.Interval
