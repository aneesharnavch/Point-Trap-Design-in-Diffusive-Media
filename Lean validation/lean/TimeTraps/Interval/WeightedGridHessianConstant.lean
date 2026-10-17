module

public import TimeTraps.Interval.WeightedGridHessian
public import TimeTraps.Analysis.DiscreteDirichletModes

@[expose] public section

/-! The equal-grid residual Jacobian in the weak-heterogeneity calculation.
Its Dirichlet energy is strictly positive on nonzero interior directions,
so the displayed finite first-variation system has a unique solution. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis
open scoped BigOperators

variable {n : ℕ}

noncomputable def weightedGridResidualCurve (W : CellWeight) (q r : Fin (n + 2) → ℝ)
    (i : Fin n) (t : ℝ) : ℝ :=
  weightedGridResidual W (q i.castSucc.castSucc + t * r i.castSucc.castSucc)
    (q i.castSucc.succ + t * r i.castSucc.succ) (q i.succ.succ + t * r i.succ.succ)

theorem weightedGridResidual_uniform_derivative (W : CellWeight) (Ω : ℝ)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω) (r : Fin (n + 2) → ℝ) (i : Fin n) :
    HasDerivAt (weightedGridResidualCurve W (StrictPartition.uniform (n + 1) (Nat.succ_pos n)).point r i)
      (Ω / (4 * ((n : ℝ) + 1)) * discreteSecondDifference r i) 0 := by
  let Q := StrictPartition.uniform (n + 1) (Nat.succ_pos n)
  have hd (e : Fin (n + 2)) : HasDerivAt (fun t => Q.point e + t * r e) (r e) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).mul_const (r e)).const_add (Q.point e) using 1
    simp only [one_mul]
  have hl : (Q.point i.castSucc.castSucc + Q.point i.castSucc.succ) / 2 ∈ Ioo (0 : ℝ) 1 :=
    Q.closed.canonicalMidpoint_interior Q.strictMono i.castSucc
  have hr : (Q.point i.castSucc.succ + Q.point i.succ.succ) / 2 ∈ Ioo (0 : ℝ) 1 := by
    have hmid := Q.closed.canonicalMidpoint_interior Q.strictMono i.succ
    change (Q.point i.succ.castSucc + Q.point i.succ.succ) / 2 ∈ Ioo (0 : ℝ) 1 at hmid
    simpa only [Fin.castSucc_succ] using hmid
  have h := weightedGridResidual_derivative W (hd i.castSucc.castSucc) (hd i.castSucc.succ)
    (hd i.succ.succ) (by simpa only [zero_mul, add_zero] using hl)
      (by simpa only [zero_mul, add_zero] using hr)
  simp only [zero_mul, add_zero] at h
  rw [weightedGridHessianEdge_constant W Ω hW (Ioo_subset_Icc_self hl),
    weightedGridHessianEdge_constant W Ω hW (Ioo_subset_Icc_self hr),
    weightedGridHessianDiagonal_constant W Ω hW (Ioo_subset_Icc_self hl)
      (Ioo_subset_Icc_self hr)] at h
  convert! h using 1
  dsimp only [Q, StrictPartition.uniform, discreteSecondDifference]
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, Fin.castSucc_succ]
  field_simp
  ring

noncomputable def weightedGridUniformJacobian (n : ℕ) (Ω : ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun r i := Ω / (4 * ((n : ℝ) + 1)) * discreteSecondDifference (nodalStrength r) i
  map_add' r s := by
    have he (v : Fin (n + 2)) : nodalStrength (r + s) v = nodalStrength r v + nodalStrength s v := by
      refine Fin.cases ?_ (fun k => ?_) v
      · simp only [nodalStrength_first, add_zero]
      · refine Fin.lastCases ?_ (fun i => ?_) k
        · change nodalStrength _ (Fin.last (n + 1)) =
            nodalStrength r (Fin.last (n + 1)) + nodalStrength s (Fin.last (n + 1))
          simp only [nodalStrength_last, add_zero]
        · change nodalStrength _ (trapNode i) = nodalStrength r (trapNode i) + nodalStrength s (trapNode i)
          simp only [nodalStrength_trap, Pi.add_apply]
    funext i
    simp only [discreteSecondDifference, he, Pi.add_apply]
    ring
  map_smul' c r := by
    have he (v : Fin (n + 2)) : nodalStrength (c • r) v = c * nodalStrength r v := by
      refine Fin.cases ?_ (fun k => ?_) v
      · simp only [nodalStrength_first, mul_zero]
      · refine Fin.lastCases ?_ (fun i => ?_) k
        · change nodalStrength _ (Fin.last (n + 1)) = c * nodalStrength r (Fin.last (n + 1))
          simp only [nodalStrength_last, mul_zero]
        · change nodalStrength _ (trapNode i) = c * nodalStrength r (trapNode i)
          simp only [nodalStrength_trap, Pi.smul_apply, smul_eq_mul]
    funext i
    simp only [discreteSecondDifference, he, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem weightedGridUniformJacobian_energy (Ω : ℝ) (r : Fin n → ℝ) :
    (∑ i, r i * weightedGridUniformJacobian n Ω r i) =
      Ω / (4 * ((n : ℝ) + 1)) *
        ∑ e : Fin (n + 1), (nodalStrength r e.succ - nodalStrength r e.castSucc) ^ 2 := by
  rw [discrete_dirichlet_energy_second_difference (nodalStrength r)
    (nodalStrength_first r) (nodalStrength_last r), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.castSucc_succ]
  change r i * (Ω / (4 * ((n : ℝ) + 1)) * discreteSecondDifference (nodalStrength r) i) =
    Ω / (4 * ((n : ℝ) + 1)) * (nodalStrength r (trapNode i) * discreteSecondDifference (nodalStrength r) i)
  rw [nodalStrength_trap]
  ring

theorem weightedGrid_nodal_energy_zero (r : Fin n → ℝ)
    (h : (∑ e : Fin (n + 1), (nodalStrength r e.succ - nodalStrength r e.castSucc) ^ 2) = 0) :
    r = 0 := by
  have hs (e : Fin (n + 1)) : nodalStrength r e.succ = nodalStrength r e.castSucc := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun e (_ : e ∈ (Finset.univ : Finset (Fin (n + 1)))) => sq_nonneg
        (nodalStrength r e.succ - nodalStrength r e.castSucc))).mp h e (Finset.mem_univ e)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  have hv (v : Fin (n + 2)) : nodalStrength r v = 0 := by
    induction v using Fin.induction with
    | zero => exact nodalStrength_first r
    | succ i ih => rw [hs i]; exact ih
  funext i
  exact (nodalStrength_trap r i).symm.trans (hv (trapNode i))

theorem weightedGridUniformJacobian_positive (Ω : ℝ) (hΩ : 0 < Ω) (r : Fin n → ℝ) (hr : r ≠ 0) :
    0 < ∑ i, r i * weightedGridUniformJacobian n Ω r i := by
  rw [weightedGridUniformJacobian_energy]
  apply mul_pos (div_pos hΩ (by positivity))
  apply lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact Ne.symm (fun hz => hr (weightedGrid_nodal_energy_zero r hz))

theorem weightedGridUniformJacobian_bijective (Ω : ℝ) (hΩ : 0 < Ω) :
    Function.Bijective (weightedGridUniformJacobian n Ω) := by
  have hinj : Function.Injective (weightedGridUniformJacobian n Ω) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro r hr
    by_contra hne
    have hp := weightedGridUniformJacobian_positive Ω hΩ r hne
    simp only [hr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, lt_self_iff_false] at hp
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

noncomputable def weightedGridUniformJacobianEquiv (n : ℕ) (Ω : ℝ) (hΩ : 0 < Ω) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  LinearEquiv.ofBijective (weightedGridUniformJacobian n Ω) (weightedGridUniformJacobian_bijective Ω hΩ)

theorem weightedGrid_first_variation_unique (B : Fin n → ℝ) :
    ∃! r : Fin n → ℝ, ∀ i,
      discreteSecondDifference (nodalStrength r) i = -4 * ((n : ℝ) + 1) * B i := by
  obtain ⟨r, hr⟩ := (weightedGridUniformJacobian_bijective (n := n) 1 zero_lt_one).2 (-B)
  have hc : (4 * ((n : ℝ) + 1)) ≠ 0 := by positivity
  have he (s : Fin n → ℝ) :
      (∀ i, discreteSecondDifference (nodalStrength s) i = -4 * ((n : ℝ) + 1) * B i) ↔
        weightedGridUniformJacobian n 1 s = -B := by
    constructor
    · intro hs
      funext i
      change (1 / (4 * ((n : ℝ) + 1))) * discreteSecondDifference (nodalStrength s) i = -B i
      rw [hs i]
      field_simp
    · intro hs i
      have hi := congrFun hs i
      change (1 / (4 * ((n : ℝ) + 1))) * discreteSecondDifference (nodalStrength s) i = -B i at hi
      field_simp at hi
      nlinarith
  refine ⟨r, (he r).mpr hr, ?_⟩
  intro s hs
  exact (weightedGridUniformJacobian_bijective (n := n) 1 zero_lt_one).1 ((he s).mp hs |>.trans hr.symm)

end TimeTraps.Interval
