module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
A finite weighted Laplacian plus nonnegative vertex reaction. Connectivity is
expressed by the equivalence closure of positive-weight adjacency. This is an
independent finite-dimensional foundation: conversion of metric-graph edge
data to these coefficients and weak/strong equivalence remain separate tasks.
-/

namespace TimeTraps.Analysis

open scoped BigOperators

variable {V : Type*} [Fintype V]

/-- The vertex flux-balance operator, defined without assuming a solution. -/
noncomputable def vertexOperator (W : V → V → ℝ) (κ : V → ℝ) :
    (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun x v := κ v * x v + ∑ w, W v w * (x v - x w)
  map_add' x y := by
    ext v
    dsimp
    simp only [add_sub_add_comm, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' a x := by
    ext v
    dsimp
    simp only [← mul_sub, mul_left_comm (W v _) a, ← Finset.mul_sum]
    ring

theorem vertexOperator_apply (W : V → V → ℝ) (κ x : V → ℝ) (v : V) :
    vertexOperator W κ x v = κ v * x v + ∑ w, W v w * (x v - x w) := rfl

/-- Exact finite energy identity; symmetry cancels the oriented cross terms. -/
theorem vertex_energy_identity (W : V → V → ℝ) (κ x : V → ℝ)
    (hW : ∀ v w, W v w = W w v) :
    ∑ v, x v * vertexOperator W κ x v =
      (∑ v, κ v * x v ^ 2) + (1 / 2 : ℝ) *
        ∑ v, ∑ w, W v w * (x v - x w) ^ 2 := by
  have hswap : (∑ v, ∑ w, W v w * x w * (x w - x v)) =
      ∑ v, ∑ w, W v w * x v * (x v - x w) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    rw [hW w v]
  have hsquare : (∑ v, ∑ w, W v w * (x v - x w) ^ 2) =
      2 * ∑ v, ∑ w, W v w * x v * (x v - x w) := by
    calc
      _ = (∑ v, ∑ w, W v w * x v * (x v - x w)) +
          ∑ v, ∑ w, W v w * x w * (x w - x v) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ = _ := by rw [hswap]; ring
  rw [hsquare]
  have hexpand : (∑ v, x v * vertexOperator W κ x v) =
      (∑ v, κ v * x v ^ 2) + ∑ v, ∑ w, W v w * x v * (x v - x w) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [vertexOperator_apply, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro w _
      ring
  rw [hexpand]
  ring

/-- Symmetric internal fluxes cancel in the total source balance. -/
theorem vertex_conservation (W : V → V → ℝ) (κ x load : V → ℝ)
    (hW : ∀ v w, W v w = W w v) (hx : vertexOperator W κ x = load) :
    ∑ v, κ v * x v = ∑ v, load v := by
  have hswap : (∑ v, ∑ w, W v w * (x v - x w)) =
      -(∑ v, ∑ w, W v w * (x v - x w)) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    rw [hW w v]
    ring
  have hzero : (∑ v, ∑ w, W v w * (x v - x w)) = 0 := by linarith
  rw [← hx]
  simp only [vertexOperator_apply, Finset.sum_add_distrib, hzero, add_zero]

/-- A kernel vector is constant on each positive-weight edge and zero at each
reactive vertex. These conclusions follow from energy, not model fields. -/
theorem vertex_kernel_constraints (W : V → V → ℝ) (κ x : V → ℝ)
    (hW : ∀ v w, W v w = W w v) (hWnonneg : ∀ v w, 0 ≤ W v w)
    (hκ : ∀ v, 0 ≤ κ v) (hx : vertexOperator W κ x = 0) :
    (∀ v, 0 < κ v → x v = 0) ∧ (∀ v w, 0 < W v w → x v = x w) := by
  have hr : 0 ≤ ∑ v, κ v * x v ^ 2 :=
    Finset.sum_nonneg fun v _ => mul_nonneg (hκ v) (sq_nonneg _)
  have he : ∀ v w, 0 ≤ W v w * (x v - x w) ^ 2 :=
    fun v w => mul_nonneg (hWnonneg v w) (sq_nonneg _)
  have hE : 0 ≤ ∑ v, ∑ w, W v w * (x v - x w) ^ 2 :=
    Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun w _ => he v w
  have hid := vertex_energy_identity W κ x hW
  rw [hx] at hid
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hid
  have hrzero : (∑ v, κ v * x v ^ 2) = 0 := by linarith
  have hezero : (∑ v, ∑ w, W v w * (x v - x w) ^ 2) = 0 := by linarith
  constructor
  · intro v hv
    have hvzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v _ => mul_nonneg (hκ v) (sq_nonneg (x v)))).mp hrzero v (Finset.mem_univ v)
    have : x v ^ 2 = 0 := (mul_eq_zero.mp hvzero).resolve_left (ne_of_gt hv)
    exact (sq_eq_zero_iff.mp this)
  · intro v w hvw
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v _ => Finset.sum_nonneg fun w _ => he v w)).mp hezero v (Finset.mem_univ v)
    have hentry := (Finset.sum_eq_zero_iff_of_nonneg
      (fun w _ => he v w)).mp hrow w (Finset.mem_univ w)
    have : (x v - x w) ^ 2 = 0 := (mul_eq_zero.mp hentry).resolve_left (ne_of_gt hvw)
    exact sub_eq_zero.mp ((sq_eq_zero_iff.mp this))

theorem vertexOperator_injective (W : V → V → ℝ) (κ : V → ℝ)
    (hW : ∀ v w, W v w = W w v) (hWnonneg : ∀ v w, 0 ≤ W v w)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v)
    (hconnected : ∀ v w, Relation.EqvGen (fun v w => 0 < W v w) v w) :
    Function.Injective (vertexOperator W κ) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨hreact, hedge⟩ := vertex_kernel_constraints W κ x hW hWnonneg hκ hx
  have hconstant : ∀ v w, x v = x w := by
    intro v w
    induction hconnected v w with
    | rel v w hvw => exact hedge v w hvw
    | refl v => rfl
    | symm v w _ ih => exact ih.symm
    | trans v w z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨v, hv⟩ := hanchor
  ext w
  exact (hconstant w v).trans (hreact v hv)

/-- Existence and uniqueness for every load on a finite connected grounded network. -/
theorem vertex_solution_existsUnique (W : V → V → ℝ) (κ load : V → ℝ)
    (hW : ∀ v w, W v w = W w v) (hWnonneg : ∀ v w, 0 ≤ W v w)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v)
    (hconnected : ∀ v w, Relation.EqvGen (fun v w => 0 < W v w) v w) :
    ∃! x, vertexOperator W κ x = load := by
  have hinj := vertexOperator_injective W κ hW hWnonneg hκ hanchor hconnected
  obtain ⟨x, hx⟩ := (LinearMap.surjective_of_injective hinj) load
  exact ⟨x, hx, fun y hy => hinj (hy.trans hx.symm)⟩

/-- Strictly positive loads imply strictly positive vertex values. -/
theorem vertex_solution_pos [Nonempty V] (W : V → V → ℝ) (κ load x : V → ℝ)
    (hW : ∀ v w, 0 ≤ W v w) (hκ : ∀ v, 0 ≤ κ v)
    (hload : ∀ v, 0 < load v) (hx : vertexOperator W κ x = load) :
    ∀ v, 0 < x v := by
  classical
  obtain ⟨v, _, hmin⟩ := Finset.univ.exists_min_image x Finset.univ_nonempty
  have hv : 0 < x v := by
    by_contra h
    have hn : x v ≤ 0 := le_of_not_gt h
    have hsum : (∑ w, W v w * (x v - x w)) ≤ 0 :=
      Finset.sum_nonpos fun w _ => mul_nonpos_of_nonneg_of_nonpos (hW v w)
        (sub_nonpos.mpr (hmin w (Finset.mem_univ w)))
    have hreaction := mul_nonpos_of_nonneg_of_nonpos (hκ v) hn
    have heq := congrFun hx v
    rw [vertexOperator_apply] at heq
    linarith [hload v]
  intro w
  exact lt_of_lt_of_le hv (hmin w (Finset.mem_univ w))

end TimeTraps.Analysis
