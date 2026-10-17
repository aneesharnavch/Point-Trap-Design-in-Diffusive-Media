module

public import TimeTraps.Interval.WeightedGridSecond

@[expose] public section

/-! The Hessian is the derivative of the actual objective's coordinate
derivatives. Interior coordinates are indexed by Fin n; the grid has n + 2
nodes including the two fixed endpoints. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter
open scoped Topology

variable {n : ℕ}

noncomputable def weightedGridGradient (W : CellWeight) (q : Fin (n + 2) → ℝ) (i : Fin n) : ℝ :=
  2 * weightedGridResidual W (q i.castSucc.castSucc) (q i.castSucc.succ) (q i.succ.succ)

noncomputable def weightedGridPartial (W : CellWeight) (q : Fin (n + 2) → ℝ) (i : Fin n) : ℝ :=
  deriv (fun c => ∫ z in (0 : ℝ)..1,
    W.value z * gridDistance (Function.update q i.castSucc.succ c) z ^ 2) (q i.castSucc.succ)

noncomputable def weightedGridHessian (W : CellWeight) (q : Fin (n + 2) → ℝ)
    (i j : Fin n) : ℝ :=
  weightedGridHessianEdge W (q i.castSucc.castSucc) (q i.castSucc.succ) *
      (if i.castSucc.castSucc = j.castSucc.succ then 1 else 0) +
    weightedGridHessianDiagonal W (q i.castSucc.castSucc) (q i.castSucc.succ) (q i.succ.succ) *
      (if i.castSucc.succ = j.castSucc.succ then 1 else 0) +
    weightedGridHessianEdge W (q i.castSucc.succ) (q i.succ.succ) *
      (if i.succ.succ = j.castSucc.succ then 1 else 0)

theorem weightedGridUpdate_derivative (q : Fin (n + 2) → ℝ) (i j : Fin (n + 2)) :
    HasDerivAt (fun c => Function.update q j c i) (if i = j then 1 else 0) (q j) := by
  classical
  by_cases h : i = j
  · subst i
    simp only [Function.update_self, ite_true]
    convert! hasDerivAt_id (q j) using 1
  · simpa only [Function.update_of_ne h, if_neg h] using hasDerivAt_const (q j) (q i)

theorem ClosedPartition.weightedGridPartial_eq (Q : ClosedPartition (n + 1))
    (W : CellWeight) (hQ : StrictMono Q.point) (i : Fin n) :
    weightedGridPartial W Q.point i = weightedGridGradient W Q.point i := by
  have hd := (Q.gridCoordinateCost_derivative W hQ i).deriv
  change weightedGridPartial W Q.point i = _ at hd
  rw [hd]
  unfold weightedGridGradient weightedGridResidual
  rw [Fin.castSucc_succ, Q.canonicalCellNode_site, ← Fin.castSucc_succ (i := i),
    Q.canonicalCellNode_site]
  simp only [ClosedPartition.canonicalMidpoint, Fin.castSucc_succ]

theorem ClosedPartition.move_strict (Q : ClosedPartition (n + 1)) (hQ : StrictMono Q.point)
    (i : Fin n) (c : ℝ) (hc : c ∈ Ioo (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    StrictMono (Q.move i c (Ioo_subset_Icc_self hc)).point := by
  apply (Q.move i c (Ioo_subset_Icc_self hc)).strict_iff_width_pos.mpr
  intro k
  by_cases hl : k = i.castSucc
  · subst k
    rw [Q.move_width_left]
    exact sub_pos.mpr hc.1
  by_cases hr : k = i.succ
  · subst k
    rw [Q.move_width_right]
    exact sub_pos.mpr hc.2
  have h₀ : k.castSucc ≠ i.castSucc.succ := by
    intro he
    apply hr
    have hv : k.val = i.val + 1 := congrArg Fin.val he
    exact Fin.ext hv
  have h₁ : k.succ ≠ i.castSucc.succ := fun he => hl (Fin.succ_injective _ he)
  change 0 < (Q.move i c (Ioo_subset_Icc_self hc)).point k.succ -
    (Q.move i c (Ioo_subset_Icc_self hc)).point k.castSucc
  rw [Q.move_other i c (Ioo_subset_Icc_self hc) k.succ h₁,
    Q.move_other i c (Ioo_subset_Icc_self hc) k.castSucc h₀]
  exact sub_pos.mpr (hQ Fin.castSucc_lt_succ)

theorem ClosedPartition.weightedGridGradient_derivative (Q : ClosedPartition (n + 1))
    (W : CellWeight) (hQ : StrictMono Q.point) (i j : Fin n) :
    HasDerivAt (fun c => weightedGridGradient W (Function.update Q.point j.castSucc.succ c) i)
      (weightedGridHessian W Q.point i j) (Q.point j.castSucc.succ) := by
  have hl : (Function.update Q.point j.castSucc.succ (Q.point j.castSucc.succ) i.castSucc.castSucc +
      Function.update Q.point j.castSucc.succ (Q.point j.castSucc.succ) i.castSucc.succ) / 2 ∈ Ioo (0 : ℝ) 1 := by
    simpa only [Function.update_eq_self, ClosedPartition.canonicalMidpoint]
      using Q.canonicalMidpoint_interior hQ i.castSucc
  have hr : (Function.update Q.point j.castSucc.succ (Q.point j.castSucc.succ) i.castSucc.succ +
      Function.update Q.point j.castSucc.succ (Q.point j.castSucc.succ) i.succ.succ) / 2 ∈ Ioo (0 : ℝ) 1 := by
    simpa only [Function.update_eq_self, ClosedPartition.canonicalMidpoint, Fin.castSucc_succ]
      using Q.canonicalMidpoint_interior hQ i.succ
  have h := weightedGridGradientCell_derivative W
    (weightedGridUpdate_derivative Q.point i.castSucc.castSucc j.castSucc.succ)
    (weightedGridUpdate_derivative Q.point i.castSucc.succ j.castSucc.succ)
    (weightedGridUpdate_derivative Q.point i.succ.succ j.castSucc.succ) hl hr
  simpa only [Function.update_eq_self, weightedGridGradient, weightedGridHessian] using h

theorem ClosedPartition.weightedGridPartial_derivative (Q : ClosedPartition (n + 1))
    (W : CellWeight) (hQ : StrictMono Q.point) (i j : Fin n) :
    HasDerivAt (fun c => weightedGridPartial W (Function.update Q.point j.castSucc.succ c) i)
      (weightedGridHessian W Q.point i j) (Q.point j.castSucc.succ) := by
  apply (Q.weightedGridGradient_derivative W hQ i j).congr_of_eventuallyEq
  have hl : Q.point j.castSucc.castSucc < Q.point j.castSucc.succ :=
    hQ (Fin.castSucc_lt_succ (i := j.castSucc))
  have hr : Q.point j.castSucc.succ < Q.point j.succ.succ := by
    apply hQ
    change j.val + 1 < j.val + 1 + 1
    omega
  filter_upwards [Ioo_mem_nhds hl hr] with c hc
  exact (Q.move j c (Ioo_subset_Icc_self hc)).weightedGridPartial_eq W (Q.move_strict hQ j c hc) i

theorem ClosedPartition.weightedGridPartial_deriv (Q : ClosedPartition (n + 1))
    (W : CellWeight) (hQ : StrictMono Q.point) (i j : Fin n) :
    deriv (fun c => weightedGridPartial W (Function.update Q.point j.castSucc.succ c) i)
      (Q.point j.castSucc.succ) = weightedGridHessian W Q.point i j :=
  (Q.weightedGridPartial_derivative W hQ i j).deriv

theorem weightedGridHessian_diagonal (W : CellWeight) (q : Fin (n + 2) → ℝ) (i : Fin n) :
    weightedGridHessian W q i i =
      weightedGridHessianDiagonal W (q i.castSucc.castSucc) (q i.castSucc.succ) (q i.succ.succ) := by
  have hl : i.castSucc.castSucc ≠ i.castSucc.succ := ne_of_lt Fin.castSucc_lt_succ
  have hr : i.succ.succ ≠ i.castSucc.succ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at this
    omega
  simp only [weightedGridHessian, if_neg hl, if_neg hr, ite_true, mul_zero, mul_one, zero_add, add_zero]

theorem weightedGridHessian_left (W : CellWeight) (q : Fin (n + 2) → ℝ) (i j : Fin n)
    (h : j.val + 1 = i.val) : weightedGridHessian W q i j =
      weightedGridHessianEdge W (q i.castSucc.castSucc) (q i.castSucc.succ) := by
  have hl : i.castSucc.castSucc = j.castSucc.succ := Fin.ext h.symm
  have hm : i.castSucc.succ ≠ j.castSucc.succ := by
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_succ, Fin.val_castSucc] at this
    omega
  have hr : i.succ.succ ≠ j.castSucc.succ := by
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_succ, Fin.val_castSucc] at this
    omega
  simp only [weightedGridHessian, if_pos hl, if_neg hm, if_neg hr, mul_one, mul_zero, add_zero]

theorem weightedGridHessian_right (W : CellWeight) (q : Fin (n + 2) → ℝ) (i j : Fin n)
    (h : i.val + 1 = j.val) : weightedGridHessian W q i j =
      weightedGridHessianEdge W (q i.castSucc.succ) (q i.succ.succ) := by
  have hl : i.castSucc.castSucc ≠ j.castSucc.succ := by
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_succ, Fin.val_castSucc] at this
    omega
  have hm : i.castSucc.succ ≠ j.castSucc.succ := by
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_succ, Fin.val_castSucc] at this
    omega
  have hr : i.succ.succ = j.castSucc.succ := Fin.ext (by simpa using congrArg Nat.succ h)
  simp only [weightedGridHessian, if_neg hl, if_neg hm, if_pos hr, mul_one, mul_zero, zero_add]

theorem weightedGridHessian_off_band (W : CellWeight) (q : Fin (n + 2) → ℝ) (i j : Fin n)
    (h0 : i ≠ j) (hl : j.val + 1 ≠ i.val) (hr : i.val + 1 ≠ j.val) :
    weightedGridHessian W q i j = 0 := by
  have hl' : i.castSucc.castSucc ≠ j.castSucc.succ := fun h => hl (congrArg Fin.val h).symm
  have hm' : i.castSucc.succ ≠ j.castSucc.succ := fun h => h0 (Fin.ext (by
    have := congrArg Fin.val h
    simpa only [Fin.val_succ, Fin.val_castSucc, Nat.add_right_cancel_iff] using this))
  have hr' : i.succ.succ ≠ j.castSucc.succ := by
    intro h
    apply hr
    have := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at this
    omega
  simp only [weightedGridHessian, if_neg hl', if_neg hm', if_neg hr', mul_zero, add_zero]

theorem weightedGridHessian_symmetric (W : CellWeight) (q : Fin (n + 2) → ℝ) (i j : Fin n) :
    weightedGridHessian W q i j = weightedGridHessian W q j i := by
  by_cases h0 : i = j
  · subst j
    rfl
  by_cases hl : j.val + 1 = i.val
  · rw [weightedGridHessian_left W q i j hl, weightedGridHessian_right W q j i hl]
    have h₁ : i.castSucc.castSucc = j.castSucc.succ := Fin.ext hl.symm
    have h₂ : i.castSucc.succ = j.succ.succ := Fin.ext (by simpa using congrArg Nat.succ hl.symm)
    rw [h₁, h₂]
  by_cases hr : i.val + 1 = j.val
  · rw [weightedGridHessian_right W q i j hr, weightedGridHessian_left W q j i hr]
    have h₁ : i.castSucc.succ = j.castSucc.castSucc := Fin.ext hr
    have h₂ : i.succ.succ = j.castSucc.succ := Fin.ext (by simpa using congrArg Nat.succ hr)
    rw [h₁, h₂]
  rw [weightedGridHessian_off_band W q i j h0 hl hr,
    weightedGridHessian_off_band W q j i (Ne.symm h0) hr hl]

end TimeTraps.Interval
