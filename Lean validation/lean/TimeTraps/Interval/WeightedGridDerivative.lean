module

public import TimeTraps.Interval.WeightedGridPrimitive
public import TimeTraps.Interval.PartitionMove

@[expose] public section

/-! Coordinate derivatives of the actual nearest-node integral objective.
The primitive telescope agrees with that independently defined objective
throughout a neighborhood of every strict grid. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter
open scoped BigOperators Topology

variable {n : ℕ}

noncomputable def weightedGridRawCost (W : CellWeight) (q : Fin (n + 1) → ℝ) : ℝ :=
  weightedCDFPrimitive W 1 1 + ∑ i : Fin n, weightedGridBoundary W (q i.castSucc) (q i.succ)

noncomputable def ClosedPartition.gridCoordinateCost (Q : ClosedPartition n) (W : CellWeight)
    (e : Fin (n + 1)) (c : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..1, W.value z * gridDistance (Function.update Q.point e c) z ^ 2

theorem ClosedPartition.gridCost_raw (Q : ClosedPartition n) (W : CellWeight) :
    Q.gridCost W = weightedGridRawCost W Q.point := by
  let A (e : Fin (n + 1)) := weightedCDFPrimitive W (Q.point e) (Q.canonicalCellNode e.castSucc)
  let B (e : Fin (n + 1)) := weightedCDFPrimitive W (Q.point e) (Q.canonicalCellNode e.succ)
  have hcost : Q.gridCost W = ∑ e : Fin (n + 1), (B e - A e) := by
    rw [Q.gridCost_canonical_integral]
    apply Finset.sum_congr rfl
    intro e _
    exact (weightedCDFPrimitive_sub W _ (Q.canonicalCellNode_mem _)
      (Q.canonicalCellNode_mem _)).symm
  have hsum : (∑ e : Fin (n + 1), (B e - A e)) = B (Fin.last n) - A 0 +
      ∑ i : Fin n, (B i.castSucc - A i.succ) := by
    simp only [Finset.sum_sub_distrib]
    rw [Fin.sum_univ_castSucc B, Fin.sum_univ_succ A]
    ring
  rw [hcost, hsum]
  change weightedCDFPrimitive W (Q.point (Fin.last n)) (Q.canonicalCellNode (Fin.last (n + 1))) -
    weightedCDFPrimitive W (Q.point 0) (Q.canonicalCellNode 0) + _ = _
  simp only [Q.last, Q.canonicalCellNode_last, Q.canonicalCellNode_first,
    weightedCDFPrimitive_zero, sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [A, B]
  rw [Fin.castSucc_succ, Q.canonicalCellNode_site]
  rfl

theorem ClosedPartition.canonicalMidpoint_interior (Q : ClosedPartition n)
    (hQ : StrictMono Q.point) (i : Fin n) : Q.canonicalMidpoint i ∈ Ioo (0 : ℝ) 1 := by
  have h := hQ (Fin.castSucc_lt_succ (i := i))
  have hl := Q.point_mem i.castSucc
  have hr := Q.point_mem i.succ
  unfold canonicalMidpoint
  constructor <;> linarith [hl.1, hr.2]

theorem ClosedPartition.gridCoordinateCost_self (Q : ClosedPartition n) (W : CellWeight)
    (e : Fin (n + 1)) : Q.gridCoordinateCost W e (Q.point e) = Q.gridCost W := by
  simp only [gridCoordinateCost, Function.update_eq_self, gridCost]

theorem ClosedPartition.gridCoordinateCost_move (Q : ClosedPartition (n + 1)) (W : CellWeight)
    (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    Q.gridCoordinateCost W i.castSucc.succ c = (Q.move i c hc).gridCost W := rfl

theorem ClosedPartition.gridRawCost_coordinate_derivative (Q : ClosedPartition (n + 1))
    (W : CellWeight) (hQ : StrictMono Q.point) (i : Fin n) :
    HasDerivAt (fun c => weightedGridRawCost W (Function.update Q.point i.castSucc.succ c))
      (2 * ∫ z in Q.canonicalCellNode i.castSucc.succ.castSucc..
        Q.canonicalCellNode i.castSucc.succ.succ, W.value z * (Q.point i.castSucc.succ - z))
      (Q.point i.castSucc.succ) := by
  classical
  let m := i.castSucc.succ
  let R (k : Fin (n + 1)) :=
    2 * (Q.point m * W.primitive (Q.canonicalMidpoint k) - W.moment (Q.canonicalMidpoint k))
  have hd (e : Fin (n + 2)) : HasDerivAt (fun c => Function.update Q.point m c e)
      (if e = m then 1 else 0) (Q.point m) := by
    by_cases he : e = m
    · subst e
      simp only [Function.update_self, ite_true]
      convert! hasDerivAt_id (Q.point m) using 1
    · simpa only [Function.update_of_ne he, if_neg he] using hasDerivAt_const (Q.point m) (Q.point e)
  have hb (k : Fin (n + 1)) :
      HasDerivAt (fun c => weightedGridBoundary W
        (Function.update Q.point m c k.castSucc) (Function.update Q.point m c k.succ))
        ((if k.castSucc = m then R k else 0) - (if k.succ = m then R k else 0)) (Q.point m) := by
    have hmid : (Function.update Q.point m (Q.point m) k.castSucc +
        Function.update Q.point m (Q.point m) k.succ) / 2 ∈ Ioo (0 : ℝ) 1 := by
      simpa only [Function.update_eq_self, canonicalMidpoint] using Q.canonicalMidpoint_interior hQ k
    have h := weightedGridBoundary_derivative W (hd k.castSucc) (hd k.succ) hmid
    simp only [Function.update_eq_self] at h
    apply h.congr_deriv
    dsimp only [R, canonicalMidpoint]
    split_ifs with hl hr <;> simp_all
  have hs := (HasDerivAt.fun_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin (n + 1)))) => hb k)).const_add
    (weightedCDFPrimitive W 1 1)
  have hl (k : Fin (n + 1)) : k.castSucc = m ↔ k = i.succ := by
    change k.castSucc = i.succ.castSucc ↔ _
    exact Fin.castSucc_inj
  have hr (k : Fin (n + 1)) : k.succ = m ↔ k = i.castSucc := Fin.succ_inj
  have hval : (∑ k : Fin (n + 1),
      ((if k.castSucc = m then R k else 0) - (if k.succ = m then R k else 0))) =
      2 * ∫ z in Q.canonicalCellNode i.castSucc.succ.castSucc..
        Q.canonicalCellNode i.castSucc.succ.succ, W.value z * (Q.point i.castSucc.succ - z) := by
    simp only [hl, hr, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [weightedGridResidual_primitive W _ (Q.canonicalCellNode_mem _) (Q.canonicalCellNode_mem _)]
    rw [Fin.castSucc_succ, Q.canonicalCellNode_site, ← Fin.castSucc_succ (i := i),
      Q.canonicalCellNode_site]
    dsimp only [R, m]
    rw [Fin.castSucc_succ]
    ring
  exact hs.congr_deriv hval

theorem ClosedPartition.gridCoordinateCost_derivative (Q : ClosedPartition (n + 1))
    (W : CellWeight) (hQ : StrictMono Q.point) (i : Fin n) :
    HasDerivAt (Q.gridCoordinateCost W i.castSucc.succ)
      (2 * ∫ z in Q.canonicalCellNode i.castSucc.succ.castSucc..
        Q.canonicalCellNode i.castSucc.succ.succ, W.value z * (Q.point i.castSucc.succ - z))
      (Q.point i.castSucc.succ) := by
  apply (Q.gridRawCost_coordinate_derivative W hQ i).congr_of_eventuallyEq
  have hl : Q.point i.castSucc.castSucc < Q.point i.castSucc.succ :=
    hQ (Fin.castSucc_lt_succ (i := i.castSucc))
  have hr : Q.point i.castSucc.succ < Q.point i.succ.succ := by
    apply hQ
    change i.val + 1 < i.val + 1 + 1
    omega
  filter_upwards [Ioo_mem_nhds hl hr] with c hc
  rw [Q.gridCoordinateCost_move W i c (Ioo_subset_Icc_self hc),
    (Q.move i c (Ioo_subset_Icc_self hc)).gridCost_raw]
  rfl

theorem StrictPartition.gridCoordinateCost_derivative (Q : StrictPartition n) (W : CellWeight)
    (e : Fin (n + 1)) (he0 : 0 < e.val) (hen : e.val < n) :
    HasDerivAt (Q.closed.gridCoordinateCost W e)
      (2 * ∫ z in Q.closed.canonicalCellNode e.castSucc..Q.closed.canonicalCellNode e.succ,
        W.value z * (Q.point e - z)) (Q.point e) := by
  cases n with
  | zero => omega
  | succ m =>
    let i : Fin m := ⟨e.val - 1, by omega⟩
    have he : e = i.castSucc.succ := by
      apply Fin.ext
      change e.val = e.val - 1 + 1
      omega
    rw [he]
    exact Q.closed.gridCoordinateCost_derivative W Q.strictMono i

theorem StrictPartition.gridCoordinateCost_deriv (Q : StrictPartition n) (W : CellWeight)
    (e : Fin (n + 1)) (he0 : 0 < e.val) (hen : e.val < n) :
    deriv (Q.closed.gridCoordinateCost W e) (Q.point e) =
      2 * ∫ z in Q.closed.canonicalCellNode e.castSucc..Q.closed.canonicalCellNode e.succ,
        W.value z * (Q.point e - z) :=
  (Q.gridCoordinateCost_derivative W e he0 hen).deriv

end TimeTraps.Interval
