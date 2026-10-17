module

public import TimeTraps.Interval.WeightedGridAssignment
public import TimeTraps.Interval.WeightedGridMinimum
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! Necessary Lloyd equations for the actual globally minimizing weighted
grid. A fixed-cell upper comparison supplies the variational argument; no
optimality or uniqueness is inferred from the centroid equations alone. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter
open scoped BigOperators Topology

variable {n : ℕ}

theorem weighted_quadratic_cost_difference (W : CellWeight) (q c : ℝ) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ z in a..b, W.value z * (c - z) ^ 2) -
      (∫ z in a..b, W.value z * (q - z) ^ 2) =
      (c - q) * ((c + q) * (∫ z in a..b, W.value z) - 2 * ∫ z in a..b, z * W.value z) := by
  have hw : IntervalIntegrable W.value volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply W.continuous.mono
    intro z hz
    exact ⟨(le_min ha.1 hb.1).trans hz.1, hz.2.trans (max_le ha.2 hb.2)⟩
  have hm : IntervalIntegrable (fun z => z * W.value z) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_id.mul W.continuous).mono
    intro z hz
    exact ⟨(le_min ha.1 hb.1).trans hz.1, hz.2.trans (max_le ha.2 hb.2)⟩
  rw [← intervalIntegral.integral_sub (weightedCDF_integrable W c ha hb)
    (weightedCDF_integrable W q ha hb)]
  calc
    _ = ∫ z in a..b, (c - q) * ((c + q) * W.value z - 2 * (z * W.value z)) := by
      apply intervalIntegral.integral_congr
      intro z _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (hw.const_mul _) (hm.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem weighted_quadratic_stationary {A B q l r : ℝ} (hq : q ∈ Ioo l r)
    (h : ∀ c ∈ Icc l r, 0 ≤ (c - q) * ((c + q) * A - 2 * B)) : q * A = B := by
  let f : ℝ → ℝ := fun c => (c - q) * ((c + q) * A - 2 * B)
  have hm : IsLocalMin f q := by
    change ∀ᶠ c in 𝓝 q, f q ≤ f c
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with c hc
    simpa only [f, sub_self, zero_mul] using h c (Ioo_subset_Icc_self hc)
  have hd0 := ((hasDerivAt_id q).sub_const q).mul
    ((((hasDerivAt_id q).add_const q).mul_const A).sub_const (2 * B))
  have hd : HasDerivAt f (2 * (q * A - B)) q := by
    exact hd0.congr_deriv (by dsimp; ring)
  have hz := hm.hasDerivAt_eq_zero hd
  linarith

theorem ClosedPartition.canonicalInteriorCell_strict (Q : ClosedPartition (n + 1))
    (hQ : StrictMono Q.point) (i : Fin n) :
    Q.point i.castSucc.succ ∈ Ioo
      (Q.canonicalCellNode i.castSucc.succ.castSucc)
      (Q.canonicalCellNode i.castSucc.succ.succ) := by
  have hl := hQ (Fin.castSucc_lt_succ (i := i.castSucc))
  have hr : Q.point i.castSucc.succ < Q.point i.succ.succ := by
    apply hQ
    change i.val + 1 < i.val + 1 + 1
    omega
  have hleft : Q.canonicalCellNode i.castSucc.succ.castSucc =
      (Q.point i.castSucc.castSucc + Q.point i.castSucc.succ) / 2 := by
    rw [Fin.castSucc_succ, Q.canonicalCellNode_site]
    rfl
  have hright : Q.canonicalCellNode i.castSucc.succ.succ =
      (Q.point i.castSucc.succ + Q.point i.succ.succ) / 2 := by
    rw [← Fin.castSucc_succ, Q.canonicalCellNode_site]
    simp only [canonicalMidpoint, Fin.castSucc_succ]
  rw [hleft, hright]
  constructor <;> linarith

theorem ClosedPartition.grid_centroid_moment (Q : ClosedPartition (n + 1)) (W : CellWeight)
    (hmin : ∀ P : ClosedPartition (n + 1), Q.gridCost W ≤ P.gridCost W) (i : Fin n) :
    Q.point i.castSucc.succ *
        (∫ z in Q.canonicalCellNode i.castSucc.succ.castSucc..
          Q.canonicalCellNode i.castSucc.succ.succ, W.value z) =
      ∫ z in Q.canonicalCellNode i.castSucc.succ.castSucc..
        Q.canonicalCellNode i.castSucc.succ.succ, z * W.value z := by
  have hQ := Q.grid_minimizer_strict W hmin
  have hq : Q.point i.castSucc.succ ∈
      Ioo (Q.point i.castSucc.castSucc) (Q.point i.succ.succ) := by
    constructor
    · exact hQ (Fin.castSucc_lt_succ (i := i.castSucc))
    · apply hQ
      change i.val + 1 < i.val + 1 + 1
      omega
  apply weighted_quadratic_stationary hq
  intro c hc
  have hm := (hmin (Q.move i c hc)).trans (Q.gridCost_le_assigned (Q.move i c hc) W)
  have hd := sub_nonneg.mpr hm
  rw [Q.assignedGridCost_move_difference W i c hc,
    weighted_quadratic_cost_difference W _ _ (Q.canonicalCellNode_mem _)
      (Q.canonicalCellNode_mem _)] at hd
  exact hd

theorem ClosedPartition.grid_centroid_mass_pos (Q : ClosedPartition (n + 1)) (W : CellWeight)
    (hmin : ∀ P : ClosedPartition (n + 1), Q.gridCost W ≤ P.gridCost W) (i : Fin n) :
    0 < ∫ z in Q.canonicalCellNode i.castSucc.succ.castSucc..
      Q.canonicalCellNode i.castSucc.succ.succ, W.value z := by
  have hq := Q.canonicalInteriorCell_strict (Q.grid_minimizer_strict W hmin) i
  have ha := Q.canonicalCellNode_mem i.castSucc.succ.castSucc
  have hb := Q.canonicalCellNode_mem i.castSucc.succ.succ
  have hab := hq.1.trans hq.2
  apply intervalIntegral.integral_pos hab (W.continuous.mono (Icc_subset_Icc ha.1 hb.2))
  · intro z hz
    exact (W.positive z ⟨ha.1.trans hz.1.le, hz.2.trans hb.2⟩).le
  · exact ⟨_, ⟨le_rfl, hab.le⟩, W.positive _ ha⟩

theorem ClosedPartition.grid_centroid (Q : ClosedPartition (n + 1)) (W : CellWeight)
    (hmin : ∀ P : ClosedPartition (n + 1), Q.gridCost W ≤ P.gridCost W) (i : Fin n) :
    Q.point i.castSucc.succ =
      (∫ z in Q.canonicalCellNode i.castSucc.succ.castSucc..
        Q.canonicalCellNode i.castSucc.succ.succ, z * W.value z) /
      (∫ z in Q.canonicalCellNode i.castSucc.succ.castSucc..
        Q.canonicalCellNode i.castSucc.succ.succ, W.value z) :=
  (eq_div_iff (ne_of_gt (Q.grid_centroid_mass_pos W hmin i))).mpr
    (Q.grid_centroid_moment W hmin i)

theorem ClosedPartition.grid_centroid_residual (Q : ClosedPartition (n + 1)) (W : CellWeight)
    (hmin : ∀ P : ClosedPartition (n + 1), Q.gridCost W ≤ P.gridCost W) (i : Fin n) :
    (∫ z in Q.canonicalCellNode i.castSucc.succ.castSucc..
      Q.canonicalCellNode i.castSucc.succ.succ,
      W.value z * (Q.point i.castSucc.succ - z)) = 0 := by
  let a := Q.canonicalCellNode i.castSucc.succ.castSucc
  let b := Q.canonicalCellNode i.castSucc.succ.succ
  have ha := Q.canonicalCellNode_mem i.castSucc.succ.castSucc
  have hb := Q.canonicalCellNode_mem i.castSucc.succ.succ
  have hw : IntervalIntegrable W.value volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply W.continuous.mono
    intro z hz
    exact ⟨(le_min ha.1 hb.1).trans hz.1, hz.2.trans (max_le ha.2 hb.2)⟩
  have hm : IntervalIntegrable (fun z => z * W.value z) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_id.mul W.continuous).mono
    intro z hz
    exact ⟨(le_min ha.1 hb.1).trans hz.1, hz.2.trans (max_le ha.2 hb.2)⟩
  calc
    _ = ∫ z in a..b, (Q.point i.castSucc.succ * W.value z - z * W.value z) := by
      apply intervalIntegral.integral_congr
      intro z _
      ring
    _ = Q.point i.castSucc.succ * (∫ z in a..b, W.value z) -
        ∫ z in a..b, z * W.value z := by
      rw [intervalIntegral.integral_sub (hw.const_mul _) hm,
        intervalIntegral.integral_const_mul]
    _ = 0 := sub_eq_zero.mpr (Q.grid_centroid_moment W hmin i)

theorem StrictPartition.grid_centroid_residual (Q : StrictPartition n) (W : CellWeight)
    (hmin : ∀ P : ClosedPartition n, Q.closed.gridCost W ≤ P.gridCost W)
    (e : Fin (n + 1)) (he0 : 0 < e.val) (hen : e.val < n) :
    (∫ z in Q.closed.canonicalCellNode e.castSucc..Q.closed.canonicalCellNode e.succ,
      W.value z * (Q.point e - z)) = 0 := by
  cases n with
  | zero => omega
  | succ m =>
    let i : Fin m := ⟨e.val - 1, by omega⟩
    have he : e = i.castSucc.succ := by
      apply Fin.ext
      change e.val = e.val - 1 + 1
      omega
    rw [he]
    exact Q.closed.grid_centroid_residual W hmin i

end TimeTraps.Interval
