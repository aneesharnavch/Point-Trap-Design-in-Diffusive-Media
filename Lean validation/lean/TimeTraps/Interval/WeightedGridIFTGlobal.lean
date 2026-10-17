module

public import TimeTraps.Interval.WeightedGridIFTVariation
public import TimeTraps.Interval.WeightedGridPerturbationFamily
public import TimeTraps.Interval.WeightedGridCentroid

@[expose] public section

/-! Identification of every global minimizer of the independently defined
nearest-node integral with the local implicit-function branch. -/

namespace TimeTraps.Interval

open Set Filter MeasureTheory
open scoped Topology ContDiff

variable {n : ℕ}

def ClosedPartition.gridIFTCoordinates (Q : ClosedPartition (n + 1)) (i : Fin n) : ℝ :=
  Q.point i.castSucc.succ

theorem ClosedPartition.gridIFTCoordinates_nodes (Q : ClosedPartition (n + 1)) :
    cdfNode Q.gridIFTCoordinates = Q.point := by
  funext v
  refine Fin.cases ?_ (fun k => ?_) v
  · rw [cdfNode_first, Q.first]
  · refine Fin.lastCases ?_ (fun i => ?_) k
    · change cdfNode Q.gridIFTCoordinates (Fin.last (n + 1)) = Q.point (Fin.last (n + 1))
      rw [cdfNode_last, Q.last]
    · rw [cdfNode_site]
      rfl

theorem ClosedPartition.gridIFTCoordinates_injective :
    Function.Injective (gridIFTCoordinates (n := n)) := by
  intro Q P h
  apply Subtype.ext
  exact Q.gridIFTCoordinates_nodes.symm.trans ((congrArg cdfNode h).trans P.gridIFTCoordinates_nodes)

theorem ClosedPartition.gridIFTCoordinates_continuous :
    Continuous (gridIFTCoordinates (n := n)) := by
  apply continuous_pi
  intro i
  exact (continuous_apply i.castSucc.succ).comp continuous_subtype_val

theorem ClosedPartition.gridIFTCoordinates_uniform :
    (StrictPartition.uniform (n + 1) (Nat.succ_pos n)).closed.gridIFTCoordinates =
      gridIFTBaseline n := by
  funext i
  simp [gridIFTCoordinates, ClosedPartition.point, StrictPartition.closed,
    StrictPartition.uniform, gridIFTBaseline, Nat.cast_add, Nat.cast_one]

theorem ClosedPartition.gridIFTCoordinates_cells (Q : ClosedPartition (n + 1)) (i : Fin n) :
    gridIFTLeft Q.gridIFTCoordinates i = Q.canonicalCellNode i.castSucc.succ.castSucc ∧
    gridIFTRight Q.gridIFTCoordinates i = Q.canonicalCellNode i.castSucc.succ.succ := by
  constructor
  · rw [Fin.castSucc_succ, Q.canonicalCellNode_site]
    simp only [gridIFTLeft, Q.gridIFTCoordinates_nodes, gridIFTCoordinates,
      ClosedPartition.canonicalMidpoint]
  · rw [← Fin.castSucc_succ, Q.canonicalCellNode_site]
    simp only [gridIFTRight, Q.gridIFTCoordinates_nodes, gridIFTCoordinates,
      ClosedPartition.canonicalMidpoint, Fin.succ_castSucc]

theorem ClosedPartition.gridIFTResidual_minimizer (Q : ClosedPartition (n + 1))
    (W : CellWeight) (h : ℝ → ℝ) (hh : ContinuousOn h (Icc (0 : ℝ) 1)) (Ω ε : ℝ)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω * (1 + ε * h z))
    (hmin : ∀ P : ClosedPartition (n + 1), Q.gridCost W ≤ P.gridCost W) :
    gridIFTResidual h Ω (ε, Q.gridIFTCoordinates) = 0 := by
  funext i
  obtain ⟨hl, hr⟩ := Q.gridIFTCoordinates_cells i
  rw [gridIFTResidual_eq_integral h hh Ω ε Q.gridIFTCoordinates i
    (hl.symm ▸ Q.canonicalCellNode_mem _) (hr.symm ▸ Q.canonicalCellNode_mem _), hl, hr]
  change (∫ z in Q.canonicalCellNode i.castSucc.succ.castSucc..
    Q.canonicalCellNode i.castSucc.succ.succ,
    Ω * (1 + ε * h z) * (Q.point i.castSucc.succ - z)) = 0
  rw [← Q.grid_centroid_residual W hmin i]
  apply intervalIntegral.integral_congr
  intro z hz
  have ha := Q.canonicalCellNode_mem i.castSucc.succ.castSucc
  have hb := Q.canonicalCellNode_mem i.castSucc.succ.succ
  have hz' : z ∈ Icc (0 : ℝ) 1 :=
    ⟨(le_min ha.1 hb.1).trans hz.1, hz.2.trans (max_le ha.2 hb.2)⟩
  dsimp only
  rw [hW z hz']

theorem gridIFTBranch_all_minimizers (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, |ε| < η → ∀ W : CellWeight,
      (∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω * (1 + ε * h z)) →
      ∀ Q : ClosedPartition (n + 1),
      (∀ P : ClosedPartition (n + 1), Q.gridCost W ≤ P.gridCost W) →
      Q.gridIFTCoordinates = gridIFTBranch h hh Ω hΩ ε := by
  obtain ⟨u, v, hu, h0u, hv, h0v, huv⟩ := mem_nhds_prod_iff'.mp
    (gridIFTBranch_local_unique (n := n) h hh Ω hΩ)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds h0u)
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn hh.continuousOn
  let V : CellWeight := ⟨fun _ => Ω, continuousOn_const, fun _ _ => hΩ⟩
  obtain ⟨η, hη, hnear⟩ := weighted_grid_affine_minimizers_near_uniform V
    (Nat.succ_pos n) hΩ (fun _ _ => rfl) (fun x hx => by simpa only [Real.norm_eq_abs] using hH x hx)
    (ClosedPartition.gridIFTCoordinates ⁻¹' v)
    (hv.preimage ClosedPartition.gridIFTCoordinates_continuous)
    (by simpa only [mem_preimage, ClosedPartition.gridIFTCoordinates_uniform] using h0v)
  refine ⟨min r η, lt_min hr hη, ?_⟩
  intro ε hε W hW Q hmin
  have hεu : ε ∈ u := hru (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
    (lt_of_lt_of_le hε (min_le_left r η)))
  have hQv : Q.gridIFTCoordinates ∈ v := hnear ε
    (lt_of_lt_of_le hε (min_le_right r η)) W hW Q hmin
  exact ((huv ⟨hεu, hQv⟩).mp (Q.gridIFTResidual_minimizer W h hh.continuousOn Ω ε hW hmin)).symm

theorem gridIFTBranch_global_unique (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, |ε| < η → ∀ W : CellWeight,
      (∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω * (1 + ε * h z)) →
      ∃! Q : ClosedPartition (n + 1),
        ∀ P : ClosedPartition (n + 1), Q.gridCost W ≤ P.gridCost W := by
  obtain ⟨η, hη, hall⟩ := gridIFTBranch_all_minimizers (n := n) h hh Ω hΩ
  refine ⟨η, hη, ?_⟩
  intro ε hε W hW
  obtain ⟨Q, hQ⟩ := ClosedPartition.grid_minimum_exists W (Nat.succ_pos n)
  refine ⟨Q, hQ, ?_⟩
  intro P hP
  apply ClosedPartition.gridIFTCoordinates_injective
  exact (hall ε hε W hW P hP).trans (hall ε hε W hW Q hQ).symm

end TimeTraps.Interval
