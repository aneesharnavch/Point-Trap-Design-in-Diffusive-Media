module

public import TimeTraps.Interval.SourceMeanPullbackOptimality
public import TimeTraps.Interval.WeightedGridConstant

@[expose] public section

/-! Constant transformed resistance: the actual physical mean minimum and
the complete, equally weighted source-quantile optimizer. -/

namespace TimeTraps.Interval

open Set MeasureTheory

variable {n : ℕ} {A : IntervalMedium} {K C : ℝ}

theorem weightedCDFMidpoint_uniform (hn : 0 < n) (i : Fin n) :
    weightedCDFMidpoint (StrictPartition.uniform n hn).width i =
      (2 * (i.val : ℝ) + 1) / (2 * (n : ℝ)) := by
  rw [weightedCDFMidpoint_width, StrictPartition.uniform_point,
    StrictPartition.uniform_point]
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

theorem source_mean_constant_grid_minimizes (hn : 0 < n) (hC : 0 < C)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, A.cellWeight.value z = C) :
    ∀ P : ClosedPartition n,
      (StrictPartition.uniform n hn).closed.gridCost A.cellWeight ≤ P.gridCost A.cellWeight := by
  intro P
  rw [StrictPartition.uniform_gridCost_constant A.cellWeight hn hC hW]
  exact P.constant_grid_lower A.cellWeight hC.le hW

theorem source_mean_constant_minimum (hn : 0 < n) (hK : 0 < K) (hC : 0 < C)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, A.cellWeight.value z = C) :
    IsLeast (range (fun E : IntervalDesign A n K => E.sourceMeanCost))
      (A.source.mass / K + C / (12 * (n : ℝ) ^ 2)) := by
  have h := source_mean_minimum hK (StrictPartition.uniform n hn)
    (source_mean_constant_grid_minimizes hn hC hW)
  rwa [StrictPartition.uniform_gridCost_constant A.cellWeight hn hC hW] at h

theorem IntervalDesign.sourceMeanCost_eq_of_parameters (E F : IntervalDesign A n K)
    (hs : ∀ i, E.geometry.site i = F.geometry.site i) (hk : E.strength = F.strength) :
    E.sourceMeanCost = F.sourceMeanCost := by
  have hu := E.state_eqOn_of_parameters F hs hk
  unfold IntervalDesign.sourceMeanCost
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [hu (by simpa only [uIcc_of_le A.source.increasing.le] using hx)]

theorem source_mean_constant_reconstruction (hn : 0 < n) (hK : 0 < K) (hC : 0 < C)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, A.cellWeight.value z = C) :
    ∃ E : IntervalDesign A n K,
      (∀ i, E.strength i = K / (n : ℝ)) ∧
      (∀ i, E.geometry.site i = A.source.inverse ((2 * (i.val : ℝ) + 1) / (2 * (n : ℝ)))) ∧
      E.sourceMeanCost = A.source.mass / K + C / (12 * (n : ℝ) ^ 2) := by
  let Q := StrictPartition.uniform n hn
  have hm := source_mean_constant_grid_minimizes (A := A) hn hC hW
  refine ⟨sourceMeanDesign A Q K hK hm, ?_, ?_, ?_⟩
  · intro i
    rw [sourceMeanDesign_strength, StrictPartition.uniform_width]
    ring
  · intro i
    rw [sourceMeanDesign_site, weightedCDFMidpoint_uniform]
  · rw [sourceMeanDesign_mean, StrictPartition.uniform_gridCost_constant A.cellWeight hn hC hW]

theorem source_mean_constant_optimal_iff (hK : 0 < K) (hC : 0 < C)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, A.cellWeight.value z = C) (E : IntervalDesign A n K) :
    E.SourceMeanOptimal ↔
      (∀ i, E.strength i = K / (n : ℝ)) ∧
      (∀ i, E.geometry.site i = A.source.inverse ((2 * (i.val : ℝ) + 1) / (2 * (n : ℝ)))) := by
  constructor
  · intro hE
    obtain ⟨hk, hx, hg⟩ := (source_mean_optimal_iff hK E).mp hE
    have hq := (E.partition.closed.constant_grid_minimizer_iff A.cellWeight hC hW).mp hg
    have hw : ∀ i, E.partition.width i = 1 / (n : ℝ) := by
      intro i
      change E.partition.closed.width i = _
      rw [hq]
      exact StrictPartition.uniform_width E.partition.size_pos i
    have hp := E.partition.eq_uniform_of_width E.partition.size_pos hw
    constructor
    · intro i
      rw [hk i, hw i]
      ring
    · intro i
      rw [hx i, hp, weightedCDFMidpoint_uniform]
  · rintro ⟨hk, hx⟩
    obtain ⟨F, hFk, hFx, hFc⟩ := source_mean_constant_reconstruction E.partition.size_pos hK hC hW
    have he : E.sourceMeanCost = F.sourceMeanCost := E.sourceMeanCost_eq_of_parameters F
      (fun i => (hx i).trans (hFx i).symm) (funext (fun i => (hk i).trans (hFk i).symm))
    intro G
    rw [he, hFc]
    exact (source_mean_constant_minimum E.partition.size_pos hK hC hW).2 ⟨G, rfl⟩

theorem source_mean_constant_eq_iff (hK : 0 < K) (hC : 0 < C)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, A.cellWeight.value z = C) (E : IntervalDesign A n K) :
    E.sourceMeanCost = A.source.mass / K + C / (12 * (n : ℝ) ^ 2) ↔
      (∀ i, E.strength i = K / (n : ℝ)) ∧
      (∀ i, E.geometry.site i = A.source.inverse ((2 * (i.val : ℝ) + 1) / (2 * (n : ℝ)))) := by
  rw [← source_mean_constant_optimal_iff hK hC hW E]
  have h := source_mean_optimal_iff_cost_eq hK (StrictPartition.uniform n E.partition.size_pos)
    (source_mean_constant_grid_minimizes E.partition.size_pos hC hW) E
  rw [StrictPartition.uniform_gridCost_constant A.cellWeight E.partition.size_pos hC hW] at h
  exact h.symm

end TimeTraps.Interval
