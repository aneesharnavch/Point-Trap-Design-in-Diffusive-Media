module

public import TimeTraps.Interval.EndpointAttainment

@[expose] public section

/-! Saturation of the actual mixed budget bound forces every cell loss,
ordinary balanced site, and permitted outer boundary height. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis
open scoped BigOperators

variable {A : EndpointArchitecture} {K : ℝ}

theorem EndpointWeakEquation.mixed_budget_equality_loss {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (hb : budget Finset.univ (R.activeShare D w) (A.barrier hw.partition.closed D.medium.cellWeight)
      (D.essentialNorm w) = K / D.source.mass) (i : Fin A.count) :
    D.essentialNorm w - w (A.physicalSite D i) = A.barrier hw.partition.closed D.medium.cellWeight i := by
  let δ : Fin A.count → ℝ := fun k => R.activeStrength k / D.source.mass -
    R.activeShare D w k / (D.essentialNorm w - A.barrier hw.partition.closed D.medium.cellWeight k)
  have hn : ∀ k, 0 ≤ δ k := fun k => sub_nonneg.mpr (hw.mixed_cell_budget_le_strength k)
  have hs : (∑ k, δ k) = 0 := by
    change (∑ k, (R.activeStrength k / D.source.mass -
      R.activeShare D w k / (D.essentialNorm w - A.barrier hw.partition.closed D.medium.cellWeight k))) = 0
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, R.activeStrength_sum]
    change K / D.source.mass - budget Finset.univ (R.activeShare D w)
      (A.barrier hw.partition.closed D.medium.cellWeight) (D.essentialNorm w) = 0
    rw [hb, sub_self]
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hn k)).mp hs i (Finset.mem_univ i)
  have he : R.activeStrength i / D.source.mass = R.activeShare D w i /
      (D.essentialNorm w - A.barrier hw.partition.closed D.medium.cellWeight i) := sub_eq_zero.mp hi
  unfold EndpointReactions.activeShare at he
  field_simp [ne_of_gt D.source.mass_pos,
    ne_of_gt (sub_pos.mpr (hw.mixed_barrier_lt_norm i))] at he
  have hl := mul_left_cancel₀ (ne_of_gt (R.activeStrength_pos i)) he
  linarith

theorem EndpointWeakEquation.mixed_height_equality_ordinary {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (i : Fin A.count) (hi : A.kind i = .ordinary)
    (hloss : D.essentialNorm w - w (A.physicalSite D i) = A.barrier hw.partition.closed D.medium.cellWeight i) :
    A.sourceSite D i = hw.partition.center D.medium.cellWeight i ∧
      D.source.transformed w (hw.partition.point i.castSucc) = D.essentialNorm w ∧
      D.source.transformed w (hw.partition.point i.succ) = D.essentialNorm w := by
  have h := D.medium.cellWeight.height_comparison
    (hw.partition.point_mem i.castSucc).1 (hw.partition.point_mem i.succ).2
    (hw.partition.strictMono (Fin.castSucc_lt_succ (i := i))) (A.sourceSite_mem D i)
    (hw.transformed_le_norm _) (hw.transformed_le_norm _)
    (hw.active_leftRise_bound i) (hw.active_rightRise_bound i)
  apply h.2
  rw [A.barrier_ordinary hw.partition.closed D.medium.cellWeight i hi] at hloss
  exact hloss

theorem EndpointWeakEquation.mixed_height_equality_left {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (i : Fin A.count) (hi : A.kind i = .leftEndpoint)
    (hloss : D.essentialNorm w - w (A.physicalSite D i) = A.barrier hw.partition.closed D.medium.cellWeight i) :
    D.source.transformed w (hw.partition.point i.succ) = D.essentialNorm w := by
  have he : i.castSucc = 0 := Fin.ext ((A.kind_left_iff i).mp hi).2
  have hc := A.sourceSite_left D i hi
  have hb := hw.active_rightRise_bound i (by rw [hc]; exact (hw.partition.point_mem i.succ).1)
  have hm := hw.transformed_le_norm (hw.partition.point i.succ)
  change _ = D.medium.cellWeight.orientedBarrier (A.kind i)
    (hw.partition.point i.castSucc) (hw.partition.point i.succ) at hloss
  simp only [CellWeight.orientedBarrier, hi, he, hw.partition.first] at hloss
  rw [hc] at hb
  linarith

theorem EndpointWeakEquation.mixed_height_equality_right {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (i : Fin A.count) (hi : A.kind i = .rightEndpoint)
    (hloss : D.essentialNorm w - w (A.physicalSite D i) = A.barrier hw.partition.closed D.medium.cellWeight i) :
    D.source.transformed w (hw.partition.point i.castSucc) = D.essentialNorm w := by
  have he : i.succ = Fin.last A.count := Fin.ext ((A.kind_right_iff i).mp hi).2
  have hc := A.sourceSite_right D i hi
  have hb := hw.active_leftRise_bound i (by rw [hc]; exact (hw.partition.point_mem i.castSucc).2)
  have hm := hw.transformed_le_norm (hw.partition.point i.castSucc)
  change _ = D.medium.cellWeight.orientedBarrier (A.kind i)
    (hw.partition.point i.castSucc) (hw.partition.point i.succ) at hloss
  simp only [CellWeight.orientedBarrier, hi, he, hw.partition.last] at hloss
  rw [hc] at hb
  linarith

theorem EndpointWeakEquation.mixed_budget_equality_sites {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (hb : budget Finset.univ (R.activeShare D w) (A.barrier hw.partition.closed D.medium.cellWeight)
      (D.essentialNorm w) = K / D.source.mass) (i : Fin A.count) :
    A.sourceSite D i = A.reconstructionSite hw.partition D.medium.cellWeight i := by
  cases hi : A.kind i with
  | ordinary =>
    rw [A.reconstructionSite_ordinary _ _ _ hi]
    exact (hw.mixed_height_equality_ordinary i hi (hw.mixed_budget_equality_loss hb i)).1
  | leftEndpoint =>
    simp only [EndpointArchitecture.reconstructionSite, hi]
    exact A.sourceSite_left D i hi
  | rightEndpoint =>
    simp only [EndpointArchitecture.reconstructionSite, hi]
    exact A.sourceSite_right D i hi

theorem EndpointWeakEquation.mixed_budget_equality_strength {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (hb : budget Finset.univ (R.activeShare D w) (A.barrier hw.partition.closed D.medium.cellWeight)
      (D.essentialNorm w) = K / D.source.mass) (i : Fin A.count) :
    R.activeStrength i = D.medium.endpointPartitionStrength A hw.partition (D.essentialNorm w) i := by
  have hl := hw.mixed_budget_equality_loss hb i
  have he : D.essentialNorm w - A.barrier hw.partition.closed D.medium.cellWeight i =
      w (A.physicalSite D i) := by linarith
  unfold IntervalMedium.endpointPartitionStrength
  change R.activeStrength i = D.source.mass * hw.partition.closed.width i /
    (D.essentialNorm w - A.barrier hw.partition.closed D.medium.cellWeight i)
  rw [hw.partition_width, he]
  unfold EndpointReactions.activeShare
  have hp := hw.positive _ (A.physicalSite_mem D i)
  field_simp [ne_of_gt hp, ne_of_gt D.source.mass_pos]

theorem EndpointWeakEquation.mixed_budget_equality_anchor {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (hb : budget Finset.univ (R.activeShare D w) (A.barrier hw.partition.closed D.medium.cellWeight)
      (D.essentialNorm w) = K / D.source.mass) :
    D.source.transformed w (hw.partition.point (A.gapBoundary 0)) = D.essentialNorm w := by
  let i : Fin A.count := ⟨0, A.count_pos⟩
  have hloss := hw.mixed_budget_equality_loss hb i
  cases hi : A.kind i with
  | ordinary =>
    have hv := ((A.kind_ordinary_iff i).mp hi).1
    have he : i.castSucc = A.gapBoundary 0 := by
      apply Fin.ext
      change A.leftReactive.toNat ≤ 0 at hv
      change 0 = A.leftReactive.toNat + 0
      omega
    rw [← he]
    exact (hw.mixed_height_equality_ordinary i hi hloss).2.1
  | leftEndpoint =>
    rw [← A.gapBoundary_left i hi]
    exact hw.mixed_height_equality_left i hi hloss
  | rightEndpoint =>
    have he := A.gapBoundary_right i hi
    have hv := ((A.kind_right_iff i).mp hi).2
    have hr := ((A.kind_right_iff i).mp hi).1
    have hm : A.interiorCount = 0 := by
      simp only [i, EndpointArchitecture.count, hr, Bool.toNat_true] at hv
      omega
    have hlast : (Fin.last A.interiorCount : Fin (A.interiorCount + 1)) = 0 := Fin.ext hm
    rw [hlast] at he
    rw [← he]
    exact hw.mixed_height_equality_right i hi hloss

end TimeTraps.Interval
