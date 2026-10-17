module

public import TimeTraps.Interval.SourceMeanEnergy
public import TimeTraps.Interval.CDFDeficit
public import TimeTraps.Interval.WeightedGridCells

@[expose] public section

/-!
Exact source-weighted physical mean deficit. Strength, transformed-position,
and nearest-grid losses are separately nonnegative at a minimizing grid.
The equality statement is expressed in physical inverse-source coordinates.
Neither stochastic identification nor optimizer attainment is assumed here.
-/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped BigOperators

variable {n : ℕ} {A : IntervalMedium} {K : ℝ}

theorem source_mean_grid_deficit (hK : 0 < K) (E : IntervalDesign A n K) (Q : ClosedPartition n) :
    E.sourceMeanCost - (A.source.mass / K + Q.gridCost A.cellWeight) =
      A.source.mass * meanStrengthLoss K E.strength E.partition.width +
      2 * (∑ i : Fin n, E.partition.width i *
        ∫ t in weightedCDFMidpoint E.partition.width i..E.geometry.sourceSite i,
          A.cellWeight.value t * (t - weightedCDFMidpoint E.partition.width i)) +
      (E.partition.closed.gridCost A.cellWeight - Q.gridCost A.cellWeight) := by
  rw [source_mean_energy, E.partition.gridCost_eq_weightedCDFScore,
    weightedCDFScore_position_identity _ E.partition _ E.sourceSite_mem,
    meanStrengthLoss_identity E.strength E.partition.width (ne_of_gt hK)
      (fun i => ne_of_gt (E.strength_pos i)) E.strength_sum E.partition.width_sum]
  ring

theorem source_mean_grid_lower_bound (hK : 0 < K) (E : IntervalDesign A n K) (Q : ClosedPartition n)
    (hmin : ∀ P : ClosedPartition n, Q.gridCost A.cellWeight ≤ P.gridCost A.cellWeight) :
    A.source.mass / K + Q.gridCost A.cellWeight ≤ E.sourceMeanCost := by
  have he := source_mean_grid_deficit hK E Q
  have hs := mul_nonneg A.source.mass_pos.le
    (meanStrengthLoss_nonneg K E.strength E.partition.width E.strength_pos)
  have hp : 0 ≤ 2 * ∑ i : Fin n, E.partition.width i *
      ∫ t in weightedCDFMidpoint E.partition.width i..E.geometry.sourceSite i,
        A.cellWeight.value t * (t - weightedCDFMidpoint E.partition.width i) :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (E.partition.width_pos i).le (weightedCDF_oriented_nonneg _
        (weightedCDFMidpoint_mem E.partition i) (E.sourceSite_mem i))))
  have hg := hmin E.partition.closed
  linarith

theorem source_mean_position_eq_iff (E : IntervalDesign A n K) :
    (∀ i, E.geometry.sourceSite i = weightedCDFMidpoint E.partition.width i) ↔
      ∀ i, E.geometry.site i = A.source.inverse (weightedCDFMidpoint E.partition.width i) := by
  constructor
  · intro h i
    have hi := congrArg A.source.inverse (h i)
    rw [E.sourceSite_eq, A.source.inverse_coordinate] at hi
    · exact hi
    · rw [← E.source_eq]
      exact Ioo_subset_Icc_self (E.geometry.site_interior i)
  · intro h i
    rw [E.sourceSite_eq, h i, A.source.coordinate_inverse (weightedCDFMidpoint_mem E.partition i)]

theorem source_mean_grid_eq_iff (hK : 0 < K) (E : IntervalDesign A n K) (Q : ClosedPartition n)
    (hmin : ∀ P : ClosedPartition n, Q.gridCost A.cellWeight ≤ P.gridCost A.cellWeight) :
    E.sourceMeanCost = A.source.mass / K + Q.gridCost A.cellWeight ↔
      (∀ i, E.partition.width i = E.strength i / K) ∧
      (∀ i, E.geometry.site i = A.source.inverse (weightedCDFMidpoint E.partition.width i)) ∧
      E.partition.closed.gridCost A.cellWeight = Q.gridCost A.cellWeight := by
  rw [← source_mean_position_eq_iff E]
  have he := source_mean_energy E
  have hs := meanStrengthLoss_identity E.strength E.partition.width (ne_of_gt hK)
    (fun i => ne_of_gt (E.strength_pos i)) E.strength_sum E.partition.width_sum
  have hscaled : A.source.mass * meanStrengthLoss K E.strength E.partition.width =
      A.source.mass * (∑ i, E.partition.width i ^ 2 / E.strength i) - A.source.mass / K := by
    rw [hs]
    ring
  have hsn := mul_nonneg A.source.mass_pos.le
    (meanStrengthLoss_nonneg K E.strength E.partition.width E.strength_pos)
  have hpn := weightedCDFScore_canonical_le A.cellWeight E.partition E.geometry.sourceSite E.sourceSite_mem
  have hg := hmin E.partition.closed
  have hbridge := E.partition.gridCost_eq_weightedCDFScore A.cellWeight
  constructor
  · intro hcost
    have hs0 : A.source.mass * meanStrengthLoss K E.strength E.partition.width = 0 := by linarith
    have hloss : meanStrengthLoss K E.strength E.partition.width = 0 :=
      (mul_eq_zero.mp hs0).resolve_left (ne_of_gt A.source.mass_pos)
    have hp0 : weightedCDFScore A.cellWeight E.partition.width E.geometry.sourceSite =
        weightedCDFScore A.cellWeight E.partition.width (weightedCDFMidpoint E.partition.width) := by linarith
    refine ⟨(meanStrengthLoss_eq_zero_iff K E.strength E.partition.width E.strength_pos).mp hloss,
      (weightedCDFScore_eq_canonical_iff _ E.partition _ E.sourceSite_mem).mp hp0, ?_⟩
    linarith
  · rintro ⟨hstrength, hposition, hgrid⟩
    have hs0 := (meanStrengthLoss_eq_zero_iff K E.strength E.partition.width E.strength_pos).mpr hstrength
    have hp0 := (weightedCDFScore_eq_canonical_iff A.cellWeight E.partition E.geometry.sourceSite
      E.sourceSite_mem).mpr hposition
    rw [hs0, mul_zero] at hscaled
    linarith

end TimeTraps.Interval
