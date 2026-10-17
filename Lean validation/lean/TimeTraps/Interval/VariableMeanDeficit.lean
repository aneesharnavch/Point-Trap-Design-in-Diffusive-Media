module

public import TimeTraps.Interval.VariableMeanEnergy
public import TimeTraps.Interval.WeightedGridCells

@[expose] public section

/-!
The three exact losses for the actual mean: strength mismatch, displacement
from cumulative-share midpoints, and excess nearest-grid energy. The last
term is nonnegative whenever the comparison grid minimizes the independently
defined weighted nearest-node integral.
-/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped BigOperators

variable {n : ℕ} {K : ℝ} {a : ℝ → ℝ}
  {ha : ContinuousOn a (Icc (0 : ℝ) 1)} {hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x}

theorem variable_mean_grid_deficit (hK : 0 < K)
    (E : IntervalDesign (variableUnitMedium a ha hapos) n K) (Q : ClosedPartition n) :
    E.meanCost - (1 / K + Q.gridCost (variableMeanWeight a ha hapos)) =
      meanStrengthLoss K E.strength E.partition.width +
      2 * (∑ i : Fin n, E.partition.width i *
        ∫ t in weightedCDFMidpoint E.partition.width i..E.geometry.site i,
          (variableMeanWeight a ha hapos).value t * (t - weightedCDFMidpoint E.partition.width i)) +
      (E.partition.closed.gridCost (variableMeanWeight a ha hapos) -
        Q.gridCost (variableMeanWeight a ha hapos)) := by
  rw [E.partition.gridCost_eq_weightedCDFScore]
  have he := variable_mean_canonical_deficit hK E
  linarith

theorem variable_mean_grid_lower_bound (hK : 0 < K)
    (E : IntervalDesign (variableUnitMedium a ha hapos) n K) (Q : ClosedPartition n)
    (hmin : ∀ P : ClosedPartition n,
      Q.gridCost (variableMeanWeight a ha hapos) ≤ P.gridCost (variableMeanWeight a ha hapos)) :
    1 / K + Q.gridCost (variableMeanWeight a ha hapos) ≤ E.meanCost := by
  have he := variable_mean_grid_deficit hK E Q
  have hs := meanStrengthLoss_nonneg K E.strength E.partition.width E.strength_pos
  have hp : 0 ≤ 2 * ∑ i : Fin n, E.partition.width i *
      ∫ t in weightedCDFMidpoint E.partition.width i..E.geometry.site i,
        (variableMeanWeight a ha hapos).value t * (t - weightedCDFMidpoint E.partition.width i) :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (E.partition.width_pos i).le (weightedCDF_oriented_nonneg _
        (weightedCDFMidpoint_mem E.partition i) (E.variable_site_mem i))))
  have hg := hmin E.partition.closed
  linarith

theorem variable_mean_grid_eq_iff (hK : 0 < K)
    (E : IntervalDesign (variableUnitMedium a ha hapos) n K) (Q : ClosedPartition n)
    (hmin : ∀ P : ClosedPartition n,
      Q.gridCost (variableMeanWeight a ha hapos) ≤ P.gridCost (variableMeanWeight a ha hapos)) :
    E.meanCost = 1 / K + Q.gridCost (variableMeanWeight a ha hapos) ↔
      (∀ i, E.partition.width i = E.strength i / K) ∧
      (∀ i, E.geometry.site i = weightedCDFMidpoint E.partition.width i) ∧
      E.partition.closed.gridCost (variableMeanWeight a ha hapos) =
        Q.gridCost (variableMeanWeight a ha hapos) := by
  have he := variable_mean_energy E
  have hs := meanStrengthLoss_identity E.strength E.partition.width (ne_of_gt hK)
    (fun i => ne_of_gt (E.strength_pos i)) E.strength_sum E.partition.width_sum
  have hsn := meanStrengthLoss_nonneg K E.strength E.partition.width E.strength_pos
  have hpn := weightedCDFScore_canonical_le (variableMeanWeight a ha hapos) E.partition
    E.geometry.site E.variable_site_mem
  have hg := hmin E.partition.closed
  have hbridge := E.partition.gridCost_eq_weightedCDFScore (variableMeanWeight a ha hapos)
  constructor
  · intro hcost
    have hs0 : meanStrengthLoss K E.strength E.partition.width = 0 := by linarith
    have hp0 : weightedCDFScore (variableMeanWeight a ha hapos) E.partition.width E.geometry.site =
        weightedCDFScore (variableMeanWeight a ha hapos) E.partition.width
          (weightedCDFMidpoint E.partition.width) := by linarith
    refine ⟨(meanStrengthLoss_eq_zero_iff K E.strength E.partition.width E.strength_pos).mp hs0,
      (weightedCDFScore_eq_canonical_iff _ E.partition _ E.variable_site_mem).mp hp0, ?_⟩
    linarith
  · rintro ⟨hstrength, hposition, hgrid⟩
    have hs0 := (meanStrengthLoss_eq_zero_iff K E.strength E.partition.width E.strength_pos).mpr hstrength
    have hp0 := (weightedCDFScore_eq_canonical_iff (variableMeanWeight a ha hapos)
      E.partition E.geometry.site E.variable_site_mem).mpr hposition
    linarith

end TimeTraps.Interval
