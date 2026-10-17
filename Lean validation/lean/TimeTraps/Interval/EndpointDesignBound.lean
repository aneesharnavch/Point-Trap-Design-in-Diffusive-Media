module

public import TimeTraps.Interval.EndpointHeightBarrier
public import TimeTraps.Interval.EndpointPartitionMinimum

@[expose] public section

/-! The physical lower-bound direction: every endpoint weak state's
actual positive absorption partition has mixed harmonic root at most its
physical essential norm. No physical reconstruction or attainment is
assumed in the objective or the comparison. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis
open scoped BigOperators

variable {A : EndpointArchitecture} {K : ℝ}

theorem EndpointWeakEquation.mixed_barrier_lt_norm {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) (i : Fin A.count) :
    A.barrier hw.partition.closed D.medium.cellWeight i < D.essentialNorm w := by
  have hb := hw.mixed_height_barrier i
  have hp := hw.positive _ (A.physicalSite_mem D i)
  linarith

theorem EndpointWeakEquation.mixed_cell_budget_le_strength {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) (i : Fin A.count) :
    R.activeShare D w i / (D.essentialNorm w - A.barrier hw.partition.closed D.medium.cellWeight i) ≤
      R.activeStrength i / D.source.mass := by
  have hp := hw.positive _ (A.physicalSite_mem D i)
  have hb : w (A.physicalSite D i) ≤
      D.essentialNorm w - A.barrier hw.partition.closed D.medium.cellWeight i := by
    have hh := hw.mixed_height_barrier i
    linarith
  calc
    _ ≤ R.activeShare D w i / w (A.physicalSite D i) :=
      div_le_div_of_nonneg_left (hw.activeShare_pos i).le hp hb
    _ = _ := by
      unfold EndpointReactions.activeShare
      field_simp [ne_of_gt hp]

theorem EndpointWeakEquation.mixed_physical_budget_bound {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) :
    budget Finset.univ (R.activeShare D w) (A.barrier hw.partition.closed D.medium.cellWeight)
      (D.essentialNorm w) ≤ K / D.source.mass := by
  calc
    _ ≤ ∑ i, R.activeStrength i / D.source.mass :=
      Finset.sum_le_sum (fun i _ => hw.mixed_cell_budget_le_strength i)
    _ = _ := by rw [← Finset.sum_div, R.activeStrength_sum]

theorem EndpointWeakEquation.partition_root_lower_bound {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) :
    A.root hw.partition.closed D.medium.cellWeight (div_pos R.budget_pos D.source.mass_pos) ≤
      D.essentialNorm w := by
  have hs := (A.root_spec hw.partition.closed D.medium.cellWeight
    (div_pos R.budget_pos D.source.mass_pos)).2
  have hwidth : hw.partition.closed.width = R.activeShare D w := funext hw.partition_width
  rw [hwidth] at hs
  exact root_le_of_budget_le Finset.univ ⟨⟨0, A.count_pos⟩, Finset.mem_univ _⟩
    (R.activeShare D w) (A.barrier hw.partition.closed D.medium.cellWeight)
    (fun i _ => hw.activeShare_pos i) (fun i _ => hw.mixed_barrier_lt_norm i)
    hs hw.mixed_physical_budget_bound

noncomputable def EndpointPhysicalDesign.partition {B : IntervalMedium}
    (E : EndpointPhysicalDesign A B K) : StrictPartition A.count := E.equation.partition

theorem EndpointPhysicalDesign.partition_root_bound {B : IntervalMedium}
    (E : EndpointPhysicalDesign A B K) :
    A.root E.partition.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) ≤ E.cost := by
  have hs : E.geometry.source = B.source := congrArg IntervalMedium.source E.medium_eq
  simpa only [partition, cost, E.medium_eq, hs] using E.equation.partition_root_lower_bound

/-- A minimizing mixed scalar partition supplies a lower bound for every
physical design. This does not assert that a physical design attains it. -/
theorem endpoint_physical_lower_bound_exists (A : EndpointArchitecture) (B : IntervalMedium)
    {K : ℝ} (hK : 0 < K) :
    ∃ Q : StrictPartition A.count, ∀ E : EndpointPhysicalDesign A B K,
      A.root Q.closed B.cellWeight (div_pos hK B.source.mass_pos) ≤ E.cost := by
  obtain ⟨Q, hQ⟩ := A.strict_minimum_exists B.cellWeight (div_pos hK B.source.mass_pos)
  exact ⟨Q, fun E => (hQ E.partition.closed).trans E.partition_root_bound⟩

end TimeTraps.Interval
