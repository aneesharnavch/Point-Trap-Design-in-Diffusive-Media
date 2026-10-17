module

public import TimeTraps.Interval.PhysicalDesign
public import TimeTraps.Interval.PartitionMinimum

@[expose] public section

/-!
The arbitrary-medium interval optimization theorem. Both independently
defined sets of values have the same attained least element. Every optimal
physical design is reconstructed from a minimizing strict partition, and
every such reconstruction is optimal.
-/

namespace TimeTraps.Interval

open Set
open scoped BigOperators

variable {n : ℕ} {A : IntervalMedium} {K : ℝ}

def IntervalDesign.Optimal (D : IntervalDesign A n K) : Prop :=
  ∀ E : IntervalDesign A n K, D.cost ≤ E.cost

theorem IntervalDesign.optimal_iff_isLeast (D : IntervalDesign A n K) :
    D.Optimal ↔ IsLeast (range (fun E : IntervalDesign A n K => E.cost)) D.cost := by
  constructor
  · intro hD
    refine ⟨⟨D, rfl⟩, ?_⟩
    rintro M ⟨E, rfl⟩
    exact hD E
  · intro hD E
    exact hD.2 ⟨E, rfl⟩

/-- Equality of the two attained minima in the arbitrary-medium theorem.
The left value set uses all admissible physical weak designs. -/
theorem IntervalMedium.global_minimum (A : IntervalMedium) (hn : 0 < n)
    {K : ℝ} (hK : 0 < K) :
    ∃ Q : StrictPartition n,
      IsLeast (range (fun P : StrictPartition n =>
        P.closed.root A.cellWeight (div_pos hK A.source.mass_pos)))
        (Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos)) ∧
      IsLeast (range (fun D : IntervalDesign A n K => D.cost))
        (Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos)) := by
  obtain ⟨Q, hQ⟩ := StrictPartition.minimum_exists A.cellWeight hn (div_pos hK A.source.mass_pos)
  refine ⟨Q, ⟨⟨Q, rfl⟩, ?_⟩, ⟨⟨A.construct Q hK, A.construct_cost Q hK⟩, ?_⟩⟩
  · rintro M ⟨P, rfl⟩
    exact hQ P.closed
  · rintro M ⟨D, rfl⟩
    exact (hQ D.partition.closed).trans (D.partition_root_lower_bound hK)

theorem IntervalMedium.construct_optimal (A : IntervalMedium) (Q : StrictPartition n)
    {K : ℝ} (hK : 0 < K)
    (hQ : ∀ P : StrictPartition n,
      Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos) ≤
        P.closed.root A.cellWeight (div_pos hK A.source.mass_pos)) :
    (A.construct Q hK).Optimal := by
  intro D
  rw [A.construct_cost Q hK]
  exact (hQ D.partition).trans (D.partition_root_lower_bound hK)

theorem IntervalDesign.optimal_root_eq_cost (D : IntervalDesign A n K)
    (hK : 0 < K) (hD : D.Optimal) :
    D.partition.closed.root A.cellWeight (div_pos hK A.source.mass_pos) = D.cost := by
  apply le_antisymm (D.partition_root_lower_bound hK)
  simpa only [A.construct_cost] using hD (A.construct D.partition hK)

theorem IntervalDesign.optimal_partition (D : IntervalDesign A n K)
    (hK : 0 < K) (hD : D.Optimal) (P : StrictPartition n) :
    D.partition.closed.root A.cellWeight (div_pos hK A.source.mass_pos) ≤
      P.closed.root A.cellWeight (div_pos hK A.source.mass_pos) := by
  rw [D.optimal_root_eq_cost hK hD]
  simpa only [A.construct_cost] using hD (A.construct P hK)

theorem IntervalDesign.optimal_budget_equality (D : IntervalDesign A n K)
    (hK : 0 < K) (hD : D.Optimal) :
    budget Finset.univ (D.geometry.stateShare D.strength D.state)
      (D.geometry.stateBarrier D.strength D.state) D.cost = (∑ i, D.strength i) / D.geometry.source.mass := by
  have h := (D.partition.closed.root_spec A.cellWeight (div_pos hK A.source.mass_pos)).2
  rw [D.optimal_root_eq_cost hK hD, funext D.partition_width, funext D.partition_barrier] at h
  rw [D.strength_sum, D.source_mass]
  exact h

/-- Optimality forces the complete position and strength formulas for the
design's own absorption partition, which is itself minimizing. -/
theorem IntervalDesign.optimal_parameters (D : IntervalDesign A n K)
    (hK : 0 < K) (hD : D.Optimal) (i : Fin n) :
    D.geometry.site i = A.partitionSites D.partition i ∧
      D.strength i = A.partitionStrength D.partition
        (D.partition.closed.root A.cellWeight (div_pos hK A.source.mass_pos)) i := by
  have hr := D.equation.budget_equality_reconstruction D.strength_pos (D.optimal_budget_equality hK hD) i
  have hs : A.source = D.geometry.source := (congrArg IntervalMedium.source D.medium_eq).symm
  have hW : A.cellWeight = D.geometry.cellWeight := D.cellWeight_eq.symm
  constructor
  · change D.geometry.site i = A.source.inverse
      (A.cellWeight.center (D.partition.point i.castSucc) (D.partition.point i.succ))
    rw [hs, hW]
    exact hr.1
  · change D.strength i = A.source.mass * D.partition.closed.width i /
      (D.partition.closed.root A.cellWeight (div_pos hK A.source.mass_pos) - D.partition.closed.barrier A.cellWeight i)
    rw [D.optimal_root_eq_cost hK hD, D.partition_width, D.partition_barrier, ← D.source_mass]
    exact hr.2.1

/-- Complete optimizer characterization, in both directions. Admissibility
and the objective were defined before the reconstruction formulas. -/
theorem IntervalDesign.optimal_iff_reconstruction (D : IntervalDesign A n K) (hK : 0 < K) :
    D.Optimal ↔ ∃ Q : StrictPartition n,
      (∀ P : StrictPartition n,
        Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos) ≤
          P.closed.root A.cellWeight (div_pos hK A.source.mass_pos)) ∧
      (∀ i, D.geometry.site i = A.partitionSites Q i) ∧
      (∀ i, D.strength i = A.partitionStrength Q
        (Q.closed.root A.cellWeight (div_pos hK A.source.mass_pos)) i) := by
  constructor
  · intro hD
    exact ⟨D.partition, D.optimal_partition hK hD,
      fun i => (D.optimal_parameters hK hD i).1, fun i => (D.optimal_parameters hK hD i).2⟩
  · rintro ⟨Q, hQ, hx, hκ⟩
    have he : D.cost = (A.construct Q hK).cost := by
      apply D.cost_eq_of_parameters
      · intro i
        exact (hx i).trans (A.construct_sites Q hK i).symm
      · exact funext (fun i => (hκ i).trans (A.construct_strength Q hK i).symm)
    intro E
    rw [he]
    exact A.construct_optimal Q hK hQ E

end TimeTraps.Interval
