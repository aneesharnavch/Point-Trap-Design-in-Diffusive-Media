module

public import TimeTraps.Interval.SourceMeanPullbackAttainment
public import TimeTraps.Interval.WeightedGridMinimum
public import TimeTraps.Interval.HomogeneousMean

@[expose] public section

/-! Attained source-weighted mean optimization over independently defined
physical weak designs. Every optimizer has a globally minimizing cumulative
grid and the prescribed physical parameters; its state is recovered too. -/

namespace TimeTraps.Interval

open Set

variable {n : ℕ} {A : IntervalMedium} {K : ℝ}

def IntervalDesign.SourceMeanOptimal (E : IntervalDesign A n K) : Prop :=
  ∀ F : IntervalDesign A n K, E.sourceMeanCost ≤ F.sourceMeanCost

theorem IntervalDesign.sourceMeanOptimal_iff_isLeast (E : IntervalDesign A n K) :
    E.SourceMeanOptimal ↔
      IsLeast (range (fun F : IntervalDesign A n K => F.sourceMeanCost)) E.sourceMeanCost := by
  constructor
  · intro hE
    refine ⟨⟨E, rfl⟩, ?_⟩
    rintro M ⟨F, rfl⟩
    exact hE F
  · intro hE F
    exact hE.2 ⟨F, rfl⟩

theorem source_mean_minimum (hK : 0 < K) (Q : StrictPartition n)
    (hmin : ∀ P : ClosedPartition n, Q.closed.gridCost A.cellWeight ≤ P.gridCost A.cellWeight) :
    IsLeast (range (fun E : IntervalDesign A n K => E.sourceMeanCost))
      (A.source.mass / K + Q.closed.gridCost A.cellWeight) := by
  refine ⟨⟨sourceMeanDesign A Q K hK hmin, sourceMeanDesign_mean A Q K hK hmin⟩, ?_⟩
  rintro M ⟨E, rfl⟩
  exact source_mean_grid_lower_bound hK E Q.closed hmin

theorem source_mean_optimal_iff_cost_eq (hK : 0 < K) (Q : StrictPartition n)
    (hmin : ∀ P : ClosedPartition n, Q.closed.gridCost A.cellWeight ≤ P.gridCost A.cellWeight)
    (E : IntervalDesign A n K) :
    E.SourceMeanOptimal ↔ E.sourceMeanCost = A.source.mass / K + Q.closed.gridCost A.cellWeight := by
  constructor
  · intro hE
    exact (E.sourceMeanOptimal_iff_isLeast.mp hE).unique (source_mean_minimum hK Q hmin)
  · intro hE F
    rw [hE]
    exact source_mean_grid_lower_bound hK F Q.closed hmin

theorem source_mean_optimal_exists (hn : 0 < n) (hK : 0 < K) :
    ∃ E : IntervalDesign A n K, E.SourceMeanOptimal := by
  obtain ⟨Q, hQ⟩ := StrictPartition.grid_minimum_exists A.cellWeight hn
  exact ⟨sourceMeanDesign A Q K hK hQ,
    (source_mean_optimal_iff_cost_eq hK Q hQ _).mpr (sourceMeanDesign_mean A Q K hK hQ)⟩

theorem source_mean_optimal_iff (hK : 0 < K) (E : IntervalDesign A n K) :
    E.SourceMeanOptimal ↔
      (∀ i, E.strength i = K * E.partition.width i) ∧
      (∀ i, E.geometry.site i = A.source.inverse (weightedCDFMidpoint E.partition.width i)) ∧
      (∀ P : ClosedPartition n, E.partition.closed.gridCost A.cellWeight ≤ P.gridCost A.cellWeight) := by
  constructor
  · intro hE
    obtain ⟨Q, hQ⟩ := StrictPartition.grid_minimum_exists A.cellWeight E.partition.size_pos
    have he := (source_mean_optimal_iff_cost_eq hK Q hQ E).mp hE
    obtain ⟨hκ, hx, hg⟩ := (source_mean_grid_eq_iff hK E Q.closed hQ).mp he
    refine ⟨?_, hx, ?_⟩
    · intro i
      have hi := (eq_div_iff (ne_of_gt hK)).mp (hκ i)
      linarith
    · intro P
      rw [hg]
      exact hQ P
  · rintro ⟨hκ, hx, hg⟩
    apply (source_mean_optimal_iff_cost_eq hK E.partition hg E).mpr
    apply (source_mean_grid_eq_iff hK E E.partition.closed hg).mpr
    refine ⟨?_, hx, rfl⟩
    intro i
    rw [hκ i]
    exact (mul_div_cancel_left₀ _ (ne_of_gt hK)).symm

theorem source_mean_optimal_state (hK : 0 < K) (E : IntervalDesign A n K) (hE : E.SourceMeanOptimal) :
    EqOn E.state (sourceMeanGridState A E.partition K) (Icc A.source.left A.source.right) := by
  obtain ⟨hκ, hx, hg⟩ := (source_mean_optimal_iff hK E).mp hE
  let F := sourceMeanDesign A E.partition K hK hg
  have hs : ∀ i, E.geometry.site i = F.geometry.site i := by
    intro i
    change E.geometry.site i = (sourceMeanDesign A E.partition K hK hg).geometry.site i
    rw [hx i, sourceMeanDesign_site]
  have hk : E.strength = F.strength := by
    funext i
    exact hκ i
  exact E.state_eqOn_of_parameters F hs hk

end TimeTraps.Interval
