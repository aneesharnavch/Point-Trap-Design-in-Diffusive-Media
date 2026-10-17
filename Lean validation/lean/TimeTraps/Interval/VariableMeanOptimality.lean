module

public import TimeTraps.Interval.VariableMeanAttainment
public import TimeTraps.Interval.HomogeneousMeanOptimality

@[expose] public section

/-! The attained variable-conductance mean optimum over independent physical
weak designs. Every optimizer comes from a globally minimizing weighted grid;
no uniqueness of that grid or sufficiency of Lloyd equations is assumed. -/

namespace TimeTraps.Interval

open Set

variable {n : ℕ} {K : ℝ} {a : ℝ → ℝ}
  {ha : ContinuousOn a (Icc (0 : ℝ) 1)}
  {hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x}

theorem variable_mean_minimum (hK : 0 < K) (Q : StrictPartition n)
    (hmin : ∀ P : ClosedPartition n, Q.closed.gridCost (variableMeanWeight a ha hapos) ≤
      P.gridCost (variableMeanWeight a ha hapos)) :
    IsLeast (range (fun E : IntervalDesign (variableUnitMedium a ha hapos) n K => E.meanCost))
      (1 / K + Q.closed.gridCost (variableMeanWeight a ha hapos)) := by
  refine ⟨⟨variableMeanDesign Q a ha hapos K hK hmin,
    variableMeanDesign_mean Q a ha hapos K hK hmin⟩, ?_⟩
  rintro M ⟨E, rfl⟩
  exact variable_mean_grid_lower_bound hK E Q.closed hmin

theorem variable_mean_optimal_iff_cost_eq (hK : 0 < K) (Q : StrictPartition n)
    (hmin : ∀ P : ClosedPartition n, Q.closed.gridCost (variableMeanWeight a ha hapos) ≤
      P.gridCost (variableMeanWeight a ha hapos))
    (E : IntervalDesign (variableUnitMedium a ha hapos) n K) :
    E.MeanOptimal ↔ E.meanCost = 1 / K + Q.closed.gridCost (variableMeanWeight a ha hapos) := by
  constructor
  · intro hE
    exact (E.meanOptimal_iff_isLeast.mp hE).unique (variable_mean_minimum hK Q hmin)
  · intro hE F
    rw [hE]
    exact variable_mean_grid_lower_bound hK F Q.closed hmin

theorem variable_mean_optimal_exists (hn : 0 < n) (hK : 0 < K) :
    ∃ E : IntervalDesign (variableUnitMedium a ha hapos) n K, E.MeanOptimal := by
  obtain ⟨Q, hQ⟩ := StrictPartition.grid_minimum_exists (variableMeanWeight a ha hapos) hn
  exact ⟨variableMeanDesign Q a ha hapos K hK hQ,
    (variable_mean_optimal_iff_cost_eq hK Q hQ _).mpr
      (variableMeanDesign_mean Q a ha hapos K hK hQ)⟩

theorem variable_mean_optimal_iff (hK : 0 < K)
    (E : IntervalDesign (variableUnitMedium a ha hapos) n K) :
    E.MeanOptimal ↔
      (∀ i, E.strength i = K * E.partition.width i) ∧
      (∀ i, E.geometry.site i = weightedCDFMidpoint E.partition.width i) ∧
      (∀ P : ClosedPartition n, E.partition.closed.gridCost (variableMeanWeight a ha hapos) ≤
        P.gridCost (variableMeanWeight a ha hapos)) := by
  constructor
  · intro hE
    obtain ⟨Q, hQ⟩ := StrictPartition.grid_minimum_exists
      (variableMeanWeight a ha hapos) E.partition.size_pos
    have he := (variable_mean_optimal_iff_cost_eq hK Q hQ E).mp hE
    obtain ⟨hκ, hx, hg⟩ := (variable_mean_grid_eq_iff hK E Q.closed hQ).mp he
    refine ⟨?_, hx, ?_⟩
    · intro i
      have hi := (eq_div_iff (ne_of_gt hK)).mp (hκ i)
      linarith
    · intro P
      rw [hg]
      exact hQ P
  · rintro ⟨hκ, hx, hg⟩
    apply (variable_mean_optimal_iff_cost_eq hK E.partition hg E).mpr
    apply (variable_mean_grid_eq_iff hK E E.partition.closed hg).mpr
    refine ⟨?_, hx, rfl⟩
    intro i
    rw [hκ i]
    exact (mul_div_cancel_left₀ _ (ne_of_gt hK)).symm

theorem variable_mean_optimal_state (hK : 0 < K)
    (E : IntervalDesign (variableUnitMedium a ha hapos) n K) (hE : E.MeanOptimal) :
    EqOn E.state (variableGridState E.partition a ha hapos K) (Icc (0 : ℝ) 1) := by
  obtain ⟨hκ, hx, hg⟩ := (variable_mean_optimal_iff hK E).mp hE
  let F := variableMeanDesign E.partition a ha hapos K hK hg
  have hs : ∀ i, E.geometry.site i = F.geometry.site i := by
    intro i
    change E.geometry.site i =
      (variableMeanDesign E.partition a ha hapos K hK hg).geometry.site i
    rw [hx i, variableMeanDesign_site, E.partition.canonicalMidpoint_eq]
  have hk : E.strength = F.strength := by
    funext i
    exact hκ i
  exact E.state_eqOn_of_parameters F hs hk

end TimeTraps.Interval
