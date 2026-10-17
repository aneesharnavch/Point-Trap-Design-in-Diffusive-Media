module

public import TimeTraps.Interval.SourceMeanPullbackOptimality
public import TimeTraps.Interval.ReversibleMean

@[expose] public section

/-! The deterministic reversible mean theorem: actual attained minimum,
physical reconstruction from every minimizing grid, existence, and the
complete optimizer converse. No stochastic interpretation is a premise. -/

namespace TimeTraps.Interval

open Set MeasureTheory

variable {n : ℕ} {K : ℝ} {a π : ℝ → ℝ}
  {ha : ContinuousOn a (Icc (0 : ℝ) 1)} {hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < a x}
  {hπ : ContinuousOn π (Icc (0 : ℝ) 1)} {hπpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < π x}

theorem reversible_mean_minimum (hK : 0 < K) (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1)
    (Q : StrictPartition n)
    (hmin : ∀ P : ClosedPartition n,
      Q.closed.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight ≤
        P.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight) :
    IsLeast (range (fun E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K =>
      reversibleMeanCost π E.state))
      (1 / K + Q.closed.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight) := by
  have he := source_mean_minimum hK Q hmin
  have hc : (fun E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K => E.sourceMeanCost) =
      (fun E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K =>
        reversibleMeanCost π E.state) := funext (reversible_mean_objective hπmass)
  rw [hc, reversibleUnitMedium_mass hπmass] at he
  exact he

theorem reversible_mean_reconstruction (hK : 0 < K) (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1)
    (Q : StrictPartition n)
    (hmin : ∀ P : ClosedPartition n,
      Q.closed.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight ≤
        P.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight) :
    ∃ E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K,
      (∀ i, E.strength i = K * Q.width i) ∧
      (∀ i, E.geometry.site i = (reversibleUnitMedium a π ha hapos hπ hπpos).source.inverse
        (weightedCDFMidpoint Q.width i)) ∧
      reversibleMeanCost π E.state =
        1 / K + Q.closed.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight := by
  let A := reversibleUnitMedium a π ha hapos hπ hπpos
  refine ⟨sourceMeanDesign A Q K hK hmin, sourceMeanDesign_strength A Q K hK hmin,
    sourceMeanDesign_site A Q K hK hmin, ?_⟩
  have he := sourceMeanDesign_mean A Q K hK hmin
  rw [reversible_mean_objective hπmass, reversibleUnitMedium_mass hπmass] at he
  exact he

theorem reversible_mean_optimal_exists (hn : 0 < n) (hK : 0 < K)
    (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1) :
    ∃ E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K,
      ∀ F : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K,
        reversibleMeanCost π E.state ≤ reversibleMeanCost π F.state := by
  obtain ⟨E, hE⟩ := source_mean_optimal_exists (A := reversibleUnitMedium a π ha hapos hπ hπpos) hn hK
  refine ⟨E, ?_⟩
  intro F
  have h := hE F
  simpa only [reversible_mean_objective hπmass] using h

theorem reversible_mean_optimal_iff (hK : 0 < K) (hπmass : (∫ x in (0 : ℝ)..1, π x) = 1)
    (E : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K) :
    (∀ F : IntervalDesign (reversibleUnitMedium a π ha hapos hπ hπpos) n K,
      reversibleMeanCost π E.state ≤ reversibleMeanCost π F.state) ↔
      (∀ i, E.strength i = K * E.partition.width i) ∧
      (∀ i, E.geometry.site i = (reversibleUnitMedium a π ha hapos hπ hπpos).source.inverse
        (weightedCDFMidpoint E.partition.width i)) ∧
      (∀ P : ClosedPartition n,
        E.partition.closed.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight ≤
          P.gridCost (reversibleUnitMedium a π ha hapos hπ hπpos).cellWeight) := by
  have he := source_mean_optimal_iff hK E
  unfold IntervalDesign.SourceMeanOptimal at he
  simpa only [reversible_mean_objective hπmass] using he

end TimeTraps.Interval
