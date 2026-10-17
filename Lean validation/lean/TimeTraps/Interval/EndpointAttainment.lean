module

public import TimeTraps.Interval.EndpointReconstructionEquation
public import TimeTraps.Interval.EndpointDesignBound

@[expose] public section

/-! Every strict mixed partition has an actual physical realization at
its scalar root, with exactly that absorption partition. Consequently
the independent physical minimax problem attains the scalar minimum. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis
open scoped BigOperators

theorem IntervalMedium.endpointPartition_activeShare (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {K M : ℝ}
    (hM : ∀ i, A.barrier Q.closed B.cellWeight i < M)
    (hroot : budget Finset.univ Q.width (A.barrier Q.closed B.cellWeight) M = K / B.source.mass)
    (i : Fin A.count) :
    (B.endpointPartitionReactions A Q hM hroot).activeShare (B.endpointPartitionGeometry A Q)
      (B.endpointPartitionState A Q M) i = Q.width i := by
  unfold EndpointReactions.activeShare
  rw [B.endpointPartitionReactions_active, B.endpointPartitionStrength_reaction A Q hM i]
  exact mul_div_cancel_left₀ _ (ne_of_gt B.source.mass_pos)

theorem IntervalMedium.endpointPartition_partition (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {K M : ℝ}
    (hM : ∀ i, A.barrier Q.closed B.cellWeight i < M)
    (hroot : budget Finset.univ Q.width (A.barrier Q.closed B.cellWeight) M = K / B.source.mass) :
    (B.endpointPartition_weak_equation A Q hM hroot).partition = Q := by
  have hs : (B.endpointPartitionReactions A Q hM hroot).activeShare (B.endpointPartitionGeometry A Q)
      (B.endpointPartitionState A Q M) = Q.width := funext (B.endpointPartition_activeShare A Q hM hroot)
  have hp : (B.endpointPartition_weak_equation A Q hM hroot).partition.point = Q.point := by
    funext e
    rw [EndpointWeakEquation.partition_point, hs, Q.prefix_width]
  generalize (B.endpointPartition_weak_equation A Q hM hroot).partition = P at hp ⊢
  cases P
  cases Q
  congr

noncomputable def IntervalMedium.endpointPartitionDesign (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {K : ℝ} (hK : 0 < K) :
    EndpointPhysicalDesign A B K where
  geometry := B.endpointPartitionGeometry A Q
  medium_eq := B.endpointPartitionGeometry_medium A Q
  reactions := B.endpointPartitionReactions A Q
    (A.root_spec Q.closed B.cellWeight (div_pos hK B.source.mass_pos)).1
    (A.root_spec Q.closed B.cellWeight (div_pos hK B.source.mass_pos)).2
  state := B.endpointPartitionState A Q (A.root Q.closed B.cellWeight (div_pos hK B.source.mass_pos))
  equation := B.endpointPartition_weak_equation A Q
    (A.root_spec Q.closed B.cellWeight (div_pos hK B.source.mass_pos)).1
    (A.root_spec Q.closed B.cellWeight (div_pos hK B.source.mass_pos)).2

theorem IntervalMedium.endpointPartitionDesign_cost (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {K : ℝ} (hK : 0 < K) :
    (B.endpointPartitionDesign A Q hK).cost = A.root Q.closed B.cellWeight (div_pos hK B.source.mass_pos) :=
  B.endpointPartition_norm A Q
    (A.root_spec Q.closed B.cellWeight (div_pos hK B.source.mass_pos)).1
    (A.root_spec Q.closed B.cellWeight (div_pos hK B.source.mass_pos)).2

theorem IntervalMedium.endpointPartitionDesign_partition (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {K : ℝ} (hK : 0 < K) :
    (B.endpointPartitionDesign A Q hK).partition = Q :=
  B.endpointPartition_partition A Q
    (A.root_spec Q.closed B.cellWeight (div_pos hK B.source.mass_pos)).1
    (A.root_spec Q.closed B.cellWeight (div_pos hK B.source.mass_pos)).2

/-- The construction realizes every strict mixed partition in the independent
full-H1 physical admissible class, including endpoint-only architectures. -/
theorem endpoint_partition_attainment (A : EndpointArchitecture) (B : IntervalMedium)
    (Q : StrictPartition A.count) {K : ℝ} (hK : 0 < K) :
    ∃ E : EndpointPhysicalDesign A B K, E.partition = Q ∧
      E.cost = A.root Q.closed B.cellWeight (div_pos hK B.source.mass_pos) :=
  ⟨B.endpointPartitionDesign A Q hK, B.endpointPartitionDesign_partition A Q hK,
    B.endpointPartitionDesign_cost A Q hK⟩

theorem endpoint_physical_minimum_exists (A : EndpointArchitecture) (B : IntervalMedium)
    {K : ℝ} (hK : 0 < K) : ∃ E : EndpointPhysicalDesign A B K, E.Optimal := by
  obtain ⟨Q, hQ⟩ := A.strict_minimum_exists B.cellWeight (div_pos hK B.source.mass_pos)
  refine ⟨B.endpointPartitionDesign A Q hK, ?_⟩
  intro F
  rw [B.endpointPartitionDesign_cost]
  exact (hQ F.partition.closed).trans F.partition_root_bound

theorem endpoint_physical_scalar_minimum (A : EndpointArchitecture) (B : IntervalMedium)
    {K : ℝ} (hK : 0 < K) :
    ∃ Q : StrictPartition A.count,
      IsLeast (range (fun P : ClosedPartition A.count =>
        A.root P B.cellWeight (div_pos hK B.source.mass_pos)))
        (A.root Q.closed B.cellWeight (div_pos hK B.source.mass_pos)) ∧
      IsLeast (range (fun E : EndpointPhysicalDesign A B K => E.cost))
        (A.root Q.closed B.cellWeight (div_pos hK B.source.mass_pos)) := by
  obtain ⟨Q, hQ⟩ := A.strict_minimum_exists B.cellWeight (div_pos hK B.source.mass_pos)
  refine ⟨Q, ⟨⟨Q.closed, rfl⟩, ?_⟩, ⟨⟨B.endpointPartitionDesign A Q hK,
    B.endpointPartitionDesign_cost A Q hK⟩, ?_⟩⟩
  · rintro M ⟨P, rfl⟩
    exact hQ P
  · rintro M ⟨E, rfl⟩
    exact (hQ E.partition.closed).trans E.partition_root_bound

end TimeTraps.Interval
