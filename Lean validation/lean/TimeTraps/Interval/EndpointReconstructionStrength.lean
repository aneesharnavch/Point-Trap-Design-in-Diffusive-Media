module

public import TimeTraps.Interval.EndpointReconstructionState
public import TimeTraps.Interval.EndpointReconstructionReactions

@[expose] public section

/-! Positive exact-budget physical strengths and their actual reactions
for the analytic mixed profile. The height is the genuine scalar root. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis
open scoped BigOperators Classical

noncomputable def IntervalMedium.endpointPartitionStrength (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ) (i : Fin A.count) : ℝ :=
  B.source.mass * Q.width i / (M - A.barrier Q.closed B.cellWeight i)

theorem IntervalMedium.endpointPartitionStrength_pos (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {M : ℝ}
    (hM : ∀ i, A.barrier Q.closed B.cellWeight i < M) (i : Fin A.count) :
    0 < B.endpointPartitionStrength A Q M i :=
  reconstructed_strength_pos B.source.mass_pos (Q.width_pos i) (hM i)

theorem IntervalMedium.endpointPartitionStrength_reaction (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {M : ℝ}
    (hM : ∀ i, A.barrier Q.closed B.cellWeight i < M) (i : Fin A.count) :
    B.endpointPartitionStrength A Q M i *
      B.endpointPartitionState A Q M (A.physicalSite (B.endpointPartitionGeometry A Q) i) =
        B.source.mass * Q.width i := by
  rw [B.endpointPartitionState_site]
  exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr (hM i)))

theorem IntervalMedium.endpointPartitionStrength_budget (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {K M : ℝ}
    (hroot : budget Finset.univ Q.width (A.barrier Q.closed B.cellWeight) M = K / B.source.mass) :
    (∑ i, B.endpointPartitionStrength A Q M i) = K :=
  reconstructed_strength_sum Finset.univ Q.width (A.barrier Q.closed B.cellWeight)
    (ne_of_gt B.source.mass_pos) hroot

noncomputable def IntervalMedium.endpointPartitionReactions (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {K M : ℝ}
    (hM : ∀ i, A.barrier Q.closed B.cellWeight i < M)
    (hroot : budget Finset.univ Q.width (A.barrier Q.closed B.cellWeight) M = K / B.source.mass) :
    EndpointReactions A K :=
  EndpointReactions.ofActive A (B.endpointPartitionStrength A Q M)
    (B.endpointPartitionStrength_pos A Q hM) (B.endpointPartitionStrength_budget A Q hroot)

theorem IntervalMedium.endpointPartitionReactions_active (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {K M : ℝ}
    (hM : ∀ i, A.barrier Q.closed B.cellWeight i < M)
    (hroot : budget Finset.univ Q.width (A.barrier Q.closed B.cellWeight) M = K / B.source.mass)
    (i : Fin A.count) :
    (B.endpointPartitionReactions A Q hM hroot).activeStrength i = B.endpointPartitionStrength A Q M i :=
  EndpointReactions.ofActive_activeStrength _ _ _ _ _

theorem IntervalMedium.endpointPartitionReaction_nodal (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) {K M : ℝ}
    (hM : ∀ i, A.barrier Q.closed B.cellWeight i < M)
    (hroot : budget Finset.univ Q.width (A.barrier Q.closed B.cellWeight) M = K / B.source.mass)
    (v : Fin (A.interiorCount + 2)) :
    (B.endpointPartitionReactions A Q hM hroot).nodal v *
      B.endpointPartitionState A Q M ((B.endpointPartitionGeometry A Q).node v) =
        B.source.mass * A.activeLift Q.width v := by
  change (EndpointReactions.ofActive _ _ _ _).nodal v * _ = _
  rw [EndpointReactions.ofActive_nodal]
  unfold EndpointArchitecture.activeLift
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : A.activeNode i = v
  · simp only [if_pos hi]
    rw [← hi]
    exact B.endpointPartitionStrength_reaction A Q hM i
  · simp only [if_neg hi, zero_mul, mul_zero]

end TimeTraps.Interval
