module

public import TimeTraps.Interval.PartitionState
public import TimeTraps.Interval.BudgetRoot

@[expose] public section

/-!
Attainment for every strict source partition. Strengths are reconstructed
from the already proved trap values, and the original weak equation and
physical essential norm are verified for the constructed state.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ}

noncomputable def IntervalMedium.partitionStrength (A : IntervalMedium) (Q : StrictPartition n)
    (M : ℝ) (i : Fin n) : ℝ := A.source.mass * Q.width i / (M - Q.barrier A.cellWeight i)

theorem IntervalMedium.partitionStrength_pos (A : IntervalMedium) (Q : StrictPartition n)
    {M : ℝ} (hM : ∀ i, Q.barrier A.cellWeight i < M) (i : Fin n) :
    0 < A.partitionStrength Q M i :=
  reconstructed_strength_pos A.source.mass_pos (Q.width_pos i) (hM i)

theorem IntervalMedium.partitionStrength_reaction (A : IntervalMedium) (Q : StrictPartition n)
    {M : ℝ} (hM : ∀ i, Q.barrier A.cellWeight i < M) (i : Fin n) :
    A.partitionStrength Q M i * A.partitionState Q M ((A.partitionDesign Q).site i) =
      A.source.mass * Q.width i := by
  rw [A.partitionState_trap]
  exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr (hM i)))

theorem IntervalMedium.partitionFlux_tail (A : IntervalMedium) (Q : StrictPartition n)
    (e : Fin (n + 1)) : A.partitionFlux Q e 0 =
      A.source.mass * (Q.point e - A.source.coordinate ((A.partitionDesign Q).node e.castSucc)) := by
  simp only [IntervalMedium.partitionFlux, add_zero]

theorem IntervalMedium.partitionFlux_head (A : IntervalMedium) (Q : StrictPartition n)
    (e : Fin (n + 1)) : A.partitionFlux Q e ((A.partitionDesign Q).gapLength e) =
      A.source.mass * (Q.point e - A.source.coordinate ((A.partitionDesign Q).node e.succ)) := by
  simp only [IntervalMedium.partitionFlux, OrderedMedium.gapLength, add_sub_cancel]

theorem IntervalMedium.partitionFlux_reflecting (A : IntervalMedium) (Q : StrictPartition n) :
    A.partitionFlux Q 0 0 = 0 ∧
      A.partitionFlux Q (Fin.last n) ((A.partitionDesign Q).gapLength (Fin.last n)) = 0 := by
  constructor
  · rw [A.partitionFlux_tail, Q.first]
    change A.source.mass * (0 - A.source.coordinate ((A.partitionDesign Q).node 0)) = 0
    rw [(A.partitionDesign Q).node_first]
    change A.source.mass * (0 - A.source.coordinate A.source.left) = 0
    rw [A.source.coordinate_left]
    ring
  · rw [A.partitionFlux_head, Q.last]
    change A.source.mass * (1 - A.source.coordinate ((A.partitionDesign Q).node (Fin.last (n + 1)))) = 0
    rw [(A.partitionDesign Q).node_last]
    change A.source.mass * (1 - A.source.coordinate A.source.right) = 0
    rw [A.source.coordinate_right]
    ring

theorem IntervalMedium.partitionFlux_jump (A : IntervalMedium) (Q : StrictPartition n) (i : Fin n) :
    A.partitionFlux Q i.succ 0 - A.partitionFlux Q i.castSucc ((A.partitionDesign Q).gapLength i.castSucc) =
      A.source.mass * Q.width i := by
  rw [A.partitionFlux_tail, A.partitionFlux_head]
  change A.source.mass * (Q.point i.succ - A.source.coordinate ((A.partitionDesign Q).site i)) -
    A.source.mass * (Q.point i.castSucc - A.source.coordinate ((A.partitionDesign Q).site i)) =
      A.source.mass * (Q.point i.succ - Q.point i.castSucc)
  ring

theorem IntervalMedium.partition_graph_equation (A : IntervalMedium) (Q : StrictPartition n)
    {M : ℝ} (hM : ∀ i, Q.barrier A.cellWeight i < M) :
    GraphEquation (A.partitionDesign Q).graph (nodalStrength (A.partitionStrength Q M))
      (fun v => A.partitionState Q M ((A.partitionDesign Q).node v))
      ((A.partitionDesign Q).gapRestriction (A.partitionState Q M)) (A.partitionFlux Q) := by
  refine ⟨A.partition_edge_equation Q M, ?_, ?_, ?_⟩
  · intro e
    change A.partitionState Q M ((A.partitionDesign Q).node e.castSucc + 0) = _
    rw [add_zero]
    rfl
  · intro e
    change A.partitionState Q M ((A.partitionDesign Q).node e.castSucc +
      ((A.partitionDesign Q).node e.succ - (A.partitionDesign Q).node e.castSucc)) = _
    rw [add_sub_cancel]
    rfl
  · intro v
    change nodalStrength (A.partitionStrength Q M) v * A.partitionState Q M ((A.partitionDesign Q).node v) =
      vertexFlux Fin.castSucc Fin.succ _ _ v
    refine Fin.cases ?_ (fun k => ?_) v
    · rw [nodalStrength_first, zero_mul, path_flux_first, (A.partitionFlux_reflecting Q).1]
    · refine Fin.lastCases ?_ (fun i => ?_) k
      · change nodalStrength (A.partitionStrength Q M) (Fin.last (n + 1)) * _ =
          vertexFlux Fin.castSucc Fin.succ _ _ (Fin.last (n + 1))
        rw [nodalStrength_last, zero_mul, path_flux_last]
        change 0 = -A.partitionFlux Q (Fin.last n) ((A.partitionDesign Q).gapLength (Fin.last n))
        rw [(A.partitionFlux_reflecting Q).2, neg_zero]
      · change nodalStrength (A.partitionStrength Q M) (trapNode i) *
          A.partitionState Q M ((A.partitionDesign Q).site i) =
            vertexFlux Fin.castSucc Fin.succ _ _ (trapNode i)
        rw [nodalStrength_trap, path_flux_trap, A.partitionStrength_reaction Q hM i]
        exact (A.partitionFlux_jump Q i).symm

theorem IntervalMedium.partition_weak_equation (A : IntervalMedium) (Q : StrictPartition n)
    {M : ℝ} (hM : ∀ i, Q.barrier A.cellWeight i < M) :
    WeakIntervalEquation (A.partitionDesign Q) (A.partitionStrength Q M) (A.partitionState Q M) :=
  (A.partitionDesign Q).weak_of_strong (A.partition_graph_equation Q hM)

theorem IntervalMedium.partition_stateShare (A : IntervalMedium) (Q : StrictPartition n)
    {M : ℝ} (hM : ∀ i, Q.barrier A.cellWeight i < M) (i : Fin n) :
    (A.partitionDesign Q).stateShare (A.partitionStrength Q M) (A.partitionState Q M) i = Q.width i := by
  change (A.partitionStrength Q M i * A.partitionState Q M ((A.partitionDesign Q).site i)) /
    A.source.mass = Q.width i
  rw [A.partitionStrength_reaction Q hM i]
  exact mul_div_cancel_left₀ _ (ne_of_gt A.source.mass_pos)

theorem IntervalMedium.partition_statePartition (A : IntervalMedium) (Q : StrictPartition n)
    {M : ℝ} (hM : ∀ i, Q.barrier A.cellWeight i < M) (e : Fin (n + 1)) :
    (A.partitionDesign Q).statePartition (A.partitionStrength Q M) (A.partitionState Q M) e = Q.point e := by
  have he : (A.partitionDesign Q).stateShare (A.partitionStrength Q M) (A.partitionState Q M) = Q.width :=
    funext (A.partition_stateShare Q hM)
  rw [OrderedMedium.statePartition, he, Q.prefix_width]

theorem IntervalMedium.partition_norm (A : IntervalMedium) (Q : StrictPartition n)
    {M : ℝ} (hM : ∀ i, Q.barrier A.cellWeight i < M) :
    (A.partitionDesign Q).essentialNorm (A.partitionState Q M) = M := by
  have hw := A.partition_weak_equation Q hM
  have hκ := A.partitionStrength_pos Q hM
  have hm := hw.essentialNorm_isGreatest (fun i => (hκ i).le) ⟨⟨0, Q.size_pos⟩, hκ ⟨0, Q.size_pos⟩⟩
  apply le_antisymm
  · obtain ⟨x, hx, he⟩ := hm.1
    rw [← he]
    exact A.partitionState_le Q M hx
  · apply hm.2
    exact ⟨A.source.left, ⟨le_rfl, A.source.increasing.le⟩, A.partitionState_left Q M⟩

theorem IntervalMedium.partition_strength_budget (A : IntervalMedium) (Q : StrictPartition n)
    {K M : ℝ}
    (hroot : budget Finset.univ Q.width (Q.barrier A.cellWeight) M = K / A.source.mass) :
    (∑ i, A.partitionStrength Q M i) = K := by
  have h := reconstructed_strength_sum Finset.univ Q.width (Q.barrier A.cellWeight)
    (ne_of_gt A.source.mass_pos) hroot
  exact h

/-- Every prescribed strict partition attains its exact scalar-budget height
with positive strengths and the original physical weak equation. -/
theorem IntervalMedium.partition_attainment (A : IntervalMedium) (Q : StrictPartition n)
    {K : ℝ} (hK : 0 < K) :
    ∃ M : ℝ, (∀ i, Q.barrier A.cellWeight i < M) ∧
      budget Finset.univ Q.width (Q.barrier A.cellWeight) M = K / A.source.mass ∧
      (∀ i, 0 < A.partitionStrength Q M i) ∧
      (∑ i, A.partitionStrength Q M i) = K ∧
      WeakIntervalEquation (A.partitionDesign Q) (A.partitionStrength Q M) (A.partitionState Q M) ∧
      (A.partitionDesign Q).essentialNorm (A.partitionState Q M) = M := by
  obtain ⟨M, hM, _⟩ := budget_root_existsUnique Finset.univ
    ⟨⟨0, Q.size_pos⟩, Finset.mem_univ _⟩ Q.width (Q.barrier A.cellWeight)
    (fun i _ => Q.width_pos i) (div_pos hK A.source.mass_pos)
  have hm : ∀ i, Q.barrier A.cellWeight i < M := fun i => hM.1 i (Finset.mem_univ i)
  exact ⟨M, hm, hM.2, A.partitionStrength_pos Q hm, A.partition_strength_budget Q hM.2,
    A.partition_weak_equation Q hm, A.partition_norm Q hm⟩

end TimeTraps.Interval
