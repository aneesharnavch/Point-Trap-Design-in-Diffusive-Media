module

public import TimeTraps.Interval.StrictPartition
public import TimeTraps.Interval.DesignLowerBound

@[expose] public section

/-!
Equality in the actual-design budget bound forces every local height loss
and the complete position/strength reconstruction. This is the equality
mechanism needed by the later global optimizer theorem.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {n : ℕ}

noncomputable def WeakIntervalEquation.partition {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i) :
    StrictPartition n where
  point := D.statePartition κ w
  strictMono := hw.statePartition_strictMono hκ
  first := D.statePartition_first κ w
  last := hw.statePartition_last

theorem WeakIntervalEquation.partition_width {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i) (i : Fin n) :
    (hw.partition hκ).width i = D.stateShare κ w i := by
  change absorptionPrefix (D.stateShare κ w) i.succ - absorptionPrefix (D.stateShare κ w) i.castSucc = _
  rw [absorptionPrefix_succ]
  ring

theorem WeakIntervalEquation.partition_barrier {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i) (i : Fin n) :
    (hw.partition hκ).barrier D.medium.cellWeight i = D.stateBarrier κ w i := rfl

theorem WeakIntervalEquation.budget_equality_loss {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i)
    (hb : budget Finset.univ (D.stateShare κ w) (D.stateBarrier κ w) (D.essentialNorm w) =
      (∑ i, κ i) / D.source.mass) (i : Fin n) :
    D.essentialNorm w - w (D.site i) = D.stateBarrier κ w i := by
  let δ : Fin n → ℝ := fun k => κ k / D.source.mass -
    D.stateShare κ w k / (D.essentialNorm w - D.stateBarrier κ w k)
  have hn : ∀ k, 0 ≤ δ k := fun k => sub_nonneg.mpr (hw.cell_budget_le_strength hκ k)
  have hs : (∑ k, δ k) = 0 := by
    change (∑ k, (κ k / D.source.mass - D.stateShare κ w k /
      (D.essentialNorm w - D.stateBarrier κ w k))) = 0
    rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    change (∑ k, κ k) / D.source.mass -
      budget Finset.univ (D.stateShare κ w) (D.stateBarrier κ w) (D.essentialNorm w) = 0
    rw [hb, sub_self]
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hn k)).mp hs i (Finset.mem_univ i)
  have he : κ i / D.source.mass =
      D.stateShare κ w i / (D.essentialNorm w - D.stateBarrier κ w i) := sub_eq_zero.mp hi
  unfold OrderedMedium.stateShare at he
  field_simp [ne_of_gt D.source.mass_pos,
    ne_of_gt (sub_pos.mpr (hw.barrier_lt_norm hκ i))] at he
  have hl := mul_left_cancel₀ (ne_of_gt (hκ i)) he
  linarith

theorem WeakIntervalEquation.budget_equality_reconstruction {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i)
    (hb : budget Finset.univ (D.stateShare κ w) (D.stateBarrier κ w) (D.essentialNorm w) =
      (∑ i, κ i) / D.source.mass) (i : Fin n) :
    D.site i = D.source.inverse (D.cellWeight.center (D.statePartition κ w i.castSucc)
      (D.statePartition κ w i.succ)) ∧
    κ i = D.source.mass * D.stateShare κ w i / (D.essentialNorm w - D.stateBarrier κ w i) ∧
    D.source.transformed w (D.statePartition κ w i.castSucc) = D.essentialNorm w ∧
    D.source.transformed w (D.statePartition κ w i.succ) = D.essentialNorm w := by
  have hl := hw.budget_equality_loss hκ hb i
  have hg := hw.height_equality hκ i hl
  refine ⟨?_, ?_, hg.2⟩
  · rw [← hg.1]
    exact (D.source.inverse_coordinate (Ioo_subset_Icc_self (D.site_interior i))).symm
  · have hi : D.essentialNorm w - D.stateBarrier κ w i = w (D.site i) := by linarith
    rw [hi]
    unfold OrderedMedium.stateShare
    have hp := hw.positive (fun k => (hκ k).le) ⟨i, hκ i⟩ _ (Ioo_subset_Icc_self (D.site_interior i))
    field_simp [ne_of_gt hp, ne_of_gt D.source.mass_pos]

end TimeTraps.Interval
