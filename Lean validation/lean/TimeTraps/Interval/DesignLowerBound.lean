module

public import TimeTraps.Interval.WeakConsequences
public import TimeTraps.Interval.BudgetRoot

@[expose] public section

/-!
The lower-bound direction of the interval optimization theorem for every
physical weak state: its actual absorption partition gives a scalar budget
root no greater than its physical essential norm. No optimal profile is
assumed or defined into the design.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {n : ℕ}

noncomputable def OrderedMedium.stateBarrier (D : OrderedMedium n) (κ : Fin n → ℝ)
    (w : ℝ → ℝ) (i : Fin n) : ℝ :=
  D.cellWeight.barrier (D.statePartition κ w i.castSucc) (D.statePartition κ w i.succ)

theorem WeakIntervalEquation.barrier_lt_norm {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i) (i : Fin n) :
    D.stateBarrier κ w i < D.essentialNorm w := by
  have hb := hw.height_barrier hκ i
  have hp := hw.positive (fun k => (hκ k).le) ⟨i, hκ i⟩ _ (Ioo_subset_Icc_self (D.site_interior i))
  change D.stateBarrier κ w i ≤ D.essentialNorm w - w (D.site i) at hb
  linarith

theorem WeakIntervalEquation.cell_budget_le_strength {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i) (i : Fin n) :
    D.stateShare κ w i / (D.essentialNorm w - D.stateBarrier κ w i) ≤ κ i / D.source.mass := by
  have hp := hw.positive (fun k => (hκ k).le) ⟨i, hκ i⟩ _ (Ioo_subset_Icc_self (D.site_interior i))
  have hb : w (D.site i) ≤ D.essentialNorm w - D.stateBarrier κ w i := by
    have hb := hw.height_barrier hκ i
    change D.stateBarrier κ w i ≤ D.essentialNorm w - w (D.site i) at hb
    linarith
  calc
    D.stateShare κ w i / (D.essentialNorm w - D.stateBarrier κ w i) ≤
        D.stateShare κ w i / w (D.site i) :=
      div_le_div_of_nonneg_left (hw.stateShare_pos hκ i).le hp hb
    _ = κ i / D.source.mass := by
      unfold OrderedMedium.stateShare
      field_simp [ne_of_gt hp]

theorem WeakIntervalEquation.physical_budget_bound {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i) :
    budget Finset.univ (D.stateShare κ w) (D.stateBarrier κ w) (D.essentialNorm w) ≤
      (∑ i, κ i) / D.source.mass := by
  unfold budget
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun i _ => hw.cell_budget_le_strength hκ i)

theorem WeakIntervalEquation.partition_root_lower_bound {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i)
    (hn : 0 < n) {T : ℝ}
    (hT : budget Finset.univ (D.stateShare κ w) (D.stateBarrier κ w) T =
      (∑ i, κ i) / D.source.mass) : T ≤ D.essentialNorm w := by
  exact root_le_of_budget_le Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (D.stateShare κ w) (D.stateBarrier κ w) (fun i _ => hw.stateShare_pos hκ i)
    (fun i _ => hw.barrier_lt_norm hκ i) hT (hw.physical_budget_bound hκ)

theorem WeakIntervalEquation.partition_root_existsUnique {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 < κ i)
    (hn : 0 < n) :
    ∃! T : ℝ, (∀ i, D.stateBarrier κ w i < T) ∧
      budget Finset.univ (D.stateShare κ w) (D.stateBarrier κ w) T = (∑ i, κ i) / D.source.mass ∧
      T ≤ D.essentialNorm w := by
  have hs : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hK : 0 < ∑ i, κ i := Finset.sum_pos (fun i _ => hκ i) hs
  obtain ⟨T, hT, hu⟩ := budget_root_existsUnique Finset.univ hs
    (D.stateShare κ w) (D.stateBarrier κ w) (fun i _ => hw.stateShare_pos hκ i)
    (div_pos hK D.source.mass_pos)
  refine ⟨T, ⟨fun i => hT.1 i (Finset.mem_univ i), hT.2,
    hw.partition_root_lower_bound hκ hn hT.2⟩, ?_⟩
  intro M hM
  exact hu M ⟨fun i _ => hM.1 i, hM.2.1⟩

end TimeTraps.Interval
